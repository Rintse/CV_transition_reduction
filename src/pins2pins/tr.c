#include <limits.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <aux/options.h>
#include <dm/dm.h>
#include <syntax/ltsmin-standard.h>
#include <pins2pins/por.h>
#include <pins2pins/process.h>
#include <pins/pins.h>
#include <pins/pins-util.h>
#include <util/dfs-stack.h>
#include <util/list.h>
#include <util/runtime.h>
#include <util/util.h>
#define MAX_CV_SIZE 64
#define MAX_N_PROCS 16

// TODO: W: geen stack maar constant size buffer voor callbacks
// TODO: O: blokkende processen: teruggeven aan mc?

typedef struct tr_ctx {
    model_t         model;
    size_t          nslots;   // number of variables in state vector
	size_t		    nactions;
	size_t          nguards;
    size_t          nprocs;

    process_t*      procs;
    int*            g2p;
    dfs_stack_t*    queue[2];
    int*            src;

	// Saves the cartesian vectors
    dfs_stack_t***  CVs;
    dfs_stack_t**   tempCVs;

    // For scheduling extensions
    int cur;
    // For keeping track of groups
    int group_start;

    // Temp storage for callback
	dfs_stack_t*    tempstack;
    bool*           extendable;
    bool*           infinite;
    bool*           blocked;
    int             extendable_count;
    // Temp storage for checking non-last commutativity (see commute_nonlast)
    int*            temp3, *res1, *res2;

    // Map groups to procs
    int*            procmap;

    // for callback
    TransitionCB    cb_org;
    void*           ctx_org;
    size_t          emitted;
} tr_context_t;


// Adding groups
// ============================================================================
static matrix_t *
enlarge_matrix (matrix_t *dm, int add_rows, int add_cols)
{
    matrix_t *new = RTmalloc (sizeof(matrix_t));
    dm_create (new, dm_nrows(dm) + add_rows, dm_ncols(dm) + add_cols);
    for (int i = 0; i < dm_nrows (dm); i++) {
        for (int j = 0; j < dm_ncols(dm); j++) {
            if (dm_is_set(dm, i, j)) {
                dm_set (new, i, j);
            }
        }
    }
    return new;
}

void
tr_fill_process_groups (tr_context_t *tr, matrix_t *dm)
{
    int cols = dm_ncols(dm);
    int rows = dm_nrows(dm);
    // for each process p
    for(process_t *p = &tr->procs[0]; p != &tr->procs[tr->nprocs]; p++) {
        int new_process_group = rows - 1 - p->id;
        // for all groups g of p
        for(int i = 0; i < list_count(p->groups); i++) {
            int g = list_get(p->groups, i);
            // for all slots i in the state vector
            for (int j = 0; j < cols; j++) {
                // if the dm has a dependency between p and i,
                // then the process group also depends on i
                if (dm_is_set(dm, g, j)) {
                    dm_set(dm, new_process_group, j);
                }
            }
        }
    }
}

void
tr_add_leap_groups(tr_context_t *tr, model_t por_model, model_t pre_por)
{
    matrix_t *dm = enlarge_matrix (GBgetDMInfo(pre_por), tr->nprocs, 0);
    tr_fill_process_groups (tr, dm);
    GBsetDMInfo (por_model, dm);

    dm = enlarge_matrix (GBgetDMInfoMayWrite(pre_por), tr->nprocs, 0);
    tr_fill_process_groups (tr, dm);
    GBsetDMInfoMayWrite (por_model, dm);

    dm = enlarge_matrix (GBgetDMInfoMustWrite(pre_por), tr->nprocs, 0);
    tr_fill_process_groups (tr, dm);
    GBsetDMInfoMustWrite (por_model, dm);

    dm = enlarge_matrix (GBgetDMInfoRead(pre_por), tr->nprocs, 0);
    tr_fill_process_groups (tr, dm);
    GBsetDMInfoRead (por_model, dm);
}

// CV ACCESS
// ============================================================================
int* get_state(int* elem) { return elem+1; }
int get_trans(int* elem) { return *elem; }

int*
last_state(dfs_stack_t* s) {
    return get_state(dfs_stack_top(s));
}

int
last_trans(dfs_stack_t* s) {
    return get_trans(dfs_stack_top(s));
}


// STACK STUFF
// ============================================================================
void
stack_push(tr_context_t* tr, dfs_stack_t* stack, int t, int* s) {
    int* temp = dfs_stack_push(stack, NULL);
    memcpy(temp, &t, sizeof(int));
    memcpy(temp+1, s, tr->nslots*sizeof(int));
}


bool
pop_temp_to_CV(tr_context_t* tr, int i, int j) {
    if(dfs_stack_size(tr->tempstack) == 0) {
        return false;
    }

    int* temp = dfs_stack_pop(tr->tempstack);
    stack_push(tr, tr->CVs[i][j], *temp, temp+1);
    return true;
}

int* pop_temp(tr_context_t* tr) {
    if(dfs_stack_size(tr->tempstack) == 0) {
        return NULL;
    }

    return dfs_stack_pop(tr->tempstack);
}

void
pop_temp_state(tr_context_t* tr, int* tempvec) {
    if(dfs_stack_size(tr->tempstack) == 0) {
        return;
    }

    int* temp = dfs_stack_pop(tr->tempstack);
    memcpy(tempvec, temp+1, tr->nslots*sizeof(int));
}

int
pop_temp_transition(tr_context_t* tr) {
    if(dfs_stack_size(tr->tempstack) == 0) {
        return -1;
    }

    return *dfs_stack_pop(tr->tempstack);
}

void
tempstack_push(void* context, transition_info_t* ti, int* dst, int* cpy) {
    tr_context_t *tr = (tr_context_t*) context;
    Assert(dfs_stack_size(tr->tempstack) == 0, "Radical! Non-determinism found.");

    fprintf(stderr, "group = %i\n", ti->group);

    stack_push(tr, tr->tempstack, ti->group, dst);
}

// NEXT STATE
// ============================================================================
void
nextStateProc(tr_context_t* tr, int* src, int proc) {
    //fprintf(stderr, "process %i heeft zoveel ", proc);
    for(int j = 0; j < list_count(tr->procs[proc].groups); j++) {
        int g = list_get(tr->procs[proc].groups, j);
        GBgetTransitionsLong(tr->model, g, src, tempstack_push, tr);
    }

    //fprintf(stderr, "process %i heeft %lu enabelde acties\n", proc, dfs_stack_size(tr->tempstack));
}

void mark_not_extendable(tr_context_t* tr, int p) {
    if(tr->extendable[p]) {
        tr->extendable[p] = false;
        tr->extendable_count--;
    }
}

// SCHEDULING STUFF
// ============================================================================
int*
RR_next(tr_context_t* tr, void* ctx) { // Round robin extensions of CVs
    bool valid = false;
    int* temp;
    int tried = 0;

    while(!valid) {
        tr->cur = (tr->cur + 1) % tr->nprocs;
        fprintf(stderr, "RR: cur is %i\n", tr->cur);

        // can't select non extendable process
        if(tr->extendable[tr->cur]) {
            nextStateProc(tr, last_state(tr->CVs[tr->cur][tr->cur]), tr->cur);
            temp = dfs_stack_pop(tr->tempstack);
            if(temp != NULL) { // Next state exists
                valid = true;
                fprintf(stderr, "process %i heeft een volgende state hoera!\n", tr->cur);
            }
            // Blocking: not extendable, and infinite
            // Processes with an empty prefix cannot be dependent on other transitions,
            // therefore they are not removed from extendable
            else if(dfs_stack_size(tr->CVs[tr->cur][tr->cur]) > 0) {
                tr->infinite[tr->cur] = true;
                tr->blocked[tr->cur] = true;
                mark_not_extendable(tr, tr->cur);
                fprintf(stderr, "process %i is geblockt geraakt :(\n", tr->cur);
            }
            else { //for debug purposes
                fprintf(stderr, "process %i is leeg en altijd al geweest\n", tr->cur);
            }
        }
        // All processes are not extendable or blocked
        if(++tried == tr->nprocs) {
            return NULL;
        }
    }
    return temp;
}

int*
DF_next(tr_context_t* tr, void* ctx) { // depth first extension of CVs
    bool valid = false;
    int* temp;
    int tried = 0;

    while(!valid) {
        // can't select non extendable process
        if(tr->extendable[tr->cur]) {
            nextStateProc(tr, last_state(tr->CVs[tr->cur][tr->cur]), tr->cur);
            temp = dfs_stack_pop(tr->tempstack);
            if(temp != NULL) { // Next state exists
                valid = true;
            }
            // Blocking: not extendable, and infinite
            // Processes with an empty prefix cannot be dependent on other transitions,
            // therefore they are not removed from extendable
            else if(dfs_stack_size(tr->CVs[tr->cur][tr->cur]) > 0) {
                tr->infinite[tr->cur] = true;
                tr->blocked[tr->cur] = true;
                mark_not_extendable(tr, tr->cur);
            }
        }

        if(!valid) tr->cur = (tr->cur + 1) % tr->nprocs;
        // All processes are not extendable or blocked
        if(++tried == tr->nprocs) {
            return NULL;
        }
    }
    return temp;
}

// ============================================================================

void
commute_last(int CV1, tr_context_t* tr) {
    for(int CV2 = 0; CV2 < tr->nprocs; CV2++) {
        if(CV2 == CV1) continue;
        // Both already not extendable: this function will do nothing, skip for
        // efficiency
        if(!tr->extendable[CV1] && !tr->extendable[CV2]) continue;

        // If CV1 or CV2 is length 0, they always commute
        if(dfs_stack_size(tr->CVs[CV1][CV2]) == 0
        || dfs_stack_size(tr->CVs[CV2][CV1]) == 0) {
            continue;
        }

        if(memcmp(
            last_state(tr->CVs[CV1][CV2]),
            last_state(tr->CVs[CV2][CV1]),
            tr->nslots*sizeof(int)
        ) != 0) {
            mark_not_extendable(tr, CV1);
            mark_not_extendable(tr, CV2);
        }
    }
}

/*     a
temp ----- temp2
 |          |
 | t        | t
 |          |
temp3 ---- (res1, res2)
       a
*/
bool
commute_nonlast(
    int CV1,
    int t,
    tr_context_t* tr,
    model_t self,
    void* ctx
) {
    for(int CV2 = 0; CV2 < tr->nprocs; CV2++) {
        if(CV2 == CV1) continue;
        if(dfs_stack_size(tr->CVs[CV2][CV2]) == 0) continue;

        int* temp = last_state(tr->CVs[CV1][CV1]);
        GBgetTransitionsLong(tr->model, t, temp, tempstack_push, ctx);
        pop_temp_state(tr, tr->temp3);
        int* temp2;

        for(int i = 0; i < dfs_stack_size(tr->CVs[CV1][CV2])-1; i++) {
            temp2 = get_state(dfs_stack_index(tr->CVs[CV1][CV2], i));
            int a = get_trans(dfs_stack_index(tr->CVs[CV1][CV2], i));

            GBgetTransitionsLong(tr->model, t, temp2, tempstack_push, ctx);
            pop_temp_state(tr, tr->res1);

            GBgetTransitionsLong(tr->model, a, tr->temp3, tempstack_push, ctx);
            pop_temp_state(tr, tr->res2);

            if(memcmp(tr->res1, tr->res2, tr->nslots*sizeof(int)) != 0) {
                return false;
            }

            temp = temp2;
            tr->temp3 = tr->res1;
        }
    }

    return true;
}

void
extendCV(tr_context_t* tr, int CV, int t, int* s, model_t self, void* ctx) {
    // extend CV itself
    stack_push(tr, tr->CVs[CV][CV], t, s);

    //fprintf(stderr, "process %i heeft lengte %lu\n", CV, dfs_stack_size(tr->CVs[CV][CV]));

    for(int CV2 = 0; CV2 < tr->nprocs; CV2++) {
        if(CV2 == CV) continue;
        // replace (a,s) with (a, t(s))
        for(int i = 0; i < dfs_stack_size(tr->CVs[CV][CV2]); i++) {
            int* item = dfs_stack_index(tr->CVs[CV][CV2], i);
            // Get t(s)
            GBgetTransitionsLong(tr->model, t, get_state(item), tempstack_push, ctx);
            pop_temp_state(tr, tr->res1);
            // Replace s with t(s)
            memcpy(item+1, tr->res1, tr->nslots*sizeof(int));
        }

        // extend with the new transition
        if(dfs_stack_size(tr->CVs[CV2][CV2]) != 0){
            int* start = dfs_stack_size(tr->CVs[CV2][CV]) == 0 ?
                            last_state(tr->CVs[CV2][CV2]) : last_state(tr->CVs[CV2][CV]);
            GBgetTransitionsLong(tr->model, t, start, tempstack_push, ctx);
            pop_temp_to_CV(tr, CV2, CV);
        }
        else{
            tr->CVs[CV2][CV] = tr->CVs[CV][CV];
        }
    }
}

void
init(tr_context_t *tr, model_t self, int *src, void *ctx) {
    tr->cur = 0;
    tr->src = src;
    tr->extendable_count = tr->nprocs;

    // Add first next state for all processes
    for(int i = 0; i < tr->nprocs; i++) {
        nextStateProc(tr, src, i);
        tr->extendable[i] = true;
        //pop_temp_to_CV(tr, i, i);
        int* temp = pop_temp(tr);
        if(temp) extendCV(tr, i, *temp, temp+1, self, ctx);
        if(dfs_stack_size(tr->CVs[i][i]) == 0) { // Initially empty
            tr->infinite[i] = true;
            tr->blocked[i] = true;
            mark_not_extendable(tr, i);
        }
        else {
            tr->infinite[i] = false;
            tr->blocked[i] = false;
        }
    }

    for(int i = 0; i < tr->nprocs; i++) {
        commute_last(i, tr);
    }
}

void
check_internal_loop(tr_context_t* tr, int CV) {
    if(!tr->extendable[CV]) return;

    int* last = last_state(tr->CVs[CV][CV]);
    for(int i = 0; i < dfs_stack_size(tr->CVs[CV][CV])-1; i++) {
        int* cur = get_state(dfs_stack_index(tr->CVs[CV][CV], i));
        if(memcmp(cur, last, tr->nslots*sizeof(int)) != 0) {
            tr->infinite[CV] = true;
            mark_not_extendable(tr, CV);
            return;
        }
    }
}

void
check_blocked(int t, tr_context_t* tr) {
    // Check if this thread is now blocked
    nextStateProc(tr, last_state(tr->CVs[t][t]), t);
    int *temp = dfs_stack_pop(tr->tempstack);
    if(temp == NULL) { // Next state does not exist
        tr->blocked[t] = true;
        mark_not_extendable(tr, t);
    }

    // Check if this thread has now enabled others
    for(int t2 = 0; t2 < tr->nprocs; t2++) {
        if(t2 != t && tr->blocked[t2]) {
            nextStateProc(tr, last_state(tr->CVs[t2][t2]), t2);
            temp = dfs_stack_pop(tr->tempstack);
            if(temp != NULL) { // Next state exists
                tr->blocked[t2] = false;
                mark_not_extendable(tr, t);
            }
        }
    }
}

void
return_states(tr_context_t* tr) {
    for(int i = 0; i < tr->nprocs; i++) {
        // Do not return states marked as infinite
        if(tr->infinite[i]) continue;

        // Otherwise, return all final states from the CVs
        int* last_s = last_state(tr->CVs[i][i]);
        if(last_s) {
            transition_info_t ti = GB_TI(NULL, tr->group_start+i);
            tr->cb_org(tr->ctx_org, &ti, last_s, NULL);
            tr->emitted++;
        }
    }
}

int
tr_next_all (model_t self, int *src, TransitionCB cb, void *ctx)
{
    tr_context_t *tr = (tr_context_t*) GBgetContext(self);
	// CV ALGO
	// ===========================================================================
    init(tr, self, src, ctx);

    while(tr->extendable_count > 0) {
        int* temp = RR_next(tr, ctx);
        fprintf(stderr, "cur is %i\n", tr->cur);
        // temp = DF_next(tr, ctx);
        if(temp == NULL) {
            break; // All processes either not extendable or blocking
        }

        int next_t = get_trans(temp);
        int* next_s = get_state(temp);

        if(!commute_nonlast(tr->cur, next_t, tr, self, ctx)) {
            mark_not_extendable(tr, tr->cur);
        }
        else {
            extendCV(tr, tr->cur, next_t, next_s, self, ctx);
            commute_last(tr->cur, tr);
            check_blocked(tr->cur, tr);
            check_internal_loop(tr, tr->cur);
        }
    }
	// ===========================================================================

    // Forward the next selected successor states to the algorithm:
    tr->cb_org = cb;
    tr->ctx_org = ctx;
    tr->emitted = 0;
    return_states(tr);
    return tr->emitted;
}

/**
 * Setup the partial order reduction layer.
 */
model_t
pins2pins_tr (model_t model)
{
    tr_context_t *tr = malloc(sizeof *tr);
    tr->model = model;
    tr->nactions = pins_get_group_count(model);
    tr->nslots = pins_get_state_variable_count (model);
    tr->g2p = (int*) malloc(pins_get_group_count(model) * sizeof(int));
    tr->procs = identify_procs(model, &tr->nprocs, tr->g2p);
    Print ("Number of actions: %zu", tr->nactions);

    // Allocate space for cartesian vectors
    tr->CVs = (dfs_stack_t***) malloc(tr->nprocs * sizeof(dfs_stack_t**));
    tr->tempCVs = (dfs_stack_t**) malloc(tr->nprocs * sizeof(dfs_stack_t*));
    for(int i = 0; i < tr->nprocs; i++) {
        tr->CVs[i] = (dfs_stack_t**) malloc(tr->nprocs * sizeof(dfs_stack_t*));
        tr->tempCVs[i] = dfs_stack_create(tr->nslots+1);
        for(int j = 0; j < tr->nprocs; j++) {
            tr->CVs[i][j] = dfs_stack_create(tr->nslots+1);
        }
    }

    tr->tempstack = dfs_stack_create(tr->nslots+1);
    tr->extendable = (bool*) malloc(tr->nprocs * sizeof(bool));
    tr->infinite = (bool*) malloc(tr->nprocs * sizeof(bool));
    tr->blocked = (bool*) malloc(tr->nprocs * sizeof(bool));

    // Temp vectors
    tr->temp3 = (int*) malloc(tr->nslots * sizeof(int));
    tr->res1 = (int*) malloc(tr->nslots * sizeof(int));
    tr->res2 = (int*) malloc(tr->nslots * sizeof(int));

	// create fresh PINS model
    model_t pormodel = GBcreateBase();
    // Create groups
    tr->group_start = pins_get_group_count(model);
    tr_add_leap_groups(tr, pormodel, model);
    // set POR as new context
    GBsetContext(pormodel, tr);
    // set por next state function
    GBsetNextStateAll(pormodel, tr_next_all);
    // copy all the other data from the original model
    GBinitModelDefaults(&pormodel, model);

    int s0[tr->nslots];
    GBgetInitialState(model, s0);
    GBsetInitialState(pormodel, s0);

    return pormodel;
}
