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

typedef struct tr_ctx {
    model_t         model;
    size_t          nslots; // number of variables in state vector
    size_t          nprocs; // number of processes in the program
    process_t*      procs; // structs representing each process

    int*            src; // The source state for the current tr_next_all call
    int*            cur_s; // The currently chosen state to expand
    int             cur_t; // The currently chosen transition to expand
    int             cur; // The index of the chosen process to expand

	// Saves the cartesian vectors and concatenations thereof
    // CVs[i][j] =
    //   The CV for process i                                       if i == j
    //   The states acquired when executing CV j after CV i         if i != j
    dfs_stack_t***  CVs;

    int             group_start; // saves the id of the first group we added to the model
	dfs_stack_t*    tempstack; // Temp storage for callback
    int*            temp3, *res1, *res2; // Temp storage for commutativity checks

    bool*           extendable; // true if process is still extendable
    bool*           infinite; // true if a process contains a self loop
    bool*           blocked; // true if a process is blocked
    int             extendable_count; // amount of extendable processes

    TransitionCB    cb_org; // callback to the mc
    void*           ctx_org; // original context
    size_t          emitted; // number of emitted states
} tr_context_t;


// Adding groups
// ============================================================================
// Adds one new group for each process, successors are returned under the group
// of their process to retain some r/w info
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
// CV elements are stored like: [ transition, state[0], state[1] ... state[nslots-1] ]
int* get_state(int* elem) { return elem+1; }
int get_trans(int* elem) { return *elem; }

// Returns the last state of a CV
int* last_state(dfs_stack_t* s) {
    return get_state(dfs_stack_top(s));
}

// Returns the last transition of a CV
int last_trans(dfs_stack_t* s) {
    return get_trans(dfs_stack_top(s));
}

// Prints a state as the values of its integers
void log_state(tr_context_t* tr, int* state) {
    for(int i = 0; i < tr->nslots; i++) {
        fprintf(stderr, "%d,", state[i]);
    }
    fprintf(stderr, "\n");
}

// Prints an entire CV
void print_CV(tr_context_t* tr, dfs_stack_t* CV) {
    fprintf(stderr, "========================\n");
    for(int i = 0; i < dfs_stack_size(CV); i++) {
        log_state(tr, get_state(dfs_stack_index(CV, i)));
    }
    fprintf(stderr, "========================\n");
}

// STACK STUFF
// ============================================================================
// Pushes a transition and state onto a stack using the above storage scheme
void stack_push(tr_context_t* tr, dfs_stack_t* stack, int t, int* s) {
    int* temp = dfs_stack_push(stack, NULL);
    memcpy(temp, &t, sizeof(int));
    memcpy(temp+1, s, tr->nslots*sizeof(int));
}

// Pops the tempstack onto a CV
bool pop_temp_to_CV(tr_context_t* tr, int i, int j) {
    if(dfs_stack_size(tr->tempstack) == 0) {
        return false;
    }

    int* temp = dfs_stack_pop(tr->tempstack);
    stack_push(tr, tr->CVs[i][j], get_trans(temp), get_state(temp));
    return true;
}

// pops a state from the tempstack into a supplied pointer
bool pop_temp_state(tr_context_t* tr, int* tempvec) {
    if(dfs_stack_size(tr->tempstack) == 0) {
        return false;
    }

    int* temp = dfs_stack_pop(tr->tempstack);
    memcpy(tempvec, get_state(temp), tr->nslots*sizeof(int));
    return true;
}

// Callback for getTransitions: pushes onto the tempstack
void tempstack_push(void* context, transition_info_t* ti, int* dst, int* cpy) {
    tr_context_t *tr = (tr_context_t*) context;
    Assert(dfs_stack_size(tr->tempstack) == 0, "Radical! Non-determinism found.");
    // TODO: add non-determinism support

    stack_push(tr, tr->tempstack, ti->group, dst);
}
// ============================================================================

// Gets all successors from src for a single process
void nextStateProc(tr_context_t* tr, int* src, int proc) {
    for(int j = 0; j < list_count(tr->procs[proc].groups); j++) {
        int g = list_get(tr->procs[proc].groups, j);
        GBgetTransitionsLong(tr->model, g, src, tempstack_push, tr);
    }
}

// Performs required tasks to mark a process as not extendable
void mark_not_extendable(tr_context_t* tr, int p) {
    if(tr->extendable[p]) {
        tr->extendable[p] = false;
        tr->extendable_count--;
    }
}

// SCHEDULING STUFF
// ============================================================================
// Round robin selector of the next process to extend further
int* RR_next(tr_context_t* tr) {
    bool valid = false;
    int* temp;
    int tried = 0;

    while(!valid) {
        tr->cur = (tr->cur + 1) % tr->nprocs;

        // can't select non extendable process
        if(tr->extendable[tr->cur]) {
            nextStateProc(tr, last_state(tr->CVs[tr->cur][tr->cur]), tr->cur);
            temp = dfs_stack_pop(tr->tempstack);
            if(temp) { // Next state exists
                valid = true;
            }
            else { // No next state
                tr->blocked[tr->cur] = true;
                mark_not_extendable(tr, tr->cur);
            }
        }
        // All processes are not extendable or blocked
        if(!valid && ++tried == tr->nprocs) {
            return NULL;
        }
    }
    return temp;
}

// Depth first selector of the next process to extend further
int* DF_next(tr_context_t* tr) {
    bool valid = false;
    int* temp;
    int tried = 0;

    while(!valid) {
        // can't select non extendable process
        if(tr->extendable[tr->cur]) {
            nextStateProc(tr, last_state(tr->CVs[tr->cur][tr->cur]), tr->cur);
            temp = dfs_stack_pop(tr->tempstack);
            if(temp) { // Next state exists
                valid = true;
            }
            else { // No next state
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

// The concatenated CVs (empty) are filled
// Assumes CV contains one transition state tuple
void fill_hcube(tr_context_t* tr, int CV, int CV2) {
    // initialize [CV2][CV]
    GBgetTransitionsLong(tr->model, tr->cur_t, last_state(tr->CVs[CV2][CV2]), tempstack_push, tr);
    pop_temp_to_CV(tr, CV2, CV);

    // initialize [CV][CV2]
    int* temp = tr->cur_s; // last state of CV
    for(int i = 0; i < dfs_stack_size(tr->CVs[CV2][CV2]); i++) {
        int a = get_trans(dfs_stack_index(tr->CVs[CV2][CV2], i));
        GBgetTransitionsLong(tr->model, a, temp, tempstack_push, tr);
        pop_temp_to_CV(tr, CV, CV2);
        temp = last_state(tr->CVs[CV][CV2]);
    }
}

// Update non-empty concatenated CVs after extension of CV
void extend_hcube(tr_context_t* tr, int CV, int CV2) {
    // extend [CV][CV2]
    for(int i = 0; i < ((int)dfs_stack_size(tr->CVs[CV][CV2])); i++) {
        int* item = dfs_stack_index(tr->CVs[CV][CV2], i);
        GBgetTransitionsLong(tr->model, tr->cur_t, get_state(item), tempstack_push, tr);
        memcpy(get_state(item), last_state(tr->tempstack), tr->nslots*sizeof(int));
        dfs_stack_pop(tr->tempstack);
    }

    // extend [CV2][CV]
    GBgetTransitionsLong(tr->model, tr->cur_t, last_state(tr->CVs[CV2][CV]), tempstack_push, tr);
    pop_temp_to_CV(tr, CV2, CV);
}

// Updates CVs[CV][CV2] and CVs[CV2][CV] after the given CV has been extended
// Asumes all states required for the update are reachable
// Assumption enforced by commute_nonlast and commute_last
void update_hcube(tr_context_t* tr, int CV, int CV2) {
    if(!tr->extendable[CV2]) { return; }

    // This extension causes both CV and CV2 to be non-empty
    if(dfs_stack_size(tr->CVs[CV][CV]) == 1 && dfs_stack_size(tr->CVs[CV2][CV2]) != 0) {
        fill_hcube(tr, CV, CV2);
    }
    // CV and CV2 were both already non-empty before this extention
    else if(dfs_stack_size(tr->CVs[CV2][CV2]) != 0) {
        extend_hcube(tr, CV, CV2);
    }
}

// Checks whether last transition of CV1 commutes with last transitions of
// all other CVs.
// Removes CVs from extendable and updates concatenated CVs when necessary.
void commute_last(int CV1, tr_context_t* tr) {
    for(int CV2 = 0; CV2 < tr->nprocs; CV2++) {
        if(CV2 == CV1) continue;
        // Both already not extendable: this function will do nothing
        if(!tr->extendable[CV1] && !tr->extendable[CV2]) continue;

        // If CV2 is length 0, CV1 and CV2 always commute
        if(dfs_stack_size(tr->CVs[CV2][CV2]) == 0) continue;

        // If CV1 wasn't empty before and [CV1][CV2] or [CV2][CV1] is empty,
        // CV1 and CV2 do not commute (either process is blocked)
        if(dfs_stack_size(tr->CVs[CV1][CV1]) > 1) {
            if(dfs_stack_size(tr->CVs[CV1][CV2]) == 0 ||
            dfs_stack_size(tr->CVs[CV2][CV1]) == 0) {
                continue;
            }
        }

        // extending [CV2][CV1], store new state in tr->res1
        int* start = dfs_stack_size(tr->CVs[CV1][CV1]) == 1 ?
        last_state(tr->CVs[CV2][CV2]) : last_state(tr->CVs[CV2][CV1]);

        GBgetTransitionsLong(tr->model, tr->cur_t, start, tempstack_push, tr);

        if(!pop_temp_state(tr, tr->res1)) continue; // CV1 is blocked

        // extending [CV1][CV2], store new state in tr-res2
        // First perform last transition of CV1
        if(dfs_stack_size(tr->CVs[CV2][CV2]) == 1) {
            memcpy(tr->temp3, last_state(tr->CVs[CV1][CV1]), tr->nslots*sizeof(int));
        }
        else {
            if(dfs_stack_size(tr->CVs[CV1][CV1]) == 1) {
                GBgetTransitionsLong(
                    tr->model, tr->cur_t,
                    get_state(dfs_stack_index(tr->CVs[CV2][CV2], dfs_stack_size(tr->CVs[CV2][CV2])-2)),
                    tempstack_push, tr
                );
            }
            else {
                if(dfs_stack_size(tr->CVs[CV1][CV2]) < 2) continue; // CV2 is already blocked
                GBgetTransitionsLong(
                    tr->model, tr->cur_t,
                    get_state(dfs_stack_index(tr->CVs[CV1][CV2], dfs_stack_size(tr->CVs[CV1][CV2])-2)),
                    tempstack_push, tr
                );
            }

            if(!pop_temp_state(tr, tr->temp3)) continue; // CV1 is blocked
        }

        // Then perform the last transition of CV2 from the resulting state (tr->temp3)
        int a = last_trans(tr->CVs[CV2][CV2]);
        GBgetTransitionsLong(tr->model, a, tr->temp3, tempstack_push, tr);

        if(!pop_temp_state(tr, tr->res2)) continue; // CV2 is blocked

        // Compare whether resulting states are the same
        if(memcmp(tr->res1, tr->res2, tr->nslots*sizeof(int)) != 0) {
            mark_not_extendable(tr, CV1);
            mark_not_extendable(tr, CV2);
        }
        else { // if last transitions commute the concatenated CVs are updated
            update_hcube(tr, CV1, CV2);
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

Checks whether the last transition in CV1 commutes with all transitions other
than the last of all other CVs.
Assumes new extension of CV1 has not yet been pushed on the tr->CVs[CV1][CV1].
Enforced by tr_next_all.
*/
bool commute_nonlast(int CV1, tr_context_t* tr) {
    for(int CV2 = 0; CV2 < tr->nprocs; CV2++) {
        if(CV2 == CV1) continue;
        // If CV2 is length 0, CV1 and CV2 always commute
        if(dfs_stack_size(tr->CVs[CV2][CV2]) == 0) continue;

        int* temp = last_state(tr->CVs[CV1][CV1]);
        GBgetTransitionsLong(tr->model, tr->cur_t, temp, tempstack_push, tr);
        pop_temp_state(tr, tr->temp3);
        int* temp2;

        for(int i = 0; i < ((int)dfs_stack_size(tr->CVs[CV1][CV2]))-1; i++) {
            temp2 = get_state(dfs_stack_index(tr->CVs[CV1][CV2], i));
            int a = get_trans(dfs_stack_index(tr->CVs[CV1][CV2], i));

            GBgetTransitionsLong(tr->model, tr->cur_t, temp2, tempstack_push, tr);
            pop_temp_state(tr, tr->res1);

            GBgetTransitionsLong(tr->model, a, tr->temp3, tempstack_push, tr);
            pop_temp_state(tr, tr->res2);

            if(memcmp(tr->res1, tr->res2, tr->nslots*sizeof(int)) != 0) {
                return false; // Resulting states are not the same
            }

            memcpy(temp, temp2, tr->nslots*sizeof(int)); //temp <- temp2
            memcpy(tr->temp3, tr->res1, tr->nslots*sizeof(int)); // temp3 <- res1
        }
    }

    return true;
}

// cleans all CVs
void clean_CVs(tr_context_t *tr) {
    for(int i = 0; i < tr->nprocs; i++) {
        for(int j = 0; j < tr->nprocs; j++) {
            dfs_stack_clear(tr->CVs[i][j]);
        }
    }
}

// Resets and cleans up variables and initializes first transition and state of all CVs
void init(tr_context_t *tr, model_t self, int *src, void *ctx) {
    clean_CVs(tr);
    tr->cur = 0;
    tr->emitted = 0;
    tr->src = src;
    tr->extendable_count = tr->nprocs;
    tr->ctx_org = ctx;

    // Add first next state for all processes
    for(int i = 0; i < tr->nprocs; i++) {
        tr->extendable[i] = true;
        nextStateProc(tr, src, i);
        int* temp = dfs_stack_pop(tr->tempstack);

        if(temp) { // Initially empty
            memcpy(tr->cur_s, get_state(temp), tr->nslots*sizeof(int));
            tr->cur_t = get_trans(temp);
            stack_push(tr, tr->CVs[i][i], tr->cur_t, tr->cur_s);
            commute_last(i, tr);
            tr->infinite[i] = false;
            tr->blocked[i] = false;
        }
        else { // Process i is blocked
            tr->infinite[i] = true;
            tr->blocked[i] = true;
            mark_not_extendable(tr, i);
        }
    }
}

// Checks whether last state of given CV occurs is unique in this CV
// and marks CV as infinite if a self loop is found
void check_internal_loop(tr_context_t* tr, int CV) {
    if(!tr->extendable[CV]) return;

    int* last = last_state(tr->CVs[CV][CV]);
    for(int i = 0; i < dfs_stack_size(tr->CVs[CV][CV])-1; i++) {
        int* cur = get_state(dfs_stack_index(tr->CVs[CV][CV], i));
        if(memcmp(cur, last, tr->nslots*sizeof(int)) == 0) {
            tr->infinite[CV] = true;
            mark_not_extendable(tr, CV);
            return;
        }
    }
}

// Checks whether extending CV t has enabled any other CVs
void check_blocked(int t, tr_context_t* tr) {
    for(int t2 = 0; t2 < tr->nprocs; t2++) {
        if(t2 != t && tr->blocked[t2]) {
            int* start = dfs_stack_size(tr->CVs[t][t2]) == 0 ?
                            last_state(tr->CVs[t][t]) : last_state(tr->CVs[t][t2]);
            nextStateProc(tr, start, t2);
            int* temp = dfs_stack_pop(tr->tempstack);
            if(temp) { // Next state is enabled, transition does not commute
                mark_not_extendable(tr, t);
                break;
            }
        }
    }
}

// Return last state of CV for each process that is not marked infinite
// to the model checker
void return_states(tr_context_t* tr) {
    for(int i = 0; i < tr->nprocs; i++) {
        // Do not return states marked as infinite
        if(tr->infinite[i]) continue;

        // Otherwise, return the final state
        transition_info_t ti = GB_TI(NULL, tr->group_start+i);
        tr->cb_org(tr->ctx_org, &ti, last_state(tr->CVs[i][i]), NULL);
        tr->emitted++;
    }
}

// Build cartesian vector for each process from given state src.
// Return the last state of every CV that is not marked infinite.
int tr_next_all (model_t self, int *src, TransitionCB cb, void *ctx)
{
    tr_context_t *tr = (tr_context_t*) GBgetContext(self);

	// CV ALGO
	// ===========================================================================
    init(tr, self, src, ctx);

    while(tr->extendable_count > 0) {
        // Next process, transition and state are selected (round robin/depth first)
        int* temp = DF_next(tr);//RR_next(tr);

        if(!temp) break; // All processes either not extendable or blocking

        tr->cur_t = get_trans(temp); // current transition
        memcpy(tr->cur_s, get_state(temp), tr->nslots*sizeof(int)); // current state

        if(!commute_nonlast(tr->cur, tr)) {
            // If cur_t does not commute with a non-last transition from another CV
            // it is not added to the CV and the process is marked not extendable.
            mark_not_extendable(tr, tr->cur);
        }
        else {
            // If cur_t commutes with every non-last transition it is added
            // to the CV.
            stack_push(tr, tr->CVs[tr->cur][tr->cur], tr->cur_t, tr->cur_s);
             // check if cur_t commutes with all last transitions and extend CVs.
            commute_last(tr->cur, tr);
            // check if cur_t enables any blocked process.
            check_blocked(tr->cur, tr);
            // check if cur_s is a unique state in its CV.
            check_internal_loop(tr, tr->cur);
        }
    }
	// ===========================================================================

    // Forward the next selected successor states to the algorithm:
    tr->cb_org = cb;
    return_states(tr);
    return tr->emitted;
}

/**
 * Setup the partial order reduction layer.
 */
model_t pins2pins_tr (model_t model)
{
    tr_context_t *tr = malloc(sizeof *tr);
    tr->model = model;
    tr->nslots = pins_get_state_variable_count (model);
    int* g2p = (int*) malloc(pins_get_group_count(model) * sizeof(int));
    tr->procs = identify_procs(model, &tr->nprocs, g2p);

    // Allocate space for cartesian vectors
    tr->CVs = (dfs_stack_t***) malloc(tr->nprocs * sizeof(dfs_stack_t**));
    for(int i = 0; i < tr->nprocs; i++) {
        tr->CVs[i] = (dfs_stack_t**) malloc(tr->nprocs * sizeof(dfs_stack_t*));
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
    tr->cur_s = (int*) malloc(tr->nslots * sizeof(int));

	// create fresh PINS model
    model_t pormodel = GBcreateBase();
    // Create extra groups
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
