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
#include "add_group.h"
#define MAX_CV_SIZE 64
#define MAX_N_PROCS 16

// TODO: geen stack maar constant size buffer voor callbacks
// TODO: CVs[X][X] -> last(CVs[X][X]):
//       Je hoeft alleen de laatste op te slaan


typedef enum {
    Disabled = 0,
    Enabled  = 1
} status_t;


typedef struct CV_elem_s {
    int transition;
    int* state;
} CV_elem_t;

typedef struct tr_ctx {
    model_t         model;
    size_t          nslots;   // number of variables in state vector
	size_t		    nactions;
	size_t          nguards;
    size_t          nprocs;

    process_t*      procs;
    int*            g2p;
    dfs_stack_t*    queue[2];

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

// Helpers for readability
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


// SCHEDULING STUFF
// ============================================================================
void
RR_next(tr_context_t* tr) { // Round robin extensions of CVs
    do {
        tr->cur = (tr->cur + 1) % tr->nprocs;
    } while(!tr->extendable[tr->cur]);
}

void
DF_next(tr_context_t* tr) { // depth first extension of CVs
    while(!tr->extendable[tr->cur]) {
        tr->cur++;
    }
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
    Assert(dfs_stack_size(tr->tempstack) > 0, "Radical! Non-determinism found.");

    stack_push(tr, tr->tempstack, ti->group, dst);
}

// ============================================================================

void
commute_last(int CV1, tr_context_t* tr) {
    for(int CV2 = 0; CV2 < tr->nprocs; CV2++) {
        if(CV2 == CV1) continue;
        if(!(tr->extendable[CV1] || tr->extendable[CV2])) continue;

        if(memcmp(
            last_state(tr->CVs[CV1][CV2]),
            last_state(tr->CVs[CV2][CV1]),
            tr->nslots*sizeof(int)
        ) != 0) {
            if(tr->extendable[CV1] == true) {
                tr->extendable[CV1] = false;
                tr->extendable_count--;
            }
            if(tr->extendable[CV2] == true) {
                tr->extendable[CV2] = false;
                tr->extendable_count--;
            }
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
        int* temp = last_state(tr->CVs[CV1][CV1]);
        GBgetTransitionsLong(self, t, temp, tempstack_push, ctx);
        pop_temp_state(tr, tr->temp3);
        int* temp2;

        for(int i = 0; i < dfs_stack_size(tr->CVs[CV1][CV2])-2; i++) {
            temp2 = get_state(dfs_stack_index(tr->CVs[CV1][CV2], i));
            int a = get_trans(dfs_stack_index(tr->CVs[CV1][CV2], i));

            GBgetTransitionsLong(self, t, temp2, tempstack_push, ctx);
            pop_temp_state(tr, tr->res1);

            GBgetTransitionsLong(self, a, tr->temp3, tempstack_push, ctx);
            pop_temp_state(tr, tr->res2);

            if(memcmp(tr->res1, tr->res2, tr->nslots*sizeof(int)) != 0) {
                return false;
            }

            temp = temp2;
            tr->temp3 = tr->res1;

            // Save (a,res1) to temp vector
            stack_push(tr, tr->tempCVs[CV2], a, tr->res1);
            //tr->tempCVs[CV2][i].state
        }
    }

    return true;
}

// Concatenate CV2 after CV1
void
concatenate(model_t self, tr_context_t* tr, void* ctx, int CV1, int CV2) {
    int* s = last_state(tr->CVs[CV1][CV1]);

    for(int i = 0; i < dfs_stack_size(tr->CVs[CV2][CV2])-1; i++) {
        int t = get_trans(dfs_stack_index(tr->CVs[CV2][CV2],i));
        GBgetTransitionsLong(self, t, s, tempstack_push, ctx);
        pop_temp_to_CV(tr, CV1, CV2);
        s = last_state(tr->CVs[CV1][CV2]);
    }
}

void
nextStateProc(model_t self, tr_context_t* tr, int* src, int proc, void* ctx) {
    for(int j = 0; j < list_count(tr->procs[proc].groups); j++) {
        int g = list_get(tr->procs[proc].groups, j);
        GBgetTransitionsLong(self, g, src, tempstack_push, ctx);
    }
}

void
init(tr_context_t *tr, model_t self, int *src, void *ctx) {
    tr->cur = 0;
    for(int i = 0; i < tr->nprocs; i++) { tr->infinite[i] = false; }
    tr->extendable_count = tr->nprocs;

    // Add first next state for all processes
    for(int i = 0; i < tr->nprocs; i++) {
        nextStateProc(self, tr, src, i, ctx);
        if(pop_temp_to_CV(tr, i, i)) {
            tr->extendable[i] = true;
        }
        else {
            tr->extendable[i] = false;
            tr->extendable_count--;
        }
    }

    for(int i = 0; i < tr->nprocs; i++) {
        for(int j = 0; j < tr->nprocs; j++) {
            if(i != j) {
                // Initialize all combinations of CVs
                concatenate(self, tr, ctx, i, j);
            }
        }
    }

    for(int i = 0; i < tr->nprocs; i++) {
        commute_last(i, tr);
    }
}


void
extendCV(tr_context_t* tr, int CV, int t, int* s, model_t self, void* ctx) {
    for(int i = 0; i < tr->nprocs; i++) {
        // replace (a,s) with (a, t(s))
        tr->CVs[CV][i] = tr->tempCVs[i];
        // extend with t
        GBgetTransitionsLong(self, t, last_state(tr->CVs[i][CV]), tempstack_push, ctx);
        pop_temp_to_CV(tr, i, CV);
    }
    // extend CV itself
    stack_push(tr, tr->CVs[CV][CV], t, s);
}

void
clean_temps(tr_context_t* tr) {
    for(int i = 0; i < tr->nprocs; i++) {
        dfs_stack_clear(tr->tempCVs[i]);
    }
}

void
check_internal_loop(tr_context_t* tr, int CV) {
    if(!tr->extendable[CV]) return;

    int* last = last_state(tr->CVs[CV][CV]);
    for(int i = 0; i < dfs_stack_size(tr->CVs[CV][CV])-2; i++) {
        int* cur = get_state(dfs_stack_index(tr->CVs[CV][CV], i));
        if(memcmp(cur, last, tr->nslots*sizeof(int)) != 0) {
            tr->infinite[CV] = true;
            tr->extendable[CV] = false;
            tr->extendable_count--;
            return;
        }
    }
}

void
return_states(tr_context_t* tr) {
    for(int i = 0; i < tr->nprocs; i++) {
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
        RR_next(tr);
        // DF_next(tr);

        nextStateProc(self, tr, last_state(tr->CVs[tr->cur][tr->cur]), tr->cur, ctx);

        int* temp = dfs_stack_pop(tr->tempstack);
        int next_t = get_trans(temp);
        int* next_s = get_state(temp);

        if(next_t == -1) {
            tr->extendable[tr->cur] = false;
            tr->extendable_count--;
            continue;
        }

        if(!commute_nonlast(tr->cur, next_t, tr, self, ctx)) {
            clean_temps(tr);
            tr->extendable[tr->cur] = false;
            tr->extendable--;
        }
        else {
            extendCV(tr, tr->cur, next_t, next_s, self, ctx);
            commute_last(tr->cur, tr);
            check_internal_loop(tr, tr->cur);
        }
    }


	// ===========================================================================

    // Forward the next selected successor states to the algorithm:
    //TODO
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
	if (!pins_has_guards(model)) {
        Abort ("Frontend doesn't have guards. Ignoring --por.");
    }

    tr_context_t *tr = malloc(sizeof *tr);
    tr->model = model;
    tr->nactions = pins_get_group_count(model);
    tr->nslots = pins_get_state_variable_count (model);
    tr->procs = identify_procs(model, &tr->nprocs, tr->g2p);
    Print ("Number of actions: %zu", tr->nactions);

    // Allocate space for cartesian vectors
    for(int i = 0; i < tr->nprocs; i++) {
        tr->tempCVs[i] = dfs_stack_create(tr->nslots+1);
        for(int j = 0; j < tr->nprocs; j++) {
            tr->CVs[i][j] = dfs_stack_create(tr->nslots+1);
        }
    }

    tr->tempstack = dfs_stack_create(tr->nslots+1);
    tr->extendable = (bool*) malloc(tr->nprocs * sizeof(bool));
    tr->infinite = (bool*) malloc(tr->nprocs * sizeof(bool));

    // Temp vectors
    tr->temp3 = (int*) malloc(tr->nslots * sizeof(int));
    tr->res1 = (int*) malloc(tr->nslots * sizeof(int));
    tr->res2 = (int*) malloc(tr->nslots * sizeof(int));

	// create fresh PINS model
    model_t pormodel = GBcreateBase();

    // set POR as new context
    GBsetContext(pormodel, tr);
    // set por next state function
    GBsetNextStateAll(pormodel, tr_next_all);

    // copy all the other data from the original model
    GBinitModelDefaults(&pormodel, model);
    int s0[tr->nslots];
    GBgetInitialState(model, s0);
    GBsetInitialState(pormodel, s0);

    // Create groups
    tr->group_start = pins_get_group_count(model);
    for(int i = 0; i < tr->nprocs; i++) {
        leap_add_leap_group(pormodel, model);
    }

    return pormodel;
}
