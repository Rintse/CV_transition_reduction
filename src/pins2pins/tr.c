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
    size_t          num_procs;

    process_t*      procs;
    int*            g2p;
    dfs_stack_t*    queue[2];

	// Saves the cartesian vectors
	CV_elem_t***    CVs; // Saves states and transitions
    CV_elem_t**     tmpCVs; // For rollback when extending a CV
    int**           CV_lens;
    // Temp storage for callback
	dfs_stack_t*    stack;
    bool*           extendable;
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

int*
last_state(int i, int j, tr_context_t* tr) {
    return tr->CVs[i][j][tr->CV_lens[i][j]-1].state;
}

// STACK STUFF
// ============================================================================
bool
pop_stack_to_CV(tr_context_t* tr, int i, int j) {
    if(dfs_stack_size(tr->stack) == 0) {
        return false;
    }

    int* temp = dfs_stack_pop(tr->stack);
    tr->CVs[i][j][tr->CV_lens[i][j]].transition = *temp;
    memcpy(tr->CVs[i][j][tr->CV_lens[i][j]].state, temp+1, tr->nslots*sizeof(int));
    tr->CV_lens[i][j]++;
    return true;
}

void
pop_state(tr_context_t* tr, int* tempvec) {
    if(dfs_stack_size(tr->stack) == 0) {
        return;
    }

    int* temp = dfs_stack_pop(tr->stack);
    memcpy(tempvec, temp+1, tr->nslots*sizeof(int));
}

int
pop_transition(tr_context_t* tr) {
    if(dfs_stack_size(tr->stack) == 0) {
        return -1;
    }

    return *dfs_stack_pop(tr->stack);
}

void
stack_push(void* context, transition_info_t* ti, int* dst, int* cpy) {
	tr_context_t *tr = (tr_context_t*) context;
	int* temp = dfs_stack_push(tr->stack, NULL);
    memcpy(temp, &ti->group, sizeof(int));
    memcpy(temp+1, dst, tr->nslots*sizeof(int));
}

// ============================================================================

void
commute_last(int CV1, tr_context_t* tr) {
    for(int CV2 = 0; CV2 < tr->num_procs; CV2++) {
        if(CV2 == CV1) continue;
        if(!(tr->extendable[CV1] || tr->extendable[CV2])) continue;

        if(memcmp(
            last_state(CV1, CV2, tr), last_state(CV2, CV1, tr), tr->nslots*sizeof(int)
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
    for(int CV2 = 0; CV2 < tr->num_procs; CV2++) {
        if(CV2 == CV1) continue;
        int* temp = last_state(CV1, CV1, tr);
        GBgetTransitionsLong(self, t, temp, stack_push, ctx);
        pop_state(tr, tr->temp3);
        int* temp2;

        for(int i = 0; i < tr->CV_lens[CV1][CV2]-2; i++) {
            temp2 = tr->CVs[CV1][CV2][i].state;
            int a = tr->CVs[CV1][CV2][i].transition;

            GBgetTransitionsLong(self, t, temp2, stack_push, ctx);
            pop_state(tr, tr->res1);

            GBgetTransitionsLong(self, a, tr->temp3, stack_push, ctx);
            pop_state(tr, tr->res2);

            if(memcmp(tr->res1, tr->res2, tr->nslots*sizeof(int)) != 0) {
                return false;
            }

            temp = temp2;
            temp3 = res1;

            // Save (a,res1) to temp vector
            tr->tempCVs[CV2][i].state
        }
    }

    return true;
}

// Concatenate CV2 after CV1
void
concatenate(model_t self, tr_context_t* tr, void* ctx, int CV1, int CV2) {
    int* temp = tr->CVs[CV1][CV1][tr->CV_lens[CV1][CV1]-1].state;

    for(int i = 0; i < tr->CV_lens[CV2][CV2]; i++) {
        GBgetTransitionsLong(self, tr->CVs[CV2][CV2][i].transition, temp, stack_push, ctx);
        pop_stack_to_CV(tr, CV1, CV2);
        temp = tr->CVs[CV1][CV2][tr->CV_lens[CV1][CV2]-1].state;
    }
}

void
nextStateProc(model_t self, tr_context_t* tr, int* src, int proc, void* ctx) {
    for(int j = 0; j < list_count(tr->procs[proc].groups); j++) {
        int g = list_get(tr->procs[proc].groups, j);
        GBgetTransitionsLong(self, g, src, stack_push, ctx);
    }

    Assert(dfs_stack_size(tr->stack) <= 1, "Radical! Non-determinism found.");
}

void
extendCV(tr_context_t* tr, int CV, int t) {
    return;
}

void
init(tr_context_t *tr, model_t self, int *src, void *ctx) {
    tr->extendable_count = tr->num_procs;

    // Add first next state for all processes
    for(int i = 0; i < tr->num_procs; i++) {
        for(int j = 0; j < tr->num_procs; j++){
            tr->CV_lens[i][j] = 0;
        }

        nextStateProc(self, tr, src, i, ctx);
        if(pop_stack_to_CV(tr, i, i)) {
            tr->extendable[i] = true;
        }
        else {
            tr->extendable[i] = false;
            tr->extendable_count--;
        }
    }

    for(int i = 0; i < tr->num_procs; i++) {
        for(int j = 0; j < tr->num_procs; j++) {
            if(i != j) {
                // Initialize all combinations of CVs
                concatenate(self, tr, ctx, i, j);
            }
        }
    }

    for(int i = 0; i < tr->num_procs; i++) {
        commute_last(i, tr);
    }
}

int
tr_next_all (model_t self, int *src, TransitionCB cb, void *ctx)
{
    tr_context_t *tr = (tr_context_t*) GBgetContext(self);
	// CV ALGO
	// ===========================================================================
    init(tr, self, src, ctx);

    int cur = 0;
    while(tr->extendable_count > 0) {
        while(!tr->extendable[cur]) { cur++; }
        nextStateProc(self, tr, last_state(cur, cur, tr), cur, ctx);

        int next_t = pop_transition(tr);
        if(next_t == -1) {
            tr->extendable[cur] = false;
            tr->extendable_count--;
            continue;
        }

        if(!commute_nonlast(cur, next_t, tr, self, ctx)) {
            tr->extendable[cur] = false;
            tr->extendable--;
        }
        else {
            extendCV(tr, cur, next_t);
            commute_last(cur, tr);
        }


    }


	// ===========================================================================

    // Forward the next selected successor states to the algorithm:
    //TODO
    tr->cb_org = cb;
    tr->ctx_org = ctx;
    tr->emitted = 0;
    return tr->emitted;
}

/**
 * Setup the partial order reduction layer.
 */
model_t
pins2pins_tr (model_t model)
{
    fprintf(stderr, "testertst/\n");
	if (!pins_has_guards(model)) {
        Abort ("Frontend doesn't have guards. Ignoring --por.");
    }

    tr_context_t *tr = malloc(sizeof *tr);
    tr->model = model;
    tr->nactions = pins_get_group_count(model);
    tr->nslots = pins_get_state_variable_count (model);
    tr->procs = identify_procs(model, &tr->num_procs, tr->g2p);
    Print ("Number of actions: %zu", tr->nactions);


    // Allocate space for cartesian vectors
	tr->CVs = (CV_elem_t***) malloc(MAX_N_PROCS * sizeof(CV_elem_t**));
    tr->tempCVs = (CV_elem_t**) malloc(MAX_N_PROCS * sizeof(CV_elem_t*));
    for(int i = 0; i < MAX_N_PROCS; i++) {
        tr->CVs[i] = (CV_elem_t**) malloc(MAX_N_PROCS * sizeof(CV_elem_t*));
        tr->tempCVs[i] = (CV_elem_t*) malloc(MAX_CV_SIZE * sizeof(CV_elem_t));

        for(int j = 0; j < MAX_CV_SIZE; j++) {
            tr->tempCVs[i][j].state = (int*) malloc(tr->nslots*sizeof(int));
        }

        for(int j = 0; j < MAX_N_PROCS; j++) {
            tr->CVs[i][j] = (CV_elem_t*) malloc(MAX_CV_SIZE * sizeof(CV_elem_t));
            for(int k = 0; k < MAX_CV_SIZE; k++) {
                tr->CVs[i][j][k].state = (int*) malloc(tr->nslots*sizeof(int));
            }
        }
    }
    tr->CV_lens = (int**) malloc(MAX_N_PROCS * sizeof(int*));
    for(int i = 0; i < MAX_N_PROCS; i++) {
        tr->CV_lens[i] = (int*) malloc(MAX_N_PROCS * sizeof(int));
    }

    tr->stack = dfs_stack_create(tr->nslots+1);
    tr->extendable = (bool*) malloc(tr->num_procs * sizeof(bool));

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

    return pormodel;
}
