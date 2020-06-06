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
#define MAX_N_PROCS 64
#define MAX_DETERMINISM 10


typedef enum {
    Disabled = 0,
    Enabled  = 1
} status_t;


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
	int***          CV_S; // Saves states
    int**           CV_T; // Saves transitions
    int*            CV_lens;
	dfs_stack_t*    state_stack;
    list_t*         trans_stack;

    // Map groups to procs
    int*            procmap;

    // for callback
    TransitionCB    cb_org;
    void*           ctx_org;
    size_t          emitted;
} tr_context_t;

// int*
// get_procgroup_map(tr_context_t* tr) {
//     int* m = (int*) malloc(tr->nactions * sizeof(int));
//
//     for(int i = 0; i < tr->num_procs; i++) {
// 		for(int j = 0; j < list_count(tr->procs[i].groups); j++) {
//             m[list_get(tr->procs->groups, j)] = i;
// 		}
// 	}
//
//     return m;
// }


// bool commuteLast(int** CV1, int** CV2, g) {
//     return true;
// }


void
stack_push(void* context, transition_info_t* ti, int* dst, int* cpy) {
	tr_context_t *tr = (tr_context_t*) context;
	dfs_stack_push(tr->state_stack, dst);
    list_add(tr->trans_stack, ti->group);
}

void nextStateProc(model_t self, tr_context_t* tr, int* src, int proc, void* ctx) {
    for(int j = 0; j < list_count(tr->procs[proc].groups); j++) {
        int g = list_get(tr->procs[proc].groups, j);
        GBgetTransitionsLong(self, g, src, stack_push, ctx);
    }

    Assert(dfs_stack_size(tr->state_stack) <= 1, "Radical! Non-determinism found.");
}

int
tr_next_all (model_t self, int *src, TransitionCB cb, void *ctx)
{
    tr_context_t *tr = (tr_context_t*) GBgetContext(self);
	// CV ALGO
	// ===========================================================================
    // Add first next state for all processes
    for(int i = 0; i < tr->num_procs; i++) {
        tr->CV_lens[i] = 1;
        nextStateProc(self, tr, src, i, ctx);
        // stack should be empty after this statement
        tr->CV_S[i][0] = dfs_stack_pop(tr->state_stack);
        tr->CV_T[i][0] = list_pop(tr->trans_stack);
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
    Print ("Number of actions: %zu", tr->nactions);


    // Allocate space for cartesian vectors
	tr->CV_S = (int***) malloc(MAX_N_PROCS * sizeof(int**));
    tr->CV_T = (int**) malloc(MAX_N_PROCS * sizeof(int*));
    tr->CV_lens = (int*) malloc(MAX_N_PROCS * sizeof(int));
	for(int i = 0; i < MAX_N_PROCS; i++) {
		tr->CV_S[i] = (int**) malloc(MAX_CV_SIZE * sizeof(int*));
        tr->CV_T[i] = (int*) malloc(MAX_CV_SIZE * sizeof(int));
	}

    tr->procs = identify_procs(model, &tr->num_procs, tr->g2p);
    // Create a (group -> process) mapping
    //tr->procmap = get_procgroup_map(tr);
    tr->state_stack = dfs_stack_create(tr->nslots);
    tr->trans_stack = list_create(MAX_DETERMINISM);

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
