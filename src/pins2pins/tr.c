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


typedef enum {
    Disabled = 0,
    Enabled  = 1
} status_t;

typedef struct tr_ctx {
    model_t         model;
    size_t          nslots;   // number of variables in state vector
	size_t			nactions;
	size_t 			nguards;

    process_t          *procs;
    int                *g2p;
    size_t              num_procs;
    dfs_stack_t        *queue[2];

	status_t       *guard_status;   // guard enabled or disabled
    status_t       *action_status;  // action enabled or disabled

	// Saves the cartesian vectors
	int*** CVs;
	list_t* tmp_next;

    // for callback
    TransitionCB    cb_org;
    void           *ctx_org;
    size_t          emitted;
} tr_context_t;

void
tr_next_push(void* context, transition_info_t* ti, int* dst, int* cpy) {
	tr_context_t *tr = (tr_context_t*) context;
	list_add(tr->tmp_next, )
}

void
tr_cb_filter (void *context, transition_info_t *ti, int *dst, int *cpy)
{
    tr_context_t *tr = (tr_context_t*) context;
    tr->cb_org(tr->ctx_org, ti, dst, cpy);
    tr->emitted++;
}


static inline int
find_disabled(tr_context_t *por, int a)
{
    // iterate over guards of a2
    guard_t *guards = GBgetGuard (por->model, a);
    for (int j = 0; j < guards->count; j++) {
        int g = guards->guard[j];
        if (por->guard_status[g] == Disabled) {
            return g;
        }
    }
    return -1;
}


int
tr_next_all (model_t self, int *src, TransitionCB cb, void *ctx)
{
    tr_context_t *tr = (tr_context_t*) GBgetContext(self);
	// read state label values (including guards)
    GBgetStateLabelsAll(tr->model, src, (int *) tr->guard_status);
	for (int a = 0; a < tr->nactions; a++) {
    	tr->action_status[a] = find_disabled(tr, a) == -1; // disabled?
    }    

	// CV ALGO
	// ===========================================================================
	int* proc_idx;
	// Add first transition for all processes
		
		
	
	// ===========================================================================

    // Forward the next selected successor states to the algorithm:
    tr->cb_org = cb;
    tr->ctx_org = ctx;
    tr->emitted = 0;
    GBgetTransitionsAll(tr->model, src, tr_cb_filter, (void *)tr);
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
	tr->nguards = GBgetStateLabelGroupInfo(model, GB_SL_GUARDS)->count;
    tr->nslots = pins_get_state_variable_count (model);
    tr->guard_status = malloc(sizeof(status_t[pins_get_state_label_count(model)]));
    tr->action_status = malloc(sizeof(status_t[tr->nactions]));
	
	tr->CVs = (int***) malloc(MAX_N_PROCS * sizeof(int**));
	for(int i = 0; i < MAX_N_PROCS; i++) {
		tr->CVs[i] = (int**) malloc(MAX_CV_SIZE * sizeof(int*));
	}

    Print ("Number of actions: %zu", tr->nactions);

    tr->procs = identify_procs (model, &tr->num_procs, tr->g2p);
    
	// create fresh PINS model
    model_t pormodel = GBcreateBase ();

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

