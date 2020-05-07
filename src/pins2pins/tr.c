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

typedef enum {
    Disabled = 0,
    Enabled  = 1
} status_t;

typedef struct tr_ctx {
    model_t         model;
    size_t          nguards;  // number of guards (groups)
    size_t          nactions; // number of actions (groups)
    size_t          nslots;   // number of variables in state vector
    list_t          **ncommute; // dna[a] is a list of not commuting actions for action a
    list_t          **nes;      // nes[g] is a list of NES actions for guard g

    status_t       *guard_status;   // guard enabled or disabled
    status_t       *action_status;  // action enabled or disabled

    // for search over ations:
    list_t         *queued;
    bool           *action_selected;// action selected or not

    process_t          *procs;
    int                *g2p;
    size_t              num_procs;
    dfs_stack_t        *queue[2];

    // for callback
    TransitionCB    cb_org;
    void           *ctx_org;
    size_t          emitted;
} tr_context_t;

void
tr_cb_filter (void *context, transition_info_t *ti, int *dst, int *cpy)
{
    int action = ti->group;
    tr_context_t *por = (tr_context_t*) context;
    if (por->action_selected[action]) {
        por->cb_org(por->ctx_org, ti, dst, cpy);
        por->emitted++;
    }
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

/**
 * Emits subset of ations to search algorithm
 */
int
tr_next_all (model_t self, int *src, TransitionCB cb, void *ctx)
{
    tr_context_t *tr = (tr_context_t*) GBgetContext(self);
	// read state label values (including guards)
    GBgetStateLabelsAll(tr->model, src, (int *) tr->guard_status);
    
	list_t* coveredset = list_create(tr->nactions);
	list_t* workset = list_create(tr->nactions);
	
	for (int a = 0; a < tr->nactions; a++) {            // actions
        tr->action_status[a] = find_disabled(tr, a) == -1; // set action enabledness
        // enable one action
		if (tr->action_status[a] && list_count(tr->queued) == 0) {
            list_add (tr->queued, a);
			list_add (workset, a);
            tr->action_selected[a] = true;
        }
    }

	while(list_count(workset) > 0) {
		// get an item from the workset
		int cur = list_top(workset);
		list_pop(workset);
		if(list_find(coveredset, cur) == -1) {
		}

	}


	// Cleanup
	list_free(coveredset);
	list_free(workset);

    // Forward the next selected successor states to the algorithm:
    tr->cb_org = cb;
    tr->ctx_org = ctx;
    tr->emitted = 0;
    GBgetTransitionsAll (tr->model, src, tr_cb_filter, (void *)tr);
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
    tr->nguards = GBgetStateLabelGroupInfo(model, GB_SL_GUARDS)->count;
    tr->nslots = pins_get_state_variable_count (model);
    tr->guard_status = malloc(sizeof(status_t[pins_get_state_label_count(model)]));
    tr->action_status = malloc(sizeof(status_t[tr->nactions]));

    Print ("Number of actions: %zu", tr->nactions);
    Print ("Number of guards: %zu / %zu state labels", tr->nguards, pins_get_state_label_count(model));

    tr->action_selected = malloc(sizeof(bool[tr->nactions]));
    tr->queued = list_create (tr->nactions);

    matrix_t *dna = GBgetDoNotAccordInfo(model); // non-commuting actions
    Assert (dm_nrows(dna) == tr->nactions && dm_ncols(dna) == tr->nactions);
    tr->ncommute = (list_t **) dm_rows_to_idx_table (dna);

    matrix_t *nes = GBgetGuardNESInfo(model); // non-commuting actions
    Assert (dm_nrows(nes) == pins_get_state_label_count(model) &&
            dm_ncols(nes) == tr->nactions);
    tr->nes = (list_t **) dm_rows_to_idx_table (nes);


    tr->g2p = RTmallocZero (sizeof(int[tr->nactions]));
    tr->procs = identify_procs (model, &tr->num_procs, tr->g2p);
    tr->queue[0] = dfs_stack_create (tr->nslots);
    tr->queue[1] = dfs_stack_create (tr->nslots);

    // create fresh PINS model
    model_t             pormodel = GBcreateBase ();

    // set POR as new context
    GBsetContext (pormodel, tr);
    // set por next state function
    GBsetNextStateAll   (pormodel, tr_next_all);

    // copy all the other data from the original model
    GBinitModelDefaults (&pormodel, model);
    int                 s0[tr->nslots];
    GBgetInitialState (model, s0);
    GBsetInitialState (pormodel, s0);

	fprintf(stdout, "lolol");

    return pormodel;
}

