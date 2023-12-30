#include "analyze.h"
#include "decide.h"
#include "eliminate.h"
#include "internal.h"
#include "logging.h"
#include "print.h"
#include "probe.h"
#include "propsearch.h"
#include "search.h"
#include "reduce.h"
#include "reluctant.h"
#include "report.h"
#include "restart.h"
#include "terminate.h"
#include "trail.h"
#include "resources.h"
#include "walk.h"
#include "literal.h"
#include "dense.h"
#include "allocate.h"
#include <inttypes.h>
#include "pr.h"
#include "simplify.h"
static void start_search(kissat *solver)
{
    START(search);
    INC(searches);

    REPORT(0, '*');


    bool stable = (GET_OPTION(stable) == 2) && !solver->PSIDS;

    solver->stable = stable;
    kissat_phase(solver, "search", GET(searches), "initializing %s search after %" PRIu64 " conflicts",
        (stable ? "stable" : "focus"), CONFLICTS);

    kissat_init_averages(solver, &AVERAGES);
    if (solver->stable)
        kissat_init_reluctant(solver);

    kissat_init_limits(solver);

    unsigned seed = GET_OPTION(seed);
    solver->random = seed;
    LOG("initialized random number generator with seed %u", seed);

    kissat_reset_rephased(solver);

    const unsigned eagersubsume = GET_OPTION(eagersubsume);
    if (eagersubsume && !solver->clueue.elements)
        kissat_init_clueue(solver, &solver->clueue, eagersubsume);
#ifndef QUIET
    limits *limits = &solver->limits;
    limited *limited = &solver->limited;
    if (!limited->conflicts && !limited->decisions)
        kissat_very_verbose(solver, "starting unlimited search");
    else if (limited->conflicts && !limited->decisions)
        kissat_very_verbose(solver, "starting search with conflicts limited to %" PRIu64, limits->conflicts);
    else if (!limited->conflicts && limited->decisions)
        kissat_very_verbose(solver, "starting search with decisions limited to %" PRIu64, limits->decisions);
    else
        kissat_very_verbose(solver,
            "starting search with decisions limited to %" PRIu64 " and conflicts limited to %" PRIu64,
            limits->decisions, limits->conflicts);
    if (stable) {
        START(stable);
        REPORT(0, '[');
    } else {
        START(focused);
        REPORT(0, '{');
    }
#endif
}

static void stop_search(kissat *solver, int res)
{
    if (solver->limited.conflicts) {
        LOG("reset conflict limit");
        solver->limited.conflicts = false;
    }

    if (solver->limited.decisions) {
        LOG("reset decision limit");
        solver->limited.decisions = false;
    }

    if (solver->terminate) {
        kissat_very_verbose(solver, "termination forced externally");
        solver->terminate = 0;
    }

#ifndef QUIET
    LOG("search result %d", res);
    if (solver->stable) {
        REPORT(0, ']');
        STOP(stable);
        solver->stable = false;
    } else {
        REPORT(0, '}');
        STOP(focused);
    }
    char type = (res == 10 ? '1' : res == 20 ? '0' : '?');
    REPORT(0, type);
#else
    (void)res;
#endif

    STOP(search);
}

static void iterate(kissat *solver)
{
    assert(solver->iterating);
    solver->iterating = false;
    REPORT(0, 'i');
}

static bool conflict_limit_hit(kissat *solver)
{
    if (!solver->limited.conflicts)
        return false;
    if (solver->limits.conflicts > solver->statistics.conflicts)
        return false;
    kissat_very_verbose(solver, "conflict limit %" PRIu64 " hit after %" PRIu64 " conflicts", solver->limits.conflicts,
        solver->statistics.conflicts);
    return true;
}

static bool decision_limit_hit(kissat *solver)
{
    if (!solver->limited.decisions)
        return false;
    if (solver->limits.decisions > solver->statistics.decisions)
        return false;
    kissat_very_verbose(solver, "decision limit %" PRIu64 " hit after %" PRIu64 " decisions", solver->limits.decisions,
        solver->statistics.decisions);
    return true;
}

inline void claim(kissat *solver, unsigned idx, value value)
{
    solver->level++;
    unsigned lit = LIT(idx);
    if (solver->values[lit] != 0) {
        printf("c error\n");
        for(;;);
    }
    if (value < 0)
        lit = NOT(lit);
    kissat_push_frame(solver, lit);
    LOG("(luckily)decide literal %s", LOGLIT(lit));
    kissat_assign_decision(solver, lit);
}

inline void unassign(kissat *solver, value *values, unsigned lit)
{
    LOG("unassign %s", LOGLIT(lit));
    const unsigned not_lit = NOT(lit);
    values[lit] = values[not_lit] = 0;
    assert(solver->unassigned < VARS);
    solver->unassigned++;
}
void unlucky_backtrack(kissat *solver, unsigned new_level)
{
    assert(solver->level >= new_level);
    if (solver->level == new_level)
        return;

    LOG("unlucky backtracking to decision level %u", new_level);

    frame *new_frame = &FRAME(new_level + 1);
    const unsigned new_size = new_frame->trail;
    SET_END_OF_STACK(solver->frames, new_frame);

    value *values = solver->values;
    unsigned *trail = BEGIN_STACK(solver->trail);

    const unsigned old_size = SIZE_STACK(solver->trail);
    unsigned unassigned = 0, reassigned = 0;

    unsigned j = new_size;
    for (unsigned i = j; i != old_size; i++) {
        const unsigned lit = trail[i];
        // const unsigned idx = IDX(lit);
        //assert(idx < VARS);
        unassign(solver, values, lit);
        unassigned++;
    }
    RESIZE_STACK(solver->trail, j);

    solver->level = new_level;
    LOG("unassigned %u literals", unassigned);
    LOG("reassigned %u literals", reassigned);
    (void)unassigned, (void)reassigned;
    assert(new_size <= SIZE_STACK(solver->trail));
    LOG("propagation will resume at trail position %u", new_size);
    solver->propagated = new_size;

    assert(!solver->extended);
}
int lucky(kissat *solver, int direction, value lv)
{
    int st, ed, delta;
    if (direction == 1) {
        st = 0;
        ed = VARS;
        delta = 1;
    } else {
        st = VARS - 1;
        ed = 0;
        delta = -1;
    }
    for (unsigned v = 0; v < VARS; v++) {
        if(!FLAGS(v)->active) continue;
        if (solver->simplified_hints[v]) {
            if (solver->values[LIT(v)] != solver->simplified_hints[v]) {
                return 30;
            } else {
                if (solver->values[LIT(v)] == 0) {
                    claim(solver, v, solver->simplified_hints[v]);
                    clause *conflict = kissat_search_propagate(solver);
                    if (conflict) {
                        return 30;
                    }
                }
            }
        }
    }
    for (int v = st; v != ed; v += delta) {
        if(!FLAGS(v)->active) continue;
        if (solver->values[LIT(v)] != 0)
            continue;
        value vh = lv; // trust hints
        claim(solver, v, vh);
        clause *conflict = kissat_search_propagate(solver);
        if (conflict) {
            unlucky_backtrack(solver, solver->level - 1);
            claim(solver, v, -vh);
            clause *conflict = kissat_search_propagate(solver);
            if (conflict) {
                // unlucky
                return 30;
            } else {
            }
        } else {
        }
        if (!solver->unassigned) {
            return 10;
        }
    }
    return 30;
}


int kissat_search(kissat *solver)
{
    start_search(solver);
    if (VARS == 0) {
        return 10;
    }
    if (true) {
        for (int dir = 1; dir >= 0; dir--) {
            for (int val = 1; val >= -1; val -= 2) {
                if (10 == lucky(solver, dir, val)) {
                    // exit(0);
                    return 10;
                }
                LOG("unlucky. backtrack to level 0.");
                /*for(unsigned i = 0; i < SIZE_STACK(solver->frames); i++) {
                    printf("frames[%u] = %lu\n", i, PEEK_STACK(solver->frames, i).decision);
                }*/
                unlucky_backtrack(solver, 0);
                //kissat_flush_trail(solver);
            }
        }
    }
    if(!solver->inner && solver->S->clauses <= 10000 && (!solver->proof || solver->proof->binary)) {
        if(20 == kissat_pr_search(solver)) {
            for(unsigned i = 0; i < VARS; i++) {
                RELEASE_STACK(solver->touched_list[i]);
            }
            return 20;
        }
    }
    for(unsigned i = 0; i < SIZE_STACK(solver->clauses); i++) {
        RELEASE_STACK(PEEK_STACK(solver->clauses, i));
    }
    RELEASE_STACK(solver->clauses);
    for(unsigned i = 0; i < VARS; i++) {
        RELEASE_STACK(solver->touched_list[i]);
    }
    int res = kissat_walk_initially(solver);


    if (true) {
        solver->mab_last_time = 0;
        solver->mab_last_propagations = 0;
        solver->mab_last_ticks = 0;
    }
    bool init_decides[2] = {true, true};
    unsigneds init_decisions[2];
    init_decides[0] = init_decides[1] = false;
    for(int d = 0; d < 2; d++) {
        INIT_STACK(init_decisions[d]);
    }
    //int _ = 0;
    int timeout = GET_OPTION(timeout);
    while (!res) {
        //printf("c _ = %d\n", _++);
        
        if (timeout && kissat_process_time() >= timeout) {
            res = 30;
            break;
        }
        unsigned unassigned_before_propagation = solver->unassigned;
        clause *conflict = kissat_search_propagate(solver);
    
        if(!conflict && solver->unassigned == unassigned_before_propagation) {
            
        }else {
            if(init_decides[solver->heuristic]) {
                unsigned size = SIZE_STACK(init_decisions[solver->heuristic]);
                heap * scores = solver->heuristic == 0 ? &solver->scores : &solver->scores_chb;
                const word *arena = BEGIN_STACK(solver->arena);
                for(unsigned i = size; ; ) {
					if(i == 0) break;
					else i--;
                    unsigned lit = PEEK_STACK(init_decisions[solver->heuristic], i);
                    double beta = (i + 1.) / size;
                    unsigned not_lit = NOT(lit);
                    watches *watches = &WATCHES(not_lit);
                    watch *begin_watches = BEGIN_WATCHES(*watches), *q = begin_watches;
                    const watch *end_watches = END_WATCHES(*watches);
                    while (q != end_watches) {
                        const watch head = *q++;
                        unsigned other = head.blocking.lit;
                        unsigned idx = IDX(other);
                        if (head.type.binary) {
							if(0 == kissat_get_heap_score(scores, idx)) {
	                            kissat_update_heap(solver, scores, idx, beta);
							}
                        } else {
                            const watch tail = *q++;
                            const reference ref = tail.raw;
                            clause *c = (clause *)(arena + ref);
                            if (c->garbage) {
                                continue;
                            }
                            unsigned *lits = BEGIN_LITS(c);
                            const unsigned *end_lits = lits + c->size;
                            for(unsigned * r = lits; r != end_lits; r++) {
                                other = *r;
                                idx = IDX(other);
								if(idx != IDX(lit) && 0 == kissat_get_heap_score(scores, idx)) {
		                            kissat_update_heap(solver, scores, idx, beta);
								}
                            }
                        }
                    }
                }
                
            }
            init_decides[solver->heuristic] = false;
        }
        //printf("conflict = %p\n", conflict);
        if (conflict) {
            res = kissat_analyze(solver, conflict);
            /*if(_ == 6332) {
                printf("res = %d\n", res);
            }*/
//            return 20;
        } else if (solver->iterating)
            iterate(solver);
        else if (!solver->unassigned)
            res = 10;
        else if (TERMINATED(11))
            break;
        else if (conflict_limit_hit(solver))
            break;
        else if (kissat_reducing(solver))
            res = kissat_reduce(solver);
        else if (kissat_restarting(solver))
            kissat_restart(solver);
        else if (kissat_rephasing(solver))
            kissat_rephase(solver);
        else if (kissat_eliminating(solver))
            res = kissat_eliminate(solver);
        else if (kissat_probing(solver))
            res = kissat_probe(solver);
        else if (!solver->level && solver->unflushed)
            kissat_flush_trail(solver);
        else if (decision_limit_hit(solver))
            break;
        else {
            
            unsigned lit = kissat_decide(solver);
            if(init_decides[solver->heuristic]) {
                PUSH_STACK(init_decisions[solver->heuristic], lit);
            }
        }
    }
    solver->mab_last_time += kissat_process_time();
    solver->mab_time[solver->heuristic] += solver->mab_last_time;

    solver->mab_last_propagations += (int64_t)solver->statistics.propagations;
    solver->mab_propagations[solver->heuristic] += solver->mab_last_propagations;
    solver->mab_last_ticks += (int64_t)solver->statistics.ticks;
    solver->mab_ticks[solver->heuristic] += solver->mab_last_ticks;
    for(int d = 0; d < 2; d++) {
        RELEASE_STACK(init_decisions[d]);
    }
    stop_search(solver, res);
    
    return res;
}
