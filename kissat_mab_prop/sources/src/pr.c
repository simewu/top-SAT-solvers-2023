#include "internal.h"
#include "search.h"
#include "propsearch.h"
#include "application.h"
#include "inline.h"
#include "simplify.h"
#include "learn.h"
#include "sort.h"
#include "resources.h"
#include "learn.h"
#include "import.h"
static unsigned next_variable(kissat * solver) {
    for(unsigned i = 0; i < VARS; i++) {
        if(ACTIVE(i) && solver->values[LIT(i)] == 0) {
            return i;
        }
    }
    return INVALID_IDX;
}
typedef struct application application;
static bool less_int(int a, int b) {
    return a < b;
}
/*static inline int binary_search(unsigned * map, int n, unsigned target) {
    int le = 0, ri = n - 1;
    while(le != ri) {
        int mid = (le + ri) / 2;
        if(map[mid] == target) return mid;
        else if(map[mid] < target) {
            le = mid + 1;
        }else {
            ri = mid - 1;
        }
    }
    if(map[le] != target) {
        for(;;);
    }
    return le;
}*/
static bool check_pr(kissat * solver, int * unsat) {
    if(kissat_process_time() > solver->pr_start_time + 100) {
        return false;
    }
    kissat * inner = kissat_init(0);
    inner->inner = true;//mark of inner solver, no simplify, no pr
    application application;
    init_app(&application, inner);
    int res = parse_options(&application, 0, NULL);
    //printf("c pr candidate: ");
    
    //static double tot_time =0 ;
        
    unsigned * map = (unsigned * )malloc(sizeof(unsigned) * SIZE_STACK(solver->trail));
    unsigned * pam = (unsigned * )calloc(VARS, sizeof(unsigned));
    
    for(unsigned t = 0; t < SIZE_STACK(solver->trail); t++) {
        map[t] = IDX(PEEK_STACK(solver->trail, t));
    }
    SORT(unsigned, SIZE_STACK(solver->trail), map, less_int);
    for(unsigned t = 0; t < SIZE_STACK(solver->trail); t++) {
        pam[map[t]] = t;
    }
    kissat_reserve(inner, SIZE_STACK(solver->trail));
    for(unsigned t = 1; t < SIZE_STACK(solver->frames); t++){
        unsigned  lit = PEEK_STACK(solver->frames, t).decision;
        int mapped_lit = pam[IDX(lit)] + 1;
        mapped_lit = -1 * mapped_lit * BOOL_TO_VALUE(lit & 1);
        kissat_add(inner, mapped_lit);
        //printf(" %d", mapped_lit);
    }
    kissat_add(inner, 0);
    //printf("\n");
    //printf("%lu\n", SIZE_STACK(solver->clauses));
    res = 0;
    for(unsigneds * clause = solver->clauses.begin; clause != solver->clauses.end; clause++) {
        bool sat = false;
        for(unsigned * itr = clause->begin; itr != clause->end; itr++) {
            unsigned lit = *itr;
            if(solver->values[lit] > 0) {
                sat = true;
                break;
            }
        }
        if(sat == false) {
            continue;
        }
        //printf("check clause: ");
        for(unsigned * itr = clause->begin; itr != clause->end; itr++) {
            unsigned lit = *itr;
            if(solver->values[lit]) {
                int mapped_lit = pam[IDX(lit)] + 1;
                mapped_lit = mapped_lit * BOOL_TO_VALUE(lit & 1);
                kissat_add(inner, mapped_lit);
        //        printf(" %d", mapped_lit);
            }
        }
        //printf("\n");
        kissat_add(inner, 0);
        if(inner->inconsistent) {
            res = 20;
            break;
        }
    }
    //printf("%.6f\n", tot_time);
    //printf("res = %d\n",res);
    if(res == 0) {
        res = kissat_solve(inner);
    }
    //printf("c inner solve result: %d (inner trail size = %lu)\n", res, inner->trail.end - inner->trail.begin);
    if(res == 10) {
        unsigneds lits;
        INIT_STACK(lits);
        for(unsigned t = 1; t < SIZE_STACK(solver->frames); t++){
            unsigned lit = PEEK_STACK(solver->frames, t).decision;
            int mapped_lit = pam[IDX(lit)] + 1;
            mapped_lit = -1 * mapped_lit * BOOL_TO_VALUE(lit & 1);
        }
        /*for(unsigned t = 0; t < SIZE_STACK(solver->trail); t++) {
            printf("innervalue[%d] = %d\n", t, inner->values[LIT(t)]);
        }*/
        for(unsigned t = 1; t < SIZE_STACK(solver->frames); t++){
            PUSH_STACK(lits, 1 ^ PEEK_STACK(solver->frames, t).decision);
            //printf("%d\n", TOP_STACK(lits));
        }   
        unsigned siz = SIZE_STACK(lits);
        unsigned head = INVALID_LIT;
        //printf("c pr head = %u\n", head);
        for(unsigned t = 0; t < SIZE_STACK(solver->trail); t++) {
            //printf("c t %u/%lu\n", t, SIZE_STACK(solver->trail));
            unsigned olit = PEEK_STACK(solver->trail, t);
            //printf("c olit = %u, idx = %u\n", olit, pam[IDX(olit)]);
            //unsigned ilit = kissat_import_literal(inner, BOOL_TO_VALUE(olit & 1) * (pam[IDX(olit)] + 1));
            int value = kissat_value(inner, BOOL_TO_VALUE(olit & 1) * (pam[IDX(olit)] + 1));
            //printf("c value of %u=%d\n", olit, value);
            //printf("c ilit = %u\n", ilit);
            PUSH_STACK(lits, ((olit >> 1) << 1) ^ (value > 0 ? 0 : 1));
            for(unsigned s = 0; s < siz; s++) {
            //printf("c s %u/%u\n", s, siz);
                if(PEEK_STACK(lits, s) == TOP_STACK(lits)) {
                    head = TOP_STACK(lits);
                }
            }
        }
        //printf("c pr head = %u\n", head);
        //proof * proof = solver->proof;
        unsigned swp = INVALID_LIT;
        for(unsigned i = 0; i < siz; i++) {
            if(i == 0) {
                swp = PEEK_STACK(lits, i);
                POKE_STACK(lits, i, head);
            }else if(PEEK_STACK(lits, i) == head) {
                POKE_STACK(lits, i, swp);
            }
        }
        for(unsigned i = siz; i < SIZE_STACK(lits); i++) {
            if(i == siz) {
                swp = PEEK_STACK(lits, i);
                POKE_STACK(lits, i, head);
            }else if(PEEK_STACK(lits, i) == head) {
                POKE_STACK(lits, i, swp);
            }
        }
        for(unsigned i = 0; i < SIZE_STACK(lits); i++) {
            int lit = PEEK_STACK(lits, i);
            //printf(" %u", lit);
            lit = (lit / 2 + 1) * BOOL_TO_VALUE(lit & 1);
            
        }
        //printf("\n");
        //printf("c pr adddddddddddddddddddddddd proof %u\n", SIZE_STACK(lits));
        if(solver->proof) {
        	kissat_add_lits_to_proof(solver, SIZE_STACK(lits), lits.begin);
        }
        //printf("backtracking\n");

        unlucky_backtrack(solver, solver->level - 1);
        //printf("backtracked\n");
        for(unsigned t = 0; t < siz; t++) {
            PUSH_STACK(solver->clause.lits, PEEK_STACK(lits, t));
        }
        *unsat = kissat_learn_pr(solver);
        kissat_release(inner);
        free(map);
        //printf("c return true\n");
        return true;
        //learn clause, backtrack for 1 level
    }
    kissat_release(inner);
    free(map);
    //printf("c return false\n");
    return false;
}
int kissat_pr_search(kissat * solver) {
    //unsigned n = VARS;
    unsigneds q;
    INIT_STACK(q);
    PUSH_STACK(q, next_variable(solver));
    if(PEEK_STACK(q, 0) == INVALID_IDX) {
        return 10;
    }
    unsigneds cand_pr, pr_decisions, pr_trail;
    INIT_STACK(cand_pr);
    INIT_STACK(pr_decisions);
    INIT_STACK(pr_trail);
    unsigned tim = 0;
    unsigned * inqueue = (unsigned *) calloc(VARS, sizeof(unsigned));
    inqueue[PEEK_STACK(q, 0)] = 1;
    unsigned * vst = (unsigned * ) calloc(VARS, sizeof(unsigned));
    int unsat = 10;
    solver->pr_start_time = kissat_process_time();
    for(unsigned op = 0; op < SIZE_STACK(q); op++) {
        if(kissat_process_time() > solver->pr_start_time + 100) break;
//    	printf("c op = %d, clauses =%d\n", op, SIZE_STACK(solver->clauses));
        unsigned v = PEEK_STACK(q, op);
        //printf("bfs %u\n", v);
        for(unsigned lit = v * 2; lit < v * 2 + 2; lit++) {
            if(solver->values[lit]) {
                continue;
            }   
            claim(solver, v, BOOL_TO_VALUE(lit & 1));
            //printf("c claim lit %d (size of frame: %lu)\n", BOOL_TO_VALUE(lit & 1) * ((int)v + 1), SIZE_STACK(solver->frames));
            clause *conflict = kissat_search_propagate(solver);
            //printf("assign %u to %d, conflict = %p\n", v, BOOL_TO_VALUE(lit & 1), conflict);
            if(conflict) {
                PUSH_STACK(solver->clause.lits, NOT(lit));
                if(20 == kissat_learn_pr(solver)) {
                    free(vst);
                    free(inqueue);
                    return 20;
                }
                continue;
            }
            if(check_pr(solver, &unsat)) {
                if(unsat == 20) {
                    free(vst);
                    free(inqueue);
                    return 20;
                }
                continue;
            }
            unsigneds neighbors;
            INIT_STACK(neighbors);
            tim++;
            for(unsigned t = 0; t < SIZE_STACK(solver->trail); t++) {
                unsigned trail_lit = PEEK_STACK(solver->trail, t);
                vst[IDX(trail_lit)] = tim;
            }
            for(unsigned t = 0; t < SIZE_STACK(solver->trail); t++) {
                unsigned trail_lit = PEEK_STACK(solver->trail, t);
                //printf("trail lit %u of decision %u\n", trail_lit, lit);
                unsigned u = IDX(trail_lit);
                for(unsigned i = 0; i < SIZE_STACK(solver->touched_list[u]); i++) {//还没初始化
                    unsigned neighbor = PEEK_STACK(solver->touched_list[u], i);
                    if(vst[neighbor] != tim) {
                        vst[neighbor] = tim;
                        PUSH_STACK(neighbors, neighbor);
                    }
                }
            }
            unlucky_backtrack(solver, 0);
            for(unsigned t = 0; t < SIZE_STACK(neighbors); t++) {
                unsigned neighbor = PEEK_STACK(neighbors, t);
                if(!inqueue[neighbor]) {
                    inqueue[neighbor] = 1;
                    PUSH_STACK(q, neighbor);
                }
                for(unsigned neighbor_lit = neighbor * 2; neighbor_lit < neighbor * 2 + 2; neighbor_lit++) {
                    if(solver->values[lit]) {
                        continue;
                    }
                    claim(solver, IDX(lit), BOOL_TO_VALUE(lit & 1));
                    clause *conflict = kissat_search_propagate(solver);
                    if(conflict) {
                        PUSH_STACK(solver->clause.lits, NOT(lit));
                        if(20 == kissat_learn_pr(solver)) {
                            free(vst);
                            free(inqueue);
                            return 20;
                        }
                        continue;
                    }
                    if(solver->values[neighbor_lit]) {
                        unlucky_backtrack(solver, 0);
                        continue;
                    }
                    claim(solver, neighbor, BOOL_TO_VALUE(neighbor_lit & 1));
                    conflict = kissat_search_propagate(solver);
                    if(!conflict) {
                        if(check_pr(solver, &unsat)) {
                            if(unsat == 20) {
                                free(vst);
                                free(inqueue);
                                return 20;
                            }
                        }
                    }else {
                        PUSH_STACK(solver->clause.lits, NOT(lit));
                        PUSH_STACK(solver->clause.lits, NOT(neighbor_lit));
                        ADD_BINARY_TO_PROOF(NOT(lit), NOT(neighbor_lit));
                        kissat_learn_pr(solver);

                        continue;
                    }
                    unlucky_backtrack(solver, 0);
                    
                }
            }
            
        }
    }
    free(vst);
    free(inqueue);
    printf("c pr over %lu %lu\n", SIZE_STACK(solver->trail), SIZE_STACK(solver->frames));
    return 10;
}
