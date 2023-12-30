/* This program prints generators for the automorphism group of an
   n-vertex polygon, where n is a number supplied by the user.
   This version uses sparse form with dynamic allocation.
*/
#include "../bliss/bliss_C.h"

#include "internal.h"
#include "symmetry.h"
#include "simplify.h"
#include "allocate.h"
#include "resources.h"
#include "sort.h"
#include "hashmap.h"
unsigned convert_lit(int lit)
{
    unsigned ex = lit < 0 ? -lit : lit;
    ex--;
    ex = ex * 2 + (lit < 0 ? 1 : 0);
    return ex;
}

simplify *__autom_S;

void print_red_line(kissat *solver, unsigneds *clause, unsigned var, unsigned val)
{
    proof *proof = solver->proof;
    if (!proof)
        return;
    simplify *S = __autom_S;
    kissat_puts(proof->file, "red");
    for (unsigned i = 0; i < SIZE_STACK(*clause); i++) {
        unsigned lit = PEEK_STACK(*clause, i);
        int idx = lit / 2;
        int neg = lit % 2;
        if (idx <= S->vars) {
            idx = solver->mapidx[idx + 1];
        } else {
            idx = S->orivars + (idx - S->vars); // compute original idx
        }
        kissat_puts(proof->file, " 1 ");
        if (neg) {
            kissat_putc(proof->file, '~');
        }
        kissat_putc(proof->file, 'x');
        kissat_putint(proof->file, idx);
    }
    kissat_puts(proof->file, " >= 1 ; x");
    if (var <= (unsigned) S->vars) {
        var = solver->mapidx[var];
    } else {
        var = S->orivars + (var - S->vars); // compute original idx
    }
    kissat_putint(proof->file, var);
    kissat_puts(proof->file, " -> ");
    kissat_putc(proof->file, val ? '1' : '0');
    kissat_putc(proof->file, '\n');
}
void print_rup_line(kissat *solver, unsigneds *clause)
{
    proof *proof = solver->proof;
    if (!proof)
        return;
    simplify *S = __autom_S;
    kissat_puts(proof->file, "rup");
    for (unsigned i = 0; i < SIZE_STACK(*clause); i++) {
        unsigned lit = PEEK_STACK(*clause, i);
        int idx = lit / 2;
        int neg = lit % 2;
        if (idx <= S->vars) {
            idx = solver->mapidx[idx + 1];
        } else {
            idx = S->orivars + (idx - S->vars); // compute original idx
        }
        kissat_puts(proof->file, " 1 ");
        if (neg) {
            kissat_putc(proof->file, '~');
        }
        kissat_putc(proof->file, 'x');
        kissat_putint(proof->file, idx);
    }
    kissat_puts(proof->file, " >= 1 ;\n");
}

void print_div_line(kissat *solver, int id, long long div)
{
    proof *proof = solver->proof;
    if (!proof)
        return;
    //simplify *S = __autom_S;
    kissat_puts(proof->file, "pol ");
    kissat_putint(proof->file, id);
    kissat_putc(proof->file, ' ');
    kissat_putint(proof->file, div);
    kissat_puts(proof->file, " d\n");
}

void print_addmul_line(kissat *solver, int op1, long long coe, int op2)
{
    proof *proof = solver->proof;
    if (!proof)
        return;
    //simplify *S = __autom_S;
    kissat_puts(proof->file, "pol ");
    kissat_putint(proof->file, op1);
    kissat_putc(proof->file, ' ');
    kissat_putint(proof->file, op2);
    kissat_putc(proof->file, ' ');
    kissat_putint(proof->file, coe);
    kissat_puts(proof->file, " * + \n");
}
void add_lex_clause(unsigneds *clause)
{
    simplify *S = __autom_S;
    kissat *solver = S->solver;
    for (unsigned i = 0; i < SIZE_STACK(*clause); i++) {
        int lit = PEEK_STACK(*clause, i);
        if (lit < 2 * S->vars) {
            lit = (lit % 2 ? -1 : 1) * (lit / 2 + 1);
        } else {
            lit = (lit % 2 ? -1 : 1) * (lit / 2);
        }
        PUSH_STACK(S->new_clause_literals, lit);
    }
    PUSH_STACK(S->new_clause_literals, 0);
}
static inline int less_int(int a, int b) {
    return a < b;
}
void symmetry_breaking(void * __S, unsigned int _, const unsigned int *perm) {
    _;
    simplify *S = (simplify *)__S;
    kissat *solver = S->solver;
    ints sparse_perm;
    INIT_STACK(sparse_perm);
    for(unsigned i = 0; i < (unsigned)S->vars * 2; i++) {
        if(perm[i] != i && i % 2 == 0) {
            int var = i / 2;
            S->sym_visit[var] = 1;
            PUSH_STACK(sparse_perm, var);
            //PUSH_STACK(sparse_perm, perm[var]);
        }
    }
    if(SIZE_STACK(sparse_perm) == 0) {
        return;
    }
    int siz = SIZE_STACK(sparse_perm);
    SORT(int, siz, BEGIN_STACK(sparse_perm), less_int);
    for(int i = siz - 1; i >= 0; i--) {
        PUSH_STACK(sparse_perm, 0);
    }
    int * bg = BEGIN_STACK(sparse_perm);
    for(int i = siz - 1; i >= 0; i--) {
        bg[i * 2] = bg[i];
        bg[i * 2 + 1] = perm[bg[i] * 2];
            
    }
    PUSH_STACK(S->perms, sparse_perm);
    //return 1;
}

static inline int pnsign(int x) {
    return (x > 0) ? 1 : x < 0 ? -1 : 0;
}
static inline bool less_size(const ints a, const ints b) {
    return SIZE_STACK(a) < SIZE_STACK(b);
}
void kissat_detect_symmetry(simplify *S)
{
    const long long LIM = 2 * 10000000;
    if ((long long)S->vars * 2 + S->clauses >= LIM)
        return; // what to return ?
    //int n = S->vars * 2 + S->clauses;
    BlissGraph * g = bliss_new(0);
    int tmp_colors = 1;
    for(int i = 1; i <= S->vars; i++) {
        //printf("[%d %d]\n", i, S->mapval[i]);
        if(S->mapval[i]) {
            bliss_add_vertex(g, ++tmp_colors);
            //printf("c fixed variable by simplify_easy do not participate the symmetry detection step\n");
            bliss_add_vertex(g, ++tmp_colors);
        }else {
            bliss_add_vertex(g, 0);
            bliss_add_vertex(g, 0);
        }
    }
    for(int i = 0; i < S->clauses; i++) {
        bliss_add_vertex(g, 1);
    }
//    g.n = n;
/*    int nde = S->vars;
    for (int i = 1; i <= S->clauses; i++) {
        nde += S->clause_size[i];
        if (nde >= LIM / 2)
            return; // what to return ?
    }
    g.e = nde;
    g.adj = (int *)calloc(n + 1, sizeof(int));
    g.edg = (int *)calloc(g.e * 2, sizeof(int));
    g.colors = (int *)calloc(n, sizeof(int));
    for (int i = 0; i < S->vars * 2; i++) {
        g.colors[i] = 0;
    }
    for (int i = S->vars * 2; i < g.n; i++) {
        g.colors[i] = 1;
    }
    int cur = 0;
    for (int i = 0; i < S->vars * 2; i++) {
        g.adj[i] = 0;
    }
    int *deg = (int *)calloc(n, sizeof(int));
    for (int i = 1; i <= S->clauses; i++) {
        for (int j = 0; j < S->clause_size[i]; j++) {
            int ex = convert_lit(S->clause[i][j]);
            int clause_id = S->vars * 2 + i - 1;
            deg[ex]++;
            deg[clause_id]++;
        }
    }
    for (int i = 0; i < 2 * S->vars; i += 2) {
        deg[i]++;
        deg[i + 1]++;
    }
    g.adj[0] = 0;
    for (int i = 0; i < n; i++) {
        g.adj[i + 1] = g.adj[i] + deg[i];
    }*/
    for (int i = 1; i <= S->clauses; i++) {
        for (int j = 0; j < S->clause_size[i]; j++) {
            int ex = convert_lit(S->clause[i][j]);
            int clause_id = S->vars * 2 + i - 1;
            bliss_add_edge(g, clause_id, ex);
            /*g.edg[g.adj[clause_id + 1] - deg[clause_id]] = ex;
            deg[clause_id]--;

            g.edg[g.adj[ex + 1] - deg[ex]] = clause_id;
            deg[ex]--;*/
        }
    }
    for (int i = 0; i < 2 * S->vars; i += 2) {
        bliss_add_edge(g, i, i + 1);
    }
    S->order_generated = calloc(31, sizeof(int));
    S->sym_visit = calloc(S->vars * 2, sizeof(int));
    __autom_S = S;
    S->newVars = S->vars + 1;
    kissat * solver = S->solver;
    INIT_STACK(S->perms);
    printf("c bliss start:\n");
    bliss_find_automorphisms(g, symmetry_breaking, S, NULL);
    printf("c number of perms: %lu\n", SIZE_STACK(S->perms));
    
    int cnt =0 ;
    for(int i = 0; i < S->vars; i++) {
        if(S->sym_visit[i]) {
            cnt++;
        }
    }
    printf("c number of variables to break: %d\n", cnt);
    proof * proof = solver->proof;
    /*if(SIZE_STACK(S->perms) >= 2 && solver->proof != NULL && !solver->unsat_but_no_proof && kissat_process_time() <= 30) {
        solver->symmetry_broken_without_proof = true; // break symmetry without proof. if unsat but proof required, need to run solver again
    }else {
        solver->symmetry_broken_without_proof = false;
    }*/
    solver->symmetry_broken_without_proof = false;
    if(proof && proof->binary == true && SIZE_STACK(S->perms)) {
        SORT(ints, SIZE_STACK(S->perms), S->perms.begin, less_size);
        int * perm = (int * )malloc(sizeof(int) * (S->vars + 1));
        for(int i = 1; i <= S->vars; i++) {
            perm[i] = i;
        }
        bool * touched = (bool *)calloc((S->vars + 1), sizeof(bool));
        for(unsigned i = 0; i < SIZE_STACK(S->perms); i++) {
			ints support = PEEK_STACK(S->perms, i);
			//if(SIZE_STACK(support) >= 20000) continue;
            unsigned siz = 0;
            bool visited = false;
            for (unsigned i = 0; i < SIZE_STACK(support); i += 2) {
                int var = PEEK_STACK(support, i) + 1;
                siz++;
                if(touched[var]) {
                    visited = true;
                    break;
                }
                
            }
            if(visited) {
                continue;
            }
            bool binary = true;
            for (unsigned i = 0; i < SIZE_STACK(support); i += 2) {
                int var = PEEK_STACK(support, i) + 1;
                int nxt = PEEK_STACK(support, i + 1);
                if(touched[var] == 0) {
                    nxt = (nxt / 2 + 1) * (nxt % 2 ? -1 : 1);
                    perm[var] = nxt;
                }
            }
            for (unsigned i = 0; i < SIZE_STACK(support); i += 2) {
                int var = PEEK_STACK(support, i) + 1;
                int nxt = PEEK_STACK(support, i + 1);
                if(touched[var] == 0) {
                    nxt = (nxt / 2 + 1) * (nxt % 2 ? -1 : 1);
                    if(perm[abs(nxt)] * pnsign(nxt) != var) {
                        binary = false;
                        break;
                    }
                }
            }
            if(!binary) {
                for (unsigned i = 0; i < SIZE_STACK(support); i += 2) {
                    int var = PEEK_STACK(support, i) + 1;
                    perm[var] = var;
                }
                continue;
            }
            //don't divide siz by 2 since the symmetries may be "x <-> NOT(x)"
            //printf("c %d\n", siz);
            //siz /= 2;
            int * x = (int * )malloc(sizeof(int) * (siz + 1) * 7);
            int * p = x + ((siz + 1));
            int * s = x + 2 * ((siz + 1));
            int * y = x + 3 * ((siz + 1));
            int * nwx = x + 4 * ((siz + 1));
            int * nwp = x + 5 * ((siz + 1));
            int * nwy = x + 6 * ((siz + 1));
            
            siz = 0;
            for (unsigned i = 0; i < SIZE_STACK(support); i += 2) {
                int var = PEEK_STACK(support, i) + 1;
                int nxt = PEEK_STACK(support, i + 1);
                if(touched[var] == 0) {
                    siz++;
                    nxt = (nxt / 2 + 1) * (nxt % 2 ? -1 : 1);
                    x[siz] = var;
                    p[siz] = nxt;
                    //printf("[%d<->%d]", var, nxt);
                    touched[var] = 1;
                    touched[abs(nxt)] = 1;
                }
            }
			bool * flag = (bool * )calloc(S->clauses + 1, sizeof(bool));
			long long proof_len = 0;
            for(int i = 1; i <= S->clauses; i++) {// add new clauses
                flag[i] = false;
                for(int j = 0; j < S->clause_size[i]; j++) {
                    if(touched[abs(S->clause[i][j])]) {
                        flag[i] = true;
                        break;
                    }
                }
                if(!flag[i]) continue;
				proof_len += S->clause_size[i] * 3 + 1;

			}
//			printf("%lld %lld\n", S->proof_len, proof_len);
			/*if(S->proof_len + proof_len >= 100000) {		
				for (unsigned i = 0; i < SIZE_STACK(support); i += 2) {
                    int var = PEEK_STACK(support, i) + 1;
                    perm[var] = var;
                }
				free(x);
				continue;
			}*/
			S->proof_len += proof_len;

            //printf("siz = %d\n", siz);
            for(unsigned i = 1; i < siz; i++) {
                nwy[i] = S->newVars++;
            }
            //int newVarsbak = S->newVars;
            //printf("\n");
            //printf("vars = %d, newVars = %d\n", S->vars, S->newVars);
            for(unsigned i = 1; i <= siz; i++) {
                s[i] = S->newVars++;
            }
            unsigned last = siz;//break up to the first self-reflection symmetry
            for(unsigned i = 1; i <= siz; i++) {
                if(x[i] == -p[i]) {
                    last = i;
                    break;
                }
            }
			/*if(last > 50) {
				last = 50;
			}*/
            //printf("c switch added\n");
            if(x[last] == -p[last]) {
                add_lits_tmp(S, proof, 2, s[last], -x[last]);
                add_lits_tmp(S, proof, 2, -s[last], x[last]);
            }else {
                add_lits_tmp(S, proof, 3, s[last], -x[last], p[last]);
                add_lits_tmp(S, proof, 2, -s[last], x[last]);
                add_lits_tmp(S, proof, 2, -s[last], -p[last]);
            }
            for(unsigned i = last - 1; i >= 1; i--) {
                add_lits_tmp(S, proof, 3, s[i], -x[i], p[i]);
                add_lits_tmp(S, proof, 3, s[i], -x[i], -s[i + 1]);
                add_lits_tmp(S, proof, 3, s[i], p[i], -s[i + 1]);
                add_lits_tmp(S, proof, 3, -s[i], x[i], -p[i]);
                add_lits_tmp(S, proof, 3, -s[i], x[i], s[i + 1]);
                add_lits_tmp(S, proof, 3, -s[i], -p[i], s[i + 1]);
            }
            //printf("c switch defined, s[1] = %d\n", s[1]);
            for(unsigned i = 1; i <= siz; i++) {
                nwx[i] = S->newVars++;
                S->symmetry_synonyms[x[i]] = nwx[i];
                if(x[i] == -p[i]) {
                    nwp[i] = -nwx[i];
                }else {
                    nwp[i] = S->newVars++;
                    S->symmetry_synonyms[abs(p[i])] = pnsign(p[i]) * nwp[i];
                }
                
            }
			
            //printf("c new vars added\n");
            
            for(unsigned i = 1; i <= siz; i++) {
                if(x[i] == -p[i]) {
                    add_lits_tmp(S, proof, 3, nwx[i], -x[i], s[1]);
                    add_lits_tmp(S, proof, 3, -nwx[i], x[i], s[1]);
                    add_lits_tmp(S, proof, 3, nwx[i], -p[i], -s[1]);
                    add_lits_tmp(S, proof, 3, -nwx[i], p[i], -s[1]);
                }else {
                    add_lits_tmp(S, proof, 3, nwx[i], -x[i], s[1]);
                    add_lits_tmp(S, proof, 3, -nwx[i], x[i], s[1]);
                    add_lits_tmp(S, proof, 3, nwx[i], -p[i], -s[1]);
                    add_lits_tmp(S, proof, 3, -nwx[i], p[i], -s[1]);
                    add_lits_tmp(S, proof, 3, nwp[i], -p[i], s[1]);
                    add_lits_tmp(S, proof, 3, -nwp[i], p[i], s[1]);
                    add_lits_tmp(S, proof, 3, nwp[i], -x[i], -s[1]);
                    add_lits_tmp(S, proof, 3, -nwp[i], x[i], -s[1]);
                }
            }
            //printf("c new vars defined\n");
            for(int i = 1; i <= S->clauses; i++) {// add new clauses
                if(!flag[i]) continue;
                PUSH_STACK(proof->line, s[1]);
                for(int j = 0; j < S->clause_size[i]; j++) {
                    int lit = S->clause[i][j];
                    int var = abs(lit);
                    int sgn = pnsign(lit);
                    if(touched[var]) {
                        lit = sgn * S->symmetry_synonyms[var];
                    }
                    PUSH_STACK(proof->line, lit);
                }
                print_added_proof_line(proof);
                for(int j = 0; j < S->clause_size[i]; j++) {
                    int lit = S->clause[i][j];
                    int var = abs(lit);
                    int sgn = pnsign(lit);
                    if(touched[var]) {
                        lit = sgn * S->symmetry_synonyms[var];
                    }
                    PUSH_STACK(proof->line, lit);
                }
                print_added_proof_line(proof);
            }
            for(int i = 1; i <= S->clauses; i++) {//del aux clauses and original clause
                if(!flag[i]) continue;
                PUSH_STACK(proof->line, s[1]);
                for(int j = 0; j < S->clause_size[i]; j++) {
                    int lit = S->clause[i][j];
                    int var = abs(lit);
                    int sgn = pnsign(lit);
                    if(touched[var]) {
                        lit = sgn * S->symmetry_synonyms[var];
                    }
                    PUSH_STACK(proof->line, lit);
                }
                print_delete_proof_line(proof);

                for(int j = 0; j < S->clause_size[i]; j++) {
                    int lit = S->clause[i][j];
                    PUSH_STACK(proof->line, lit);
                }
                print_delete_proof_line(proof);
            }
            //printf("c new clauses defined\n");
            for(unsigned i = 1; i < last; i++) {
                y[i] = S->newVars++;
            }
            //printf("c lex header variables added\n");
            if(last >= 2) {
                add_lits_tmp(S, proof, 2, y[1], -nwx[1]);
                add_lits_tmp(S, proof, 2, y[1], nwp[1]);
                add_lits_tmp(S, proof, 3, -y[1], nwx[1], -nwp[1]);
            }
            for(unsigned i = 2; i <= last - 1; i++) {
                    add_lits_tmp(S, proof, 3, y[i], -y[i - 1], -nwx[i]);
                    add_lits_tmp(S, proof, 3, y[i], -y[i - 1], nwp[i]);
                    add_lits_tmp(S, proof, 2, -y[i], y[i - 1]);
                    add_lits_tmp(S, proof, 3, -y[i], nwx[i], -nwp[i]);
            }
            if(nwx[1] == -nwp[1]) {
                add_lits_tmp(S, proof, 2, -nwx[1], s[1]);
                add_lits_tmp(S, proof, 2, -nwx[1], -s[1]);
                add_lits_tmp(S, proof, 1, -nwx[1]);
            }else {
                add_lits_tmp(S, proof, 3, -nwx[1], nwp[1], s[1]);
                add_lits_tmp(S, proof, 3, -nwx[1], nwp[1], -s[1]);
                add_lits_tmp(S, proof, 2, -nwx[1], nwp[1]);
            }
            for(unsigned i = 1; i < last; i++) {
                add_lits_tmp(S, proof, 4, -s[1], -y[i], p[i], -x[i]);
                add_lits_tmp(S, proof, 4, -s[1], -y[i], -p[i], x[i]);
                add_lits_tmp(S, proof, 4, s[1], -y[i], p[i], -x[i]);
                add_lits_tmp(S, proof, 4, s[1], -y[i], -p[i], x[i]);
                add_lits_tmp(S, proof, 3, -y[i], p[i], -x[i]);
                add_lits_tmp(S, proof, 3, -y[i], -p[i], x[i]);
                
                add_lits_tmp(S, proof, 4, -y[i], x[i], -s[i], s[i + 1]);
                add_lits_tmp(S, proof, 4, -y[i], x[i], s[i], -s[i + 1]);
                add_lits_tmp(S, proof, 4, -y[i], -x[i], -s[i], s[i + 1]);
                add_lits_tmp(S, proof, 4, -y[i], -x[i], s[i], -s[i + 1]);
                add_lits_tmp(S, proof, 3, -y[i], -s[i], s[i + 1]);
                add_lits_tmp(S, proof, 3, -y[i], s[i], -s[i + 1]);
                if(nwx[i + 1] == -nwp[i + 1]) {
                    add_lits_tmp(S, proof, 3, -y[i], -nwx[i + 1], s[1]);
                    add_lits_tmp(S, proof, 3, -y[i], -nwx[i + 1], -s[1]);
                    add_lits_tmp(S, proof, 2, -y[i], -nwx[i + 1]);
                }else {
                    add_lits_tmp(S, proof, 4, -y[i], -nwx[i + 1], nwp[i + 1], s[1]);
                    add_lits_tmp(S, proof, 4, -y[i], -nwx[i + 1], nwp[i + 1], -s[1]);
                    add_lits_tmp(S, proof, 3, -y[i], -nwx[i + 1], nwp[i + 1]);
                }
            }
            if(x[last] == -p[last]) {
                del_lits(S, proof, 2, s[last], -x[last]);
                del_lits(S, proof, 2, -s[last], x[last]);
            }else {
                del_lits(S, proof, 3, s[last], -x[last], p[last]);
                del_lits(S, proof, 2, -s[last], x[last]);
                del_lits(S, proof, 2, -s[last], -p[last]);
            }
            for(unsigned i = last - 1; i >= 1; i--) {
                del_lits(S, proof, 3, s[i], -x[i], p[i]);
                del_lits(S, proof, 3, s[i], -x[i], -s[i + 1]);
                del_lits(S, proof, 3, s[i], p[i], -s[i + 1]);
                del_lits(S, proof, 3, -s[i], x[i], -p[i]);
                del_lits(S, proof, 3, -s[i], x[i], s[i + 1]);
                del_lits(S, proof, 3, -s[i], -p[i], s[i + 1]);
            }
            for(unsigned i = 1; i <= siz; i++) {
                if(x[i] == -p[i]) {
                    del_lits(S, proof, 3, nwx[i], -x[i], s[1]);
                    del_lits(S, proof, 3, -nwx[i], x[i], s[1]);
                    del_lits(S, proof, 3, nwx[i], -p[i], -s[1]);
                    del_lits(S, proof, 3, -nwx[i], p[i], -s[1]);
                }else {
                    del_lits(S, proof, 3, nwx[i], -x[i], s[1]);
                    del_lits(S, proof, 3, -nwx[i], x[i], s[1]);
                    del_lits(S, proof, 3, nwx[i], -p[i], -s[1]);
                    del_lits(S, proof, 3, -nwx[i], p[i], -s[1]);
                    del_lits(S, proof, 3, nwp[i], -p[i], s[1]);
                    del_lits(S, proof, 3, -nwp[i], p[i], s[1]);
                    del_lits(S, proof, 3, nwp[i], -x[i], -s[1]);
                    del_lits(S, proof, 3, -nwp[i], x[i], -s[1]);
                }
            }

            if(nwx[1] == -nwp[1]) {
                del_lits(S, proof, 2, -nwx[1], s[1]);
                del_lits(S, proof, 2, -nwx[1], -s[1]);
            }else {
                del_lits(S, proof, 3, -nwx[1], nwp[1], s[1]);
                del_lits(S, proof, 3, -nwx[1], nwp[1], -s[1]);
            }
            for(unsigned i = 1; i < last; i++) {
                del_lits(S, proof, 4, -s[1], -y[i], p[i], -x[i]);
                del_lits(S, proof, 4, -s[1], -y[i], -p[i], x[i]);
                del_lits(S, proof, 4, s[1], -y[i], p[i], -x[i]);
                del_lits(S, proof, 4, s[1], -y[i], -p[i], x[i]);
                del_lits(S, proof, 3, -y[i], p[i], -x[i]);
                del_lits(S, proof, 3, -y[i], -p[i], x[i]);
                
                del_lits(S, proof, 4, -y[i], x[i], -s[i], s[i + 1]);
                del_lits(S, proof, 4, -y[i], x[i], s[i], -s[i + 1]);
                del_lits(S, proof, 4, -y[i], -x[i], -s[i], s[i + 1]);
                del_lits(S, proof, 4, -y[i], -x[i], s[i], -s[i + 1]);
                del_lits(S, proof, 3, -y[i], -s[i], s[i + 1]);
                del_lits(S, proof, 3, -y[i], s[i], -s[i + 1]);
                if(nwx[i + 1] == -nwp[i + 1]) {
                    del_lits(S, proof, 3, -y[i], -nwx[i + 1], s[1]);
                    del_lits(S, proof, 3, -y[i], -nwx[i + 1], -s[1]);
                }else {
                    del_lits(S, proof, 4, -y[i], -nwx[i + 1], nwp[i + 1], s[1]);
                    del_lits(S, proof, 4, -y[i], -nwx[i + 1], nwp[i + 1], -s[1]);
                }
            }

            for(unsigned i = 1; i < last; i++) {//transfer lex header and clauses back
                add_lits_tmp(S, proof, 2, nwy[i], -y[i]);
                add_lits_tmp(S, proof, 2, -nwy[i], y[i]);
            }
            for(unsigned i = 1; i <= siz; i++) {
                if(x[i] == -p[i]) {
                    add_lits_tmp(S, proof, 2, x[i], -nwx[i]);
                    add_lits_tmp(S, proof, 2, -x[i], nwx[i]);
                }else {
                    add_lits_tmp(S, proof, 2, x[i], -nwx[i]);
                    add_lits_tmp(S, proof, 2, -x[i], nwx[i]);
                    add_lits_tmp(S, proof, 2, p[i], -nwp[i]);
                    add_lits_tmp(S, proof, 2, -p[i], nwp[i]);
                }
            }
            for(int i = 1; i <= S->clauses; i++) {//
                if(!flag[i]) continue;
                for(int j = 0; j < S->clause_size[i]; j++) {
                    int lit = S->clause[i][j];
                    PUSH_STACK(proof->line, lit);
                }
                print_added_proof_line(proof);
                
                for(int j = 0; j < S->clause_size[i]; j++) {
                    int lit = S->clause[i][j];
                    int var = abs(lit);
                    int sgn = pnsign(lit);
                    if(touched[var]) {
                        lit = sgn * S->symmetry_synonyms[var];
                    }
                    PUSH_STACK(proof->line, lit);
                }
                print_delete_proof_line(proof);
            }
            if(last >= 2) {
                add_lits(S, proof, 2, nwy[1], -x[1]);
                add_lits(S, proof, 2, nwy[1], p[1]);
                add_lits(S, proof, 3, -nwy[1], x[1], -p[1]);
            }
            for(unsigned i = 2; i <= last - 1; i++) {
                add_lits(S, proof, 3, nwy[i], -nwy[i - 1], -x[i]);
                add_lits(S, proof, 3, nwy[i], -nwy[i - 1], p[i]);
                add_lits(S, proof, 2, -nwy[i], nwy[i - 1]);
                add_lits(S, proof, 3, -nwy[i], x[i], -p[i]);
            }
            if(x[1] == -p[1]) {
                add_lits(S, proof, 1, -x[1]);
            }else {
                add_lits(S, proof, 2, -x[1], p[1]);
            }
            for(unsigned i = 1; i < last; i++) {
                //printf("%d %d %d\n", -nwy[i], -x[i + 1], p[i + 1]);
                if(x[i + 1] == -p[i + 1]) {
                    add_lits(S, proof, 2, -nwy[i], -x[i + 1]);
                }else {
                    add_lits(S, proof, 3, -nwy[i], -x[i + 1], p[i + 1]);
                }
            }
            if(last >= 2) {//del x' lex header part 1
                del_lits(S, proof, 2, y[1], -nwx[1]);
                del_lits(S, proof, 2, y[1], nwp[1]);
                del_lits(S, proof, 3, -y[1], nwx[1], -nwp[1]);
            }
            for(unsigned i = 2; i <= last - 1; i++) {
                del_lits(S, proof, 3, y[i], -y[i - 1], -nwx[i]);
                del_lits(S, proof, 3, y[i], -y[i - 1], nwp[i]);
                del_lits(S, proof, 2, -y[i], y[i - 1]);
                del_lits(S, proof, 3, -y[i], nwx[i], -nwp[i]);
            }
            
            if(nwx[1] == -nwp[1]) {//del x' lex header part 2
                del_lits(S, proof, 1, -nwx[1]);
            }else {
                del_lits(S, proof, 2, -nwx[1], nwp[1]);
            }
            for(unsigned i = 1; i < last; i++) {
                if(nwx[i + 1] == -nwp[i + 1]) {
                    del_lits(S, proof, 2, -y[i], -nwx[i + 1]);
                }else {
                    del_lits(S, proof, 3, -y[i], -nwx[i + 1], nwp[i + 1]);
                }
            }
            for(unsigned i = 1; i < last; i++) {//del transfer clauses
                del_lits(S, proof, 2, nwy[i], -y[i]);
                del_lits(S, proof, 2, -nwy[i], y[i]);
            }
            for(unsigned i = 1; i <= siz; i++) {
                if(x[i] == -p[i]) {
                    del_lits(S, proof, 2, x[i], -nwx[i]);
                    del_lits(S, proof, 2, -x[i], nwx[i]);
                }else {
                    del_lits(S, proof, 2, x[i], -nwx[i]);
                    del_lits(S, proof, 2, -x[i], nwx[i]);
                    del_lits(S, proof, 2, p[i], -nwp[i]);
                    del_lits(S, proof, 2, -p[i], nwp[i]);
                }
            }
            free(flag);
            /*del_3_lits(S, proof, -y[1], nwx[1], -nwp[1]);
            for(unsigned i = 2; i <= siz - 1; i++) {
                del_2_lits(S, proof, -y[i], y[i - 1]);
                del_3_lits(S, proof, -y[i], nwx[i], -nwp[i]);
            }*/
            //printf("c lex header for new variables defined\n");
            //printf("c partial break symmetry, current new literals: %lu\n", SIZE_STACK(S->new_clause_literals));
            /*for (unsigned i = 0; i < SIZE_STACK(support); i += 2) {//restore the permutation
                int var = PEEK_STACK(support, i);
                perm[var] = var;
            }*/
            free(x);
            for (unsigned i = 0; i < SIZE_STACK(support); i += 2) {
                int var = PEEK_STACK(support, i) + 1;
                perm[var] = var;
                S->symmetry_synonyms[var] = var;
//                touched[var] = 0;
            }
//			printf("%zu %lld %zu\n", SIZE_STACK(support), S->proof_len, SIZE_STACK(S->new_clause_literals));
            
            //S->newVars = newVarsbak; //enable this once dpr trim can cleanly delete clauses...
        }
        free(touched);
        free(perm);
    }else if(proof && proof->binary == false) {
        for(unsigned i = 0; i < SIZE_STACK(S->perms); i++) {
            bool flag = true;
            ints support = PEEK_STACK(S->perms, i);
            int siz = SIZE_STACK(support);
            if(siz >= 120) continue;
            for (unsigned i = 0; i < SIZE_STACK(support); i += 2) {
                int var = PEEK_STACK(support, i);
                if(S->sym_visit[var]) {
                    S->sym_visit[var] = 0;
                }else {
                    flag = false;
                    break;
                }
            }
            if(flag == false) {
                continue;
            }
            siz /= 2;
            if (S->order_generated[siz] == 0) {
                kissat_generate_preorder(S->solver, siz, siz);
                S->order_generated[siz] = 1;
            }
            kissat_derive_lex_order(S->solver, &support, siz);
            unsigneds clause;
            int newVars = S->newVars;
            INIT_STACK(clause);
            PUSH_STACK(clause, LIT(newVars));
            print_red_line(solver, &clause, newVars, 1);
            add_lex_clause(&clause);
            CLEAR_STACK(clause);
            for (int i = 1; i < siz; i++) {
                int xij = PEEK_STACK(support, 2 * (i - 1)) * 2;
                int pixij = PEEK_STACK(support, 2 * (i - 1) + 1);

                PUSH_STACK(clause, (LIT(newVars + i)));
                PUSH_STACK(clause, NOT(LIT(newVars + i - 1)));
                PUSH_STACK(clause, xij ^ 1);
                print_red_line(solver, &clause, newVars + i, 1);
                add_lex_clause(&clause);
                CLEAR_STACK(clause);

                PUSH_STACK(clause, (LIT(newVars + i)));
                PUSH_STACK(clause, NOT(LIT(newVars + i - 1)));
                PUSH_STACK(clause, pixij);
                print_red_line(solver, &clause, newVars + i, 1);
                add_lex_clause(&clause);
                CLEAR_STACK(clause);


                PUSH_STACK(clause, LIT(newVars + i - 1));
                PUSH_STACK(clause, NOT(LIT(newVars + i)));
                print_red_line(solver, &clause, newVars + i, 0);
                add_lex_clause(&clause);
                CLEAR_STACK(clause);

                PUSH_STACK(clause, NOT(LIT(newVars + i)));
                PUSH_STACK(clause, pixij ^ 1);
                PUSH_STACK(clause, xij);
                print_red_line(solver, &clause, newVars + i, 0);
                add_lex_clause(&clause);
                CLEAR_STACK(clause);
            }
            for (int i = 0; i < siz; i++) {
                int xij = PEEK_STACK(support, 2 * i) * 2;
                int pixij = PEEK_STACK(support, 2 * i + 1);

                if (i == 0) {
                    PUSH_STACK(clause, pixij);
                    PUSH_STACK(clause, xij ^ 1);
                    print_rup_line(solver, &clause);
                    add_lex_clause(&clause);
                    CLEAR_STACK(clause);
                } else {
                    print_addmul_line(solver, i == 1 ? -4 * siz + 1 : -2, 1ll << (siz - i), -4 * siz + 2 + i * 4 - (i - 1) * 2);
                    PUSH_STACK(clause, NOT(LIT(newVars + i)));
                    PUSH_STACK(clause, xij ^ 1);
                    PUSH_STACK(clause, pixij);
                    print_rup_line(solver, &clause);
                    add_lex_clause(&clause);
                    CLEAR_STACK(clause);
                }
            }

            S->newVars += siz;

        }
        
    }else if(proof == NULL) {
        for(unsigned i = 0; i < SIZE_STACK(S->perms); i++) {
            //bool flag = true;
            ints support = PEEK_STACK(S->perms, i);
            int siz = SIZE_STACK(support) / 2;
            unsigneds clause;
            int newVars = S->newVars;
            INIT_STACK(clause);
            PUSH_STACK(clause, LIT(newVars));
            add_lex_clause(&clause);
            CLEAR_STACK(clause);
            for (int i = 1; i < siz; i++) {
                int xij = PEEK_STACK(support, 2 * (i - 1)) * 2;
                int pixij = PEEK_STACK(support, 2 * (i - 1) + 1);

                PUSH_STACK(clause, (LIT(newVars + i)));
                PUSH_STACK(clause, NOT(LIT(newVars + i - 1)));
                PUSH_STACK(clause, xij ^ 1);
                add_lex_clause(&clause);
                CLEAR_STACK(clause);

                PUSH_STACK(clause, (LIT(newVars + i)));
                PUSH_STACK(clause, NOT(LIT(newVars + i - 1)));
                PUSH_STACK(clause, pixij);
                add_lex_clause(&clause);
                CLEAR_STACK(clause);


                PUSH_STACK(clause, LIT(newVars + i - 1));
                PUSH_STACK(clause, NOT(LIT(newVars + i)));
                add_lex_clause(&clause);
                CLEAR_STACK(clause);

                PUSH_STACK(clause, NOT(LIT(newVars + i)));
                PUSH_STACK(clause, pixij ^ 1);
                PUSH_STACK(clause, xij);
                add_lex_clause(&clause);
                CLEAR_STACK(clause);
            }
            for (int i = 0; i < siz; i++) {
                int xij = PEEK_STACK(support, 2 * i) * 2;
                int pixij = PEEK_STACK(support, 2 * i + 1);
                
                if (i == 0) {
                    PUSH_STACK(clause, pixij);
                    PUSH_STACK(clause, xij ^ 1);
                    add_lex_clause(&clause);
                    CLEAR_STACK(clause);
                } else {
                    PUSH_STACK(clause, NOT(LIT(newVars + i)));
                    PUSH_STACK(clause, xij ^ 1);
                    PUSH_STACK(clause, pixij);
                    add_lex_clause(&clause);
                    CLEAR_STACK(clause);
                }
            }

            S->newVars += siz;
            /*for(unsigned i = 0; i < SIZE_STACK(S->new_clause_literals); i++) {
                int x = PEEK_STACK(S->new_clause_literals, i);
            }*/
        }
    }
    //kissat_generate_preorder_with_aux(solver, cnt);
    S->newVars--;
    S->solver->mapidx = (int *)realloc(S->solver->mapidx, sizeof(int) * (S->newVars + 1));
    for (int i = S->vars + 1; i <= S->newVars; i++) {
        S->solver->mapidx[i] = S->orivars + i - (S->vars);
    }
    
    for(unsigned i = 0; i < SIZE_STACK(S->perms); i++) {
        ints perm = PEEK_STACK(S->perms, i);
        RELEASE_STACK(perm);
    }
    free(S->sym_visit);
    free(S->order_generated);
    bliss_release(g);
    RELEASE_STACK(S->perms);
}
