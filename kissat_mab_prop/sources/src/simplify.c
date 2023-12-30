#include "allocate.h"
#include "simplify.h"
#include "internal.h"
#include "import.h"
#include "proof.h"
#include "check.h"
#include "hashmap.h"
#include "math.h"
#include "symmetry.h"
#include "sort.h"
#include <stdio.h>
#include <stdlib.h>
#include "resources.h"
#include <ctype.h>
#include <inttypes.h>
#define TOLIT(x) ((x) > 0 ? (x) : ((-x) + S->vars))
#define NEG(x) ((x) > S->vars ? ((x)-S->vars) : ((x) + S->vars))
typedef long long ll;
int nlit;
void add_lits(simplify * S, proof * proof, int count, ...) {
	S->proof_len += count;
    kissat * solver = S->solver;
    va_list list;
    va_list list2;
    va_start(list, count); 
    va_copy(list2, list); 
    //printf("a ");
    for(int j = 0; j < count; j++) {
        int x = va_arg(list, int);
        PUSH_STACK(proof->line, x);
        //printf("%d ", x);
    }
    //printf("\n");
    va_end(list);
    print_added_proof_line(proof);

    for(int j = 0; j < count; j++) {
        PUSH_STACK(S->new_clause_literals, va_arg(list2, int));
    }
    PUSH_STACK(S->new_clause_literals, 0);
    va_end(list2);
	
}
void add_lits_tmp(simplify * S, proof * proof, int count, ...) {
	S->proof_len += count;
    kissat * solver = S->solver;
    va_list list;
    va_start(list, count); 
    //printf("a ");
    for(int j = 0; j < count; j++) {
        int x = va_arg(list, int);
        PUSH_STACK(proof->line, x);
        //printf("%d ", x);
    }
    //printf("\n");
    va_end(list);
    print_added_proof_line(proof);
	
}
void del_lits(simplify * S, proof * proof, int count, ...) {
    kissat * solver = S->solver;
    va_list list;
    va_start(list, count); 
    //printf("d ");
    for(int j = 0; j < count; j++) {
        int x = va_arg(list, int);
        PUSH_STACK(proof->line, x);
        //printf("%d ", x);
    }
    //printf("\n");
    va_end(list);
    print_delete_proof_line(proof);
}

simplify *simplify_init()
{
    simplify *s = (simplify *)malloc(sizeof(simplify));
    return s;
}

#define NEXT() next(file, lineno_ptr)
static inline char GET_CHAR(file * file){
    //const int maxn = 1048576;
    static char buf[1048576],*p1=buf,*p2=buf;
    return p1==p2&&(p2=(p1=buf)+fread(buf,1,1048576,file->file),p1==p2)?EOF:*p1++;
}
static int next(file *file, uint64_t *lineno_ptr)
{
    int ch = GET_CHAR(file);//kissat_getc(file);
    if (ch == '\n')
        *lineno_ptr += 1;
    return ch;
}

static const char *nonl(int ch, const char *str, uint64_t *lineno_ptr)
{
    if (ch == '\n') {
        assert(*lineno_ptr > 1);
        *lineno_ptr -= 1;
    }
    return str;
}

bool simplify_store_clause(simplify *S, int v)
{
    if (v == 0) {
        S->real_clauses++;
        int sz = S->store_clause->sz;
        S->clause_size[S->real_clauses] = sz;
        S->clause[S->real_clauses] = (int *)malloc(sizeof(int) * sz);
        for (int i = 0; i < sz; i++)
            S->clause[S->real_clauses][i] = cvec_data(S->store_clause, i);
        cvec_clear(S->store_clause);
        if (!sz)
            return false;
        // S->clause_id[S->real_clauses] = S->real_clauses;//ID in pseudo boolean proof
    } else
        cvec_push(S->store_clause, v);
    return true;
}

void simplify_alloc(simplify *S, int vars, int clauses)
{
    S->vars = S->orivars = vars;
    // printf("------------%d\n", vars);
    S->clauses = S->oriclauses = clauses;
    // S->clause_id = (int*) malloc(sizeof(int*) * (clauses + 1));
    S->real_clauses = 0;
    S->clause = (int **)malloc(sizeof(int *) * (clauses + 1));
    S->clause_size = (int *)malloc(sizeof(int) * (clauses + 1));
    S->color = (int *)malloc(sizeof(int) * (vars + 1));
    S->varval = (int *)malloc(sizeof(int) * (vars + 1));
    S->clean = (int *)malloc(sizeof(int) * (vars + 1));
    S->queue = (int *)malloc(sizeof(int) * (vars + 1));
    //kissat * solver = S->solver;
    INIT_STACK(S->units);
    S->mapval = (int *)malloc(sizeof(int) * (vars + 1));
    S->mapto = (int *)malloc(sizeof(int) * (vars + 1));

    S->occurp = (int **)calloc((vars + 1), sizeof(int *));
    S->occurn = (int **)calloc((vars + 1), sizeof(int *));
    S->occurp_size = (int *)malloc(sizeof(int) * (vars + 1));
    S->occurn_size = (int *)malloc(sizeof(int) * (vars + 1));

    S->seen = (int *)malloc(sizeof(int) * (2 * vars + 2));
    S->clause_delete = (int *)malloc(sizeof(int) * (clauses + 1));
    S->resseen = (int *)malloc(sizeof(int) * (2 * vars + 2));
    // printf("resseen %lld\n", S->resseen);
    S->store_clause = cvec_init();

    for (int i = 1; i <= vars; i++) {
        S->mapto[i] = i, S->mapval[i] = 0;
        // S->units[i] = 0;
    }
	S->buf = NULL;
	S->buf_siz = 0;
	S->proof_len = 0;
    // S->units[0] = 0;
}

void reallocintp(int ***a /* , int ori */, int upd)
{
    *a = realloc(*a, sizeof(int *) * upd);
}
void reallocint(int **a /* , int ori */, int upd)
{
    // printf("realloc %lld\n", *a);
    *a = realloc(*a, sizeof(int) * upd);
}


void simplify_realloc(simplify *S, int new_vars)
{
    int vars = S->vars;

    reallocint(&(S->clean), new_vars + 1);
    reallocint(&(S->color), new_vars + 1);
    reallocint(&(S->queue), new_vars + 1);
    reallocint(&(S->varval), new_vars + 1);
    reallocint(&(S->mapval), new_vars + 1);
    reallocint(&(S->mapto), new_vars + 1);
    reallocint(&(S->mapfrom), new_vars + 1);

    reallocintp(&(S->occurp), new_vars + 1);
    for (int i = vars + 1; i < new_vars + 1; i++) {
        S->occurp[i] = NULL;
        S->mapto[i] = 0;
        S->mapval[i] = 0;
    }
    reallocintp(&(S->occurn), new_vars + 1);
    for (int i = vars + 1; i < new_vars + 1; i++) {
        S->occurn[i] = NULL;
    }
    reallocint(&(S->occurp_size), new_vars + 1);
    reallocint(&(S->occurn_size), new_vars + 1);
    reallocint(&(S->seen), (2 * new_vars + 2));
    reallocint(&(S->resseen), (2 * new_vars + 2));

    S->vars = new_vars;
}

void simplify_release(simplify *S)
{
    //    return;//
    kissat *solver = S->solver;
    RELEASE_STACK(S->units);


    free(S->varval);
    for (int i = 1; i <= S->vars; i++) {
        if (S->occurp[i] != NULL)
            free(S->occurp[i]);
        if (S->occurn[i] != NULL)
            free(S->occurn[i]);
    }
        for (int i = 1; i <= S->clauses; i++) {
            free(S->clause[i]);
        }
        free(S->clause);
        S->clause = NULL;
        free(S->clause_size);

    // free(S->clause_id);
    free(S->color);
    free(S->clean);
    free(S->queue);
    free(S->occurp);
    free(S->occurn);
    free(S->occurn_size);
    free(S->occurp_size);
    free(S->seen);
    free(S->clause_delete);
    free(S->resseen);
    free(S->mapfrom); // comment when easy & resolution are disabled
    cvec_release(S->store_clause);
	free(S->buf);
}
const int MAX_CLAUSES = 1000000000;
static const char *simplify_parse(simplify *S, file *file, uint64_t *lineno_ptr)
{
    *lineno_ptr = 1;
    bool first = true;
    int ch;
    for (;;) {
        ch = NEXT();
        if (ch == 'p')
            break;
        else if (ch == EOF) {
            if (first)
                return "empty file";
            else
                return "end-of-file before header";
        }
        first = false;
        if (ch == '\r') {
            ch = NEXT();
            if (ch != '\n')
                return "expected new-line after carriage-return";
        } else if (ch == '\n') {
        } else if (ch == 'c') {
        START:
            ch = NEXT();
            if (ch == '\n')
                continue;
            else if (ch == '\r') {
                ch = NEXT();
                if (ch != '\n')
                    return "expected new-line after carriage-return";
                continue;
            } else if (ch == EOF)
                return "end-of-file in header comment";
            else if (ch == ' ' || ch == '\t')
                goto START;
            while ((ch = NEXT()) != '\n')
                if (ch == EOF)
                    return "end-of-file in header comment";
                else if (ch == '\r') {
                    ch = NEXT();
                    if (ch != '\n')
                        return "expected new-line after carriage-return";
                    break;
                }
        } else
            return "expected 'c' or 'p' at start of line";
    }
    assert(ch == 'p');
    ch = NEXT();
    if (ch != ' ')
        return nonl(ch, "expected space after 'p'", lineno_ptr);
    ch = NEXT();
    if (ch != 'c')
        return nonl(ch, "expected 'c' after 'p '", lineno_ptr);
    ch = NEXT();
    if (ch != 'n')
        return nonl(ch, "expected 'n' after 'p c'", lineno_ptr);
    ch = NEXT();
    if (ch != 'f')
        return nonl(ch, "expected 'n' after 'p cn'", lineno_ptr);
    ch = NEXT();
    if (ch != ' ')
        return nonl(ch, "expected space after 'p cnf'", lineno_ptr);
    ch = NEXT();
    if (!isdigit(ch))
        return nonl(ch, "expected digit after 'p cnf '", lineno_ptr);
    int variables = ch - '0';
    while (isdigit(ch = NEXT())) {
        if (EXTERNAL_MAX_VAR / 10 < variables)
            return "maximum variable too large";
        variables *= 10;
        const int digit = ch - '0';
        if (EXTERNAL_MAX_VAR - digit < variables)
            return "maximum variable too large";
        variables += digit;
    }
    if (ch == EOF)
        return "unexpected end-of-file while parsing maximum variable";
    if (ch == '\r') {
        ch = NEXT();
        if (ch != '\n')
            return "expected new-line after carriage-return";
    }
    if (ch == '\n')
        return nonl(ch, "unexpected new-line after maximum variable", lineno_ptr);
    if (ch != ' ')
        return "expected space after maximum variable";
    ch = NEXT();
    while (ch == ' ' || ch == '\t')
        ch = NEXT();
    if (!isdigit(ch))
        return "expected number of clauses after maximum variable";
    uint64_t clauses = ch - '0';
    while (isdigit(ch = NEXT())) {
        if (MAX_CLAUSES / 10 < clauses)
            return "number of clauses too large";
        clauses *= 10;
        const int digit = ch - '0';
        if (MAX_CLAUSES - digit < (long long)clauses)
            return "number of clauses too large";
        clauses += digit;
    }
    simplify_alloc(S, variables, clauses);
    if (ch == EOF)
        return "unexpected end-of-file while parsing number of clauses";
    while (ch == ' ' || ch == '\t')
        ch = NEXT();
    if (ch == '\r') {
        ch = NEXT();
        if (ch != '\n')
            return "expected new-line after carriage-return";
    }
    if (ch == EOF)
        return "unexpected end-of-file after parsing number of clauses";
    if (ch != '\n')
        return "expected new-line after parsing number of clauses";

    uint64_t parsed = 0;
    int lit = 0;
    /*for (;;) {
        ch = NEXT();
        if (ch == ' ')
            continue;
        if (ch == '\t')
            continue;
        if (ch == '\n')
            continue;
        if (ch == '\r') {
            ch = NEXT();
            if (ch != '\n')
                return "expected new-line after carriage-return";
            continue;
        }
        if (ch == 'c') {
            while ((ch = NEXT()) != '\n')
                if (ch == EOF)
                    break;
            if (ch == EOF)
                break;
            continue;
        }
        if (ch == EOF)
            break;
        int sign;
        if (ch == '-') {
            ch = NEXT();
            if (ch == EOF)
                return "unexpected end-of-file after '-'";
            if (ch == '\n')
                return nonl(ch, "unexpected new-line after '-'", lineno_ptr);
            if (!isdigit(ch))
                return "expected digit after '-'";
            if (ch == '0')
                return "expected non-zero digit after '-'";
            sign = -1;
        } else if (!isdigit(ch))
            return "expected digit or '-'";
        else
            sign = 1;
        assert(isdigit(ch));
        int idx = ch - '0';
        while (isdigit(ch = NEXT())) {
            if (EXTERNAL_MAX_VAR / 10 < idx)
                return "variable index too large";
            idx *= 10;
            const int digit = ch - '0';
            if (EXTERNAL_MAX_VAR - digit < idx)
                return "variable index too large";
            idx += digit;
        }
        if (ch == EOF) {
        } else if (ch == '\r') {
            ch = NEXT();
            if (ch != '\n')
                return "expected new-line after carriage-return";
        } else if (ch == 'c') {
            while ((ch = NEXT()) != '\n')
                if (ch == EOF)
                    break;
        } else if (ch != ' ' && ch != '\t' && ch != '\n')
            return "expected white space after literal";
        if (idx > variables)
            return nonl(ch, "maximum variable index exceeded ", lineno_ptr);
        if (idx) {
            assert(sign == 1 || sign == -1);
            assert(idx != INT_MIN);
            lit = sign * idx;
        } else {
            if (parsed == clauses)
                return "too many clauses ";
            parsed++;
            lit = 0;
        }
        // kissat_add(solver, lit);
        int res = simplify_store_clause(S, lit);
        if (!res)
            return "empty clause";
    }*/
    for (;;) {
        int sgn = 1;
        while(ch != '-' && (ch < '0' || ch > '9')) {
            ch = NEXT();
        }
        if(ch == '-') {
            sgn = -1;
        }
        while(ch < '0' || ch > '9') {
            ch = NEXT();
        }
        int idx = 0;
        while (isdigit(ch)) {
            if (EXTERNAL_MAX_VAR / 10 < idx)
                return "variable index too large";
            idx *= 10;
            const int digit = ch - '0';
            if (EXTERNAL_MAX_VAR - digit < idx)
                return "variable index too large";
            idx += digit;
            ch = NEXT();
        }
        lit = sgn * idx;
        int res = simplify_store_clause(S, lit);
        if (!res) {
            return "empty clause";
        }
        if(S->real_clauses == S->clauses) {
            break;
        }
    }
    if (lit)
        return "trailing zero missing";
    if (parsed < clauses) {
        if (parsed + 1 == clauses)
            return "one clause missing ";
        return "more than one clause missing ";
    }
    return 0;
}

static inline int pnsign(int x)
{
    return (x > 0 ? 1 : -1);
}
static inline int sign(int x)
{
    return x % 2 == 1 ? -1 : 1;
}
static inline int tolit(int x)
{
    if (x > 0)
        return x * 2;
    else
        return (-x) * 2 + 1;
}
static inline int toidx(int x)
{
    return (x & 1 ? -(x >> 1) : (x >> 1));
}
static inline int reverse(int x)
{
    if (x % 2 == 1)
        return x - 1;
    else
        return x + 1;
}
static inline ll mapv(int a, int b)
{
    return 1ll * a * nlit + (ll)b;
}
void backup_clause(simplify * S, int id) {
	if(S->solver->proof == NULL) return;
	if(S->buf_siz < S->clause_size[id]) {
		S->buf_siz = S->clause_size[id];
		S->buf = realloc(S->buf, sizeof(int) * S->buf_siz);
	}
	memcpy(S->buf, S->clause[id], sizeof(int) * S->clause_size[id]);
	S->buf_len = S->clause_size[id];
}
void print_del_backup(simplify * S) {
	if(S->solver->proof == NULL) return;
	kissat * solver = S->solver;
	for(int i = 0; i < S->buf_len; i++) {
		int x = S->buf[i];
		x = pnsign(x) * solver->mapidx[abs(x)];
		PUSH_STACK(solver->proof->line, x);
	}
	print_delete_proof_line(solver->proof);
}
void update_var_clause_label(simplify *S, bool keep_all_variables)
{
    int remain_var = 0;
    if(keep_all_variables) {
        for(int i = 1; i <= S->vars; i++) {
            S->color[i] = i;
        }
        remain_var = S->vars;
    }else {
        for (int i = 1; i <= S->vars; i++)
            S->color[i] = 0;
        for (int i = 1; i <= S->clauses; i++) {
            if (S->clause_delete[i])
                continue;
            int l = S->clause_size[i];
            for (int j = 0; j < l; j++) {
                if (S->color[abs(S->clause[i][j])] == 0) {
                    // printf("%d %d\n", i, S->clause[i][j]);
                    S->color[abs(S->clause[i][j])] = ++remain_var;
                }
            }
        }
    }
    int nl = 0;
    for(unsigned i = 0; i < SIZE_STACK(S->units); i++) {
        int lit = S->units.begin[i];
        if(S->color[abs(lit)]) {
            S->units.begin[nl++] = pnsign(lit) * S->color[abs(lit)];
        }else {
//            S->units.begin[i] = 0;
        }
    }
    RESIZE_STACK(S->units, nl);
    int id = 0;
    int oriid = 0;
    for (int i = 1; i <= S->clauses; i++) {
        if (S->clause_delete[i])
            continue;
        ++id;
        if(i <= S->oriclauses) {
            oriid = id;
        }
        int l = S->clause_size[i];
        // S->clause_id[id] = S->clause_id[i];
        if (i == id) {
            for (int j = 0; j < l; j++)
                S->clause[id][j] = S->color[abs(S->clause[i][j])] * pnsign(S->clause[i][j]);
            continue;
        }
        if (l != S->clause_size[id]) {
            S->clause[id] = (int *)realloc(S->clause[id], sizeof(int) * l);
        }
        S->clause_size[id] = 0;
        for (int j = 0; j < l; j++)
            S->clause[id][S->clause_size[id]++] = S->color[abs(S->clause[i][j])] * pnsign(S->clause[i][j]);
        ;
    }
    for (int i = id + 1; i <= S->clauses; i++)
        free(S->clause[i]);
    for (int i = remain_var + 1; i <= S->vars; i++) {
        if (S->occurp[i] != NULL)
            free(S->occurp[i]);
        if (S->occurn[i] != NULL)
            free(S->occurn[i]);
    }
    S->vars = remain_var, S->clauses = id;
    S->oriclauses = oriid;
}

bool res_is_empty(simplify *S, int x)
{
    int op = S->occurp_size[x], on = S->occurn_size[x];
    for (int i = 0; i < op; i++) {
        int o1 = S->occurp[x][i], l1 = S->clause_size[o1];
        if (S->clause_delete[o1])
            continue;
        for (int j = 0; j < l1; j++)
            if (abs(S->clause[o1][j]) != x)
                S->resseen[abs(S->clause[o1][j])] = pnsign(S->clause[o1][j]);
        for (int j = 0; j < on; j++) {
            int o2 = S->occurn[x][j], l2 = S->clause_size[o2], flag = 0;
            if (S->clause_delete[o2])
                continue;
            for (int k = 0; k < l2; k++)
                if (abs(S->clause[o2][k]) != x && S->resseen[abs(S->clause[o2][k])] == -pnsign(S->clause[o2][k])) {
                    flag = 1;
                    break;
                }
            if (!flag) {
                for (int j = 0; j < l1; j++)
                    S->resseen[abs(S->clause[o1][j])] = 0;
                return false;
            }
        }
        for (int j = 0; j < l1; j++)
            S->resseen[abs(S->clause[o1][j])] = 0;
    }
    return true;
}

bool simplify_resolution(simplify *S)
{
    memset(S->occurn_size + 1, 0, sizeof(int) * S->vars);
    memset(S->occurp_size + 1, 0, sizeof(int) * S->vars);
    memset(S->resseen + 1, 0, sizeof(int) * S->vars * 2);
    memset(S->clean + 1, 0, sizeof(int) * S->vars);
    memset(S->clause_delete + 1, 0, sizeof(int) * S->clauses);
    for (int i = 1; i <= S->clauses; i++) {
        int l = S->clause_size[i];
        for (int j = 0; j < l; j++) {
            int x = S->clause[i][j];
            if (x > 0) {
                S->occurp_size[x]++;
            } else {
                S->occurn_size[-x]++;
            }
        }
    }
    for (int i = 1; i <= S->vars; i++) {
        if (S->occurp_size[i]) {
            S->occurp[i] = (int *)realloc(S->occurp[i], sizeof(int) * S->occurp_size[i]);
        }
        if (S->occurn_size[i]) {
            S->occurn[i] = (int *)realloc(S->occurn[i], sizeof(int) * S->occurn_size[i]);
        }
        S->occurp_size[i] = S->occurn_size[i] = 0;
    }
    for (int i = 1; i <= S->clauses; i++) {
        
        for (int j = 0; j < S->clause_size[i]; j++) {
            int v = S->clause[i][j];
            if (v > 0)
                S->occurp[v][S->occurp_size[v]++] = i;
            else
                S->occurn[-v][S->occurn_size[-v]++] = i;
        }
    }
    for (int i = 1; i <= S->vars; i++)
        if (S->occurn_size[i] == 0 && S->occurp_size[i] == 0)
            S->clean[i] = S->seen[i] = 1;

    int l = 1, r = 0;
    for (int i = 1; i <= S->vars; i++) {
        int op = S->occurp_size[i], on = S->occurn_size[i];
        if (op * on > op + on || S->clean[i])
            continue;
        if (res_is_empty(S, i)) {
            S->queue[++r] = i, S->clean[i] = 1;
        }
    }
    int now_turn = 0, seen_flag = 0, vars_sz = 0;
    int *vars = (int *)malloc(sizeof(int) * S->vars);
    while (l <= r) {
        ++now_turn;
        for (int j = l; j <= r; j++) {
            int i = S->queue[j];
            int op = S->occurp_size[i], on = S->occurn_size[i];
            for (int j = 0; j < op; j++) {
				int id = S->occurp[i][j];
                S->clause_delete[id] = 1;
				backup_clause(S, id);
				print_del_backup(S);
			}
            for (int j = 0; j < on; j++) {
				int id = S->occurn[i][j];
                S->clause_delete[id] = 1;
				backup_clause(S, id);
				print_del_backup(S);
			}
        }
        int ll = l;
        l = r + 1;

        vars_sz = 0;
        ++seen_flag;
        for (int u = ll; u <= r; u++) {
            int i = S->queue[u];
            int op = S->occurp_size[i], on = S->occurn_size[i];
            for (int j = 0; j < op; j++) {
                int o = S->occurp[i][j], l = S->clause_size[o];
                for (int k = 0; k < l; k++) {
                    int v = abs(S->clause[o][k]);
                    if (!S->clean[v] && S->seen[v] != seen_flag)
                        vars[vars_sz++] = v, S->seen[v] = seen_flag;
                }
            }
            for (int j = 0; j < on; j++) {
                int o = S->occurn[i][j], l = S->clause_size[o];
                for (int k = 0; k < l; k++) {
                    int v = abs(S->clause[o][k]);
                    if (!S->clean[v] && S->seen[v] != seen_flag)
                        vars[vars_sz++] = v, S->seen[v] = seen_flag;
                }
            }
        }
        for (int u = 0; u < vars_sz; u++) {
            int i = vars[u];
            int op = 0, on = 0;
            for (int j = 0; j < S->occurp_size[i]; j++)
                op += 1 - S->clause_delete[S->occurp[i][j]];
            for (int j = 0; j < S->occurn_size[i]; j++)
                on += 1 - S->clause_delete[S->occurn[i][j]];
            if (op * on > op + on)
                continue;
            if (res_is_empty(S, i)) {
                S->queue[++r] = i, S->clean[i] = 1;
            }
        }
    }
    S->res_clauses = 0;
    S->resolutions = r;
    if (r) {
        for (int i = 1; i <= S->clauses; i++) {
            if (S->clause_delete[i])
                S->res_clauses++;
        }
        S->res_clause = (int **)malloc(sizeof(int *) * (S->res_clauses + 1));
        S->res_clause_size = (int *)malloc(sizeof(int) * (S->res_clauses + 1));
        int id = 0;
        for (int i = 1; i <= S->clauses; i++) {
            if (!S->clause_delete[i])
                continue;
            int l = S->clause_size[i];
            S->res_clause_size[++id] = l;
            S->res_clause[id] = (int *)malloc(sizeof(int) * l);
            for (int j = 0; j < l; j++)
                S->res_clause[id][j] = pnsign(S->clause[i][j]) * S->mapfrom[abs(S->clause[i][j])];
        }

        S->resolution = (int *)malloc(sizeof(int) * (r + 1));
        update_var_clause_label(S, false);
        for (int i = 1; i <= r; i++) {
            int v = S->mapfrom[S->queue[i]];
            S->resolution[i] = v;
            //printf("c S->queue[i] = %d, v =%d, vars = %d, orivas = %d, newvars = %d\n", S->queue[i], v, S->vars, S->orivars, S->newVars);
            if (!v) {
                puts("c wrong mapfrom");
            }
            S->mapto[v] = 0, S->mapval[v] = -10;
        }
        for (int i = 1; i <= S->newVars; i++) {
            if (S->mapto[i]) {
                if (!S->color[S->mapto[i]]) {
                    //puts("c wrong color");
                    S->mapto[i] = 0;
                    if(!S->mapval[i]) {
                        S->mapval[i] = 1;
                    }
                }else {
                    S->mapto[i] = S->color[S->mapto[i]];
                }
            }
        }
    }else {
        int v = S->vars;
        int c = S->clauses;
        update_var_clause_label(S, false);
        for (int i = 1; i <= S->newVars; i++) {
            if (S->mapto[i]) {
                if (!S->color[S->mapto[i]]) {
                    S->mapto[i] = 0;
                    if(!S->mapval[i]) {
                        S->mapval[i] = 1;
                    }
                }else {
                    S->mapto[i] = S->color[S->mapto[i]];
                }
            }
        }
    }
    free(vars);
    return true;
}

bool simplify_easy_clause(simplify *S)
{
    S->mapfrom = NULL;
    proof *proof = S->solver->proof;
    memset(S->occurn_size + 1, 0, sizeof(int) * S->vars);
    memset(S->occurp_size + 1, 0, sizeof(int) * S->vars);
    memset(S->resseen + 1, 0, sizeof(int) * S->vars * 2);
    memset(S->varval + 1, 0, sizeof(int) * S->vars);
    memset(S->clause_delete + 1, 0, sizeof(int) * S->clauses);
    
    //for (int i = 1; i <= S->vars; i++) {
    //    S->occurn[i] = S->occurp[i] = NULL;
    //}
    for (int i = 1; i <= S->clauses; i++)
        S->clause_delete[i] = 0;
    int head = 1, tail = 0;
    kissat *solver = S->solver;
    for (int i = 1; i <= S->clauses; i++) {
        int l = S->clause_size[i], t = 0;
		backup_clause(S, i);
        for (int j = 0; j < l; j++) {
            int lit = TOLIT(S->clause[i][j]);
            if (S->resseen[lit] == i)
                continue;
            if (S->resseen[NEG(lit)] == i) {
                S->clause_delete[i] = 1;
                break;
            }
            S->clause[i][t++] = S->clause[i][j];
            S->resseen[lit] = i;
        }
        if (S->clause_delete[i]) {
            print_del_backup(S);
			continue;
		}
        S->clause_size[i] = t;
        for (int j = 0; j < t; j++) {
            if (S->clause[i][j] > 0)
                S->occurp_size[S->clause[i][j]]++;
            else
                S->occurn_size[-S->clause[i][j]]++;
            if ((t == 0 || t == 1 || t < l) && proof != NULL) {
                int var = solver->mapidx[abs(S->clause[i][j])];
                var = var * pnsign(S->clause[i][j]);
                PUSH_STACK(proof->line, var);
                proof->literals += 1;
            }
        }
        if ((t == 0 || t == 1 || t < l) && proof != NULL) {
            print_added_proof_line(proof);
			print_del_backup(S);
            // S->clause_id[i] = S->oriclauses + proof->added;
        }
        if (t == 0) {
            return false;
        }
        if (t == 1) {
            int lit = S->clause[i][0];
            S->clause_delete[i] = 1;
            if (S->varval[abs(lit)]) {
                if (S->varval[abs(lit)] == pnsign(lit))
                    continue;
                else
                    return false;
            }
            S->varval[abs(lit)] = pnsign(lit);
            S->queue[++tail] = abs(lit);
        }
    }
    //printf("c easy pre %f\n", kissat_process_time());
    
    for (int i = 1; i <= S->vars; i++) {
        if (S->occurp_size[i]) {
            S->occurp[i] = (int *)malloc(sizeof(int) * (S->occurp_size[i]));
        }
        if (S->occurn_size[i]) {
            int * tmp = (int *)malloc(sizeof(int) * (S->occurn_size[i]));
            S->occurn[i] = tmp;
        }
        S->occurp_size[i] = S->occurn_size[i] = 0;
    }
    //printf("c easy pre1 %f\n", kissat_process_time());
    for (int i = 1; i <= S->clauses; i++) {
        if (S->clause_delete[i])
            continue;
        for (int j = 0; j < S->clause_size[i]; j++) {
            int v = S->clause[i][j];
            if (v > 0)
                S->occurp[v][S->occurp_size[v]++] = i;
            else
                S->occurn[-v][S->occurn_size[-v]++] = i;
        }
    }
    //printf("c easy mid %f\n", kissat_process_time());
    memset(S->resseen + 1, 0, sizeof(int) * S->vars * 2);
    while (head <= tail) {
        int x = S->queue[head++];
        if (S->varval[x] == 1) {
            for (int i = 0; i < S->occurp_size[x]; i++)
                S->clause_delete[S->occurp[x][i]] = 1;
            for (int i = 0; i < S->occurn_size[x]; i++) {
                int o = S->occurn[x][i], t = 0;
                if (S->clause_delete[o])
                    continue;
				backup_clause(S, o);
                for (int j = 0; j < S->clause_size[o]; j++) {
                    if (S->varval[abs(S->clause[o][j])] == pnsign(S->clause[o][j])) {
                        S->clause_delete[o] = 1;
                        break;
                    }
                    if (S->varval[abs(S->clause[o][j])] == -pnsign(S->clause[o][j]))
                        continue;
                    S->clause[o][t++] = S->clause[o][j];
                }
                if (S->clause_delete[o]) {
                    print_del_backup(S);
					continue;
				}
                if ((t == 0 || t == 1 || t < S->clause_size[o]) && proof != NULL) {
                    for (int j = 0; j < t; j++) {
                        int var = solver->mapidx[abs(S->clause[o][j])];
                        var = var * pnsign(S->clause[o][j]);
                        PUSH_STACK(proof->line, var);
                        proof->literals += 1;
                    }
                    print_added_proof_line(proof);
					print_del_backup(S);
					// S->clause_id[o] = S->oriclauses + proof->added;
                }
                S->clause_size[o] = t;
                if (t == 0) {
                    //printf("false0 %d\n", x);
                    return false;
                }
                if (t == 1) {
                    int lit = S->clause[o][0];
                    S->clause_delete[o] = 1;
                    if (S->varval[abs(lit)]) {
                        if (S->varval[abs(lit)] == pnsign(lit))
                            continue;
                        else
                            return false;
                    }
                    S->varval[abs(lit)] = pnsign(lit);
                    S->queue[++tail] = abs(lit);
                }
            }
        } else {
            for (int i = 0; i < S->occurn_size[x]; i++)
                S->clause_delete[S->occurn[x][i]] = 1;
            for (int i = 0; i < S->occurp_size[x]; i++) {
                int o = S->occurp[x][i], t = 0;
                if (S->clause_delete[o])
                    continue;
				backup_clause(S, o);
                for (int j = 0; j < S->clause_size[o]; j++) {
                    if (S->varval[abs(S->clause[o][j])] == pnsign(S->clause[o][j])) {
                        S->clause_delete[o] = 1;
                        break;
                    }
                    if (S->varval[abs(S->clause[o][j])] == -pnsign(S->clause[o][j]))
                        continue;
                    S->clause[o][t++] = S->clause[o][j];
                }
                if (S->clause_delete[o]) {
                    print_del_backup(S);
					continue;
				}
                if ((t == 0 || t == 1 || t < S->clause_size[o]) && proof != NULL) {
                    for (int j = 0; j < t; j++) {
                        int var = solver->mapidx[abs(S->clause[o][j])];
                        var = var * pnsign(S->clause[o][j]);
                        PUSH_STACK(proof->line, var);
                        proof->literals += 1;
                    }
                    print_added_proof_line(proof);
					print_del_backup(S);
                    // S->clause_id[o] = S->oriclauses + proof->added;
                }
                S->clause_size[o] = t;
                if (t == 0) {
                    //printf("false1%d\n", x);
                    return false;
                }
               if (t == 1) {
                    int lit = S->clause[o][0];
                    S->clause_delete[o] = 1;
                    if (S->varval[abs(lit)]) {
                        if (S->varval[abs(lit)] == pnsign(lit))
                            continue;
                        else
                            return false;
                    }
                    S->varval[abs(lit)] = pnsign(lit);
                    S->queue[++tail] = abs(lit);
                }
            }
        }
    }
    update_var_clause_label(S, true);//keep all variables.

    for (int i = 1; i <= tail; i++) {
        int v = S->queue[i];
        S->mapval[v] = S->varval[v];
        if (S->color[v]) {
            //puts("c wrong unit");
            //we keep all variables now so this is normal.
        }
    }
    S->mapfrom = (int *)malloc(sizeof(int) * (S->vars + 1));
    for (int i = 1; i <= S->vars; i++)
        S->mapfrom[i] = 0;
    for (int i = 1; i <= S->newVars; i++) {
        if (S->color[i])
            S->mapto[i] = S->color[i], S->mapfrom[S->color[i]] = i;
        else if (!S->mapval[i]) // not in unit queue, then it is no use var
            S->mapto[i] = 0, S->mapval[i] = 1;
        else
            S->mapto[i] = 0;
    }
    return true;
}

simplify *S;
int search_almost_one(simplify *S)
{
    HashMap *H = map_init(40000003);
    nlit = 2 * S->vars + 2;
    int **occur = (int **)calloc((nlit), sizeof(int *));
    int *occur_size = (int *)calloc((nlit), sizeof(int));
    for (int i = 1; i <= S->oriclauses; i++) {
        S->clause_delete[i] = 0;
        if (S->clause_size[i] != 2)
            continue;
        int x = tolit(S->clause[i][0]);
        int y = tolit(S->clause[i][1]);
        ll id1 = mapv(x, y);
        ll id2 = mapv(y, x);
        map_insert(H, id1, i);
        map_insert(H, id2, i);
        occur_size[x]++;
        occur_size[y]++;
        // printf("xy %d %d %d\n", x, y, nlit);
    }
    //    S->resseen = realloc(S->resseen, 754);
    for (int i = 2; i < nlit; i++) {
        if (occur_size[i])
            occur[i] = (int *)malloc(sizeof(int) * (occur_size[i]));
        occur_size[i] = S->seen[i] = 0;
    }
    for (int i = 1; i <= S->oriclauses; i++) {
        if (S->clause_size[i] != 2)
            continue;
        int x = tolit(S->clause[i][0]);
        int y = tolit(S->clause[i][1]);
        occur[x][occur_size[x]++] = y;
        occur[y][occur_size[y]++] = x;
        // printf("occur %d %d\n", x, y);
    }
    S->cards = 0;
    cvec *nei = cvec_init();
    cvec *ino = cvec_init();
    // printf("%d\n", occur);
    // printf("%d\n", occur);
    long long tot_size = 0;
    for (int i = 2; i <= S->vars * 2 + 1; i++) {
        if (S->seen[i] || !occur_size[i])
            continue;
        S->seen[i] = 1;
        cvec_clear(nei);
        for (int j = 0; j < occur_size[i]; j++) {
            if (!S->seen[occur[i][j]]) {
                cvec_push(nei, occur[i][j]);
            }
        }
        do {
            // printf("!\n");
            cvec_clear(ino);
            cvec_push(ino, i);
            for (int j = 0; j < nei->sz; j++) {
                // printf("%d\n", j);
                int v = cvec_data(nei, j), flag = 1;
                for (int k = 0; k < ino->sz; k++) {
                    ll id = mapv(v, cvec_data(ino, k));
                    int d1 = map_get(H, id, 0);
                    if (!d1) {
                        flag = 0;
                        break;
                    }
                    S->queue[k] = d1;
                }
                if (flag) {
                    // printf("extend %d\n", v);
                    for (int k = 0; k < ino->sz; k++) {
                        S->clause_delete[S->queue[k]] = 1;
                        ll id1 = mapv(v, cvec_data(ino, k)), id2 = mapv(cvec_data(ino, k), v);
                        map_delete(H, id1);
                        map_delete(H, id2);
                    }
                    cvec_push(ino, v);
                }
            }
            if (ino->sz >= 2) {
                
                S->card_one[S->cards] = (int *)malloc(sizeof(int) * (ino->sz));
                S->card_one_size[S->cards] = 0;
                for (int j = 0; j < ino->sz; j++) {
                    S->card_one[S->cards][S->card_one_size[S->cards]++] = -toidx(cvec_data(ino, j));
                }
                S->cards++;
                tot_size += ino->sz;
                if (S->cards >= S->M_card || tot_size >= 10000000) {
                    cvec_release(ino);
                    cvec_release(nei);
                    map_free(H);
                    free(occur_size);
                    for (int i = 0; i < nlit; i++)
                        if (occur[i] != NULL)
                            free(occur[i]);

                    free(occur);
                    return 0;
                }
                // printf("c catch constrain: ");
                // for (int j = 0; j < ino->sz; j++) printf("%d ", toidx(cvec_data(ino, j)));
                // puts("");
            }
        } while (ino->sz != 1);
    }
    cvec_release(ino);
    cvec_release(nei);
    map_free(H);
    free(occur_size);
    for (int i = 0; i < nlit; i++) {
        if (occur[i] != NULL) {
            free(occur[i]);
        }
    }
    free(occur);
    return S->cards;
}
void move_clause(simplify *S, int to, int frm)
{
    if (to != frm) {
        // free(S->clause[to]);
        S->clause[to] = S->clause[frm];
        S->clause[frm] = NULL;
        S->clause_size[to] = S->clause_size[frm];
        S->clause_size[frm] = 0;
    }
}

void upd_occur(simplify *S, int v, int s)
{
    int x = abs(v);
    int t = 0;
    if (v > 0) {
        for (int j = 0; j < S->occurp_size[x]; j++)
            if (S->occurp[x][j] != s)
                S->occurp[x][t++] = S->occurp[x][j];
        S->occurp_size[x] = t;
    } else {
        for (int j = 0; j < S->occurn_size[x]; j++)
            if (S->occurn[x][j] != s)
                S->occurn[x][t++] = S->occurn[x][j];
        S->occurn_size[x] = t;
    }
}

int scc_almost_one(simplify *S)
{
    memset(S->occurp_size + 1, 0, sizeof(int) * S->vars);
    memset(S->occurn_size + 1, 0, sizeof(int) * S->vars);
    memset(S->cdel + 1, 0, sizeof(int) * S->cards);
    for (int i = 1; i <= S->vars; i++) {
        S->occurp[i] = (int *)realloc(S->occurp[i], sizeof(int) * S->M_card);
        S->occurn[i] = (int *)realloc(S->occurn[i], sizeof(int) * S->M_card);
    }
    for (int i = 0; i < S->cards; i++) {
        S->cdel[i] = 0;
        for (int j = 0; j < S->card_one_size[i]; j++) {
            int v = S->card_one[i][j];
            if (v > 0)
                S->occurp[v][S->occurp_size[v]++] = i;
            else
                S->occurn[-v][S->occurn_size[-v]++] = i;
        }
    }

    int flag = 1;
    do {
        flag = 0;
        for (int i = 1; i <= S->vars; i++) {
            if (!S->occurp_size[i] || !S->occurn_size[i])
                continue;
            if (S->cards + S->occurp_size[i] * S->occurn_size[i] >= S->M_card)
                return 0;
            flag = 1;
            for (int ip = 0; ip < S->occurp_size[i]; ip++)
                S->cdel[S->occurp[i][ip]] = 1;
            for (int in = 0; in < S->occurn_size[i]; in++)
                S->cdel[S->occurn[i][in]] = 1;
            for (int ip = 0; ip < S->occurp_size[i]; ip++) {
                int op = S->occurp[i][ip];
                for (int in = 0; in < S->occurn_size[i]; in++) {
                    int on = S->occurn[i][in];
                    S->card_one[S->cards] =
                        (int *)malloc(sizeof(int) * (S->card_one_size[op] + S->card_one_size[on] - 2));
                    S->card_one_size[S->cards] = 0;
                    S->cdel[S->cards] = 0;

                    int find = 0;
                    for (int j = 0; j < S->card_one_size[op]; j++) {
                        int v = S->card_one[op][j];
                        if (abs(v) == i && !find)
                            continue;
                        if (abs(v) == i)
                            find = 1;
                        S->card_one[S->cards][S->card_one_size[S->cards]++] = v;
                        if (v > 0) {
                            if (S->occurp_size[v] && S->occurp[v][S->occurp_size[v] - 1] != S->cards)
                                S->occurp[v][S->occurp_size[v]++] = S->cards;
                        } else {
                            if (S->occurn_size[-v] && S->occurn[-v][S->occurn_size[-v] - 1] != S->cards)
                                S->occurn[-v][S->occurn_size[-v]++] = S->cards;
                        }
                    }
                    find = 0;
                    for (int j = 0; j < S->card_one_size[on]; j++) {
                        int v = S->card_one[on][j];
                        if (abs(v) == i && !find)
                            continue;
                        if (abs(v) == i)
                            find = 1;
                        S->card_one[S->cards][S->card_one_size[S->cards]++] = v;
                        if (v > 0) {
                            if (S->occurp_size[v] && S->occurp[v][S->occurp_size[v] - 1] != S->cards)
                                S->occurp[v][S->occurp_size[v]++] = S->cards;
                        } else {
                            if (S->occurn_size[-v] && S->occurn[-v][S->occurn_size[-v] - 1] != S->cards)
                                S->occurn[-v][S->occurn_size[-v]++] = S->cards;
                        }
                    }
                    ++S->cards;
                }
            }
            for (int ip = 0; ip < S->occurp_size[i]; ip++) {
                int op = S->occurp[i][ip];
                for (int j = 0; j < S->card_one_size[op]; j++)
                    upd_occur(S, S->card_one[op][j], op);
            }

            for (int in = 0; in < S->occurn_size[i]; in++) {
                int on = S->occurn[i][in];
                for (int j = 0; j < S->card_one_size[on]; j++)
                    upd_occur(S, S->card_one[on][j], on);
            }
        }
    } while (flag);

    int t = 0;
    for (int i = 0; i < S->cards; i++) {
        if (S->cdel[i])
            continue;
        ++t;
        // if (S->card_one_size[i] >= 2) {
        //     printf("c catch constrain: ");
        //     for (int j = 0; j < S->card_one_size[i]; j++) printf("%d ", S->card_one[i][j]);
        //     puts("");
        // }
    }
    return t;
}


void set_unit(simplify *S, int id, int val)
{
    kissat *solver = S->solver;

    PUSH_STACK(S->units, id * val);// when PB proof required, print these clauses..
}


int check_card(simplify *S, int id)
{ // 0: wrong  -1:useless    1:normal
    int ps = 0, ns = 0, t = -1;
    MatType poss = 0, negs = 0;

    for (int j = 1; j <= S->vars; j++) {
        if (fabs(S->mat[id][j]) < 1e-6)
            continue;
        /*if(S->mat[id][j] == 0) {
            continue;
        }*/
        t = j;
        if (S->mat[id][j] > 0)
            ++ps, poss += S->mat[id][j];
        if (S->mat[id][j] < 0)
            ++ns, negs += S->mat[id][j];
    }

    if (ns + ps == 1) {
        MatType r = S->mat[id][0] / S->mat[id][t];
        if (ps) {
            if (fabs(r) < 1e-6) {
                set_unit(S, t, -1);
                // printf("c [CE] get unit: %d = 0\n", t);//这里不考虑unit吗？
            } else if (r < 0) {
                // printf("c [CE] get wrong: %d < 0\n", t);
                return 0;
            }
            return -1;
        }
        if (ns) {
            if (fabs(r - 1) < 1e-6) {
                set_unit(S, t, 1);
                // printf("c [CE] get unit: %d = 1\n", t);
            } else if (r > 1) {
                // printf("c [CE] get wrong: %d > 1\n", t);
                return 0;
            }
            return -1;
        }
    }
    if (ns + ps == 0) {
        if (S->mat[id][0] < -(1e-6)) {
            // printf("c [CE] get empty wrong clause: 0 < %.3lf\n", S->mat[id][0]);
            return 0;
        }
        return -1;
    }
    if (poss <= S->mat[id][0]) {
        return -1;
    }
    if (negs >= S->mat[id][0]) {
        if (negs < S->mat[id][0] + 1e-6) {
            // unit
            for (int j = 1; j <= S->vars; j++) {
                if (fabs(S->mat[id][j]) < 1e-6)
                    continue;
                if (S->mat[id][j] < 0) {
                    set_unit(S, j, 1);
                }
            }
        } else
            return 0;
    }
    if (S->mat[id][0] == 0) {
        if (ps == 0) {
            return -1;
        } else if (ns == 0) {
            for (int j = 1; j <= S->vars; j++) {
                if (fabs(S->mat[id][j]) < 1e-6)
                    continue;
                if (S->mat[id][j] > 0) {
                    set_unit(S, j, -1);
                }
            }
            // unit
        }
    }
    return 1;
}
void print_card(simplify *S, int id)
{
	return;
    printf("%f>=", S->mat[id][0]);
    for (int i = 1; i <= S->vars; i++)
        printf("%f ", S->mat[id][i]);
    printf("\n");
}

int dfs(int v, int *vst, int *match, int **e)
{
    for (int i = 0; i < S->clause_size[v]; i++) {
        int y = e[v][i];
        if (!vst[y]) {
            vst[y] = 1;
            if (match[y] == -1 || dfs(match[y], vst, match, e)) {
                match[y] = v;
                return 1;
            }
        }
    }
    return 0;
}
void dfs_mark(int v, int *vst, int *match, int **e, kissat * solver, unsigneds * le, unsigneds * ri) {
    //printf("%d\n", v);
    PUSH_STACK(*le, v);
    for (int i = 0; i < S->clause_size[v]; i++) {
        int y = e[v][i];
        //printf("%d->%d\n", v, y);
        if (!vst[y]) {
            PUSH_STACK(*ri, y);
            vst[y] = 1;
            dfs_mark(match[y], vst, match, e, solver, le, ri);
        }
    }
}
static inline bool lequ(unsigned a, unsigned b) {
    return a < b;
}
enum {
    GE, LE
};
void print_inequality(simplify * S, int type, long long b) {
    longlongs * l = &(S->ineq);
    proof * proof = S->solver->proof;
    kissat * solver = S->solver;
    kissat_puts(proof->file, "rup");
    for(unsigned i = 0; i < SIZE_STACK(*l); i += 2) {
        kissat_putc(proof->file, ' ');
        kissat_putint(proof->file, PEEK_STACK(*l, i + 1));
        kissat_putc(proof->file, ' ');
        int lit = PEEK_STACK(*l, i);
//        printf("lit %d %d\n", lit, solver->mapidx[abs(lit)]);
        lit = pnsign(lit) * solver->mapidx[abs(lit)];

        if(lit < 0) {
            kissat_putc(proof->file, '~');
        }
        kissat_putc(proof->file, 'x');
        kissat_putint(proof->file, abs(lit));
    }
    if(type == GE) {
        kissat_puts(proof->file, " >= ");
    }else {
        kissat_puts(proof->file, " <= ");
    }
    kissat_putint(proof->file, b);
    kissat_puts(proof->file, " ;\n");
    CLEAR_STACK(*l);
}
void print_pol(simplify * S) {
    longlongs * l = &(S->ineq);
    proof * proof = S->solver->proof;
    //kissat * solver = S->solver;
    kissat_puts(proof->file, "pol");
    kissat_putc(proof->file, ' ');
    kissat_putint(proof->file, PEEK_STACK(*l, 0));

    for(unsigned i = 1; i < SIZE_STACK(*l); i += 2) {
        kissat_putc(proof->file, ' ');
        kissat_putint(proof->file, PEEK_STACK(*l, i));
        kissat_putc(proof->file, ' ');
        kissat_putc(proof->file, PEEK_STACK(*l, i + 1));
    }
    kissat_putc(proof->file, '\n');
    CLEAR_STACK(*l);
}
void print_axby_line(simplify * S, long long a, long long b, long long c, long long d) {
    proof * proof = S->solver->proof;
    kissat_puts(proof->file, "pol");
    kissat_putc(proof->file, ' ');
    kissat_putint(proof->file, a);
    kissat_putc(proof->file, ' ');
    kissat_putint(proof->file, b);
    kissat_putc(proof->file, ' ');
    kissat_putc(proof->file, '*');
    kissat_putc(proof->file, ' ');
    kissat_putint(proof->file, c);
    kissat_putc(proof->file, ' ');
    kissat_putint(proof->file, d);
    kissat_putc(proof->file, ' ');
    kissat_putc(proof->file, '*');
    kissat_puts(proof->file, " +\n");
}
void print_unit(simplify * S, int lit) {
    proof * proof = S->solver->proof;
    kissat * solver = S->solver;
    kissat_puts(proof->file, "rup 1");
    lit = pnsign(lit) * solver->mapidx[abs(lit)];

    if(lit < 0) {
        kissat_putc(proof->file, '~');
    }
    kissat_putc(proof->file, 'x');
    kissat_putint(proof->file, abs(lit));
    kissat_puts(proof->file, " ;\n");
}
void generate_amo_proof(simplify * S, unsigned id) {
    int len = S->card_one_size[id];
    kissat * solver = S->solver;
    int * labels = (int*)malloc(sizeof(int) * len * len);
    for(int delta = 1; delta < len; delta++) {
        for(int i = 0; i + delta < len; i++) {
            int j = i + delta;
            if(j == i + 1) {
                PUSH_STACK(S->ineq, S->card_one[id][i]);
                PUSH_STACK(S->ineq, -1);
                PUSH_STACK(S->ineq, S->card_one[id][j]);
                PUSH_STACK(S->ineq, -1);
                print_inequality(S, GE, -1);
                labels[i * len + j] = ++S->pbcounter;
            }else {
                PUSH_STACK(S->ineq, S->card_one[id][i]);
                PUSH_STACK(S->ineq, -1);
                PUSH_STACK(S->ineq, S->card_one[id][j]);
                PUSH_STACK(S->ineq, -1);
                print_inequality(S, GE, -1);
                ++S->pbcounter;
                PUSH_STACK(S->ineq, labels[i * len + j - 1] - S->pbcounter - 1);
                PUSH_STACK(S->ineq, labels[(i + 1) * len + j] - S->pbcounter - 1);
                PUSH_STACK(S->ineq, '+');
                PUSH_STACK(S->ineq, -1);
                PUSH_STACK(S->ineq, '+');
                PUSH_STACK(S->ineq, 2);
                PUSH_STACK(S->ineq, 'd');
                print_pol(S);
                labels[i * len + j] = ++S->pbcounter;
            }
        }
    }
}
int bipartite_check(simplify *S) {
    int *ey = (int *)malloc(sizeof(int) * (S->vars + 1));
    int *sgn = (int *)malloc(sizeof(int) * (S->vars + 1));
    int *baksgn = (int *)malloc(sizeof(int) * (S->vars + 1));
    int *mark = (int *)malloc(sizeof(int) * (S->clauses + 1));
    int **e = (int **)malloc(sizeof(int *) * (S->clauses + 1));
    memset(e, 0, sizeof(int *) * (S->clauses + 1));
    memset(ey, 0, sizeof(int) * (S->vars + 1));
    memset(sgn, 0, sizeof(int) * (S->vars + 1));
    memset(mark, 0, sizeof(int) * (S->clauses + 1));
    long long cntvar = 0, cntcls = 0;
    for (int i = 0; i < S->cards; i++) {
        if (S->cdel[i])
            continue;
        // bipartite graph, right side (<=1)
        bool used = false;
        for (int j = 0; j < S->card_one_size[i]; j++) {
            //printf("%d ", S->card_one[i][j]);
            if (ey[abs(S->card_one[i][j])]) {
                used = true;
                break;
            }
        }
        //printf("\n");

        //if(used) printf("??\n");
        if (!used) {
            for (int j = 0; j < S->card_one_size[i]; j++) {
                ey[abs(S->card_one[i][j])] = i;
                sgn[abs(S->card_one[i][j])] = S->card_one[i][j];
                cntvar++;
            }
            //printf("S->cardonesize[%d] = %d\n", i, S->card_one_size[i]);
            cntcls += (S->card_one_size[i]) * (S->card_one_size[i] - 1ll) / 2;
        }
    }
    int delta = 0;
    for(int i = 1; i <= S->vars; i++) {
        if(sgn[i] == 0) {
            sgn[i] = S->vars + 1;
            ey[i] = S->cards;
            S->cards++;
            delta++;
            //printf("!%d\n", i);
        }
    }
    //printf("sgn[13508] = %d\n", sgn[13508]);
    memcpy(baksgn, sgn, sizeof(int) * (S->vars + 1));
    for (int i = 1; i <= S->clauses; i++) {
        if (S->clause_delete[i])
            continue;
        // bipartite graph, left side, >=1
        int flag = true;
        for (int j = 0; j < S->clause_size[i]; j++) {
            int lit = S->clause[i][j];
            //if(abs(lit) == 13508) printf("!!!%d\n", i);
            if (sgn[abs(lit)] == S->vars + 1) {
                sgn[abs(lit)] = lit;
                baksgn[abs(lit)] = lit;
            }
            if (sgn[abs(lit)] != lit) {
                //printf("%d??\n", lit);
                flag = false;
            }
        }
        //printf("%d %d %d\n", i, S->clause_size[i], flag);
        if (flag) {
            mark[i] = 1;
            e[i] = malloc(sizeof(int) * S->clause_size[i]);
            cntcls++;
            for (int j = 0; j < S->clause_size[i]; j++) {
                int lit = S->clause[i][j];
                e[i][j] = ey[abs(lit)];
                //printf("%d->%d\n", i, e[i][j]);
                sgn[abs(lit)] = 0;
            }
            // printf("c biparite LHS clause vertex: %d\n", i);
        }
    }
    
    int *vst = malloc(sizeof(int) * (S->cards));
    int *match = malloc(sizeof(int) * (S->cards));
    memset(match, -1, sizeof(int) * (S->cards));

    bool matched = true;
    unsigneds conflict_set_clauses, conflict_set_cards;
    kissat * solver = S->solver;
    INIT_STACK(conflict_set_clauses);
    INIT_STACK(conflict_set_cards);
    for (int i = 1; i <= S->clauses; i++) {
        if (mark[i]) {
            memset(vst, 0, sizeof(int) * (S->cards));
            if (!dfs(i, vst, match, e)) {
                matched = false;
                memset(vst, 0, sizeof(int) * (S->cards));
                dfs_mark(i, vst, match, e, solver, &conflict_set_clauses, &conflict_set_cards);
                break;
            }
        }
    }
    //printf("c %lld %d %lld %d\n", cntvar, S->vars, cntcls, S->clauses);
    if(matched == true && cntcls == S->clauses) {
        int * matchc = malloc((S->clauses + 1) * sizeof(int));
        bool * vst = calloc((S->vars + 1), sizeof(bool));
        memset(matchc, -1, (S->clauses + 1) * sizeof(int));
        for(int i = 0; i < S->cards; i++) {
            if(match[i] != -1) {
                matchc[match[i]] = i;
                //printf("matchc[%d] = %d\n", match[i], i);
            }
        }
        for (int i = 1; i <= S->clauses; i++) {
            if (matchc[i] == -1) {
                continue;
            }
            bool flag = true;
            for (int j = 0; j < S->clause_size[i]; j++) {
                int lit = S->clause[i][j];
                //printf("ey[%d] = %d\n", abs(lit), ey[abs(lit)]);
                if(flag && ey[abs(lit)] == matchc[i]) {
                    PUSH_STACK(S->units, lit);
                    vst[abs(lit)] = 1;
                    flag = false;
                    break;
                }else {
                }
            }
        }
        for (int i = 1; i <= S->vars; i++) {
            if(!vst[i]) {
                if(abs(baksgn[i]) != i) {
                    baksgn[i] = i;
                    //printf("i = %d\n", i);
                }
                PUSH_STACK(S->units, -baksgn[i]);
            }
        }
        free(vst);
        free(matchc);
        //printf("c bipartite graph solution hint: size %lu, number of variables: %u\n", SIZE_STACK(S->units), S->vars);
        S->solved = true;
    }
    //printf("%d %d\n", SIZE_STACK(conflict_set_clauses), SIZE_STACK(conflict_set_cards));
    /*printf("matched = %d\n", matched);
    for(int i = 0; i < S->cards; i++) {
        printf("%d-%d\n", match[i], i);
    }*/
    INIT_STACK(S->ineq);
    S->pbcounter = 0;
    //proof * proof = solver->proof;
    if(matched == false && solver->proof) {
        if(solver->proof->binary == false) {
            //pseudo boolean proof
            ints polpos, polneg;
            INIT_STACK(polpos);
            INIT_STACK(polneg);
            for(unsigned i = 0; i < SIZE_STACK(conflict_set_clauses); i++) {
                unsigned c = PEEK_STACK(conflict_set_clauses, i);
                for(int j = 0; j < S->clause_size[c]; j++) {
                    int lit = S->clause[c][j];
                    //int y = ey[abs(lit)];
                    PUSH_STACK(S->ineq, lit);
                    //printf("%d ", lit);
                    PUSH_STACK(S->ineq, 1);
                }
                //printf("\n");
                print_inequality(S, GE, 1);
                S->pbcounter++;
                PUSH_STACK(polpos, S->pbcounter);
                
            }
            SORT(unsigned, SIZE_STACK(conflict_set_cards), BEGIN_STACK(conflict_set_cards), lequ);
            unsigned j = 0;
            for(unsigned i = 0; i < SIZE_STACK(conflict_set_cards); i++) {
                if(i == 0 || PEEK_STACK(conflict_set_cards, i) != PEEK_STACK(conflict_set_cards, i - 1)) {
                    POKE_STACK(conflict_set_cards, j, PEEK_STACK(conflict_set_cards, i));
                    j++;
                }
            }
            RESIZE_STACK(conflict_set_cards, j);
            for(unsigned i = 0; i < SIZE_STACK(conflict_set_cards); i++) {
                generate_amo_proof(S, PEEK_STACK(conflict_set_cards, i));
                PUSH_STACK(polneg, S->pbcounter);
            }
            PUSH_STACK(S->ineq, PEEK_STACK(polpos, 0) - S->pbcounter - 1);
            for(unsigned i = 1; i < SIZE_STACK(polpos); i++) {
                PUSH_STACK(S->ineq, PEEK_STACK(polpos, i) - S->pbcounter - 1);
                PUSH_STACK(S->ineq, '+');
            }
            for(unsigned i = 0; i < SIZE_STACK(polneg); i++) {
                PUSH_STACK(S->ineq, PEEK_STACK(polneg, i) - S->pbcounter - 1);
                PUSH_STACK(S->ineq, '+');
            }
            
            print_pol(S);//conflict
            RELEASE_STACK(polpos);
            RELEASE_STACK(polneg);
        }else if(SIZE_STACK(conflict_set_cards) <= 1000u && SIZE_STACK(conflict_set_clauses) >= 3u) {
            //PR proof
            int nh = SIZE_STACK(conflict_set_cards);
            int ** ori_vars = (int **) malloc(sizeof(int*) * (nh + 1));
            int tmp_vars = S->vars;
            int sw = ++tmp_vars;
            int ** ph_vars = (int**)malloc(sizeof(int * ) * (nh + 1));
            int * hole_id = (int *) malloc(sizeof(int) * S->cards);
            for(int i = 0; i < nh; i++) {
                hole_id[PEEK_STACK(conflict_set_cards, i)] = i;
            }
            proof * proof = solver->proof;
            //printf("%lu %lu\n", SIZE_STACK(conflict_set_clauses), SIZE_STACK(conflict_set_cards));
            for(int i = 0; i < nh + 1; i++) {
                ori_vars[i] = (int * )calloc(nh, sizeof(int));
                ph_vars[i] = (int * )calloc(nh, sizeof(int));
            }
            int * new_vars = (int *) calloc((S->vars + 1), sizeof(int));
            intss new_cards;
            INIT_STACK(new_cards);
            for(int i = 0; i < nh + 1; i++) {//create variable copies.
                int c = PEEK_STACK(conflict_set_clauses, i);
                int l = S->clause_size[c];
                for(int j = 0; j < l; j++) {//add a fake switch sw. if sw is true, the new copied variable is set to be equal to the old variable. if sw is false, the same happens.
                    
                    int lit = S->clause[c][j];
                    int var = abs(lit);
                    if(new_vars[var] == 0) {
                        new_vars[var] = ++tmp_vars;
                        add_lits_tmp(S, proof, 3, -new_vars[var], sw, var);
                        add_lits_tmp(S, proof, 3, new_vars[var], sw, -var);
                        add_lits_tmp(S, proof, 3, -new_vars[var], -sw, var);
                        add_lits_tmp(S, proof, 3, new_vars[var], -sw, -var);
                    }
                    int new_lit = pnsign(lit) * new_vars[abs(lit)];
                    int card_id = ey[var];
                    ori_vars[i][hole_id[card_id]] = lit;
                    ph_vars[i][hole_id[card_id]] = new_lit;
                }
            }
            for(int i = 0; i < nh; i++) {//copy related amo constraints
                int card = PEEK_STACK(conflict_set_cards, i);
                ints new_card;
                INIT_STACK(new_card);
                for(int j = 0; j < S->card_one_size[card]; j++) {
                    int vj = S->card_one[card][j];
                    if(new_vars[abs(vj)]) {
                        vj = new_vars[abs(vj)] * pnsign(vj);
                        PUSH_STACK(new_card, vj);
                    }
                }
                PUSH_STACK(new_cards, new_card);
                int siz = SIZE_STACK(new_card);
                for(int j = 0; j < siz; j++) {
                    for(int k = j + 1; k < siz; k++) {
                        int vj = PEEK_STACK(new_card, j);
                        int vk = PEEK_STACK(new_card, k);
                        add_lits_tmp(S, proof, 3, -vj, -vk, sw);
                        add_lits_tmp(S, proof, 3, -vj, -vk, -sw);
                        add_lits_tmp(S, proof, 2, -vj, -vk);
                    }
                }
            }
            for(int i = 0; i < nh + 1; i++) {//copy conflict core clauses. (to prevent influence of unrelated clauses)
                int c = PEEK_STACK(conflict_set_clauses, i);
                int l = S->clause_size[c];
                for(int j = 0; j < nh; j++) {//complete new (pigeon hole) variables.
                    if(ori_vars[i][j] == 0) {
                        ph_vars[i][j] = ++tmp_vars;
                        ints * card = &PEEK_STACK(new_cards, j);
                        for(all_stack(int, lit, *card)) {
                            add_lits_tmp(S, proof, 2, -tmp_vars, -lit);
                        }
                        PUSH_STACK(*card, tmp_vars);
                    }
                }
                //printf("i = %d, c = %d\n", i, c);
                for(int k = 0; k < l; k++) {
                    int lit = S->clause[c][k];
                    int new_lit = pnsign(lit) * new_vars[abs(lit)];
                    //printf("%d ", new_lit);
                    PUSH_STACK(proof->line, new_lit);
                }
                //printf("\n");
                for(int k = 0; k < nh; k++) {
                    if(ori_vars[i][k] == 0 && ph_vars[i][k]) {
                        PUSH_STACK(proof->line, ph_vars[i][k]);
                    }
                }
                PUSH_STACK(proof->line, sw);
                print_added_proof_line(proof);
                for(int k = 0; k < l; k++) {
                    int lit = S->clause[c][k];
                    int new_lit = pnsign(lit) * new_vars[abs(lit)];
                    PUSH_STACK(proof->line, new_lit);
                }
                for(int k = 0; k < nh; k++) {
                    if(ori_vars[i][k] == 0 && ph_vars[i][k]) {
                        PUSH_STACK(proof->line, ph_vars[i][k]);
                    }
                }
                PUSH_STACK(proof->line, -sw);
                print_added_proof_line(proof);
                for(int k = 0; k < l; k++) {
                    int lit = S->clause[c][k];
                    int new_lit = pnsign(lit) * new_vars[abs(lit)];
                    PUSH_STACK(proof->line, new_lit);
                }
                for(int k = 0; k < nh; k++) {
                    if(ori_vars[i][k] == 0 && ph_vars[i][k]) {
                        PUSH_STACK(proof->line, ph_vars[i][k]);
                    }
                }
                print_added_proof_line(proof);
            }
            
            for(int i = 0; i < nh + 1; i++) {//detach new and old vars
                int c = PEEK_STACK(conflict_set_clauses, i);
                int l = S->clause_size[c];
                for(int j = 0; j < l; j++) {
                    int lit = S->clause[c][j];
                    int var = abs(lit);
                    if(new_vars[var] > 0) {
                        del_lits(S, proof, 3, var, -new_vars[var], sw);
                        del_lits(S, proof, 3, -var, new_vars[var], sw);
                        del_lits(S, proof, 3, var, -new_vars[var], -sw);
                        del_lits(S, proof, 3, -var, new_vars[var], -sw);
                        new_vars[var] *= -1;
                    }
                }
            }
            for(int i = 1; i <= S->vars; i++) {
                new_vars[i] *= -1;
            }
            for(int i = 0; i < nh + 1; i++) {//erase parallel edges
                int c = PEEK_STACK(conflict_set_clauses, i);
                int l = S->clause_size[c];
                for(int j = 0; j < l; j++) {
                    int lit = S->clause[c][j];
                    int var = abs(lit);
                    int card_id = ey[var];
                    int new_lit = pnsign(lit) * new_vars[var];
                    if(ori_vars[i][hole_id[card_id]] != lit) {
                        //printf("c assume %d %d because of parallel edges\n", lit, new_lit);
                        PUSH_STACK(proof->line, -new_lit);
                        PUSH_STACK(proof->line, -new_lit);
                        PUSH_STACK(proof->line, ph_vars[i][hole_id[card_id]]);
                        print_added_proof_line(proof);
                        for(int k = 0; k < l; k++) {
                            int lit = S->clause[c][k];
                            int new_lit = new_vars[abs(lit)] * pnsign(lit);
                            if(k != j && S->clause[c][k] != 0) {
                                PUSH_STACK(proof->line, new_lit);
                            }else {
                            }
                        }
                        for(int k = 0; k < nh; k++) {
                            if(ori_vars[i][k] == 0 && ph_vars[i][k]) {
                                PUSH_STACK(proof->line, ph_vars[i][k]);
                            }
                        }
                        print_added_proof_line(proof);
                        for(int k = 0; k < l; k++) {
                            int lit = S->clause[c][k];
                            int new_lit = new_vars[abs(lit)] * pnsign(lit);
                            if(S->clause[c][k] != 0) {
                                PUSH_STACK(proof->line, new_lit);
                            }else {
                            }
                        }
                        for(int k = 0; k < nh; k++) {
                            if(ori_vars[i][k] == 0 && ph_vars[i][k]) {
                                PUSH_STACK(proof->line, ph_vars[i][k]);
                            }
                        }
                        print_delete_proof_line(proof);
                        S->clause[c][j] = 0;
                        //printf("c erase parallel edge\n");
                    }
                }
            }
            for( ; nh >= 2; nh--) {//prove ph formula
                for(int i = 0; i < nh; i++) {
                    for(int j = 0; j < nh; j++) {
                        if(j != nh - 1) {//pr
                            PUSH_STACK(proof->line, -ph_vars[nh][j]);
                            PUSH_STACK(proof->line, -ph_vars[i][nh - 1]);
                            PUSH_STACK(proof->line, -ph_vars[nh][j]);
                            PUSH_STACK(proof->line, -ph_vars[i][nh - 1]);
                            PUSH_STACK(proof->line, ph_vars[nh][nh - 1]);
                            PUSH_STACK(proof->line, ph_vars[i][j]);
                            print_added_proof_line(proof);
                        }
                    }
                    PUSH_STACK(proof->line, -ph_vars[i][nh - 1]);
                    print_added_proof_line(proof);
                    for(int j = 0; j < nh - 1; j++) {
                        PUSH_STACK(proof->line, ph_vars[i][j]);
                    }
                    print_added_proof_line(proof);
                }
            }
            S->solved = true;
            free(hole_id);
            for(int i = 0; i < nh + 1; i++) {
                free(ori_vars[i]);
                free(ph_vars[i]);
            }
            free(ori_vars);
            free(ph_vars);
            

        }
    }
    RELEASE_STACK(S->ineq);
    RELEASE_STACK(conflict_set_clauses);
    RELEASE_STACK(conflict_set_cards);
    free(vst);
    free(match);
    free(ey);
    free(sgn);
    free(mark);
    free(baksgn);
    for (int i = 1; i <= S->clauses; i++) {
        free(e[i]);
    }
    free(e);
    S->cards -= delta;
    if (matched == false) {
        printf("c bipartite graph no solution\n");
        return 0;
    }
    return 1;
}

bool check_overflow(LL a, LL b, LL c, LL d) {
    const LL M = 1ll << 60;
    if(a < 0) a = -a;
    if(b < 0) b = -b;
    if(c < 0) c = -c;
    if(d < 0) d = -d;
    if((a > 0 && M / a < b) || (c > 0 && M / c < d)) {
        return true;
    }else {
        return false;
    }
}

int card_elimination(simplify *S)
{
    // sigma aixi <= b
    S->mat = (MatType **)malloc(sizeof(double *) * (S->M_card));
    S->mats = 0;
    S->pbcounter = 0;
    kissat * solver = S->solver;
    proof * proof = solver->proof;
    int *row_size = (int *)malloc(sizeof(int) * (S->M_card));
    //int * tracel traceu
    int * tracel = NULL,  * traceu = NULL,  * proof_line_id = NULL;
    if(proof && !proof->binary) {
        tracel = (int * )malloc(sizeof(int) * (S->M_card));
        traceu = (int * )malloc(sizeof(int) * (S->M_card));
        proof_line_id = (int * )malloc(sizeof(int) * (S->M_card));
        INIT_STACK(S->ineq);
    }
    for (int i = 0; i < S->cards; i++) {
        if (S->cdel[i])
            continue;
        int b = 1;
        row_size[S->mats] = S->card_one_size[i];
        S->mat[S->mats] = (MatType *)malloc(sizeof(MatType) * (S->vars + 1));
        for (int i = 0; i <= S->vars; i++)
            S->mat[S->mats][i] = 0;
        for (int j = 0; j < S->card_one_size[i]; j++) {
            if (S->card_one[i][j] < 0)
                b--;
            S->mat[S->mats][abs(S->card_one[i][j])] += pnsign(S->card_one[i][j]);
        }
        S->mat[S->mats][0] = b;
        if(proof && !proof->binary) {
            generate_amo_proof(S, i); // Note: PB proof requires >=. card_elimination() stores <=.
            proof_line_id[S->mats] = S->pbcounter;
        }
        ++S->mats;
    }
    for (int i = 0; i < S->cards; i++)
        free(S->card_one[i]);
    free(S->card_one);
    free(S->card_one_size);
    free(S->cdel);

    for (int i = 1; i <= S->clauses; i++) {
        if (S->clause_delete[i])
            continue;
        int b = 1;
        for (int j = 0; j < S->clause_size[i]; j++)
            if (S->clause[i][j] < 0)
                b--;
        row_size[S->mats] = S->clause_size[i];
        S->mat[S->mats] = (MatType *)malloc(sizeof(MatType) * (S->vars + 1));
        for (int i = 0; i <= S->vars; i++)
            S->mat[S->mats][i] = 0;
        for (int j = 0; j < S->clause_size[i]; j++) {
            S->mat[S->mats][abs(S->clause[i][j])] += -pnsign(S->clause[i][j]);
        }
        S->mat[S->mats][0] = -b;
        if(proof && !proof->binary) {
            for(int j = 0; j < S->clause_size[i]; j++) {
                int lit = S->clause[i][j];
                PUSH_STACK(S->ineq, lit);
                PUSH_STACK(S->ineq, 1);
            }
            print_inequality(S, GE, 1);
            proof_line_id[S->mats] = ++S->pbcounter;
        }
        ++S->mats;
    }


    int *low = (int *)malloc(sizeof(int) * (S->M_card));
    int *upp = (int *)malloc(sizeof(int) * (S->M_card));
    int *mat_del = (int *)malloc(sizeof(int) * (S->M_card));


    int *var_score1 = (int *)malloc(sizeof(int) * (S->vars + 1));
    int *var_score2 = (int *)malloc(sizeof(int) * (S->vars + 1));
    int *elim = (int *)malloc(sizeof(int) * (S->vars + 1));

    for (int i = 0; i < S->mats; i++)
        mat_del[i] = 0;
    for (int v = 1; v <= S->vars; v++) {
        var_score1[v] = var_score2[v] = elim[v] = 0;
        int lows = 0, upps = 0;
        for (int i = 0; i < S->mats; i++) {
            if (fabs(S->mat[i][v]) < 1e-6)
                continue;
            
            if (S->mat[i][v] > 0)
                upp[upps++] = i;
            else
                low[lows++] = i;
        }
        var_score1[v] = upps * lows;
        for (int i = 0; i < upps; i++)
            for (int j = 0; j < lows; j++)
                var_score2[v] += row_size[upp[i]] * row_size[low[j]];
    }
    for (int turn = 1; turn <= S->vars; turn++) {
        int v = 0;
        for (int i = 1; i <= S->vars; i++) {
            if (elim[i])
                continue;
            if (!v)
                v = i;
            else {
                if (var_score1[i] < var_score1[v])
                    v = i;
                else if (var_score1[i] == var_score1[v] && var_score2[i] < var_score2[v])
                    v = i;
            }
        }
        elim[v] = 1;
        int lows = 0, upps = 0;
        for (int i = 0; i < S->mats; i++) {
            if (mat_del[i])
                continue;
            if (fabs(S->mat[i][v]) < 1e-6)
                continue;
            
            mat_del[i] = 1;
            if (S->mat[i][v] > 0) {
                upp[upps++] = i;
            } else {
                low[lows++] = i;
            }
        }
        if (S->mats + upps * lows >= S->M_card || S->mats > 1e3)
            break;
        for (int iu = 0; iu < upps; iu++) {
            int u = upp[iu];
            for (int il = 0; il < lows; il++) {
                int l = low[il];
                mat_del[S->mats] = 0;
                S->mat[S->mats] = (MatType *)malloc(sizeof(MatType) * (S->vars + 1));
                for (int i = 0; i <= S->vars; i++)
                    S->mat[S->mats][i] = 0;
                //check overflow.
                for (int j = 0; j <= S->vars; j++) {
                    /*if(check_overflow(S->mat[u][j], (-S->mat[l][v]), S->mat[l][j], S->mat[u][v])) {
                        overflow = true;
                        break;
                    }*/
                    S->mat[S->mats][j] = S->mat[u][j] / S->mat[u][v] + S->mat[l][j] / -S->mat[l][v] ;
                }
                /*if(overflow) {
                    break;
                }*/
                ++S->mats;
                print_card(S, S->mats - 1);

                int check_res = check_card(S, S->mats - 1);
                if (check_res == 0) {
                    if(proof && !proof->binary) {
                        free(tracel);
                        free(traceu);
                        RELEASE_STACK(S->ineq);
                    }
                    free(row_size);
                    free(mat_del);
                    free(low);
                    free(upp);
                    free(var_score1);
                    free(var_score2);
                    free(elim);
                    return 0;
                }
                if (check_res == -1) {
                    free(S->mat[S->mats - 1]);
                    S->mats--;
                }
            }
        }
        //if(overflow) break;
    }
    if(proof && !proof->binary) {
        free(tracel);
        free(traceu);
        RELEASE_STACK(S->ineq);
    }
    free(row_size);
    free(mat_del);
    free(low);
    free(upp);
    free(var_score1);
    free(var_score2);
    free(elim);

    return 1;
}

int simplify_bip(simplify *S)
{
    S->M_card = (int)(2e7 / S->vars);
    if(S->M_card <= 10000) S->M_card = 10000;
    S->card_one = (int **)malloc(sizeof(int *) * (S->M_card));
    S->card_one_size = (int *)malloc(sizeof(int) * (S->M_card));
    S->cdel = (int *)malloc(sizeof(int) * (S->M_card));
    int sone = search_almost_one(S);
    if (!sone) {
        for (int i = 0; i < S->cards; i++)
            free(S->card_one[i]);
        free(S->card_one);
        free(S->card_one_size);
        free(S->cdel);
        return 1;
    }
    /*int scc = scc_almost_one(S);
    //printf("scc = %d\n", scc);
    if (!scc) {
        for (int i = 0; i < S->cards; i++)
            free(S->card_one[i]);
        free(S->card_one);
        free(S->card_one_size);
        free(S->cdel);
        return 1;
    }*/
    //printf("c start bipartite check\n");
    int bip = bipartite_check(S);
    
    if (bip == 0) {
        for (int i = 0; i < S->cards; i++)
            free(S->card_one[i]);
        free(S->card_one);
        free(S->card_one_size);
        free(S->cdel);
        return 0;
    }
    return 1;
}

int simplify_card(simplify *S)
{
    S->M_card = 2e7 / S->vars;
    S->card_one = (int **)malloc(sizeof(int *) * (S->M_card));
    S->card_one_size = (int *)malloc(sizeof(int) * (S->M_card));
    S->cdel = (int *)malloc(sizeof(int) * (S->M_card));
    int sone = search_almost_one(S);
    if (!sone) {
        for (int i = 0; i < S->cards; i++)
            free(S->card_one[i]);
        free(S->card_one);
        free(S->card_one_size);
        free(S->cdel);
        return 1;
    }
    int scc = scc_almost_one(S);
    if (!scc) {
        for (int i = 0; i < S->cards; i++)
            free(S->card_one[i]);
        free(S->card_one);
        free(S->card_one_size);
        free(S->cdel);
        return 1;
    }
    

    int sz = S->cards;
    for (int i = 1; i <= S->clauses; i++)
        if (!S->clause_delete[i])
            ++sz;
    if (sz >= S->M_card || sz > 1e3) {
        for (int i = 0; i < S->cards; i++)
            free(S->card_one[i]);
        free(S->card_one);
        free(S->card_one_size);
        free(S->cdel);
        return 1;
    }

    printf("c start card elimination\n");
    int res = card_elimination(S);
    for (int i = 0; i < S->mats; i++)
        free(S->mat[i]);
    free(S->mat);
    return res;
}

struct PDI {
    double d;
    int i;
};
typedef struct PDI PDI;
static inline bool cmpPDI(const PDI a, const PDI b) {
    return a.d < b.d;
}

bool kissat_simplify(kissat *solver, int *maxvar, file *file)
{
    S = simplify_init();
    S->solver = solver;
    uint64_t lineno_ptr;
    simplify_parse(S, file, &lineno_ptr);
    printf("c after parse time = %lf, var = %d, clauses = %d\n", kissat_process_time(), S->vars, S->clauses);
    int min_len = 1e9, max_len = 0;
    long long tot_len = 0;
    for (int i = 1; i <= S->clauses; i++) {
        int len = S->clause_size[i];
        if (len < min_len)
            min_len = len;
        if (len > max_len)
            max_len = len;
        tot_len += len;
    }

    solver->walk_strategy = GET_OPTION(walkstrategy);
    printf("c walk strategy = %d\n", solver->walk_strategy);
    if(solver->walk_strategy == 3) {
        solver->walk_strategy = select_walking_strategy_unweighted(S->vars, S->clauses, (double)S->clauses / S->vars,
        (double)tot_len / S->clauses, min_len, max_len);
    }
    printf("c chosen walk strategy = %d\n", solver->walk_strategy);
    proof *proof = solver->proof;
    if (proof && !proof->binary) {
        kissat_puts(proof->file, "f ");
        kissat_putint(proof->file, S->clauses);
        kissat_putc(proof->file, '\n');
    }
    solver->mapidx = (int *)malloc(sizeof(int) * (S->orivars + 1));
    for (int i = 1; i <= S->orivars; i++) {
        solver->mapidx[i] = i;
    }
    S->solved = false;
    if (S->vars <= 1e6 && S->clauses <= 4e7) {
        int res = simplify_bip(S);
        if (res == false && proof && proof->binary == true && S->solved == false) {//bipartite graph no solution but we can't find a PR proof
            solver->PSIDS = true;
            res = true;
        }
        if (!res) {
            simplify_release(S);
            free(S->mapto);
            free(S->mapval);
            free(S);
            RELEASE_STACK(S->units);
            return false;
        }
    }
    //printf("c after bip %lf\n", kissat_process_time());
    S->newVars = S->orivars;
    int res = simplify_easy_clause(S);


    for (int i = 1; i <= S->vars; i++) {
        if (S->mapto[i]) {
            solver->mapidx[S->mapto[i]] = i;
        }
    }
    if (!res) {
        simplify_release(S);
        free(S->mapto);
        free(S->mapval);
        free(S);
        return false;
    }

    INIT_STACK(S->new_clause_literals);
    S->newVars = S->vars;
    //printf("%d %d %d\n", solver->unsat_but_no_proof, proof, proof ? proof->binary : 0);
    S->symmetry_synonyms = (int * )malloc(sizeof(int) * (S->vars + 1));
    for(int i = 1; i <= S->vars; i++) {
            S->symmetry_synonyms[i] = i;
    }
    printf("c option: detect symmetry %d\n", GET_OPTION(symmetry));
    if (GET_OPTION(symmetry) && S->solved == false && (proof == NULL || proof->binary == false || proof->binary == true)) {//get decision tree without partial symmetry breaking
        kissat_detect_symmetry(S);//actually we break symmetry in all cases...
        
    }
	int new_clauses = 0;
    for (unsigned i = 0; i < SIZE_STACK(S->new_clause_literals); i++) {
        int lit = PEEK_STACK(S->new_clause_literals, i);        
        if(lit) {
        }else {
            new_clauses++;
        }
    }
    if(new_clauses > 0) {
        printf("c %d new clauses\n", new_clauses);
        S->clause = realloc(S->clause, sizeof(int *) * (S->clauses + new_clauses + 1));
        S->clause_size = realloc(S->clause_size, sizeof(int) * (S->clauses + new_clauses + 1));
        int p = S->clauses;
        for (unsigned i = 0, j; i < SIZE_STACK(S->new_clause_literals); i = j + 1) {
            for(j = i; j < SIZE_STACK(S->new_clause_literals) && PEEK_STACK(S->new_clause_literals, j) != 0; j++);

            p++;
            S->clause[p] = malloc((j - i) * sizeof(int));
            for(size_t k = i; k < j; k++) {
                S->clause[p][k - i] = PEEK_STACK(S->new_clause_literals, k);
            }
            S->clause_size[p] = j - i;
        }
        S->clause_delete = realloc(S->clause_delete, sizeof(int) * (p + 1));
        S->clauses = p;
        solver->mapidx = (int*)realloc(solver->mapidx, sizeof(int) * (S->newVars + 1));
        
        simplify_realloc(S, S->newVars);
        for(int i = S->orivars + 1; i <= S->newVars; i++) {
            solver->mapidx[i] = i;
            S->mapto[i] = i;
            S->mapfrom[i] = i;
        }
		int res = simplify_easy_clause(S);

		for (int i = 1; i <= S->newVars; i++) {
			if (S->mapto[i]) {
				solver->mapidx[S->mapto[i]] = i;
			}
		}
		if (!res) {
			simplify_release(S);
			free(S->mapto);
			free(S->mapval);
			free(S);
			return false;
		}

	}

	printf("c after sym time = %lf, var = %d, clauses = %d, new literals = %zu\n", kissat_process_time(), S->vars, S->clauses, SIZE_STACK(S->new_clause_literals));

	//printf("c after easy %lf\n", kissat_process_time());
	//return false;
    
	solver->PSIDS = false;
	if (S->vars <= 1e6 && S->clauses <= 4e7) {
		if (true) {
			int res = simplify_card(S);

			//res = true;
			if (res == false && proof && proof->binary == true) {
				printf("c solved (UNSAT) by card elim. But cannot prove by PR/RAT/RUP");
				solver->PSIDS = true;
				res = true;
			}
			if (!res) {
				simplify_release(S);
				free(S->mapto);
				free(S->mapval);
				free(S);
				RELEASE_STACK(S->units);
				return false;
			} else {
				/* for(unsigned i = 0; i < SIZE_STACK(S->units); i++) {
				   int x = PEEK_STACK(S->units, i);
				   if(x == 0) {
				   free(S->mapto);
				   free(S->mapval);
				   free(S);
				   RELEASE_STACK(S->units);
				   return false;
				   }
				   } */
				if ((proof == NULL || proof->binary == false) && SIZE_STACK(S->units) + S->clauses <= (int)MAX_CLAUSES) { // if no proof required,
					// enable.
					//printf("SIZE_STACK = %lu\n", SIZE_STACK(S->units));
					S->clause = realloc(S->clause, sizeof(int *) * (S->clauses + SIZE_STACK(S->units) + 1));
					S->clause_size = realloc(S->clause_size, sizeof(int) * (S->clauses + SIZE_STACK(S->units) + 1));
					for (unsigned i = S->clauses + 1; i <= S->clauses + SIZE_STACK(S->units); i++) {
						S->clause[i] = malloc(sizeof(int));
						S->clause[i][0] = PEEK_STACK(S->units, i - S->clauses - 1);
						//if(S->clause[i][0] == 0) printf("!!!%d\n", i);
						S->clause_size[i] = 1;
						if(proof && !proof->binary) {
							print_unit(S, PEEK_STACK(S->units, i - S->clauses - 1));
						}
					}
					S->clause_delete = realloc(S->clause_delete, sizeof(int) * (S->clauses + SIZE_STACK(S->units) + 1));
					S->clauses += SIZE_STACK(S->units);
				} else {
				}
			}
		}
	}
	//printf("size of units : %d %d\n", SIZE_STACK(S->units), S->vars);
	//printf("c after card %lf\n", kissat_process_time());

	res = simplify_resolution(S);
	printf("c after reso time = %lf, var = %d, clauses = %d\n", kissat_process_time(), S->vars, S->clauses);
	if (!res) { // this never happens...
		simplify_release(S);
		free(S->mapto);
		free(S->mapval);
		free(S->res_clause_size);
		for (int i = 1; i <= S->res_clauses; i++)
			free(S->res_clause[i]);
		free(S->res_clause);
		free(S->resolution);
		free(S);
		RELEASE_STACK(S->units);
		return false;
	}

	// printf("c simplify resolution completed, current vars: %d, clauses: %d\n", S->vars, S->clauses);
	// printf("mapto[%d] = %d\n", 5826, S->mapto[5826]);

	solver->mapidx = (int *)realloc(solver->mapidx, sizeof(int) * (S->vars + 1));
	for (int i = 1; i <= S->vars; i++)
		solver->mapidx[i] = 0;
	for (int i = 1; i <= S->newVars; i++) {
		if (S->mapto[i]) {
			solver->mapidx[S->mapto[i]] = i;
		}
	}


	*maxvar = S->vars;
	kissat_reserve(solver, S->vars);

	/*PDI * pos = (PDI * ) malloc(sizeof(PDI) * (S->clauses + 1));
	  for(int i = 1; i <= S->clauses; i++) {
	  double s = 0;

	  for(int j = 0; j < S->clause_size[i]; j++) {
	  s += abs(S->clause[i][j]);
	  }
	  pos[i].d = s / S->clause_size[i];
	  pos[i].i = i;
	  }*/
	//SORT(PDI, S->clauses, pos + 1, cmpPDI);
	//double * score = calloc(S->vars + 1, sizeof(double));
	for (int i = 1; i <= S->clauses; i++) {
		int v = i;
		for (int j = 0; j < S->clause_size[v]; j++) {
			//score[abs(S->clause[v][j])] += pnsign(S->clause[v][j]) / (double)S->clause_size[v];
			kissat_add(solver, S->clause[v][j]);
			if (proof != NULL) {
				int var = solver->mapidx[abs(S->clause[v][j])];
				var = var * pnsign(S->clause[v][j]);
				//PUSH_STACK(proof->line, var);
				proof->literals += 1;
			}
		}
		//if (proof != NULL)
		//    print_added_proof_line(proof);
		kissat_add(solver, 0);
	}
	/*for(int i = 1; i <= S->vars; i++) {
	  unsigned ilit = kissat_import_literal(solver, i);
	  unsigned var = IDX(ilit);
	  solver->phases[var].greedy = pnsign(score[i]);
	  }
	  free(score);*/
	//printf("c found %d units by simplify\n", SIZE_STACK(S->units));

	//return false;

	for (unsigned i = 0; i < SIZE_STACK(S->units); i++) {
		if(PEEK_STACK(S->units, i) == 0) {
			continue;
		}
		unsigned ilit = kissat_import_literal(solver, PEEK_STACK(S->units, i));
		solver->simplified_hints[IDX(ilit)] = pnsign(PEEK_STACK(S->units, i));
		//printf("[%d %d]", IDX(ilit), PEEK_STACK(S->units, i));
	}
	INIT_STACK(solver->clauses);
	if(GET_OPTION(pr) && S->clauses <= 10000) {
		for (int i = 1; i <= S->clauses; i++) {
			for (int j = 0; j < S->clause_size[i]; j++) {
				unsigned vj = IDX(kissat_import_literal(solver, S->clause[i][j]));
				for(int k = 0; k < S->clause_size[i]; k++) {
					unsigned vk = IDX(kissat_import_literal(solver, S->clause[i][k]));
					if(vj != vk) {
						PUSH_STACK(solver->touched_list[vj], vk);
					}
				}
			}
			unsigneds c;
			INIT_STACK(c);
			for(int j = 0; j < S->clause_size[i]; j++) {
				PUSH_STACK(c, kissat_import_literal(solver, S->clause[i][j]));
			}
			PUSH_STACK(solver->clauses, c);
		}
	}
	//printf("\n");
	//exit(0);
	printf("c after preprocess %lf, number of unit hints : %lu %u\n", kissat_process_time(), SIZE_STACK(S->units), S->vars);
	RELEASE_STACK(S->new_clause_literals);
	simplify_release(S);
	solver->S = S;
	return true;
}

static void flush_buffer(chars *buffer)
{
	fputs("v", stdout);
	for (all_stack(char, ch, *buffer))
		fputc(ch, stdout);
	fputc('\n', stdout);
	CLEAR_STACK(*buffer);
}

static void print_int(kissat *solver, chars *buffer, int i)
{
	char tmp[16];
	sprintf(tmp, " %d", i);
	size_t tmp_len = strlen(tmp);
	size_t buf_len = SIZE_STACK(*buffer);
	if (buf_len + tmp_len > 77)
		flush_buffer(buffer);
	for (const char *p = tmp; *p; p++)
		PUSH_STACK(*buffer, *p);
}

void kissat_complete_val(kissat *solver)
{
	int r = 0;
	for (int i = 1; i <= S->newVars; i++) {
		if (S->mapto[i])
			S->mapval[i] = pnsign(S->mapto[i]) * solver->last_val[abs(S->mapto[i])];
		else {
			if (!S->mapval[i])
				puts("c wrong empty val");
			else if (abs(S->mapval[i]) != 1)
				S->mapval[i] = 0, ++r;
		}
	}
	if (r != S->resolutions)
		puts("c wrong reso num");
	if (r) {
		S->occurp = (int **)malloc(sizeof(int *) * (S->/*orivars*/newVars + 1));
		S->occurn = (int **)malloc(sizeof(int *) * (S->/*orivars*/newVars + 1));
		S->occurp_size = (int *)malloc(sizeof(int) * (S->/*orivars*/newVars + 1));
		S->occurn_size = (int *)malloc(sizeof(int) * (S->/*orivars*/newVars + 1));
		for (int i = 1; i <= S->/*orivars*/newVars; i++) {
			S->occurp_size[i] = S->occurn_size[i] = 0;
			S->occurp[i] = S->occurn[i] = NULL;
		}
		for (int i = 1; i <= S->res_clauses; i++) {
			for (int j = 0; j < S->res_clause_size[i]; j++) {
				int v = S->res_clause[i][j];
				if (v > 0)
					S->occurp_size[v]++;
				else
					S->occurn_size[-v]++;
			}
		}
		for (int i = 1; i <= S->newVars; i++) {
			if (S->occurp_size[i])
				S->occurp[i] = (int *)malloc(sizeof(int) * (S->occurp_size[i]));
			if (S->occurn_size[i])
				S->occurn[i] = (int *)malloc(sizeof(int) * (S->occurn_size[i]));
			S->occurp_size[i] = S->occurn_size[i] = 0;
		}
		S->clause_state = (int *)malloc(sizeof(int) * (S->res_clauses + 1));
		for (int i = 1; i <= S->res_clauses; i++) {
			S->clause_state[i] = 0;
			int satisify = 0;
			for (int j = 0; j < S->res_clause_size[i]; j++) {
				int v = S->res_clause[i][j];
				if (abs(v) > S->orivars || v == 0) {
					//puts("c resolved non original variable");
				}
				if (v > 0)
					S->occurp[v][S->occurp_size[v]++] = i;
				else
					S->occurn[-v][S->occurn_size[-v]++] = i;
				if (pnsign(v) * S->mapval[abs(v)] == 1)
					satisify = 1;
				if (!S->mapval[abs(v)])
					++S->clause_state[i];
			}
			if (satisify)
				S->clause_state[i] = -1;
			if (!S->clause_state)
				puts("c wrong unsat clause");
		}
		for (int ii = S->resolutions; ii >= 1; ii--) {
			int v = S->resolution[ii];
			if (v > S->orivars || v <= 0) {
				//puts("c resolved non original variable");
			}
			// attempt 1
			int assign = 1;
			for (int i = 0; i < S->occurn_size[v]; i++) {
				int o = S->occurn[v][i];
				if (S->clause_state[o] != -1 && S->clause_state[o] <= 1) {
					assign = 0;
					break;
				}
			}
			if (assign == 1) {
				S->mapval[v] = 1;
				for (int i = 0; i < S->occurn_size[v]; i++) {
					int o = S->occurn[v][i];
					if (S->clause_state[o] != -1)
						S->clause_state[o]--;
				}
				for (int i = 0; i < S->occurp_size[v]; i++)
					S->clause_state[S->occurp[v][i]] = -1;
				continue;
			}
			// attempt -1
			assign = -1;
			for (int i = 0; i < S->occurp_size[v]; i++) {
				int o = S->occurp[v][i];
				if (S->clause_state[o] != -1 && S->clause_state[o] <= 1) {
					assign = 0;
					break;
				}
			}
			if (assign == -1) {
				S->mapval[v] = -1;
				for (int i = 0; i < S->occurp_size[v]; i++) {
					int o = S->occurp[v][i];
					if (S->clause_state[o] != -1)
						S->clause_state[o]--;
				}
				for (int i = 0; i < S->occurn_size[v]; i++)
					S->clause_state[S->occurn[v][i]] = -1;
				continue;
			}
			printf("c wrong assign");
		}
		free(S->clause_state);
		for (int i = 1; i <= S->/*orivars*/newVars; i++) {
			if (S->occurn[i] != NULL)
				free(S->occurn[i]);
			if (S->occurp[i] != NULL)
				free(S->occurp[i]);
		}
		free(S->occurn_size);
		free(S->occurp_size);
		free(S->occurn);
		free(S->occurp);

		free(S->res_clause_size);
		for (int i = 1; i <= S->res_clauses; i++)
			free(S->res_clause[i]);
		free(S->res_clause);
		free(S->resolution);
	}

	chars buffer;
	INIT_STACK(buffer);
	for (int i = 1; i <= S->orivars; i++) {
		print_int(solver, &buffer, i * S->mapval[i]);
	}
	print_int(solver, &buffer, 0);
	assert(!EMPTY_STACK(buffer));
	flush_buffer(&buffer);
	RELEASE_STACK(buffer);
	free(S->mapto);
	free(S->mapval);
	free(S->symmetry_synonyms);
}
int select_walking_strategy_weighted(int vars, int clauses, double ratio, double avg_len, int min_len, int max_len)
{
	min_len;
	if (ratio <= 3.994418978691101) {
		if (max_len <= 68983.5) {
			if (vars <= 77118.0) {
				return 2;
			} else {  // if vars > 77118.0
				if (avg_len <= 2.7391685247421265) {
					if (ratio <= 3.457582473754883) {
						return 0;
					} else {  // if ratio > 3.457582473754883
						return 0;
					}
				} else {  // if avg_len > 2.7391685247421265
					return 1;
				}
			}
		} else {  // if max_len > 68983.5
			return 2;
		}
	} else {  // if ratio > 3.994418978691101
		if (ratio <= 5.100248575210571) {
			if (max_len <= 32990.0) {
				if (max_len <= 25405.5) {
					if (max_len <= 9924.0) {
						if (ratio <= 5.037616968154907) {
							if (avg_len <= 2.8895225524902344) {
								if (vars <= 2412327.5) {
									return 0;
								} else {  // if vars > 2412327.5
									return 2;
								}
							} else {  // if avg_len > 2.8895225524902344
								if (ratio <= 4.939579963684082) {
									return 0;
								} else {  // if ratio > 4.939579963684082
									return 0;
								}
							}
						} else {  // if ratio > 5.037616968154907
							return 2;
						}
					} else {  // if max_len > 9924.0
						if (vars <= 5271403.0) {
							return 0;
						} else {  // if vars > 5271403.0
							if (avg_len <= 2.9653334617614746) {
								return 1;
							} else {  // if avg_len > 2.9653334617614746
								return 0;
							}
						}
					}
				} else {  // if max_len > 25405.5
					return 2;
				}
			} else {  // if max_len > 32990.0
				return 0;
			}
		} else {  // if ratio > 5.100248575210571
			if (max_len <= 64716.5) {
				if (ratio <= 16.65182590484619) {
					if (avg_len <= 2.88206148147583) {
						if (max_len <= 9024.0) {
							return 1;
						} else {  // if max_len > 9024.0
							return 1;
						}
					} else {  // if avg_len > 2.88206148147583
						if (max_len <= 33915.0) {
							if (ratio <= 12.353093147277832) {
								if (ratio <= 5.455706357955933) {
									if (vars <= 6774013.5) {
										if (max_len <= 11424.0) {
											return 1;
										} else {  // if max_len > 11424.0
											return 1;
										}
									} else {  // if vars > 6774013.5
										return 2;
									}
								} else {  // if ratio > 5.455706357955933
									if (vars <= 2721138.0) {
										if (vars <= 1998254.0) {
											if (ratio <= 10.131261825561523) {
												return 0;
											} else {  // if ratio > 10.131261825561523
												return 1;
											}
										} else {  // if vars > 1998254.0
											if (vars <= 2051170.0) {
												return 2;
											} else {  // if vars > 2051170.0
												return 2;
											}
										}
									} else {  // if vars > 2721138.0
										return 0;
									}
								}
							} else {  // if ratio > 12.353093147277832
								if (ratio <= 16.349488258361816) {
									return 1;
								} else {  // if ratio > 16.349488258361816
									return 1;
								}
							}
						} else {  // if max_len > 33915.0
							return 0;
						}
					}
				} else {  // if ratio > 16.65182590484619
					if (max_len <= 6495.0) {
						if (clauses <= 13894788.0) {
							return 0;
						} else {  // if clauses > 13894788.0
							return 0;
						}
					} else {  // if max_len > 6495.0
						return 2;
					}
				}
			} else {  // if max_len > 64716.5
				return 2;
			}
		}
	}
}
int select_walking_strategy_unweighted(int vars, int clauses, double ratio, double avg_len, int min_len, int max_len)
{
	if (ratio <= 40.96073341369629) {
		if (ratio <= 6.315191030502319) {
			if (ratio <= 5.626317501068115) {
				if (vars <= 3837.0) {
					if (ratio <= 3.444085955619812) {
						return 0;
					} else { // if ratio > 3.444085955619812
						if (avg_len <= 3.695209503173828) {
							if (ratio <= 4.337011098861694) {
								if (max_len <= 9.0) {
									if (ratio <= 3.8763744831085205) {
										if (max_len <= 5.5) {
											if (avg_len <= 2.712442994117737) {
												return 0;
											} else { // if avg_len > 2.712442994117737
												if (ratio <= 3.5157430171966553) {
													return 2;
												} else { // if ratio > 3.5157430171966553
													return 2;
												}
											}
										} else { // if max_len > 5.5
											return 1;
										}
									} else { // if ratio > 3.8763744831085205
										return 2;
									}
								} else { // if max_len > 9.0
									return 0;
								}
							} else { // if ratio > 4.337011098861694
								return 0;
							}
						} else { // if avg_len > 3.695209503173828
							return 0;
						}
					}
				} else { // if vars > 3837.0
					if (ratio <= 1.2001570165157318) {
						return 0;
					} else { // if ratio > 1.2001570165157318
						if (vars <= 4344.5) {
							return 0;
						} else { // if vars > 4344.5
							if (avg_len <= 2.9941145181655884) {
								if (ratio <= 3.005972981452942) {
									if (vars <= 190541.5) {
										if (avg_len <= 2.3131449222564697) {
											return 2;
										} else { // if avg_len > 2.3131449222564697
											if (clauses <= 174635.5) {
												if (avg_len <= 2.3333219289779663) {
													return 1;
												} else { // if avg_len > 2.3333219289779663
													return 0;
												}
											} else { // if clauses > 174635.5
												return 1;
											}
										}
									} else { // if vars > 190541.5
										if (avg_len <= 2.3333334922790527) {
											return 0;
										} else { // if avg_len > 2.3333334922790527
											return 2;
										}
									}
								} else { // if ratio > 3.005972981452942
									if (vars <= 6341.5) {
										return 2;
									} else { // if vars > 6341.5
										if (max_len <= 46.0) {
											if (max_len <= 35.5) {
												if (avg_len <= 2.878322958946228) {
													if (ratio <= 3.0467259883880615) {
														return 0;
													} else { // if ratio > 3.0467259883880615
														if (avg_len <= 2.7818615436553955) {
															if (avg_len <= 2.4128350019454956) {
																return 1;
															} else { // if avg_len > 2.4128350019454956
																if (clauses <= 46111.5) {
																	return 1;
																} else { // if clauses > 46111.5
																	if (ratio <= 3.1715710163116455) {
																		return 1;
																	} else { // if ratio > 3.1715710163116455
																		if (min_len <= 1.5) {
																			if (vars <= 12839.5) {
																				return 2;
																			} else { // if vars > 12839.5
																				if (clauses <= 253969.5) {
																					return 0;
																				} else { // if clauses > 253969.5
																					return 0;
																				}
																			}
																		} else { // if min_len > 1.5
																			return 2;
																		}
																	}
																}
															}
														} else { // if avg_len > 2.7818615436553955
															return 2;
														}
													}
												} else { // if avg_len > 2.878322958946228
													return 0;
												}
											} else { // if max_len > 35.5
												return 0;
											}
										} else { // if max_len > 46.0
											if (avg_len <= 2.963694930076599) {
												if (max_len <= 21212.5) {
													if (ratio <= 4.192485570907593) {
														return 0;
													} else { // if ratio > 4.192485570907593
														if (ratio <= 4.743157863616943) {
															return 1;
														} else { // if ratio > 4.743157863616943
															return 0;
														}
													}
												} else { // if max_len > 21212.5
													return 0;
												}
											} else { // if avg_len > 2.963694930076599
												return 0;
											}
										}
									}
								}
							} else { // if avg_len > 2.9941145181655884
								if (vars <= 379620.5) {
									if (avg_len <= 2.9963390827178955) {
										return 1;
									} else { // if avg_len > 2.9963390827178955
										if (clauses <= 42532.5) {
											return 0;
										} else { // if clauses > 42532.5
											if (clauses <= 227371.0) {
												if (ratio <= 4.6170244216918945) {
													return 0;
												} else { // if ratio > 4.6170244216918945
													return 1;
												}
											} else { // if clauses > 227371.0
												return 0;
											}
										}
									}
								} else { // if vars > 379620.5
									if (ratio <= 3.4725250005722046) {
										return 2;
									} else { // if ratio > 3.4725250005722046
										if (avg_len <= 3.7048420906066895) {
											return 1;
										} else { // if avg_len > 3.7048420906066895
											return 1;
										}
									}
								}
							}
						}
					}
				}
			} else { // if ratio > 5.626317501068115
				if (avg_len <= 2.7998855113983154) {
					return 0;
				} else { // if avg_len > 2.7998855113983154
					if (max_len <= 609.0) {
						if (vars <= 866.5) {
							return 0;
						} else { // if vars > 866.5
							return 0;
						}
					} else { // if max_len > 609.0
						return 2;
					}
				}
			}
		} else { // if ratio > 6.315191030502319
			if (vars <= 4770.5) {
				if (vars <= 1127.0) {
					if (ratio <= 30.866000175476074) {
						if (vars <= 736.5) {
							return 0;
						} else { // if vars > 736.5
							return 1;
						}
					} else { // if ratio > 30.866000175476074
						return 1;
					}
				} else { // if vars > 1127.0
					if (ratio <= 14.72365665435791) {
						return 2;
					} else { // if ratio > 14.72365665435791
						return 0;
					}
				}
			} else { // if vars > 4770.5
				if (avg_len <= 2.8921024799346924) {
					if (ratio <= 6.624927997589111) {
						return 2;
					} else { // if ratio > 6.624927997589111
						if (avg_len <= 2.8822264671325684) {
							if (avg_len <= 2.39153254032135) {
								return 0;
							} else { // if avg_len > 2.39153254032135
								return 1;
							}
						} else { // if avg_len > 2.8822264671325684
							return 0;
						}
					}
				} else { // if avg_len > 2.8921024799346924
					if (vars <= 579343.0) {
						if (ratio <= 8.652268886566162) {
							return 1;
						} else { // if ratio > 8.652268886566162
							if (avg_len <= 6.559267997741699) {
								if (ratio <= 17.723286628723145) {
									if (vars <= 20646.5) {
										return 2;
									} else { // if vars > 20646.5
										return 1;
									}
								} else { // if ratio > 17.723286628723145
									return 2;
								}
							} else { // if avg_len > 6.559267997741699
								return 1;
							}
						}
					} else { // if vars > 579343.0
						return 0;
					}
				}
			}
		}
	} else { // if ratio > 40.96073341369629
		if (max_len <= 42.0) {
			if (max_len <= 4.5) {
				return 0;
			} else { // if max_len > 4.5
				if (vars <= 47.0) {
					return 2;
				} else { // if vars > 47.0
					if (vars <= 50089.0) {
						if (vars <= 7048.5) {
							if (avg_len <= 2.007456421852112) {
								return 1;
							} else { // if avg_len > 2.007456421852112
								if (min_len <= 5.0) {
									if (ratio <= 17369.4140625) {
										if (vars <= 53.0) {
											return 0;
										} else { // if vars > 53.0
											if (clauses <= 49774.5) {
												return 0;
											} else { // if clauses > 49774.5
												if (avg_len <= 30.990617752075195) {
													return 0;
												} else { // if avg_len > 30.990617752075195
													return 0;
												}
											}
										}
									} else { // if ratio > 17369.4140625
										return 0;
									}
								} else { // if min_len > 5.0
									return 2;
								}
							}
						} else { // if vars > 7048.5
							return 0;
						}
					} else { // if vars > 50089.0
						return 0;
					}
				}
			}
		} else { // if max_len > 42.0
			if (avg_len <= 2.9975420236587524) {
				if (clauses <= 10485097.5) {
					return 1;
				} else { // if clauses > 10485097.5
					return 2;
				}
			} else { // if avg_len > 2.9975420236587524
				return 0;
			}
		}
	}
}
