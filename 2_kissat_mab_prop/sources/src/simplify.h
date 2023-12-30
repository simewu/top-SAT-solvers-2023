#ifndef _simplify_h_INCLUDED
#define _simplify_h_INCLUDED
#include <stdbool.h>
#include "file.h"
#include "cvec.h"
#include "internal.h"
#include <stdarg.h>
typedef struct simplify simplify;
typedef long long LL;
typedef double MatType;
struct simplify {
    bool solved;
    int vars;
    int clauses;
    int orivars;
    int oriclauses;
    int real_clauses;
    int **clause;
    int *clause_size;
    int res_clauses;
    int **res_clause;
    int *res_clause_size;
    int *resolution;
    int resolutions;
    int *clause_state;
    int *clause_delete;
    int *seen;
    int **occurp;
    int **occurn;
    int *occurp_size;
    int *occurn_size;
    int *clean;
    int *color;
    int *queue;
    int *varval;
    int *resseen;
    int *mapto;
    int *mapfrom;
    int *mapval;
    int cards;
    int **card_one;
    int *card_one_size;
    MatType **mat;
    int mats;
    int *cdel;
    int M_card;
    ints units;
    cvec *store_clause;
    kissat *solver;
    int *order_generated;
    int *sym_visit;
    int newVars;
    ints new_clause_literals;
    intss perms;
    longlongs ineq;
    int pbcounter;
    int * symmetry_synonyms;
    // int new_clauses;
    int * buf;
    int buf_siz;
	int buf_len;
	long long proof_len;
};


struct kissat;

bool kissat_simplify(struct kissat *solver, int *maxvar, file *file);
void kissat_complete_val(struct kissat *solver);

int select_walking_strategy_weighted(int , int , double , double , int , int );
int select_walking_strategy_unweighted(int , int , double , double , int , int );

void add_lits(simplify * S, proof * proof, int count, ...);
void add_lits_tmp(simplify * S, proof * proof, int count, ...);
void del_lits(simplify * S, proof * proof, int count, ...);

#endif
