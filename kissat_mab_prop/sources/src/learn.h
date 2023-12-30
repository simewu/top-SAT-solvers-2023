#ifndef _learn_h_INCLUDED
#define _learn_h_INCLUDED

struct kissat;

void kissat_learn_clause(struct kissat *);
int kissat_learn_pr(struct kissat *);

#endif
