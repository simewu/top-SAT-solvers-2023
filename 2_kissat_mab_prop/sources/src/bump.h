#ifndef _bump_h_INCLUDED
#define _bump_h_INCLUDED

struct kissat;

void kissat_bump_variables(struct kissat *);
void kissat_bump_chb(struct kissat *, unsigned idx, double multiplier);
void kissat_decay_chb(struct kissat *);
void kissat_update_conflicted_chb(struct kissat *);
void kissat_decay_p_scores(struct kissat *);
void kissat_inc_p_score(struct kissat *, unsigned);
#define MAX_SCORE 1e150

#endif
