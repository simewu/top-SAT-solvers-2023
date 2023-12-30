#ifndef _search_h_INCLUDED
#define _search_h_INCLUDED
#include "value.h"
struct kissat;

int kissat_search(struct kissat *);
void claim(struct kissat *, unsigned , value );
void unassign(struct kissat *, value *, unsigned );
void unlucky_backtrack(struct kissat *, unsigned );
#endif
