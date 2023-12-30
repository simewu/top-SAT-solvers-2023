#ifndef _symmetry_h_INCLUDED
#define _symmetry_h_INCLUDED
#include "internal.h"
typedef struct simplify simplify;
struct kissat;
void kissat_detect_symmetry(simplify *);
#endif