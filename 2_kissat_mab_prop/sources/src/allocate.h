#ifndef _allocate_h_INCLUDED
#define _allocate_h_INCLUDED

#include <stdlib.h>

struct kissat;

void *kissat_malloc(struct kissat *, size_t bytes);
void kissat_free(struct kissat *, void *, size_t bytes);

void *kissat_calloc(struct kissat *, size_t n, size_t size);
void kissat_dealloc(struct kissat *, void *ptr, size_t n, size_t size);

void *kissat_realloc(struct kissat *, void *, size_t old, size_t bytes);
void *kissat_nrealloc(struct kissat *, void *, size_t o, size_t n, size_t);

char *kissat_strdup(struct kissat *, const char *);
void kissat_delstr(struct kissat *, char *str);

#define DEALLOC(P, N)                                  \
    do {                                               \
        kissat_dealloc(solver, (P), (N), sizeof *(P)); \
    } while (0)

#endif
