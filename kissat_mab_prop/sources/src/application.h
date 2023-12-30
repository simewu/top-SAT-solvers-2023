#ifndef _application_h_INCLUDED
#define _application_h_INCLUDED
#include "parse.h"
struct kissat;
struct application;
struct application {
    struct kissat *solver;
    const char *input_path;
#ifndef NPROOFS
    const char *proof_path;
    file proof_file;
    bool force;
    int binary;
#endif
    int time;
    int conflicts;
    int decisions;
    strictness strict;
    bool partial;
    bool witness;
    int max_var;
};
void init_app(struct application *, struct kissat *);
int kissat_application(struct kissat *, int argc, char **argv);
bool parse_options(struct application *, int , char **);
#endif
