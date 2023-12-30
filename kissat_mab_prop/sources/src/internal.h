#ifndef _internal_h_INCLUDED
#define _internal_h_INCLUDED

#include "arena.h"
#include "assign.h"
#include "averages.h"
#include "check.h"
#include "clause.h"
#include "clueue.h"
#include "cover.h"
#include "extend.h"
#include "smooth.h"
#include "flags.h"
#include "format.h"
#include "frames.h"
#include "heap.h"
#include "kissat.h"
#include "limits.h"
#include "literal.h"
#include "mode.h"
#include "options.h"
#include "phases.h"
#include "profile.h"
#include "proof.h"
#include "queue.h"
#include "random.h"
#include "reluctant.h"
#include "rephase.h"
#include "stack.h"
#include "statistics.h"
#include "literal.h"
#include "value.h"
#include "vector.h"
#include "watch.h"

//#pragma GCC optimize("Ofast")
//#pragma GCC target("avx,avx2,fma")
//#pragma GCC target("sse,sse2,sse3,ssse3,sse4,popcnt,abm,mmx,tune=native")
//#pragma GCC optimize("unroll-loops")
typedef struct temporary temporary;

struct temporary {
    bool satisfied;
    bool shrink;
    bool trivial;
    unsigneds lits;
};

typedef struct idxrank idxrank;

struct idxrank {
    unsigned idx;
    unsigned rank;
};

typedef struct import import;

struct import {
    unsigned lit : 30;
    bool imported : 1;
    bool eliminated : 1;
};
struct simplify;

// *INDENT-OFF*
typedef STACK(value)eliminated;
typedef STACK(import)imports;
typedef STACK(idxrank)idxranks;
typedef STACK(watch)statches;
typedef STACK(watch *) patches;

// *INDENT-ON*

struct kissat {
    int *last_val;
    int *mapidx;
#ifdef LOGGING
    bool compacting;
#endif
    bool extended;
    bool inconsistent;
    bool iterating;
    bool probing;
#ifndef QUIET
    bool sectioned;
#endif
    bool stable;
    bool watching;
#ifdef COVERAGE
    volatile unsigned terminate;
#else
    volatile bool terminate;
#endif

    unsigned vars;
    unsigned size;
    unsigned active;

    ints export;
    ints units;
    imports import;
    extensions extend;
    unsigneds witness;

    assigned *assigned;
    flags *flags;

    mark *marks;

    value *values;
    phase *phases;

    eliminated eliminated;
    unsigneds etrail;

    links *links;
    queue queue;

    rephased rephased;

    heap scores;
    double scinc;

    // no proof claims from simplify
    int *simplified_hints;
    struct simplify * S;
    // CHB
    heap scores_chb;
    unsigned *conflicted_chb;
    double step_chb;
    double step_dec_chb;
    double step_min_chb;

    // MAB
    unsigned heuristic;
    bool mab;
    double mabc;
    double mab_reward[2];
    double mab_time[2];
    int64_t mab_propagations[2];
    int64_t mab_ticks[2];
    int64_t mab_last_propagations;
    int64_t mab_tot_propagations;
    int64_t mab_last_ticks;
    int64_t mab_tot_ticks;
    int64_t mab_last_conflicts;
    double mab_last_time;
    double mab_tot_time;
    unsigned mab_select[2];
    unsigned mab_heuristics;
    double mab_decisions;
    unsigned *mab_chosen;
    unsigned mab_chosen_tot;

    // MAB of luby and EMA
    // status: solver->stable
    bool mode_mab;
    double mode_reward[2];
    double mode_count[4][2]; // 0: chosen, 1:time, 2:propagations, 3:ticks
    double mode_last_count[4];
    double mode_tot_count[4];
    unsigned *mode_chosen;
    unsigned mode_chosen_tot;
    double mode_decisions;
    double modec; // initialize! count!
    // GENE
    //unsigned max_seed_count;
    //STACK(value *) seeds;
    // PSIDS
    bool PSIDS;
    //hywalk
    int walk_strategy;
    double *p_scores;
    double p_inc;
    double p_decay;
    heap schedule;

    //symmetry
    bool unsat_but_no_proof;
    bool symmetry_broken_without_proof;

    unsigned level;
    frames frames;

    unsigneds trail;
    unsigned propagated;

    unsigned best_assigned;
    unsigned consistently_assigned;
    unsigned target_assigned;
    unsigned unflushed;
    unsigned unassigned;

    //pr
    unsigneds * touched_list;
    bool inner;
    unsignedss clauses;
    double pr_start_time;
    unsigneds delayed;

#if defined(LOGGING) || !defined(NDEBUG)
    unsigneds resolvent_lits;
#endif
    unsigned resolvent_size;
    unsigned antecedent_size;

    unsigned transitive;

    unsigneds analyzed;
    idxranks bump;
    unsigneds levels;
    unsigneds minimize;
    unsigneds poisoned;
    unsigneds promote;
    unsigneds removable;

    clause conflict;

    temporary clause;

    arena arena;
    clueue clueue;
    vectors vectors;
    reference first_reducible;
    reference last_irredundant;
    watches *watches;

    sizes sorter;

    generator random;
    averages averages[2];
    reluctant reluctant;

    bounds bounds;
    delays delays;
    enabled enabled;
    limited limited;
    limits limits;
    waiting waiting;

    statistics statistics;
    mode mode;

    uint64_t ticks;

    format format;

    statches antecedents[2];
    statches gates[2];
    patches xorted[2];
    unsigneds resolvents;
    bool resolve_gate;

#ifndef NMETRICS
    uint64_t *gate_eliminated;
#else
    bool gate_eliminated;
#endif

#if !defined(NDEBUG) || !defined(NPROOFS)
    unsigneds added;
    unsigneds removed;
#endif

#if !defined(NDEBUG) || !defined(NPROOFS) || defined(LOGGING)
    ints original;
    size_t offset_of_last_original_clause;
#endif

#ifndef QUIET
    profiles profiles;
#endif

#ifndef NOPTIONS
    options options;
#endif

#ifndef NDEBUG
    checker *checker;
#endif

#ifndef NPROOFS
    proof *proof;
#endif

//cd
unsigned total_glue, total_size, total_learnt;
unsigned rand_selection;
struct cdata
{
  unsigned succ_no_confs; 
  unsigned confs_last_decision; 
  unsigned total_cdp_len;
  unsigned num_cdp;
  unsigned decisions_with_confs;
  unsigned decisions_without_confs;
  bool substantial_cd_phase, backtrack_at_substantial_cd_phase;
  unsigned start_dlevel_current_cd_phase;
  unsigned confs_since_restart;
  unsigneds cd_phase_decisions;
  unsigned action_applied_amid_cd;
  unsigned last_decision;
  int decide_rand;
  unsigned rand_select_start;
  int exploration_depth_bound;
  unsigned rand_dec_confs;
  unsigned rand_dec_learn_glue;
  unsigned rand_dec_learn_size;
  unsigned decide_rand_success;
  unsigned decide_rand_success_tries;

  } cdata;

};

#define VARS (solver->vars)
#define LITS (2 * solver->vars)

static inline unsigned kissat_assigned(kissat *solver)
{
    assert(VARS >= solver->unassigned);
    return VARS - solver->unassigned;
}

#define all_variables(IDX)                    \
    unsigned IDX = 0, IDX_END = solver->vars; \
    IDX != IDX_END;                           \
    ++IDX

#define all_literals(LIT)             \
    unsigned LIT = 0, LIT_END = LITS; \
    LIT != LIT_END;                   \
    ++LIT

#define all_clauses(C)                                                                                      \
    clause *C = (clause *)BEGIN_STACK(solver->arena), *C_END = (clause *)END_STACK(solver->arena), *C_NEXT; \
    C != C_END && (C_NEXT = kissat_next_clause(C), true);                                                   \
    C = C_NEXT

#endif
