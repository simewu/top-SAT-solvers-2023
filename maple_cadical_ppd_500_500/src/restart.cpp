#include "internal.hpp"

namespace CaDiCaL {

// As observed by Chanseok Oh and implemented in MapleSAT solvers too,
// various mostly satisfiable instances benefit from long quiet phases
// with less or almost no restarts.  We implement this idea by prohibiting
// the Glucose style restart scheme in a geometric fashion, which is very
// similar to how originally restarts were scheduled in MiniSAT and earlier
// solvers.  We start with say 1e3 = 1000 (opts.stabilizeinit) conflicts of
// Glucose restarts.  Then in a "stabilizing" phase we disable these
// until 1e4 = 2000 conflicts (if 'opts.stabilizefactor' is '200' percent)
// have passed. After that we switch back to regular Glucose style restarts
// until again 2 times more conflicts than the previous limit are reached.
// Actually, in the latest version we still restarts during stabilization
// but only in a reluctant doubling scheme with a rather high interval.

bool Internal::stabilizing () {
  if (!opts.stabilize) return false;
  if (stable && opts.stabilizeonly) return true;
  if (stats.conflicts >= lim.stabilize) {
    report (stable ? ']' : '}');
    if (stable) STOP (stable);
    else        STOP (unstable);
    stable = !stable;
    if (stable) stats.stabphases++;
    PHASE ("stabilizing", stats.stabphases,
      "reached stabilization limit %" PRId64 " after %" PRId64 " conflicts",
      lim.stabilize, stats.conflicts);
    inc.stabilize *= opts.stabilizefactor*1e-2;
    if (inc.stabilize > opts.stabilizemaxint)
      inc.stabilize = opts.stabilizemaxint;
    lim.stabilize = stats.conflicts + inc.stabilize;
    if (lim.stabilize <= stats.conflicts)
      lim.stabilize = stats.conflicts + 1;
    swap_averages ();
    PHASE ("stabilizing", stats.stabphases,
      "new stabilization limit %" PRId64 " at conflicts interval %" PRId64 "",
      lim.stabilize, inc.stabilize);
    report (stable ? '[' : '{');
    if (stable) START (stable);
    else        START (unstable);
  }
  return stable;
}

// Restarts are scheduled by a variant of the Glucose scheme as presented in
// our POS'15 paper using exponential moving averages.  There is a slow
// moving average of the average recent glucose level of learned clauses as
// well as a fast moving average of those glues.  If the end of a base
// restart conflict interval has passed and the fast moving average is above
// a certain margin over the slow moving average then we restart.

bool Internal::restarting () {
  if (!opts.restart) return false;
  if ((size_t) level < assumptions.size () + 2) return false;
  if (stabilizing ()) return reluctant;
  if (stats.conflicts <= lim.restart) return false;
  double f = averages.current.glue.fast;
  double margin = (100.0 + opts.restartmargin)/100.0;
  double s = averages.current.glue.slow, l = margin * s;
  LOG ("EMA glue slow %.2f fast %.2f limit %.2f", s, f, l);
  return l <= f;
}

// This is Marijn's reuse trail idea.  Instead of always backtracking to the
// top we figure out which decisions will be made again anyhow and only
// backtrack to the level of the last such decision or to the top if no such
// decision exists top (in which case we do not reuse any level).

int Internal::reuse_trail () {
  const int trivial_decisions = assumptions.size ()
    // Plus 1 if the constraint is satisfied via implications of assumptions
    // and a pseudo-decision level was introduced
    + !control[assumptions.size () + 1].decision;
  if (!opts.restartreusetrail) return trivial_decisions;
  int decision = next_decision_variable ();
  assert (1 <= decision);
  int res = trivial_decisions;
  if (use_scores ()) {
    while (res < level &&
           score_smaller (this)(decision, abs (control[res+1].decision)))
      res++;
  } else {
    int64_t limit = bumped (decision);
    while (res < level && bumped (control[res+1].decision) > limit)
      res++;
  }
  int reused = res - trivial_decisions;
  if (reused > 0) {
    stats.reused++;
    stats.reusedlevels += reused;
    if (stable) stats.reusedstable++;
  }
  return res;
}

inline void Internal::update_bcp_mode_random () {
  bcpmode = (rl_random.generate_double() < opts.bcpratio * 1e-3) ? BCPMode::DELAYED : BCPMode::IMMEDIATE;
  (bcpmode == BCPMode::IMMEDIATE ? stats.bcprl.immediate : stats.bcprl.delayed)++;
}

void Internal::clear_scores_rl () {
  rl_prevConflicts    = stats.learned.clauses;
  rl_prevPropagations = stats.propagations.search;
  rl_prevDecisions    = stats.decisions;
  rl_lbdsum           = 0;
}

template <Internal::RLScoreType scoretype>
inline double Internal::get_prev_round_score_rl () {
  switch (scoretype) {
    case RLScoreType::LBD: return rl_lbdsum / static_cast<double>(stats.learned.clauses - rl_prevConflicts);
    case RLScoreType::GLR: return (stats.learned.clauses - rl_prevConflicts) / static_cast<double>(stats.decisions - rl_prevDecisions);
    case RLScoreType::PPD: return (stats.propagations.search - rl_prevPropagations) / static_cast<double>(stats.decisions - rl_prevDecisions);
    default: __builtin_unreachable ();
  }
}

// Solver configuration
static constexpr bool                  ENABLE_RESETS       = false;
static constexpr bool                  ENABLE_PRIORITY_BCP = true;
static constexpr Internal::RLScoreType BCP_SCORETYPE       = Internal::RLScoreType::PPD;
static constexpr Internal::RLScoreType RESET_SCORETYPE     = Internal::RLScoreType::GLR;

inline Internal::BCPMode Internal::update_bcp_mode_rl () {
  if (stats.restarts > 1) {
    // Update (bump and decay) reward values
    const double prevRoundScore = get_prev_round_score_rl<BCP_SCORETYPE> ();
    bcprl_thompson.update_dist(static_cast<size_t>(bcpmode), prevRoundScore >= bcprl_historicalScore, 1e-3 * opts.bcprlbetadecay);

    // Update historical score as a weighted average
    const double DECAY_FACTOR = 1e-3 * opts.bcprlscoredecay;
    bcprl_historicalScore = bcprl_historicalScore * DECAY_FACTOR + prevRoundScore * (1 - DECAY_FACTOR);
  }

  // Pick new BCP mode
  bcpmode = static_cast<BCPMode>(bcprl_thompson.select_lever ());
  (bcpmode == BCPMode::IMMEDIATE ? stats.bcprl.immediate : stats.bcprl.delayed)++;
  return bcpmode;
}

inline Internal::RestartMode Internal::update_restart_mode_rl () {
  if (stats.restarts > 1) {
    // Update (bump and decay) reward values
    const double prevRoundScore = get_prev_round_score_rl<RESET_SCORETYPE> ();
    resetrl_thompson.update_dist(static_cast<size_t>(restartmode), prevRoundScore >= resetrl_historicalScore, 1e-3 * opts.resetrlbetadecay);

    // Update historical score as a weighted average
    const double DECAY_FACTOR = 1e-3 * opts.resetrlscoredecay;
    resetrl_historicalScore = resetrl_historicalScore * DECAY_FACTOR + prevRoundScore * (1 - DECAY_FACTOR);
  }

  // Pick whether to perform a reset
  restartmode = static_cast<RestartMode>(resetrl_thompson.select_lever ());
  if (restartmode == RestartMode::RESET) stats.resets++;
  return restartmode;
}

inline void Internal::reset_scores () {
  constexpr double SCALE_FACTOR = 1e-3;
  assert (!level);

  scores.clear();
  for (int idx = max_var; idx; idx--) {
    stab[idx] = rl_random.generate_double() * SCALE_FACTOR;
    scores.push_back(idx);
  }
}

void Internal::restart () {
  START (restart);
  stats.restarts++;
  stats.restartlevels += level;
  if (stable) stats.restartstable++;
  LOG ("restart %" PRId64 "", stats.restarts);

  // Check if we should reset
  if (ENABLE_RESETS && update_restart_mode_rl () == RestartMode::RESET) {
    backtrack (0);
    reset_scores ();
  } else {
    backtrack (reuse_trail ());
  }

  lim.restart = stats.conflicts + opts.restartint;
  LOG ("new restart limit at %" PRId64 " conflicts", lim.restart);

  // Pick the next BCP mode
  if (ENABLE_PRIORITY_BCP) update_bcp_mode_rl ();
  // update_bcp_mode_random ();

  if (ENABLE_RESETS || ENABLE_PRIORITY_BCP) clear_scores_rl ();

  report ('R', 2);
  STOP (restart);
}

}
