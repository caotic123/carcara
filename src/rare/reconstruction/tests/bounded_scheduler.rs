//! Prototype: bounding egglog work with the 3.0 scheduler hook.
//!
//! The production engine runs on egglog 0.4, where a ruleset iteration is one
//! uninterruptible call: a budget can only be observed *between* iterations,
//! and a single iteration is free to apply millions of matches.  That is the
//! failure mode behind the holes that overrun `--rare-check-timeout`.
//!
//! egglog 3.0 adds a `Scheduler` trait whose `filter_matches` is called once
//! per rule per iteration, with the matches that iteration found and the right
//! to apply only some of them.  This module measures what that buys: the
//! caller drives the iteration loop, so the deadline is checked at every
//! iteration boundary, and the match cap bounds how far the e-graph can grow
//! in any one of them.
//!
//! What it still does not buy is preemption: `filter_matches` runs *after* the
//! query produced its matches, so one expensive e-matching query remains
//! uninterruptible.  The bound is on growth and on iteration count, not on
//! wall-clock.
use std::{
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
    time::{Duration, Instant},
};

use egglog_proofs::{
    EGraph as ProofEGraph,
    scheduler::{Matches, Scheduler},
};

/// Counters shared with the scheduler, which the e-graph takes ownership of.
#[derive(Clone, Debug, Default)]
struct BudgetStats {
    /// Matches the rules produced, whether or not they were applied.
    offered: Arc<AtomicUsize>,
    /// Matches actually fired.
    applied: Arc<AtomicUsize>,
    /// Times the deadline turned a rule's matches away.
    refused: Arc<AtomicUsize>,
}

impl BudgetStats {
    fn read(&self) -> (usize, usize, usize) {
        (
            self.offered.load(Ordering::Relaxed),
            self.applied.load(Ordering::Relaxed),
            self.refused.load(Ordering::Relaxed),
        )
    }
}

/// Applies at most `per_iteration` matches of each rule, and stops applying
/// anything once `deadline` passes.
#[derive(Clone)]
struct BudgetScheduler {
    deadline: Option<Instant>,
    per_iteration: usize,
    stats: BudgetStats,
}

impl BudgetScheduler {
    fn expired(&self) -> bool {
        self.deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
    }
}

impl Scheduler for BudgetScheduler {
    /// Once the budget is gone there is no deferred work worth another
    /// iteration, so the runner is free to stop.
    fn can_stop(&mut self, _rules: &[&str], _ruleset: &str) -> bool {
        true
    }

    fn filter_matches(&mut self, _rule: &str, _ruleset: &str, matches: &mut Matches) -> bool {
        let offered = matches.match_size();
        self.stats.offered.fetch_add(offered, Ordering::Relaxed);
        if self.expired() {
            // Choose nothing and ask for no further iterations: the matches
            // were already computed, but none of them reach the database.
            self.stats.refused.fetch_add(1, Ordering::Relaxed);
            return false;
        }
        let take = offered.min(self.per_iteration);
        for index in 0..take {
            matches.choose(index);
        }
        self.stats.applied.fetch_add(take, Ordering::Relaxed);
        // Ask for another iteration only while matches are being held back.
        take < offered
    }
}

#[derive(Debug)]
struct BoundedRun {
    iterations: usize,
    tuples: usize,
    offered: usize,
    applied: usize,
    refused: usize,
    elapsed: Duration,
}

/// Drives `ruleset` under a budget, one iteration at a time.
fn run_bounded(
    program: &str,
    ruleset: &str,
    budget: Option<Duration>,
    per_iteration: usize,
    max_iterations: usize,
    check_before_stepping: bool,
) -> BoundedRun {
    let mut egraph = ProofEGraph::default();
    egraph
        .parse_and_run_program(None, program)
        .expect("the prototype program should load");

    let stats = BudgetStats::default();
    let deadline = budget.and_then(|budget| Instant::now().checked_add(budget));
    let scheduler = egraph.add_scheduler(Box::new(BudgetScheduler {
        deadline,
        per_iteration,
        stats: stats.clone(),
    }));

    let started = Instant::now();
    let mut iterations = 0;
    for _ in 0..max_iterations {
        // The driver checks the budget here, at the iteration boundary.  A
        // test can turn this off to isolate what the scheduler hook alone does.
        if check_before_stepping && deadline.is_some_and(|deadline| Instant::now() >= deadline) {
            break;
        }
        let report = egraph
            .step_rules_with_scheduler(scheduler, ruleset)
            .expect("stepping the ruleset should not fail");
        iterations += 1;
        if report.can_stop {
            break;
        }
    }
    let elapsed = started.elapsed();
    let (offered, applied, refused) = stats.read();
    BoundedRun {
        iterations,
        tuples: egraph.num_tuples(),
        offered,
        applied,
        refused,
        elapsed,
    }
}

/// The same ruleset with no scheduler: every match of every iteration fires.
fn run_unbounded(program: &str, ruleset: &str, iterations: usize) -> usize {
    let mut egraph = ProofEGraph::default();
    egraph
        .parse_and_run_program(None, program)
        .expect("the prototype program should load");
    for _ in 0..iterations {
        let report = egraph
            .step_rules(ruleset)
            .expect("stepping the ruleset should not fail");
        if report.can_stop {
            break;
        }
    }
    egraph.num_tuples()
}

/// A ruleset with far more matches available than any one iteration should
/// be allowed to fire.  Rewrites alone are a poor fixture here: congruence
/// folds them back into one e-class and the e-graph saturates immediately.
/// This rule instead *builds* a new term from every existing one, and the
/// seeds give the first iteration `seeds` matches to offer.
fn growing_program(seeds: usize) -> String {
    let constants: String = (0..seeds).map(|i| format!(" (C{i})")).collect();
    let terms: String = (0..seeds)
        .map(|i| format!("(let s{i} (F (C{i}) (C{})))\n", (i + 1) % seeds))
        .collect();
    format!(
        "(datatype T{constants} (F T T))\n\
         (ruleset grow)\n\
         (rule ((= x (F a b))) ((F x x)) :ruleset grow)\n\
         {terms}"
    )
}

#[test]
fn match_cap_bounds_growth_per_iteration() {
    // 32 matches are available in the first iteration; the cap lets 3 through.
    const ITERATIONS: usize = 4;
    const CAP: usize = 3;
    let program = growing_program(32);
    let unbounded = run_unbounded(&program, "grow", ITERATIONS);
    let bounded = run_bounded(&program, "grow", None, CAP, ITERATIONS, true);

    eprintln!("unbounded tuples after {ITERATIONS} iterations: {unbounded}");
    eprintln!("bounded (cap {CAP}): {bounded:?}");

    // The cap is the whole point: most matches never reach the database, so
    // the e-graph the next iteration has to search stays small.
    assert!(
        bounded.applied < bounded.offered,
        "the cap should hold matches back: {bounded:?}"
    );
    assert!(
        bounded.tuples < unbounded,
        "capping matches should keep the e-graph smaller: {} vs {unbounded}",
        bounded.tuples
    );
    // Growth is bounded by the cap, one rule, one application per iteration.
    assert!(
        bounded.applied <= CAP * ITERATIONS,
        "at most cap * iterations matches should fire: {bounded:?}"
    );
}

#[test]
fn the_hook_refuses_to_apply_matches_after_the_deadline() {
    // The driver's own pre-check is disabled, so the only thing standing
    // between the rules and the database is `filter_matches`.  The matches are
    // still computed — that is the limit of this hook — but none are applied,
    // so the e-graph cannot grow.
    let program = growing_program(16);
    let before = run_bounded(&program, "grow", Some(Duration::ZERO), 64, 3, false);
    eprintln!("hook-only, expired budget: {before:?}");

    assert!(
        before.iterations > 0,
        "the driver should have stepped the ruleset: {before:?}"
    );
    assert!(
        before.offered > 0,
        "the rules should still have produced matches: {before:?}"
    );
    assert!(
        before.refused > 0,
        "the hook should have turned matches away: {before:?}"
    );
    assert_eq!(
        before.applied, 0,
        "no match should reach the database after the deadline: {before:?}"
    );

    // And the e-graph is exactly the one the program loaded with.
    let untouched = run_bounded(&program, "grow", Some(Duration::ZERO), 64, 0, false);
    assert_eq!(
        before.tuples, untouched.tuples,
        "a refused run should not grow the e-graph: {before:?} vs {untouched:?}"
    );
}

#[test]
fn the_driver_stops_at_an_iteration_boundary() {
    // With the pre-check on, an expired budget means no iteration is entered
    // at all: the deadline is observed before any egglog work is started.
    let bounded = run_bounded(
        &growing_program(16),
        "grow",
        Some(Duration::ZERO),
        64,
        10_000,
        true,
    );
    eprintln!("driver pre-check, expired budget: {bounded:?}");

    assert_eq!(
        bounded.iterations, 0,
        "an expired budget should not start an iteration: {bounded:?}"
    );
    assert_eq!(bounded.offered, 0, "no rule should have run: {bounded:?}");
    assert!(
        bounded.elapsed < Duration::from_millis(10),
        "stopping at the boundary should be immediate: {bounded:?}"
    );
}
