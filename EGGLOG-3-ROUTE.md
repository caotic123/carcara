# The egglog 3.0 route for the hole engine

What is left after run `small4` (EGGLOG-ELABORATION-NOTES.md §17) is the
same in the checking and the elaboration pass and all of it is inside
egglog's saturation: per pass about 140 holes killed at the 30 s bound, about
65 killed at the 5 GB memory limit, and 12 the engine cannot prove. Neither
the reconstruction nor the snapshot is involved any more. This note collects
what has been established about moving the engine from egglog 0.4 to 3.0 to
attack those losses, so the decision can be made without re-deriving it.

## Why 0.4 cannot bound its own work

The production engine (`src/rare/engine.rs`) runs on egglog 0.4.0. A ruleset
iteration there is one call into the crate: every rule's matches are found
and all of them applied before control returns. A budget can therefore only
be observed *between* iterations (`run_statement_within_deadline` steps
`Saturate` as `Run{iterations:1}` and checks the clock around each step),
and one iteration is free to apply millions of matches. That is exactly the
failure behind the remaining kills: the e-graph blows up inside a single
iteration, either past 30 s or past 5 GB, and nothing short of killing the
process stops it. The child-per-hole design (`--hole-isolate`) exists to
make that kill safe; it cannot make it cheaper.

## What 3.0 offers

egglog 3.0.0 is already a dev-dependency (`egglog-proofs`, used by the
reconstruction tests to build proof-producing fixtures). Two things matter:

1. **A `Scheduler` hook.** `egglog::scheduler::Scheduler` has
   `filter_matches(rule, ruleset, &mut Matches) -> bool`, called once per
   rule per iteration with the matches that iteration found and the right to
   apply only some of them (`Matches::choose`), and `can_stop`. The caller
   drives the loop with `step_rules_with_scheduler`. The prototype in
   `src/rare/reconstruction/tests/bounded_scheduler.rs` (commit `a9c4e797`)
   shows what this buys: a cap on the matches applied per rule per iteration
   bounds how far the e-graph can grow in any one iteration, and an expired
   deadline makes the hook refuse every match, so the e-graph stops growing
   at the next rule boundary instead of the next iteration boundary. The
   three tests there pass (growth stays under `cap × iterations`; after the
   deadline nothing reaches the database; the driver's pre-check stops
   before any work).

2. **What it does not offer: preemption.** `filter_matches` runs *after* the
   query produced its matches, so one expensive e-matching query is still
   uninterruptible; the bound is on growth and iteration count, not on
   wall-clock. 3.0 also has no cancellation flag. The child-per-hole kill
   remains the hard bound; 3.0 makes it fire less often by keeping
   iterations small, it does not replace it.

## What it costs

* **The engine rewrite.** `engine.rs` drives 0.4 through its textual
  program API (`parse_and_run_program`, `Saturate`/`Run` statements,
  `eval_expr`, `value_to_class_id`). 3.0 changed the surface: statements
  are stepped through `step_rules`/`step_rules_with_scheduler`, the run
  report differs, and the RARE-to-egglog encoding (`build_args_list`,
  sorts) must be re-checked against 3.0's syntax. Order of a few days of
  work, mostly mechanical, with the reconstruction unit tests and the RQ1
  corpus (`~/exp/egglog-holes/local/`, `tests/rare/sliced_proofs/`) as
  the regression suite.

* **The snapshot.** Reconstruction reads the saturated e-graph through
  `EGraph::serialize` (`EGraphSnapshot::serialize_production`). 3.0
  serializes through `egglog_bridge`, and the bridge's row iterator
  (`for_each`) exists but is not reachable from `egglog::EGraph`
  (`backend` and `Function::backend_id` are private). So 3.0 needs its own
  vendored change for the snapshot, like `third-party/egglog-0.4.0` does
  for the extractor bug, unless its `serialize` turns out fast enough as
  is; that has not been measured.

* **Memory.** The 5 GB kills are the same blow-up seen through a different
  limit. The match cap addresses them the same way it addresses the time
  kills. There is no separate memory hook.

## What it would buy, and what to measure first

The upper bound on the gain is the egglog-phase losses: about 4% of
attempted holes per pass (small4: 218 of 5,392 unproved; 140 + 66 + 12).
The 12 "could not prove" are rule coverage, not engine. So a perfect 3.0
port recovers at most ~3.8% of holes on this sample; on the full run the
share may be larger in QF_LRA, where saturation blow-ups concentrate (99 of
144 egglog-phase kills in small4).

Before committing to the port, two cheap measurements decide it:

1. **Does a match cap keep the killed holes provable?** Take the small4
   holes killed in the egglog phase (their inputs are reproducible with
   `carcara reconstruct-hole`), run them through the 3.0 prototype driver
   with the RARE program translated by hand for a few of them, and see
   whether the goal equality is reached under the cap. If the cap merely
   delays the blow-up until the goal is unreachable, the port buys nothing.
2. **Is 3.0's `serialize` fast enough?** Serialize the same saturated
   e-graphs through 3.0 and time it. If it is, the snapshot needs no
   vendored change.

If both come out favourably, the port is worth doing; otherwise the
remaining losses are better attacked on the RARE side (rule ordering,
smaller rulesets per hole kind), which needs no engine change.
