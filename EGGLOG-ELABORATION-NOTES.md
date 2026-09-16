# Justifying arbitrary Alethe equality steps with egglog — orientation notes

Branch: `egglog/elaborator` (23 commits on top of `main`).
Written 2026-09-13 after reproducing the flow end to end locally.

Companion thesis: `/home/hbarbosa/papers/these/msc-tiago` (Tiago Campos,
*Independent justification of rewrites in SMT proofs via equality saturation*).

---

## 1. The shape of proof the technique expects

The input is a **cvc5 Alethe proof produced at `theory-rewrite` granularity**.
At that granularity cvc5 does *not* justify its preprocessing/rewriting
equalities; it emits them as trusted holes:

```
(step t3 (cl (= <lhs> <rhs>)) :rule hole
      :args ("TRUST_THEORY_REWRITE" (= <lhs> <rhs>) 1 6))
```

* The first `:args` element is the literal string `"TRUST_THEORY_REWRITE"` —
  this is the *only* thing `rare_hole::is_theory_rewrite_hole` keys on
  (`src/elaborator/rare_hole.rs`).
* The equality repeated in `:args`, plus the two trailing integers, is what
  `--parse-hole-args` makes Carcara parse as real terms. Without that flag the
  args stay uninterpreted and the pipeline cannot read the obligation.
* The step's **clause must be a single literal** — an equality. A multi-literal
  clause is rejected at the `setup` stage.
* The proof must be a **refutation** (conclude `(cl)`). A bare hole file such as
  `demo.smt2.alethe` is rejected with *"proof does not conclude empty clause"*
  before elaboration even starts. This is why per-hole work goes through
  `carcara slice`, which appends a synthetic
  `(step slice_end (cl) :rule hole :premises (tN) :args ("trust"))`.

Produce such proofs with (this repo's `scripts/solve.sh`):

```
cvc5 problem.smt2 --produce-proofs --dump-proofs \
  --proof-format-mode=alethe --proof-granularity=theory-rewrite \
  --proof-alethe-res-pivots --proof-elim-subtypes --print-arith-lit-token \
  > problem.smt2.alethe
```

### What comes out

`--elaborate-hole-rewrites` replaces each such hole with a subproof. The core
of that subproof is one of:

| Certificate node | Emitted Alethe rule | Trusted? |
|---|---|---|
| `Rule` with a name in the RARE db | `rare_rewrite :args ("<rule>" <inst>...)` | no — `check_rare` re-checks it |
| `Rule` engine-internal (no RARE name) | `hole :args ("TRUST_THEORY_REWRITE" "<name>")` | **yes** |
| `Computational::Evaluation` | `evaluate` | no |
| `Computational::AciNorm` | `aci_simp` | no |
| `Computational::ArithPolyNorm` | `poly_simp` | no |
| `Computational::DistinctElim` | `distinct_elim` | no |
| `Computational::ArithPolyNormRel` | `hole :args (... "arith_poly_norm_rel")` | **yes** |
| `Refl/Symm/Trans/Congruence` | `refl` / `symm` / `trans` / `cong` | no |

All of the non-trusted rules above are implemented in
`src/checker/shared.rs` (lines 299–488), so the elaborated proof re-checks
with a plain `carcara check`.

Observed output for a `bool-double-not-elim` hole (real QF_LIA benchmark):

```
(anchor :step t2.t1)
(assume t2.t1.t2.h (not (= (not (not (>= ...))) (>= ...))))
(step t2.t1.t2.1 (cl (= (not (not (>= ...))) (>= ...)))
      :rule rare_rewrite :args ("bool-double-not-elim" (>= ...)))
(step t2.t1.t2.2 (cl) :rule resolution :premises (t2.t1.t2.1 t2.t1.t2.h))
(step t2.t1 (cl (not (not (= ...))) false) :rule subproof :discharge (t2.t1.t2.h))
(step t2.t2 ... :rule not_not)
(step t2.t3 (cl (not false)) :rule false)
(step t2.t4 (cl (= ...)) :rule resolution :premises (t2.t1 t2.t2 t2.t3))
```

The subproof shape comes from `external::insert_solver_proof`: the equality
proof is closed by resolving against the negated conclusion, exactly as an
external solver's proof would be inserted.

---

## 2. Building

Nothing special. `rust-toolchain.toml` pins 1.93; `rustc 1.93.1` is installed.

```
cd /home/hbarbosa/carcara/wt-tiago
cargo build --release        # ~41 s from a warm cargo registry
./target/release/carcara --version
# carcara 1.1.0 [git f1f22055 egglog/elaborator]
```

egglog 0.4.0 is a normal `Cargo.toml` dependency (the production engine).
egglog 3.0.0 (`egglog-proofs`) is a **dev-dependency only**, used by the
reconstruction unit tests to build proof-producing fixture e-graphs; the
shipped pipeline never uses it. There are no feature flags to enable
(`debug-egglog` is only extra logging).

The pre-existing `target/release/carcara` in the worktree was from Jul 9 and
predates the elaborator commits — rebuild before using it.

---

## 3. Running Carcara with egglog

Two distinct modes:

### (a) Check only — validate the hole, keep it a hole

```
carcara check proof.smt2.alethe problem.smt2 \
  --rare-file tests/rare/big.rare --check-hole-rewrites \
  --expand-let-bindings --allow-int-real-subtyping --parse-hole-args
```

egglog saturates and answers "the two sides are in the same e-class". Nothing
is reconstructed; the proof is simply accepted. This is the mode the **thesis
evaluation (RQ1/RQ2) measures**.

### (b) Elaborate — reconstruct a checkable Alethe subproof

```
carcara elaborate proof.smt2.alethe problem.smt2 \
  --rare-file tests/rare/big.rare --elaborate-hole-rewrites --pipeline hole \
  --expand-let-bindings --allow-int-real-subtyping --parse-hole-args \
  --no-print-with-sharing > elaborated.alethe
```

This is the command in `instructions.txt` and in
`tests/rare/sliced_proofs/Running.MD`.

Shared egglog knobs (they apply to both modes):
`--continuous-saturation`, `--rare-check-timeout <ms>`, `--print-egglog`.

RARE databases available in-tree: `tests/rare/big.rare` (674 lines, the real
one), plus `rules.rare`, `rules2.rare`, `prop.rare`, `bug.rare`, `demo.rare`.

#### Gotchas found while running this

1. **`carcara elaborate` prints the pre-elaboration status as the first line of
   stdout.** `> elaborated.alethe` therefore yields a file starting with
   `holey`, and feeding it back to `carcara check` fails with
   `unexpected token: 'holey'`. Strip line 1 (`tail -n +2`).
   The RQ1 runner did the equivalent with a perl one-liner.
2. **`--sliced-output`'s help text is reversed.** `app.rs` declares
   `value_names = ["SLICED_PROBLEM", "SLICED_PROOF"]` but `main.rs:304` reads
   `(proof_filename, problem_filename) = (&files[0], &files[1])`. The correct
   order on the command line is **proof first, then problem**.
3. **A slice always checks as `holey`**, because `slice_end` is itself a
   `hole` step with `:args ("trust")`. Success must be measured by counting
   remaining `TRUST_THEORY_REWRITE` occurrences, not by the verdict — which is
   exactly what the JSON in `instructions.txt` does
   (`"verdict": "holey"`, `"remaining_holes": 0`, `"fully_checked": true`).
4. `--pipeline hole` is required: the `hole` pass must be in the pipeline, and
   restricting to it avoids paying for polyeq/local/uncrowd/reordering.
5. The CLI already runs on a 512 MiB stack thread (`main.rs`), so the
   deep-recursion stack overflows reported in the thesis' `Err` column should
   be less frequent than they were.

---

## 4. Is the e-graph → Alethe reconstruction present on this branch?

**Yes.** It is the substance of the branch. `src/rare/reconstruction/`:

| File | Role |
|---|---|
| `snapshot.rs` | `EGraphSnapshot::capture_production` serializes the saturated egglog 0.4 e-graph into a **provenance-free** snapshot: e-nodes, interned operators, canonical e-class ids, three indices (by class, by (class, op), by signature). |
| `search.rs` (44 k) | Searches that snapshot for a replayable rewrite chain between the goal's lhs and rhs. |
| `certificate.rs` | The `Certificate` tree (`Refl`/`Rule`/`Computational`/`Symm`/`Congruence`/`Trans`) and `verify_in`, which re-checks the certificate **without consulting the e-graph** — rule instantiation is re-matched, ACI/poly/evaluation steps are recomputed. |
| `computation.rs` | The non-RARE computational kinds (ACI norm, poly norm, evaluation, distinct elim). |
| `program.rs` | Recovers the goal terms, the compiled rewrite rules and the arithmetic sorts *from the generated egglog program text* (`generated_goals`, `rules_from_generated_program`, `ArithSorts::from_generated_program`). |
| `term.rs` | Decoding back from the `Mk`/`Args`/`Empty`/`@f` encoding to Alethe syntax. |

The orchestration is `src/elaborator/rare_hole.rs::elaborate`:
`run_egglog` → `capture_production` → `reconstruct_with_sorts` →
`AletheElaborator::elaborate_full` → parse + **check the emitted steps with the
real checker** → `insert_solver_proof`.

Note the design point: egglog is used only as an *oracle*. It is not asked for
a proof (egglog 0.4 has no provenance). The certificate is rediscovered by
searching the saturated e-graph afterwards, and is then independently verified
— so a buggy search cannot produce an unsound proof, only a failure.

Tests: `src/rare/reconstruction/tests/mod.rs`, notably
`elaborates_cvc5_theory_rewrite_holes_end_to_end` (RF-12), and the
`#[ignore]`d corpus sweep `reconstructs_benchmark_corpus`, driven by
`BENCH_LIST` (TSV: `<slice.alethe>\t<problem.smt2>\t<hole id>`), `BENCH_RARE`,
optional `BENCH_SKIP`/`BENCH_LIMIT`/`BENCH_OUT`/`BENCH_DUMP`/`BENCH_PRINT`.

---

## 5. What `instructions.txt` asks for, and how it relates

`instructions.txt` gives two things:

1. The **single-proof command** (§3b above) — verified working.
2. A **`pipeline.py <root> --rare-file ... --max-holes-per-proof N --jobs 8
   --carcara <bin> --slice-timeout-sec 120 --elab-timeout-sec 900
   --check-timeout-sec 300`** driver that, per the JSON record, does:
   slice each `TRUST_THEORY_REWRITE` hole out of each proof → elaborate the
   slice → check the elaborated slice → record timings and hole counts into
   `pipeline_runs/<root>/<logic>/<problem>/` plus a final JSON at the root.

**`pipeline.py` is not in this repository and is not anywhere under
`/home/hbarbosa`.** It has to be obtained from Tiago (or rewritten — it is a
thin driver over three `carcara` invocations; see §6).

The JSON record in `instructions.txt` is reproducible by hand today. Its fields
map one-to-one onto:

```
carcara slice  <proof> <problem> --from <hole>
               --sliced-output <slice.alethe> <slice.smt2> ...   # proof FIRST
carcara elaborate <slice.alethe> <slice.smt2> --elaborate-hole-rewrites ...
carcara check     <elaborated>   <slice.smt2> ...
```

I reproduced the exact record from `instructions.txt`
(`QF_LIA/ex8200_2600_100.smt2`, hole `t2`): slice has 1 hole, elaboration
succeeds (0.12 s here vs 1.07 s in the record), `remaining_holes` 0, check
verdict `holey`. The obligation is a `bool-double-not-elim`. In my cvc5
(1.3.4.dev) the hole `t2` lands on line 6 rather than line 5 — a one-line
prelude difference from the cvc5 version used for the record.

---

## 6. The `small_benchmark` set — status in this worktree

`small_benchmark/` contains `non-incremental.tar.gz` and 12 per-logic
tarballs (QF_LIA, QF_LRA, QF_IDL, QF_RDL, QF_UF, QF_UFIDL, QF_UFLIA,
QF_UFLRA, UF, UFIDL, UFLIA, UFLRA). Nothing is extracted.

**These are SMT-LIB *problems* only — 45,717 `.smt2` files and zero
`.alethe` files.** The `instructions.txt` JSON, by contrast, refers to
`small_benchmark/QF_LIA/ex8200_2600_100.smt2.alethe`, i.e. a *flat*
`<logic>/<name>.smt2` + `<name>.smt2.alethe` layout with proofs already
present.

So there are two gaps before the experiment can run:

* the proofs must be generated (cvc5 `theory-rewrite`, §1), and
* the layout must be flattened to `<root>/<logic>/<name>.smt2[.alethe]`,
  because the tarballs nest `<logic>/<family>/<subfamily>/<name>.smt2`.

Per-logic `.smt2` counts:

```
QF_LIA 13306   UF 7590      QF_UF 7503    UFLIA 10128
QF_IDL 2528    QF_LRA 1753  QF_UFLRA 1284 QF_UFLIA 659
QF_UFIDL 628   QF_RDL 255   UFIDL 68      UFLRA 15
```

Note the thesis evaluates six logics (QF_LIA, QF_LIRA, QF_LRA, QF_UF,
QF_UFLIA, QF_UFLRA); this tarball set has no QF_LIRA and adds
QF_IDL/QF_RDL/QF_UFIDL/UF/UFIDL/UFLIA/UFLRA.

---

## 7. Reproducing the thesis' partial experiments

The raw data is committed in the thesis repo:

* `raw/data_rq1.tar.gz` (98 MB, ~1,002,070 entries) — one directory per proof
  obligation, `<problem>.smt2.proof__<step-path>.proof/{run.out,output.log}`,
  grouped under `carcara_theory_check_outputs_modified_arith_poly_norm/<LOGIC>_random_sample/`,
  each with `benchmarks`, `script.sh`, `options`, `carcara_theory_check.sh`
  and assorted `grep_*` / `cmpr` / `salida` post-processing files.
* `raw/data_rq2.tar.gz` — six CSVs `data_<logic>` with header
  `item,dsl-theory,carcara` (problem path, `t_DSL − t_REWRITE` in ms,
  pipeline checking time in ms). Row counts: qf_lia 1425, qf_uf 1592,
  qf_lra 143, qf_uflia 113, qf_uflra 12, qf_lira 1.

Both experiments ran on the **barrett cluster**, under
`/barrett/scratch/mallku/rare_paper_benchmarks/`, via
`/barrett/scratch/local/bin/submit-job.sh`. The RQ1 QF_LIA job was a SLURM
array of 171,534 tasks, partition `octa`, `-j 7`, `--time-limit 600`,
`--memory-limit 8000`, `--cpus 8`, each task wrapped in
`runexec --walltimelimit 600 --memlimit 8000MB`.

### The important caveat

The RQ1 runner (`carcara_theory_check.sh`) invoked:

```
carcara elaborate /tmp/$proof /tmp/$problem \
  --expand-let-bindings --allow-int-real-subtyping \
  --hole-solver=rare-rewrite --rare-file $rare_file \
  --parse-hole-args --continous-saturation
```

**Neither `--hole-solver=rare-rewrite` nor `--continous-saturation` (sic)
exists on this branch.** The binary was
`carcara_arith_poly_norm_tiago/target/release/carcara` — a different Carcara
tree. Its log lines (`Elaborating t9282:`, `Running goal check schedule round
1...`, `Elaboration succeeded in 0.093638s`) appear nowhere in this source.

On `egglog/elaborator` the equivalents are:

* `--hole-solver=rare-rewrite`  →  `--check-hole-rewrites` (check mode, what
  RQ1/RQ2 actually measured) or `--elaborate-hole-rewrites --pipeline hole`
  (reconstruct mode, new on this branch).
* `--continous-saturation`  →  `--continuous-saturation`.

`--hole-solver` is gone entirely; the current `hole_solver` field is fed by
`--smt-solver` and only handles `all_simplify`/`rare_rewrite` steps via an
external SMT solver — a different mechanism.

Also note the RARE file used there was `scripts/rq1/.../rules.rare`, not
this repo's `tests/rare/big.rare`; they are not guaranteed to match.

So the thesis numbers are **not** directly reproducible with this branch's
binary. Re-running RQ1/RQ2 means re-running with the current flags, which
produces comparable-but-new numbers.

### Recipe sketch, current branch

RQ1 (single-step, checking):

```
# 1. proofs
cvc5 <p>.smt2 --produce-proofs --dump-proofs --proof-format-mode=alethe \
  --proof-granularity=theory-rewrite --proof-alethe-res-pivots \
  --proof-elim-subtypes --print-arith-lit-token > <p>.smt2.alethe
# 2. one slice per TRUST_THEORY_REWRITE hole
carcara slice <p>.smt2.alethe <p>.smt2 --from <hole> \
  --sliced-output <slice>.alethe <slice>.smt2 \
  --expand-let-bindings --allow-int-real-subtyping --parse-hole-args -v
# 3a. check mode (the thesis metric)
carcara check <slice>.alethe <slice>.smt2 --rare-file big.rare \
  --check-hole-rewrites --continuous-saturation \
  --expand-let-bindings --allow-int-real-subtyping --parse-hole-args
# 3b. or reconstruct mode (this branch's contribution)
carcara elaborate <slice>.alethe <slice>.smt2 --rare-file big.rare \
  --elaborate-hole-rewrites --pipeline hole \
  --expand-let-bindings --allow-int-real-subtyping --parse-hole-args -v \
  | tail -n +2 > <slice>.elaborated.alethe
carcara check <slice>.elaborated.alethe <slice>.smt2 --rare-file big.rare \
  --expand-let-bindings --allow-int-real-subtyping --parse-hole-args
```

Steps 2–3 for a whole corpus are precisely what `pipeline.py` automated, and
what the `reconstructs_benchmark_corpus` sweep does in-process from a
`BENCH_LIST` TSV.

RQ2 additionally needs, per problem, a second cvc5 run at
`--proof-granularity=dsl-rewrite`, and records `t_DSL − t_REWRITE`.

---

## 8. Measured cost and sizing (added 2026-09-13)

### 8.1 Per-slice distribution, from the thesis' own RQ1 raw data

Parsed all 333,901 `run.out` records in `raw/data_rq1.tar.gz` (walltime,
cputime, peak memory, `terminationreason`). Recomputed success rates match the
thesis table (QF_LIA 90.16% vs 90.27%, QF_UF 99.21% vs 99.16%), so the parse is
sound. Note the archive holds exactly 2x the obligation count the table
reports, but the rates agree.

At the original 600 s / 8 GB limits:

| logic | N | ok% | TO | MO | p50 | p90 | p99 | max |
|---|---|---|---|---|---|---|---|---|
| QF_LIA | 171,534 | 90.16 | 660 | 16,224 | 0.24 | 0.84 | 20.44 | 599.0 |
| QF_LIRA | 405 | 96.79 | 6 | 7 | 0.12 | 0.39 | 342.95 | 448.6 |
| QF_LRA | 125,919 | 97.36 | 257 | 3,048 | 0.79 | 4.17 | 28.14 | 589.5 |
| QF_UFLIA | 7,985 | 90.17 | 1 | 784 | 0.15 | 0.59 | 0.74 | 39.7 |
| QF_UFLRA | 4,892 | 97.75 | 54 | 56 | 0.44 | 0.78 | 7.15 | 570.4 |
| QF_UF | 23,166 | 99.21 | 95 | 88 | 0.15 | 0.24 | 19.09 | 502.3 |
| **ALL** | **333,901** | **93.62** | **1,073** | **20,207** | 0.30 | 1.57 | 27.61 | 599.0 |

**Failures are memory, not time: 20,207 memouts vs 1,073 timeouts.** Successful
runs use trivial memory (QF_LIA p99.9 = 529 MB) while memouts saturate 8 GB in a
median of 38 s. That is a cliff, not a tail.

Cumulative success (% of all obligations) vs wall cap, at 8 GB:

| cap | 20 s | 60 s | 120 s | 180 s | 300 s | 600 s |
|---|---|---|---|---|---|---|
| QF_LIA | 89.25 | 89.68 | 89.95 | **90.02** | 90.08 | 90.16 |
| QF_UFLIA | 90.16 | 90.17 | 90.17 | 90.17 | 90.17 | 90.17 |
| QF_LRA | 95.94 | 96.93 | 97.13 | 97.19 | 97.28 | 97.36 |
| QF_UF | 98.29 | 98.92 | 99.00 | 99.01 | 99.20 | 99.21 |
| **ALL** | 92.54 | 93.18 | 93.41 | **93.47** | 93.54 | 93.62 |

Cluster cost for a sample of this size (333,901 obligations), 168 concurrent
slots:

| cap | CPU-hours | wall | success |
|---|---|---|---|
| 20 s | 212.8 | 1.27 h | 92.54% |
| 60 s | 363.9 | 2.17 h | 93.18% |
| 120 s | 497.6 | 2.96 h | 93.41% |
| **180 s** | **583.0** | **3.47 h** | **93.47%** |
| 600 s | 841.9 | 5.01 h | 93.62% |

### 8.2 Recommended sizing on `quad`

`quad` = 24 nodes x 8 cores x 64,110 MB (8.0 GB/core — the same ratio as the
`octa` nodes the thesis used).

```
submit-job.sh -w -t 180 --memory-limit 8000 --cpus 1 -j 7 -p quad ...
```

* **180 s wall** is where every logic clears 90% (QF_LIA crosses at exactly
  180 s). 120 s costs 15% less CPU with QF_LIA at 89.95%. 600 s buys +0.15 pp
  for +44% CPU.
* **`-j 7`, not 8**: 8 x 8000 MB = 64,000 of the node's 64,110 MB leaves nothing
  for the OS. This is almost certainly why the original runs used `-j 7`.
* **`-w` matters**: `submit-job.sh -t` is CPU seconds by default; the original
  experiment's `runexec --walltimelimit` is wall.

### 8.3 Per-benchmark (complete certificate)

From `raw/data_rq2.tar.gz` (per-certificate pipeline time, ms; the QF_LIA sum
119,882.9 s matches the thesis table's 119,882.87 exactly):

| logic | rows | sum (s) | p50 | p90 | p99 | max |
|---|---|---|---|---|---|---|
| qf_lia | 1,424 | 119,882.9 | 6.20 | 304.00 | 887.44 | 1,189.0 |
| qf_lra | 142 | 1,957.6 | 3.08 | 12.95 | 276.96 | 609.8 |
| qf_uf | 1,591 | 468,196.3 | 237.01 | 505.44 | 2,455.34 | 5,340.9 |
| qf_uflia | 112 | 3,615.9 | 0.42 | 98.86 | 330.64 | 343.3 |
| qf_uflra | 11 | 489.3 | 2.05 | 116.75 | 126.11 | 126.1 |

Sequential whole-certificate: 900 s covers 99.1% of QF_LIA's *checkable*
certificates and 97.4% of QF_UF's; 1200 s (the submit-job.sh default) is ample.

**But ~90% per benchmark is not attainable, and no timeout fixes it.** RQ2 fully
checked 1,488/2,513 QF_LIA paired certificates (59%) and 11/497 QF_UFLRA (2%).
A certificate is fully justified only if *every* hole succeeds; with per-hole
success ~0.90 over proofs carrying hundreds to thousands of holes, the product
collapses. Report *fraction of holes justified per benchmark* rather than
all-or-nothing, or attack the memory side.

Raising memory is worth testing before paying for it: successful runs sit three
orders of magnitude below the 8 GB limit while memouts saturate it in seconds.
On quad, 16 GB means `-j 3` — a third of the throughput. Re-run just the ~20k
memouts at 16/32 GB first and measure the rescue rate.

### 8.4 Local measurements on this branch

40 holes sampled uniformly from the 1,836-hole QF_LIA proof
(`ex8200_2600_100.smt2`), each sliced and elaborated separately, 900 s / 6 GB:

* slicing is free: max 0.04 s.
* elaboration wall: p50 1.27 s, p75 5.00 s, p90 8.16 s, max 144.52 s.
* 39/40 completed; one (`t120.t37.t289`) hit the 900 s timeout.
* Sum over the sample = 452.6 s for 39 holes + one 900 s timeout.
  Extrapolated to 1,836 holes: **~17 CPU-hours for this single proof.**

That settles the whole-proof question: `carcara elaborate` over a full cvc5
proof in place **does not finish** at this scale (a 900 s run and a 7,200 s run
both failed to produce output; the file is written only at the end, so nothing
is salvaged from a kill). Per-hole slicing is a necessity, not a
parallelization convenience — and at ~17 CPU-h spread over 168 slots it is
~6 minutes of wall time.

**`--elaborate-hole-rewrites` success is not the same as full justification.**
14 of the 39 completed elaborations (**36%**) produced a subproof that still
contains one trusted `hole :args ("TRUST_THEORY_REWRITE" "arith_poly_norm_rel")`
step. This is by design (`rare_hole.rs`: Carcara's native `poly_simp_rel` needs
a scaled-difference premise and matching relation operators, which these
certificates do not supply). Notably, every one of the slowest completions
carries this residue — the expensive holes are exactly the arithmetic ones that
stay partly trusted. The RQ1 rates in 8.1 are *check* mode, where this
distinction does not arise.

---

## 9. Throughput for the 30 s/hole + 1200 s/benchmark + 60 s cvc5 plan

### 9.1 Measured inputs

**cvc5 at 60 s**, on 150 problems sampled uniformly from `small_benchmark`
(30 each from QF_LIA, QF_LRA, QF_UF, QF_UFLIA, QF_UFLRA):

| logic | n | proofs | yield | holes p50 | p90 | max | mean holes |
|---|---|---|---|---|---|---|---|
| QF_LIA | 30 | 10 | 33% | 144 | 3,391 | 3,391 | 806 |
| QF_LRA | 30 | 10 | 33% | 117 | 3,491 | 3,491 | 676 |
| QF_UF | 30 | 17 | 57% | 434 | 749 | 753 | 398 |
| QF_UFLIA | 30 | 7 | 23% | 4 | 828 | 828 | 122 |
| QF_UFLRA | 30 | 9 | 30% | 587 | 2,591 | 2,591 | 951 |
| **ALL** | **150** | **53** | **35%** | | | | **585** |

31,000 holes across 53 proofs. cvc5 wall (48-problem subsample): mean 7.4 s,
p50 0.4 s, p90 42.0 s; proofs land in 1.9 s mean, failures burn 11.4 s mean
(most fail fast, not at the cap).

**Per-hole carcara cost under a 30 s cap**, from the RQ1 records
(mean of `min(t, 30)`, so failures charge their full 30 s):

| logic | mean | p50 | p90 | success @30s |
|---|---|---|---|---|
| QF_LIA | 3.33 s | 0.25 | 16.71 | 89.35% |
| QF_LRA | 2.65 s | 0.82 | 7.42 | 96.64% |
| QF_UF | 0.85 s | 0.15 | 0.25 | 98.40% |
| QF_UFLIA | 2.33 s | 0.29 | 1.18 | 90.16% |
| QF_UFLRA | 1.31 s | 0.45 | 0.82 | 97.32% |
| **ALL** | **2.84 s** | 0.30 | — | **~92.9%** |

### 9.2 The 1200 s benchmark cap is the binding constraint

Sequential per-benchmark cost = mean holes x mean per-hole cost:

| logic | mean cost | fraction over 1200 s |
|---|---|---|
| QF_LIA | 2,685 s | 30% |
| QF_LRA | 1,792 s | 20% |
| QF_UFLRA | 1,246 s | 44% |
| QF_UFLIA | 284 s | 14% |
| QF_UF | 338 s | 0% |
| **ALL** | **1,202 s** | **19%** |

The mean lands *exactly* on the 1200 s cap, and 19% of proofs exceed it. With
one job per benchmark you discard those regardless of the 30 s hole limit.

### 9.3 Slot count on quad

24 nodes x 8 cores x 64,110 MB.

* `-j 7 --memory-limit 8000` = **168 slots** (56,000 MB/node, 8 GB headroom).
* `-j 8 --memory-limit 7500` = **192 slots** (60,000 MB/node, 4 GB headroom) —
  **+14% throughput for free.** Justified by the data: successful runs use
  under 600 MB at p99.9, so the 8000 -> 7500 cut loses essentially nothing.

### 9.4 Throughput

| scheme | rate (192 slots) |
|---|---|
| one job per hole, 30 s cap | **243,000 holes/hour** |
| one job per benchmark, 1200 s cap | **576 benchmarks/hour** (19% hit the cap) |
| end to end, per 1,000 problems submitted | cvc5 0.01 h + carcara 0.61 h = **0.62 h** |

cvc5 is **1.3%** of the pipeline; carcara is ~98.7%. Do not spend effort
tuning the 60 s proof-production limit.

Whole-corpus estimate: 45,717 problems x 35% yield = ~16,000 proofs x 585 holes
= **~9.4M holes** = ~7,400 CPU-hours = **~38 h of quad wall time** at 192 slots.
Sample if that is too much; the RQ1 precedent was 0.5% of holes.

### 9.5 The 30 s per-hole limit is not enforceable in-process

Measured: `--rare-check-timeout 30000` on the hole that took 900 s in the
sample of 8.4 ran the full **300 s** until an external `timeout` killed it, and
produced nothing — 10x over budget.

Cause: `goal_run_schedule` (`src/rare/engine.rs:1194`) emits
`Saturate{list-ruleset}`, `Saturate{evaluation}`, then a bounded `Run`.
`run_goal_schedule_round` gives `Saturate` `repeats = 1` and calls
`run_and_record_statements`, which runs it to fixpoint inside egglog 0.4.
`check_timeout` only fires *around* that call (lines 1341/1343), never within
it. A saturation that blows up is uninterruptible.

Consequence: **threads alone will not stop workers getting stuck.** A blown-up
saturate pins its worker for the life of the job.

### 9.6 Making hole checking parallel — options

**(a) Process per hole. No code change. Use this.**
Slice, then `timeout 30 carcara elaborate` per slice. SIGKILL is a hard bound,
isolation is total, and a SLURM array or `xargs -P` parallelizes it. Overhead
measured at max 0.04 s slicing plus ~0.1 s startup, against a 2.84 s mean.
It also dissolves the 1200 s/benchmark cap, since the benchmark stops being a
unit of work — recovering the 19% lost in 9.2 and the full 243k holes/hour.

**(b) Make the cooperative timeout real.**
Replace the two unbounded `Saturate` statements with bounded
`Run { iterations: k }` loops. The machinery exists: the non-saturating
statement is already stepped with `check_timeout` before and after each
iteration; the saturating ones opt out via `repeats = 1`. Contained change.
Risk: rulesets needing a true fixpoint may stop early, so re-validate against
the RQ1 corpus before trusting success rates.

**(c) Threads inside Carcara.**
Hole elaboration is embarrassingly parallel — each hole needs only its clause,
the prelude, and the RARE database. Obstacles:

* `Elaborator` holds `pool: &'e mut PrimitivePool` (exclusive borrow), and
  `elaborate_hole` runs inside `mutate_impl` (`src/elaborator/mod.rs:429`), a
  single-threaded DFS with `FnMut` and `&mut ContextStack`. Restructure into
  three passes: collect the `TRUST_THEORY_REWRITE` steps, run them on a thread
  pool, splice results back with a lookup-only second `mutate`. Passes 1 and 3
  stay sequential and cheap.
* The term-pool merge is easier than it looks: `rare_hole::elaborate` already
  round-trips through text (it formats Alethe steps and re-parses via
  `parse_and_check`). A worker can return a `String` for the main thread to
  parse into the main pool, sidestepping pool merging. `ParallelProofChecker`
  also demonstrates the `Arc<PrimitivePool>` + per-thread `ContextPool`/
  `LocalPool` pattern if sharing terms is preferred.

**(c) without (b) still gets stuck** — a thread inside an uninterruptible
saturate cannot be killed in Rust. (c)'s real benefit is one-job-per-benchmark
accounting, not avoiding slow holes.

Recommended order: **(a) now, (b) as the one worthwhile code change, (c) only
if one-job-per-benchmark is a requirement.**

---

## 10. Implementation: bounded budgets, parallel holes, `poly_simp_rel`

Three changes on top of `f1f22055`.

### 10.1 (b) The per-hole budget is now real

`--rare-check-timeout` previously bounded nothing: measured at 10x over budget
(§9.5). Three separate unbounded phases were involved, fixed in turn.

**Saturation** (`src/rare/engine.rs`). `run_statement_within_deadline` replaces
the direct execution of every statement. With no deadline a `Saturate` runs to
its fixpoint in one egglog call, exactly as before. Under a deadline it is
instead stepped as single `Run { iterations: 1 }` calls, with `check_timeout`
between them and the loop ending as soon as `egraph.num_tuples()` stops growing
— egglog 0.4 cannot be interrupted inside one `(saturate ...)`, so the fixpoint
has to be approached rather than requested. Used by `run_goal_schedule_round`
and by both setup loops of `run_goal_fallback_attempt`.

**The certificate search** (`src/rare/reconstruction/search.rs`). `SearchStrategy`
gains a `deadline`, checked where `max_states` already was (`neighbors`), in the
bidirectional driver loop, and in `expand_level`. Expiry trips the existing
`over_budget` path, so no new failure mode is introduced.

**The e-graph snapshot** (`src/elaborator/rare_hole.rs`). Serializing the
saturated e-graph is one uninterruptible copy proportional to its size. A
deadline already spent now stops the hole before the snapshot, and
`MAX_SATURATION_TUPLES` (4M, deadline path only) stops saturation from building
an e-graph too large to copy in the first place.

The budget is shared: `reconstruct_steps` computes one deadline and passes it to
both egglog and the search, so a hole's total cost is bounded, not each phase
separately.

Measured, on the hole that previously ignored a 30 s budget for 300 s:

| budget | before | after |
|---|---|---|
| 1 s | — | 1.06 s |
| 5 s | — | 5.13 s |
| 10 s | — | 28.0 s (snapshot-bound, pre-cap) |
| 30 s | 300 s+, no output | see §10.4 |

It remains a **soft** budget: one egglog iteration and one snapshot are
uninterruptible, so overshoot is possible on pathological holes. The hard bound
is still the external process timeout — which is what the cluster provides.

### 10.2 (c) Holes are reconstructed in parallel

`--hole-threads N` (default 1, so the old path is untouched).

`rare_hole::elaborate` was split at its natural seam:

* `reconstruct_steps(pool, node, step, rules, options) -> Vec<String>` — all the
  cost (egglog, snapshot, search, Alethe emission). Takes `&mut dyn TermPool`,
  reads only the immutable proof node and rule database, and returns **text**.
* `insert_steps(elaborator, step, steps)` — parses that text against the problem,
  checks it, and splices it in. Always on the proof's own pool.

`Elaborator::reconstruct_holes_in_parallel` collects every hole
(`theory_rewrite_holes`, a DFS over the forest), runs `reconstruct_steps` on
`hole_threads` workers via `std::thread::scope` — each with a fresh
`PrimitivePool` — and returns a `step id -> Vec<String>` map. `elaborate_hole`
then splices from the map, falling back to the sequential path for any hole
whose worker failed, so errors are still reported at the right step.

Terms cross threads safely because Carcara's `ast::Rc` wraps `sync::Arc`
(`src/ast/rc.rs`). The text round-trip is what avoids merging term pools: each
worker's terms stay in its own pool and die with it; only strings come back,
and they are interned once by `insert_steps`.

Verified: on `tests/rare/elaborate/RF-12`, `--hole-threads 1` and
`--hole-threads 4` produce **byte-identical** output, both re-checking `valid`.

### 10.3 `arith_poly_norm_rel` is discharged via `poly_simp_rel`

Previously every relation certificate became a trusted hole, which was 36% of
completed elaborations in the §8.4 sample. The code comment claimed these were
"negated, mixed-operator, integer-tightened relations" that `poly_simp_rel`
could not serve. Inspecting the actual obligations showed three regular shapes:

| shape | example | route |
|---|---|---|
| `>=` vs `>=` | `(= (>= a (+ -3776 b c d)) (>= (+ a -b -c -d) -3776))` | direct |
| `=` vs `=` | `(= (= a (+ 3603 b -c -d)) (= b (+ -3603 a c d)))` | direct, sign flip allowed |
| `<=` vs `(not (>= ...))` | `(= (<= x 8472) (not (>= x 8473)))` | integer tightening |

`AletheElaborator::poly_simp_rel_chain` handles all three:

* Equalities go straight to `poly_simp_rel`, whose `Equals` case permits
  opposite-sign coefficients.
* Everything else is routed to a `>=` form on both sides by `to_geq`, using the
  RARE rules `arith-elim-leq`, `arith-elim-lt` and `arith-elim-int-lt` — emitted
  as checkable `rare_rewrite` steps — and the two `>=` forms are then related by
  a single `poly_simp_rel`. The routing steps are glued back with `trans`/`symm`.
* `scaling` derives the premise coefficients from the polynomial normal forms:
  with `d1`, `d2` the two scaled differences and `p1`, `p2` their pivots,
  `c1 = p2`, `c2 = p1` satisfies `c1*d1 = c2*d2`. The identity is **verified**
  before emission and denominators are cleared, so the premise is an integer
  `poly_simp` obligation. A sign-reversing pair is tried only for `=`, which is
  exactly `poly_simp_rel`'s own restriction.
* Integer tightening is applied only when `Poly::is_int_valued` says the
  difference really is integer-valued.
* Anything not covered keeps the trusted hole, and a partially emitted chain is
  rolled back (`steps.truncate(mark)`) so the fallback is not appended to a
  half-built chain.

The premise is proved by `poly_simp`, which is exactly the "scaled difference"
`poly_simp_rel` asks for:

```
(step p (cl (= (* c1 (- x1 x2)) (* c2 (- y1 y2)))) :rule poly_simp)
(step c (cl (= (>= x1 x2) (>= y1 y2))) :rule poly_simp_rel :premises (p))
```

Measured on the eight captured obligations: **6 fully justified, 0 trusted**,
2 exceeded the test's own 120 s cap (they succeed with a longer one). The
integer-tightening family — the majority — is covered.

All 244 library tests pass.

### 10.4 Validation

Per-slice, the way the pipeline actually runs (slice each hole, elaborate it,
re-check), across the three requested logics, 15 s per-hole budget, 8 GB:

| logic | holes | elaborated | avg | `arith_poly_norm_rel` left | any trusted step left |
|---|---|---|---|---|---|
| QF_UF | 20 | 20 | 78 ms | **0** | **0** |
| QF_LRA | 15 | 15 | 311 ms | **0** | **0** |
| QF_LIA | 10 | 10 | 3.9 s | **0** | **0** |
| **all** | **45** | **45** | | **0** | **0** |

Against the §8.4 baseline where 36% of completed elaborations kept an
`arith_poly_norm_rel` trust hole, this is 0 of 45. 12 of the elaborated proofs
were re-checked from their printed text with a plain `carcara check`: all 12
returned `holey`, whose only remaining hole is the synthetic `slice_end`
`("trust")` step the slicer appends — i.e. every reconstructed step checks.

Note this is on top of a guarantee already in the pipeline: `rare_hole` runs
`parse_and_check` on the reconstructed steps *before* splicing them in, so an
elaboration that succeeds has already passed Carcara's own checker.

Plus, separately: 244 library tests pass, and RF-12 elaborates byte-identically
at `--hole-threads 1` and `4`, re-checking `valid`.

### 10.5 Two findings from the validation

**Slicing is not just a scheduling convenience — it changes the work.** The
first hole of a 77-hole QF_LIA proof elaborates in **99 ms as a slice**, while
the same proof elaborated in place did not finish in 600 s. `run_egglog` seeds
the e-graph from `proof_node.get_assumptions()`; in a slice that is a handful of
assumptions, in a full proof it is the entire transitive premise set. This, not
parallelism, is the dominant cost difference, and it is the real reason the
`pipeline.py` design slices.

**The budget remains soft on pathological holes.** Hole `t9.t9` of RC-02 took
36.9 s under a 15 s budget — a 2.5x overshoot, from the uninterruptible egglog
iteration and e-graph snapshot described in §10.1. `MAX_SATURATION_TUPLES` caps
the worst case but does not make the bound exact. On the cluster this is
harmless (`runexec` provides the hard bound); in-process it means
`--rare-check-timeout` should be read as a target, not a guarantee.

### 10.6 Internal validation via the in-repo corpus sweep

The right harness for this was already in the repo: `reconstructs_benchmark_corpus`
(`src/rare/reconstruction/tests/mod.rs`), driven by a `BENCH_LIST` TSV of
`(slice, problem, hole)`. It runs the real pipeline per case and round-trips the
emitted steps through Carcara's checker (`check_with_carcara`), panicking on any
reconstruction, elaboration, or check failure. So `reconstructed=N` means N cases
passed the checker.

Two changes make it usable on a sample:

* `BENCH_TIMEOUT_MS` — per-case budget, passed to both `RunEgglogOptions.timeout`
  and `SearchStrategy::with_deadline`. Without it one diverging case stalls the
  whole sweep.
* The same pre-snapshot guards as the production path: skip the case when the
  budget is spent, and when the e-graph exceeds `MAX_SNAPSHOT_TUPLES`.

Run over 74 slices (24 QF_LIA, 30 QF_LRA, 20 QF_UF) at a 3-5 s per-case budget:

| cases | reconstructed | oracle-failed | stalled |
|---|---|---|---|
| 0-12 | 13 | 0 | — |
| 13 | — | — | 1 |
| 14-21 | 8 | 0 | — |
| 22-25 | 3 | 1 | — |
| 26-37 | 11 | 1 | — |
| 38-73 | 36 | 0 | — |
| **total** | **71 / 74** | **2** | **1** |

Zero reconstruction failures, zero Alethe-elaboration failures, zero checker
failures. The two oracle failures are egglog not closing the goal inside the
budget. Case 13 (`RC-02` hole `t9.t29.t28`) is the honest limit of §10.1:

**egglog 0.4 has no cancellation hook, so a single rule-matching iteration is
uninterruptible.** The budget is honoured at every boundary that exists —
between statements, between saturation iterations, in the search, before the
snapshot — but one iteration that runs for minutes cannot be cut short from
outside. `MAX_SATURATION_TUPLES` and `MAX_SNAPSHOT_TUPLES` cap the e-graph so
this is rare, but they cannot make the bound exact. A hard per-hole bound needs
either a process boundary (what `runexec` and `pipeline.py` provide) or a
cancellation hook added to egglog.

---

## 11. Hard per-hole limit: `--hole-isolate` (child process per hole)

The in-process budget cannot interrupt one egglog iteration (§10.6), and a
Rust thread cannot be killed, so the only hard bound is a process boundary.
`--hole-isolate` keeps the whole-proof, N-worker model of `--hole-threads`
but runs each hole's reconstruction in a child process:

* the worker builds `hole_input`: the problem prelude, a boundary line, the
  hole's depth-0 assumptions as top-level `assume`s and the hole citing them
  as premises — exactly what `run_egglog` reads off the in-process node
  (`get_assumptions` collects the depth-0 assumptions beneath it), so the
  child works from the same inputs; nothing is written to disk;
* it spawns the same binary's hidden `reconstruct-hole` subcommand, feeds
  that text on stdin, drains stdout/stderr on threads, and **kills the child
  outright** when `--rare-check-timeout` elapses; `--hole-memory-limit MB`
  applies `ulimit -v` to the child through `sh -c '... && exec ...'`, so the
  pid stays on carcara and the limit is on the child alone;
* a killed or failed child leaves its hole **as it was** (warned as
  `hole <id>: kept as trusted: <reason>`), so one bad hole no longer fails
  the whole elaboration. In thread mode the previous behaviour is unchanged.

Measured (`--hole-threads 4`, `tests/rare/big.rare`):

| case | result |
|---|---|
| RF-12, threads vs isolate | byte-identical output, 0.17 s |
| QF_LIA `pb2010__normalized-j907_8-unsat` (29 holes), 1 s/hole, isolate | **3.7 s** wall, 2 holes killed at 1.0 s, 27 justified, rc 0 |
| same proof, same 1 s/hole, in-process | **61 s** wall — the soft budget blown ~60x |
| RF-12, `--hole-memory-limit 30` | every child dies at start (the 512 MiB stack reservation needs ~700 MB), parent exits 0 with both holes kept |

Cost: ~0.1 s per hole for the child to parse the prelude and RARE file.

### Cluster run (`~/exp/egglog-holes/`)

`run-holes.sh` follows the pfchk runner contract (extra keys `elab_rc`,
`elab_time`, `holes_before`, `holes_after`, `holes_kept`; `ok=1` when the
elaborated proof re-checks valid or holey). cvc5 60 s at theory-rewrite
granularity, then `elaborate --hole-threads 4 --hole-isolate
--hole-memory-limit 5000 --rare-check-timeout 30000` under `timeout 600`,
then a `check` of the result. `gen-sets.py` takes the alethecore-eval sample
(seed 20260816) restricted to benchmarks whose local proof has at most 600
holes, 15 per logic. `submit-egglog-holes.sh`: quad, `-j 2 --cpus 4`,
24 GB, 900 s wall.

### cvc5 renamed the hole tag

cvc5 #12639 (`11c7a24fc1`, after April 2026) changed what the Alethe printer
emits for `ProofRule::TRUST_THEORY_REWRITE`: `:args ("TRUST_THEORY_REWRITE"
<eq> 1 6)` became `:args ("untranslated rewrite")` — same rule, same code path
(`src/proof/alethe/alethe_post_processor.cpp`). Builds from newer main (and
the `aletheLagFixes` static cvc5) print the new tag, so a run keyed on the old
one finds zero holes. `is_theory_rewrite_hole` now accepts both
(`THEORY_REWRITE_TAGS`); the runner counts both. On a newer-cvc5 QF_UF proof
with 43 such holes, four isolated workers at 30 s justified 40 and kept 3
(each killed at the 30 s bound), 30 s wall, and the result re-checks.

---

## 12. Cluster run `egglog-holes/small` (2026-09-14)

quad, 45 jobs (15 per logic from the alethecore-eval sample, proofs of at most
600 holes), one job per benchmark: cvc5 `main@f9e5d3c312` at theory-rewrite
granularity (60 s) → `carcara c7cc24a4 elaborate --hole-threads 4
--hole-isolate --hole-memory-limit 5000 --rare-check-timeout 30000` under
`timeout 600` with `big.rare` → `carcara check` of the result. Whole run:
**11 minutes** wall. Results in `~/exp/results/egglog-holes/small/`;
`~/exp/egglog-holes/analyze.py` summarizes.

| logic | proofs | ok | holes | justified | kept | elab p50 | elab max | peak mem |
|---|---|---|---|---|---|---|---|---|
| QF_LIA | 15 | 14 | 347 | 145 | 3 | 2.1 s | 600 s (timeout) | 3.5 GB |
| QF_LRA | 15 | 12 | 1,343 | 521 | 70 | 13.4 s | 379 s | 12.6 GB |
| QF_UF | 15 | 13 | 4,689 | 3,413 | 146 | 112 s | 272 s | 11.2 GB |
| **all** | **45** | **39** | **6,379** | **4,079 (63.9%)** | **219** | | | |

**Correction (2026-09-15):** the first version of this table claimed 6,037
justified (94.6%); the analysis script had counted the holes of proofs that
errored or timed out as justified. `justified` here is strict: holes of
proofs that finished elaboration and are no longer any trusted step in the
output (so it also excludes the elaborator's own residual trusted steps,
which `kept` does not count). The six proofs that produced nothing hold
1,958 of the 6,379 holes — the strongest argument for keeping partial results.

`ok` = the elaborated proof re-checks (valid or holey). Every `ok` proof's
reconstructed steps passed the checker; the holes that remain are exactly the
`kept` ones plus, in QF_LIA/QF_LRA, a few `arith_poly_norm_rel` shapes.

Why holes were kept (219): **killed at the 30 s hard budget 166** (QF_UF 117,
QF_LRA 48, QF_LIA 1), **memory limit 35**, **egglog could not prove 12**,
**no certificate found 6** (egglog proved it, the search found no replayable
chain). The hard budget held: no hole ran past ~30.2 s, and no worker took a
proof down with it.

The six non-`ok` benchmarks are not hole failures:

* 2 QF_LRA (`pd_not_sc_seen`, `pd_no_op_accs`) — **the up-front check of the
  original cvc5 proof fails** on a `rare_rewrite` step citing `ite-eq`, which
  `big.rare` lacks (rewrites.eo has it, but declares `t2 @T1` without a
  `(@T1 Type)` parameter, so that file does not parse). Fixed for the next run
  by `holes.rare` = big.rare + `ite-eq` (with `@T1` declared) + `distinct-false`.
* 2 QF_UF (`iso_icl850`, `iso_icl941`) — the original proof's `resolution`
  step is rejected ("pivot was not found in clause"): the cvc5-main resolution
  defect the alethe-lag notes already record; not reproducible with a main
  cvc5 without that branch's fix.
* 1 QF_LRA (`no_op_accs`, 203 holes, 379 s) — a reconstructed `evaluate` step
  was rejected by the checker (`(ite false x t) = t` is not what `evaluate`
  proves), and because that rejection happened on the main thread it failed
  the whole proof. `a6bf0d00` makes isolate mode keep such a hole instead.
  The `Evaluation` → `evaluate` mapping for `ite` with a constant condition
  is a real gap to fix (RARE's `ite-false-cond` is the right rule).
* 1 QF_LIA (`ring_2exp6_6vars`, 199 holes) hit the runner's 600 s elaborate
  cap: 199 holes at up to 30 s each over 4 workers is 1,492 s worst case.
  All partial work is lost on that path; a larger cap or per-hole result
  streaming would keep it.

Time per hole is dominated by the kills: QF_UF's 117 killed holes alone are
58 CPU-minutes of the run.

---

## 13. Runs `small2` and the partial-result design (2026-09-15)

`small2` = `small` with carcara `a6bf0d00` (a reconstruction the checker
rejects keeps its hole) and `holes.rare`:

| run | justified | ok | what changed |
|---|---|---|---|
| small | 4,079 / 6,379 (63.9%) | 39/45 | |
| small2 | **4,404 / 6,379 (69.0%)** | **41/45** | `no_op_accs` and `pd_no_op_accs` now `ok`; `pd_not_sc_seen` gets past the up-front check but hits the 600 s cap; `iso_icl850/941` unchanged (cvc5 resolution defect) |

The remaining non-`ok` proofs are exactly the lost-partial-work cases and the
cvc5 defect, which motivated the next changes (`3ba399fe`):

**`--hole-total-budget MS`** — a per-proof budget for all holes together.
Workers start no new hole past it, isolated children still running are
killed at it, and the proof is printed with whatever was justified in time;
holes never started are logged as `skipped`, holes cut short as `kept`. On the
43-hole QF_UF proof an 8 s budget returns in 8.1 s with 17 justified, 4 kept,
22 skipped, and the output re-checks.

**`--hole-check-only`** — the same workers and limits, but each child only
asks egglog whether the equality holds; nothing is reconstructed or spliced.
This separates *checking* (the thesis' RQ1 notion) from *elaboration*, which
is dearer and can fail where checking succeeds: on the 43-hole proof checking
proves 41, elaboration justifies 40 — the difference is a hole egglog proves
but the search finds no certificate for.

Per-hole verdicts and timings are logged at `info` (`hole t3: proved in
0.194s`, `hole t7: justified in 1.2s`, kept/skipped likewise) with a closing
`hole summary: total= proved|justified= kept= skipped= time=` line; the runner
reads that line. In every budgeted, isolated or check-only run a prepass
result is final for its hole — nothing is retried in-process.

`run-holes.sh` now does both passes per proof (check-only, then elaboration),
each under a 240 s hole budget and a 300 s safety net, cvc5 90 s, final check
120 s; new keys `upfront`, `chk_*`, `holes_skipped`, `elab_holes_time`.
Run `small3` is prepared with it.

---

## 14. Run `small3`: checking vs elaboration, partial results (2026-09-15)

Same 45 benchmarks; cvc5 60 s; two passes per proof with carcara `3ba399fe`,
four isolated workers, 30 s / 5 GB per hole, **600 s hole budget per pass**;
final `check` of the elaborated proof. Whole run ~30 minutes wall (the two
600 s proofs bound it). Results in `~/exp/results/egglog-holes/small3/`.

Two QF_UF proofs (`iso_icl850`, `iso_icl941`, 987 holes) still fail the
up-front check on cvc5-main's resolution defect; "attempted" below excludes
them. Every other proof is `ok` (43/45) — the two that lost everything to the
600 s cap in `small2` (`ring_2exp6`, `pd_not_sc_seen`) now return partial
results.

| logic | proofs ok | holes attempted | **checking: proved** | c-kept | **elaboration: justified** | kept | elab p50 |
|---|---|---|---|---|---|---|---|
| QF_LIA | 15/15 | 347 | 341 (98.3%) | 6 | 276 (79.5%) | 71 | 1.0 s |
| QF_LRA | 15/15 | 1,343 | 1,199 (89.3%) | 144 | 1,133 (84.4%) | 208 | 30 s |
| QF_UF | 13/15 | 3,702 | 3,634 (98.2%) | 68 | 3,413 (92.2%) | 146 | 111 s |
| **all** | **43/45** | **5,392** | **5,174 (96.0%)** | **218** | **4,822 (89.4%)** | **425** | |

`justified` is strict (no trusted step left for the hole); over all 6,379
holes it is 75.6%, up from 69.0% in `small2`. `skipped` is 0 everywhere: with
four workers the 600 s budget was never reached before every hole had been
started; the holes cut short at the budget are the 5 "proof's hole budget ran
out" kills (3 QF_LIA, 2 QF_LRA).

**What separating the passes shows.** Checking proves 352 more holes than
elaboration justifies (5,174 vs 4,822, 6.8% of the proved). The gap is almost
entirely time, not logic: reconstruction adds the e-graph snapshot and the
certificate search on top of egglog's run, and pushes holes that egglog alone
proves inside 30 s past the same bound. The clearest case is
`ring_2exp6_6vars` (QF_LIA, 199 holes): checking proves 195 in 108 s total;
elaboration justifies 131 in the full 600 s, 65 of its holes killed at 30 s.
The logic-level part of the gap is small: 6 "no certificate found" (egglog
proved it, no replayable chain), 2 reconstructions the checker rejected.

Kept-hole reasons across both passes: killed at the 30 s bound 480, memory
limit 126, egglog could not prove 24, no certificate 6, checker rejected 2,
proof budget 5. Peak memory 12.9 GB (QF_LRA), against the 24 GB job limit.

Against the thesis' RQ1 (single holes, 600 s / 8 GB, 0.5% sample): this
check pass, at 30 s / 5 GB with four workers, proves 96.0% of the attempted
holes, in the same range as the thesis' 90–99% per logic.

---

## 15. Where elaboration loses its holes: the snapshot (2026-09-15)

Per-hole analysis of `small3` (`~/exp/egglog-holes/perhole.py`), 5,389 holes
seen by both passes:

| | elaboration justified | elaboration kept |
|---|---|---|
| **checking proved** | 4,964 | **207** |
| checking did not prove | 0 | 218 |

The 207 holes checking proves but elaboration loses: 198 killed at the 30 s
bound, 6 no certificate, 2 checker-rejected, 1 proof budget. Memory kills are
63 in *both* passes — they happen in the egglog phase. Per finished hole,
elaboration costs 1.4–1.7x checking at the median but ~10x at p90 in the
arithmetic logics.

Phase attribution (child reports each phase; `4e0458d7`), re-running the two
proofs with the most losses locally under `small3`'s elaboration limits:

| proof | egglog | **snapshot** | search | emit | killed during |
|---|---|---|---|---|---|
| `ring_2exp6` (QF_LIA, 200 holes) | 29.6% | **69.7%** | 0.7% | 0.0% | snapshot 54, egglog 4 |
| `pd_not_sc_seen` (QF_LRA, 528 holes) | 38.2% | **57.8%** | 3.9% | 0.0% | egglog 42, snapshot 16 (+24 memory in egglog) |

For the 27 `ring_2exp6` holes whose snapshot took over 5 s, egglog took a
median 0.2 s and the snapshot a median 12.5 s (max 27.5 s): the equality is
proved almost instantly, then serializing the saturated e-graph
(`EGraphSnapshot::capture_production` → `egraph.serialize`) eats the budget.
The certificate search is never the problem.

Consequences:

* The elaboration-only losses are a **Carcara** problem — the full e-graph
  serialization — not an egglog one. The fix is to snapshot less: only the
  e-classes reachable from the goal terms (what the search actually walks),
  or a direct read of the e-graph without going through egglog's serializer.
  `MAX_SNAPSHOT_TUPLES` (4M) is far too loose to prevent this.
* An egglog 3.0 migration targets the *other* losses: the 63 memory kills per
  pass and QF_LRA's 42 egglog-phase kills (growth inside one iteration). It
  does not touch the snapshot cost, except indirectly by keeping e-graphs
  smaller.

## 16. The snapshot cost was egglog's serializer; fixed by vendoring 0.4.0 (2026-09-15)

§15 blamed the losses on "Carcara's full e-graph serialization". Splitting the
snapshot phase into egglog's `serialize()` and Carcara's indexing of its
output (`serialize` / `index` phases, `EGraphSnapshot::serialize_production`)
put the whole cost in egglog: indexing is ~0, and the serialized graphs are
small (a 1,452-node graph took 0.72 s, a 5,493-node one 10.8 s — ~2 ms per
node and super-linear). Instrumenting a vendored copy of egglog 0.4.0
(`EGGLOG_SERIALIZE_STATS`) showed the time entirely inside the per-node loop,
with no stale-row problem (`offsets ≈ live`, 175 tables, 28.5k live rows).

The cause, in `src/serialize.rs::serialize_value`: to print a *primitive*
value (an `i64`, a big rational, a string) egglog constructs a fresh
`Extractor` — whose `new` runs `find_costs`, a fixpoint cost computation over
**every row of every function in the e-graph** — for every primitive node it
emits, then calls the sort's `extract_term`, which for primitives never looks
at the extractor. Polynomial e-graphs are full of coefficient primitives, so
serialization was (#primitive nodes) × (#rows): quadratic. (3.0 serializes
through a different path but exposes no row iteration publicly either, so
migrating would not have been the shorter route — see the 20:02 status.)

**Fix:** `third-party/egglog-0.4.0/` is the released crate with one change
(`serialize-one-extractor.patch`): one `Extractor` built lazily per
`serialize` call, shared by all primitive nodes; `Cargo.toml` selects it via
`[patch.crates-io]`. The crate's tests/benches are left out
(`CARCARA-PATCHES.md`). Serializing a 1,452-node graph went from 0.72 s to
0.002 s; a 70k-node graph takes 0.22 s.

**Validation on `ring_2exp6`** (QF_LIA, 200 holes; local, `small3`'s
elaboration limits: 4 isolated workers, 30 s / 5 GB per hole, 600 s per
proof; `~/exp/egglog-holes/local/fix-ring.sh`, output `*.fix.err`):

| | before (§15) | after |
|---|---|---|
| justified / kept | 142 / 58 | **197 / 3** |
| pass time | 566 s | **91 s** |
| killed during | snapshot 54, egglog 4 | egglog 3 |
| phase share: egglog / serialize / index / search | 29.6 / 69.7 (snapshot) / – / 0.7 % | 89.9 / 6.6 / 1.2 / 2.3 % |
| serialize p50 / p90 / max | 0.48 / 10.9 / 27.5 s | 0.006 / 0.145 / 3.2 s |

The elaborated proof (4 holes left, 172 `poly_simp`, 20 `rare_rewrite`,
12 `evaluate` steps) re-checks `holey`. The three remaining kills are the
egglog phase itself (saturation past 30 s), the same holes checking loses.
Elaboration now costs what checking costs plus a few percent, so the
"proved & kept" column of §15's 2×2 (207 holes, 198 of them 30 s kills)
should mostly vanish on the next cluster run (`small4`, same parameters as
`small3`); what remains for both passes is the egglog-phase losses (memory,
saturation blow-up), which are the egglog 3.0 question.

The `reconstruction` tests pass against the vendored crate. `cargo build`
prints four `hiding a lifetime` warnings from the vendored `gj.rs`; they are
upstream's, untouched.

## 17. Run `small4`: the serializer fix on the cluster (2026-09-15)

Same sample, parameters and runner as `small3` (§14); carcara `e7f7b048`
(vendored egglog 0.4.0 with the one-extractor serializer, §16). Results in
`~/exp/results/egglog-holes/small4`; 16 min wall for the whole run. Checking
is unchanged by the fix and reproduced exactly (5,174 proved, same kept
reasons); elaboration:

| logic | holes | proved | justified small3 → **small4** | kept small3 → small4 | elab max / proof small3 → small4 |
|---|---|---|---|---|---|
| QF_LIA | 347 | 341 | 276 → **341** | 71 → 6 | 600 s → 115 s |
| QF_LRA | 1,343 | 1,199 | 1,133 → **1,190** | 208 → 151 | 600 s → 469 s |
| QF_UF | 4,689 | 3,634 | 3,413 → **3,489** | 146 → 70 | 271 s → 162 s |
| all | 6,379 | 5,174 | 4,822 → **5,020** | 425 → 227 | |

Of the 5,392 holes the passes attempted (two QF_UF proofs still fail upfront,
987 holes, as before): checking proves 96.0%, elaboration now justifies
**93.1%** (was 89.4%); 43/45 proofs `ok`. No proof hit the 600 s budget in
either pass (`skipped=0`, no proof-budget kills).

Per hole (§15's 2×2), 5,389 holes seen by both passes:

| | elaboration justified | elaboration kept |
|---|---|---|
| **checking proved** | 5,162 (was 4,964) | **9** (was 207) |
| checking did not prove | 0 | 218 |

The 9: 6 no certificate, 2 checker-rejected, 1 killed at 30 s (QF_UF, in
the search). The 198 snapshot-time losses are gone. Elaboration now costs
1.15–1.33x checking at the median and ≤1.45x at p90 (was ~10x at p90 in the
arithmetic logics); per finished hole the phases are egglog 74–90%,
serialize 5–11%, search 4–12%, index ≤2.4%.

What remains is the same in both passes and is all the egglog phase:
killed at 30 s 140/144 (chk/elab), memory limit 66/63, egglog could not
prove 12, i.e. saturation that blows up inside one egglog iteration
(QF_LRA: 99 of its 144 egglog-phase kills). That is the egglog 3.0 question
(§9, §15): a scheduler-bounded saturation and smaller e-graphs, not anything
on the reconstruction side.

## 18. The full run: design (2026-09-15)

Every unsat-status benchmark of QF_UF, QF_LIA and QF_LRA — the alethe-core
sets (`benchmark_set_unsat_<LOGIC>`, SMT-LIB 2025 catalog): 4,361 + 4,748 +
703 = **9,812 benchmarks**, copied to `~/exp/egglog-holes/sets/` from the
alethe-core task list. Runner `run-holes.sh` (per-pass parameters), submit
script run `full`:

| stage | limit |
|---|---|
| cvc5 solve + Alethe proof (theory-rewrite granularity) | `--tlimit` 60 s, external kill 75 s |
| counts as unsat only if the proof is complete | exit 0, last step `(cl)`, closing `)` printed (`proof_complete`) |
| checking pass (4 isolated workers) | **600 s for the whole pass**, 30 s and 5 GB per hole |
| elaboration pass (4 isolated workers) | **900 s for the whole pass**, 45 s and 5 GB per hole |
| re-check of the elaborated proof | 180 s |
| SLURM: quad, `-j 2`, 4 cpus, 24,000 MB, wall | 2,000 s |

"For the whole pass" is now literal: `--hole-total-budget` is a deadline
counted from the CLI's start (`elaborate_command` takes the clock before
parsing), so parsing and checking the non-hole steps come out of the same
budget; a 5 s budget on `ring_2exp6` ends the run at 5.02 s wall with
25 proved, 4 kept, 171 skipped. The external `timeout` per pass (660 s /
990 s) is only a safety net.

Expected yield, from the alethe-core cvc5 run (120 s `tlimit`, dsl-rewrite
granularity) restricted to proofs delivered within 60 s: QF_UF 4,245,
QF_LIA 2,526, QF_LRA 499 — about **7,270 proofs** (74%), the rest
sat/unknown/timeouts costing ≤ 75 s each. Proof sizes are much larger than
the small samples' (QF_UF p50 18.6k steps, p90 136k), so the pass budgets
will bind often. Wall-time estimate on 48 slots (24 nodes × 2): 11 h at a
250 s mean per proof task, 26 h at 600 s, hard cap 84 h if every proof task
ran to its 2,000 s limit.

## 19. The full run: results (2026-09-16)

Submitted 2026-09-15 19:52 (cluster time), aggregator stopped 2026-09-16
13:21: about 17.5 h wall, of which the first hours ran on a handful of
slots because the `max2` QOS pool was shared with other jobs; 48 slots for
the rest. Binary: static build of `444621fa` (before the two fixes of
`49c3e518`, see the end of this section). Results in
`~/exp/results/egglog-holes/full/` (`results.json.gz`, 125 MB);
`analyze.py`, `perhole.py` and the task-level script used here are in
`~/exp/egglog-holes/`.

### Yield

| logic | tasks | complete proofs | proofs with an `ok` end-to-end | holes | holes per proof p50 / p90 / max |
|---|---|---|---|---|---|
| QF_UF | 4,361 | 4,326 | 4,126 | 2,421,863 | 553 / 828 / 5,136 |
| QF_LIA | 4,748 | 2,542 | 2,495 | 5,528,247 | 47 / 2,617 / 104,276 |
| QF_LRA | 703 | 537 | 515 | 4,395,839 | 595 / 27,520 / 117,845 |

"Complete" is the `proof_complete` criterion of §18; no cvc5 run that
exited 0 printed a truncated proof. The proofs that did not reach `ok`:
QF_UF 198 upfront failures (all `pivot was not found in clause`, the
QG-classification `iso_*` family: a cvc5 resolution-pivot problem, not
ours), 1 checking-pass timeout, 1 re-check timeout; QF_LIA 5 upfront
failures (2 pivot, 3 unspecific), 29 checking-pass external timeouts
(660 s), 4 elaboration external timeouts (990 s), 9 re-check timeouts
(180 s); QF_LRA 7 upfront (pivot), 15 checking-pass external timeouts.
The external timeouts fire when the pass deadline expires inside a step
the budget cannot interrupt (parsing, or the non-hole checking of a proof
with hundreds of thousands of steps). Five QF_LIA tasks
(`30_Function_Pointer3_vs-O0`, `SpamAssassin-loop-O0`, `cggmp2005_variant-O0`,
`linear-inequality-inv-a-O0`, `prp-3-18`) hit the 24 GB job limit before
printing anything, so they count as cvc5 failures.

### Holes: the budgets bind on the arithmetic logics

| logic | checking: proved / kept / skipped | elaboration: justified / kept / skipped |
|---|---|---|
| QF_UF | 2,266,130 / 31,762 / 15,865 | 2,194,555 / 33,290 / 14,638 |
| QF_LIA | 1,574,011 / 23,028 / 3,921,150 | 1,626,925 / 26,638 / 3,790,597 |
| QF_LRA | 380,758 / 19,837 / 3,685,946 | 434,653 / 23,985 / 3,618,144 |

Skipped means the pass budget (600 s / 900 s) ran out before the hole was
tried. The skipped mass is concentrated in a few hundred giant proofs:

| logic | proofs that hit the checking budget | holes in them | share of the logic's holes in proofs > 10k holes |
|---|---|---|---|
| QF_UF | 10 | 24,480 | 0% |
| QF_LIA | 225 | 4,549,797 | 74% (104 proofs) |
| QF_LRA | 244 | 4,032,981 | 88% (107 proofs) |

Families: QF_LIA `rings` and `rings_preprocessed` alone hold 2.8 M holes,
of which 2.56 M were kept or skipped; QF_LRA `uart`, `sc`, `LassoRanker`
and `UltimateInvariantSynthesis` similar. Whatever the pass budget, a
proof with 100k holes at 0.2 s each needs 5.5 CPU-hours per pass.

Among the holes that were actually attempted the picture is the same as
in the small runs:

| logic | attempted (checking) | success | attempted (elaboration) | success | proofs left hole-free |
|---|---|---|---|---|---|
| QF_UF | 2,297,892 | 98.6% | 2,299,119 | 98.6% | 505 of 4,326 |
| QF_LIA | 1,597,039 | 98.6% | 1,700,833 | 98.4% | 1,258 of 2,542 |
| QF_LRA | 400,595 | 95.0% | 468,397 | 94.9% | 130 of 537 |

Per-hole time (holes the pass finished): checking p50 0.22 s (QF_LIA),
0.23 s (QF_LRA), 0.09 s (QF_UF); elaboration 1.2× to 1.33× checking at
the median. Phase shares of elaboration time: egglog 71% (QF_UF) to 85%
(QF_LIA), serialize 5.5% to 14% (QF_UF), search 9% to 11%, index and
emit under 3%. The serializer fix (§16) holds: only 255 holes were killed
in the serialize phase across the run, 32k in the egglog phase.

### Why holes are kept (per pass, all logics)

| reason | checking | elaboration |
|---|---|---|
| killed at the per-hole limit (30 s / 45 s) | 40,932 | 30,568 |
| killed at the 5 GB per-hole memory limit | 24,391 | 39,805 |
| egglog could not prove (saturated, goal not reached) | 6,667 | 7,329 |
| killed by the pass budget while running | 1,905 | 1,791 |
| no certificate found in the snapshot | 2 | 2,960 |
| independent checker rejected the reconstruction | – | 544 |
| worker errors (below) | 63 | 120 |

So 96% of the kept holes die inside egglog's saturation, by time or by
memory, exactly the loss profile of §17 and EGGLOG-3-ROUTE.md; the
reconstruction side (no certificate + checker rejected + decode) is 3.5k
of 83k in the elaboration pass. Holes proved by checking but kept by
elaboration: 3,919 of 4.14 M proved (0.09%), mostly `no certificate`
(2,711) and `checker rejected` (525).

Worker errors, all reproducible offline:

* 120 `identifier 'x' is not defined`: holes under `bind` anchors that
  bind variables. In these quantifier-free logics that comes from
  parameterized `define-fun`: cvc5 keeps `f` as
  `(= f (lambda ((x Int)) body))` and rewrites the body under an anchor
  with `:args ((x Int) (:= (x Int) x))`. Fixed in `49c3e518` (the hole's
  problem text declares the anchor-bound variables). Affected: 13 QF_LIA
  `2019-ezsmt/incrementalScheduling` benchmarks; parameterized
  `define-fun` exists in 23 QF_LIA and 19 QF_LRA benchmarks of the sets,
  none in QF_UF. Minimal reproducer: `define-fun-anchor.smt2` +
  `.smt2.alethe` in the repo root (untracked), fixture
  `tests/rare/elaborate/anchor-vars.smt2`.
* The same `define-fun` applications also produce one beta-reduction hole
  each, `(= ((lambda ((x Int)) body) a) body[a/x])`. The engine has no
  beta reduction: `Term::App` names the egglog function after the head's
  printed text, so the lambda-headed application is an opaque symbol and
  the goal is unreachable. With the goal unreachable the rewrite ruleset
  does not saturate: the seed rules that build `(= t s)` for every pair
  of available terms feed `eq-symm`/`arith-eq-elim` → `and` of `>=`/`<=`
  → `arith-elim-leq`/`arith-leq-norm`/`arith-geq-norm1`, whose outputs
  become available and pair up again; quadratic growth per iteration
  (160 → 4,421 eq-elim matches in two iterations) and a memory kill after
  ~10 s. Open. Cheapest fix: refuse lambda-headed goals up front; right
  fix: substitute the parameters before encoding.
* 29 panics at `search.rs:1087` (`a reconstructed certificate must pass
  the independent checker`): now a warning that keeps the hole
  (`49c3e518`).
* 29 `a certificate term failed to decode`, 6 `Illegal merge attempted
  for function to_formula` (QF_UF), 59 `e-graph too large to capture`
  (QF_LIA): open.

### What a rerun should change

1. The static binary must be rebuilt from `49c3e518` or later.
2. The pass budgets are the wrong knob for the arithmetic logics: 3.9 M of
   5.5 M QF_LIA holes and 3.7 M of 4.4 M QF_LRA holes were never tried.
   Either accept that (report per-hole rates over attempted holes, which is
   what the small runs measured) or cap the proof size and give the giant
   proofs their own run with a budget proportional to the hole count.
3. The re-check limit (180 s) is too short for the elaborated giant
   proofs (10 timeouts); the external pass timeouts (49) mean the
   `--hole-total-budget` deadline needs to be observed inside the non-hole
   checking too.
4. The 24 GB job limit was hit by 5 tasks before cvc5 finished; either
   raise it or accept those as cvc5 failures.
