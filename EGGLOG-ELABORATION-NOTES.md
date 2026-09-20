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

### 19.1 Two corrections found while writing the report (2026-09-16)

**"Justified" overstates.** `QF_UF_h_b05_ab_reg_max` (2018-Goel-hwbench):
25 holes, summary says 22 justified, 3 kept, but the elaborated proof has
4 `hole` steps. Hole t133, `(= (and X true) X)`, is emitted as a subproof
whose only step is `:rule hole :args ("TRUST_THEORY_REWRITE" "gen-14")`:
the certificate used one of the unconditional egglog rewrites of the
generated program that is not a named RARE rule (the n-ary `and`/`or`
normalisations; `rules_from_generated_program` names them `gen-N`), and
the emitter has no Alethe step for it, so it emits a hole. Counting the
hole steps left in the emitted proofs minus kept minus skipped gives the
residual: QF_UF 71,009 (3.1% of the closed holes), QF_LIA 1,992, QF_LRA
4,457. The honest elaboration rate over attempted holes is therefore
95.5% / 98.3% / 93.9% (checking: 98.6 / 98.6 / 95.0). The report and
`make-report.py` count these as "closed with a gen hole".

**Time/memory kills are largely unreachable goals.** The three kept holes
of the same proof are `(= (or X true) true)`, `(= (and true true true X) X)`
and `(= (= false X) (not X))`; two died at the memory limit. Both
identities, run as isolated holes, blow 3 GB in ~10 s. `holes.rare` has 27
`bool-*` rules and no `bool-or-true`, `bool-and-true` or flattening, so
the goal is unreachable, and an unreachable goal triggers the quadratic
pair-equality growth described for the beta-reduction holes. So the 70k
kills per pass are not evidence of hard holes; a to-be-measured share are
rule-coverage gaps. Two cheap checks: add the missing Boolean rules and
re-run the kept holes of a sample; make an unreachable goal fail fast
(bound the pair seeding or check the goal before the open ruleset).

Report: `~/exp/egglog-holes/report/report.pdf` (`make-report.py` renders
every table and plot from `results.json.gz`).

## 20. Batching hole justifications (2026-09-16)

Question: does batching holes the way the skeletons paper batches theory
lemmas (one query for a disjunction of k lemmas, batch size 50) help the
hole engine attempt more holes within a budget?  Two designs were built
behind `--hole-batch N` (checking pass only), both grouping holes that
share their assumptions into batches of N in proof order, one child per
batch, and retrying a batch's holes one by one when the batch dies:

* **Shared e-graph** (commit `c91fd8ec`): the batch's goals go into one
  e-graph, saturated once, every open goal checked after each round.
  Budget `--hole-batch-timeout`, default 4× the per-hole one.
* **Sequential** (`--hole-batch-sequential`, commits `b05cea24`,
  `2d8e846a`): the child prepares the rule database once and checks its
  holes one at a time, each in its own e-graph, printing each verdict as
  it is reached; a watchdog kills a hole at the per-hole budget, and a
  killed child loses only the holes it had not reached.

Sample: 10 arithmetic proofs of the full run with 1k–4.5k holes that the
run had fully attempted (7 QF_LIA: c_inference, FISCHER9, ring_2exp10,
cut_lemma_01_008, SMPT RwMutex RF-09, MULTIPLIER_3, bofill ex4880; 3
QF_LRA: vpm2-0, clocksynchro_3clocks, tgc_io-safe-6), re-proved locally
(cvc5 1.3.4.dev, same flags), 29,479 holes.  Local machine, 8 cores, two
runs at a time, each with 4 workers, 30 s and 3 GB per hole.  Runner and
logs: `~/exp/egglog-holes/batch/` (`run-batch-exp.sh`, `run-seq-exp.sh`,
`summarize.py`, `results/`).

### The fixed cost of a hole

A child on a trivial goal (`a = a`) takes 0.18 s; with an empty RARE file
0.01 s.  So the 163-rule database (its egglog program, and the per-rule
overhead of each saturation round even with nothing to match) is most of
a median hole (0.17–0.25 s).  That is the amortizable part; the rest is
the goal's own saturation.

### Shared e-graph: a loss at every size

Three-proof subset with every size run (c_inference, FISCHER9, vpm2;
7,750 holes; verdicts identical in all configurations, 7,682 proved):

| batch | wall s | failed batches | holes in them |
|---|---|---|---|
| 1 (per hole) | 571 | 0 | 0 |
| 10 | 1,351 | 59 of 777 | 586 |
| 50 | 1,403 | 58 of 156 | 2,850 |
| 100 | 1,594 | 40 of 79 | 3,850 |
| 500 | 1,113 | 16 of 17 | 7,250 |
| 1000 | 896 | 10 of 10 | 7,750 |

Two effects.  Batches die, mostly at the 3 GB limit, after 60–70 s, and
their holes are redone one by one.  And batches that succeed are slower
than their holes alone: on RwMutex the successful batches of 10 took 21 s
at the median where the ten holes take ~9 s (RwMutex and bofill at size
10 were stopped after 30 min with 51 of 216 and 39 of 236 batches failed;
their baselines are 8 and 7 min).  The goals interact: every goal's
subterms are available to every rule, and the pair-equality seed rules
(§19.1) grow quadratically in the available terms, so the batch's
saturation costs more than the sum of its holes and blows up where none
of them would.  At 500 and 1000 every batch dies within a minute or two
and the run is the baseline plus that.  Batching holes in one e-graph is
therefore out, at least while the seeding is what it is.

### Sequential batches: the amortizable cost is small

Sequential batches of 10 on all ten proofs (`results/*.b10s.err`, final
binary with the watchdog and the death attribution):

| proof | holes | per hole (s) | sequential 10 (s) |
|---|---|---|---|
| c_inference | 2,143 | 131 | 114 |
| RwMutex RF-09 | 4,343 | 471 | 449 |
| bofill ex4880 | 2,517 | 437 | 435 |
| MULTIPLIER_3 | 3,374 | 460 | 486 |
| FISCHER9 | 2,116 | 193 | 200 |
| cut_lemma_01_008 | 1,944 | 704 | 722 |
| ring_2exp10 | 3,818 | 269 | 230 |
| vpm2-0 | 3,491 | 246 | 280 |
| clocksynchro_3clocks | 1,663 | 480 | 551 |

Gains of 5–16% where the holes are cheap (c_inference, ring), nothing
outside this machine's ±10% noise elsewhere.  A micro-test says why: 20
copies of `(< a i) = (not (>= a i))` cost 1.4 s sequentially against
0.21 s each alone, but 20 copies of an arithmetic normalization goal cost
10.0 s against 0.51 s each: nothing amortized.  A trivial goal's program
has 397 rules and 3 schedule runs; an arithmetic goal's has 681 rules, 183
functions and 63 schedule runs, 58 of them iterations of the polynomial
normalizer, all declared and run per goal (`declare_goal_eliminations`,
`declare_opaque_arith_poly_rules`, the `arith_poly` fallbacks).  The
sequential mode removes the 0.14 s database cost and nothing else.

### Overlap grouping (commit `90334e2e`)

`--hole-batch-by-overlap [--hole-batch-terms CAP]`: a hole joins the open
batch of its context sharing the most compound subterms (16 open batches
per context), closed at the hole count or the distinct-subterm cap.
Measured potential first (`overlap.py` over the proof texts): distinct
subterms over summed subterm occurrences is 0.10–0.33 per proof, but
0.71–0.82 in proof-order batches of 10, and adjacent holes share nothing
at the median on three of five proofs.  Results on the subset (7,750
holes, `results-overlap/`):

| configuration | wall s | failed batches | sharing achieved |
|---|---|---|---|
| per hole | 571 | 0 | – |
| proof order, 10 | 1,351 | 59 | 0.74–0.82 |
| overlap, up to 10 | 992 | 42 | 0.59–0.77 |
| overlap, up to 50 / 100 / 500 / 1000 | 1,237 / 1,246 / 1,086 / 1,126 | 40–42 | 0.39–0.75 |
| overlap, cap 30 / 60 / 120 subterms | 928 / 1,291 / 1,071 | 54 / 54 / 42 | 0.74–0.80 / 0.58–0.76 / 0.40–0.75 |

Only c_inference gains (109 s at up to 10, 92 s at cap 30, against 131 s);
FISCHER9 (56 hopeless holes) and vpm2 lose everywhere.  The greedy pass
makes batches of 3–4 holes and 10–17 distinct subterms and reaches
sharing 0.4–0.8, far from the proof's 0.1–0.3; and a batch inherits its
worst hole: every batch with one of FISCHER9's hopeless holes dies at the
memory limit after 20–30 s and is retried.

### Conclusion

No batching for the next run.  The costs a batch could amortize are
small (the database) or not shared (the per-goal arithmetic machinery),
and the shared e-graph turns every unreachable goal into a dead batch.
The same losses are attacked directly by making an unreachable goal fail
fast (§19.1) and by adding the missing Boolean rules; after that, overlap
batching may be worth re-measuring as a pure hash-consing gain.

### Fail-fast attempt 1: seed conditional rules' premises from the goal only (commit `29e4f7f3`)

`--rare-seed-from-goal` (`--seed-from-goal` for the hole worker): the
premise instances of conditional RARE rules (`create_avaliable_premise`,
e.g. `((Avaliable i1) (Avaliable j1)) → (Mk (@= i1 j1))` for
`array-read-over-write2`'s premise) range over an `Origin` relation that
holds the goal's sides, the proof premises and their subterms, asserted
per goal and never propagated, instead of over every available term.
Check-only pass on the ten sample proofs (`scratchpad batch/seed/`):

| proof | per hole (s) | seed-from-goal (s) | verdicts |
|---|---|---|---|
| c_inference | 131 | 101 | same |
| RwMutex RF-09 | 471 | 459 | same |
| bofill ex4880 | 437 | 377 | same |
| MULTIPLIER_3 | 460 | 518 | same |
| FISCHER9 | 193 | 125 | same |
| cut_lemma_01_008 | 704 | 712 | same |
| ring_2exp10 | 269 | 299 | same |
| vpm2-0 | 246 | 240 | same |
| clocksynchro_3clocks | 480 | 426 | 6 fewer proved |
| tgc_io-safe-6 | 373 | 307 | 3 fewer proved |

5% less time overall, up to 35% on the proofs with many equalities in
their goals, but 9 provable holes lost: linear normalizations such as
`(<= t 0) = (>= (- t) 0)`, proved in 0.6 s by the baseline through a
conditional rule whose premise is instantiated over a term the
polynomial normalizer produces; with the seeds restricted that path is
cut, the goal is unreachable, and it then dies at the memory limit.  Not
verdict-preserving, so not for the next run as it stands.

**The blow-up's real driver is sort-blind rule application.**  With the
seeds bounded, the debug trace of `(or x true) = true` still shows
`arith-eq-elim` firing 12k times on a goal whose only equality is over an
uninterpreted sort, `bool-not-eq-elim` turning `(not (= x y))` into new
equalities `(= x (not y))`, and the arithmetic normalizers rewriting the
resulting nonsense `>=` terms, round after round.  The encoding has one
untyped `Term` sort; the Int/Real/Bool parameter sorts of the RARE rules
are never checked.  With the arith/bv/str/array/set/seq rules removed
from the file (68 rules left) both Boolean goals fail in 0.19 s.  The
fail-fast to build is therefore **sort guards**: a sort relation on
classes, seeded from Carcara's sorts for the goal's subterms and
propagated by operator heads and declared function result sorts
(`application_result_sort`), with a guard premise on every rule parameter
declared Int, Real or Bool (`TypeParameter::sort`).  About a day; it also
removes the ill-sorted terms from every reachable goal's saturation.

The 8 GB shared-batch run was stopped after its first result
(c_inference, batches of 10, 300 s budget: 146 s against 131 s) with
FISCHER9 at 146 good and 36 dead batches; more memory only lets a doomed
batch take longer to die.

### What the ACI normalization covers, and the Boolean gaps (2026-09-17)

Isolated holes, `holes.rare` (163 rules) against the same file without the
arith/bv/str/array/set/seq rules (68 rules):

| identity | full file | without arith |
|---|---|---|
| nested `and`/`or` flattening (3 forms) | proved 0.06 s | proved 0.03 s |
| `(or p p) = p`, `(or p q p) = (or p q)`, `(and p) = p` | proved | proved |
| `(and p true) = p` | proved | proved |
| `(= false p) = (not p)`, `(= p true) = p`, `(ite true p q) = p`, `(=> p q) = (or (not p) q)` | proved | proved |
| `(and true true true p) = p` | fails 6.3 s | fails 0.10 s |
| `(or p true) = true` | fails 6.6 s | fails 0.08 s |
| `(and p false) = false` | fails 0.5 s | fails 0.07 s |
| `(not (and p q)) = (or (not p) (not q))` | fails 1.9 s | fails 0.17 s |

The ACI rules (`aci_norm.rs`) handle flattening, duplicates, singletons
and the two-element identity form `(op x identity)`; in the `Assoc` set
representation the identity stays an element, so `(and true true true p)`
stops at `{true, p}`.  Missing: list-form identity elimination
(`bool-and-true`, `bool-or-false`), absorbing elements (`bool-or-true`,
`bool-and-false`) and De Morgan (`bool-not-and`, `bool-not-or`), all in
cvc5's `rewrites.rare` and absent from `holes.rare`.  The b05 proof's
kept holes were the first two: coverage gaps, not engine limits.  Fix:
add the six rules to the file (list-form rules already work, cf.
`bool-xor-*` and the bv rules) or extend the ACI identity rule to the set
form plus an absorbing-element rule.  The timing column repeats the
sort-blindness point: the same unprovable goal fails in 0.1 s without the
arithmetic rules and takes 6 s to die with them.

## 21. ACI identities, sort guards, growth bound (2026-09-17)

Three engine changes from the full run's loss analysis (§19.1, §20),
measured with the check-only pass on the ten sample proofs of §20
(baseline: per hole, 4 workers, 30 s / 3 GB per hole, `results/*.b1.err`;
today's passes ran two at a time with one job each under heavy load from
another worktree's experiment, so only verdicts are compared).

### ACI identity and absorbing rules (commit `1c280cd5`)

The ACI normalization handled flattening, duplicates, singletons and the
two-element identity form only; three `list-ruleset` rules on the set form
(`(op (Assoc s))`, which the conversion unions into the formula's class
without `Mk`) now remove an identity element from the set, collapse the
empty set to the identity, and collapse a set holding the absorbing
element to it.  `(and true true true p) = p`, `(or p true) = true` and
`(and p false) = false` are proved in ~0.1 s where they died at the memory
limit.  The reconstruction has no certificate kind for the set-form rules,
so in the elaboration pass these holes are proved by egglog but come out
as no-certificate holes, like the other ACI steps (`gen` holes, §19.1).
De Morgan stays out: cvc5's `bool-and/or-de-morgan` are `define-rule*`
fixed-point rules with a context hole, which Carcara's RARE format does
not have, and no hole of that shape occurs in the 29k holes of the sample.

### Sort guards (commit `58bc6945`, `--rare-sort-guards`)

The blow-up driver of §19.1/§20 was sort-blind rule application (one
untyped `Term` sort).  Relations `SortInt`/`SortReal`/`SortBool` on
classes, seeded from the goal's and the premises' subterms (sort computed
structurally from the term: constants, variables' declared sorts, the
operator table, declared function result sorts), propagated by rules per
declared function (Bool for the logical and comparison operators, Real for
`/` and `to_real`, Int for `to_int`/`div`/`mod`, the first argument's sort
for `+ - * abs`, the then-branch's for `ite`, the declared result sort for
uninterpreted functions, and the constants the rewrites produce), and a
guard premise on every non-list Int/Real/Bool rule parameter the LHS
binds.  Named rewrites keep their name with the guards as conditions; the
reconstruction strips the guard facts when reading the rules back, so
elaboration and re-check work unchanged.  Micro-tests: the unprovable De
Morgan goal fails in 1.4 s instead of 6.2 s (still not milliseconds: the
Boolean rules keep growing the e-graph within their sort), the arithmetic
micro-goal drops from 0.51 s to 0.28 s.

### Verdicts on the sample

| proof | baseline proved / kept | ACI only | ACI + guards |
|---|---|---|---|
| c_inference | 2,143 / 0 | 2,143 / 0 | 2,143 / 0 |
| RwMutex RF-09 | 4,339 / 4 | 4,339 / 4 | 4,339 / 4 |
| bofill ex4880 | 2,497 / 20 | 2,513 / 4 | 2,513 / 4 |
| MULTIPLIER_3 | 3,374 / 0 | 3,366 / 8 (load) | 3,370 / 4 (load) |
| FISCHER9 | 2,060 / 56 | 2,116 / 0 | 2,116 / 0 |
| cut_lemma_01_008 | 1,881 / 63 | 1,879 / 65 (load) | 1,879 / 65 (load) |
| ring_2exp10 | 3,818 / 0 | 3,818 / 0 | 3,818 / 0 |
| vpm2-0 | 3,479 / 12 | 3,479 / 12 | 3,479 / 12 |
| clocksynchro_3clocks | 1,615 / 48 | 1,622 / 41 | 1,658 / 5 |
| tgc_io-safe-6 | 778 / 64 | 807 / 35 | 807 / 35 |
| total kept | 267 | 169 | 129 |

"(load)" marks losses that are holes at 16–29 s in the baseline killed at
30 s under the day's doubled load, not verdict changes.  The ACI rules
recover FISCHER9's 56, bofill's 16 and tgc's 29; the guards add
clocksynchro's 36 (and 4 on MULTIPLIER).  No hole the baseline proved
comfortably was lost.

### Normalizer in the baseline: measured and rejected

Preparing the polynomial normalizer's rules (goal-independent, in their
own rulesets) once per child instead of per goal was implemented and
measured on the micro-goals: non-arithmetic holes went from 0.09–0.13 s to
0.19–0.25 s (every hole clones a bigger baseline e-graph) and the
arithmetic hole did not change (0.5–0.7 s either way: its cost is the
normalizer's ~60 iterations, not the declaration).  Reverted; the note
stays in `prepare_database`.

### Growth caps and the soft memory cap (commits `1aac6c13`, `04f36c2b`)

Calibration (in-process pass logging each goal's tuples after loading and
at the end, by class): a goal's e-graph holds 17–120 tuples after its
program is loaded; provable goals without the normalizer end below 400
tuples on cut_lemma and tgc but at 25k–45k on tgc's large Boolean
formulas; provable goals with the normalizer end at a median of ~500,
p99 208k, max 348k (cut_lemma).  So a factor on the initial size means
nothing and the caps are absolute, per class: `--rare-growth-cap-arith`
(1,000,000 used) and `--rare-growth-cap-plain` (200,000; a first try at
20,000 lost five provable tgc goals), checked after every statement and
saturation step.  `--rare-memory-soft-cap MB` fails a goal when the
worker's resident set passes the cap between statements; at 1,000 MB it
never fired: the memory deaths are single 4 GB allocations (a table or
container doubling) inside one statement, at a modest tuple count, so
neither cap sees them coming.

Final configuration (guards + ACI rules + caps 1M/200k + soft cap 1 GB),
check-only, isolated, 4 workers, 30 s / 3 GB per hole, machine lightly
loaded, against the unloaded baseline:

| proof | baseline proved / kept, wall s | final proved / kept, wall s |
|---|---|---|
| cut_lemma_01_008 | 1,881 / 63, 704 | 1,881 / 63, 500 |
| tgc_io-safe-6 | 778 / 64, 373 | 807 / 35, 162 |
| clocksynchro_3clocks | 1,615 / 48, 480 | 1,659 / 4, 171 |
| FISCHER9 | 2,060 / 56, 193 | 2,116 / 0, 81 |
| MULTIPLIER_3 | 3,374 / 0, 460 | 3,374 / 0, 304 |
| vpm2-0 | 3,479 / 12, 246 | 3,479 / 12, 205 |
| total | 243 kept, 2,456 s | 114 kept, 1,423 s |

Verdicts: 129 holes recovered, none lost.  Time: 42% less on these six,
from three sources: the guards (fewer rules fire per round), the
identities (holes that ran to the kill now close in 0.1 s), and the
tuple cap (on cut_lemma 18 of the 63 hopeless holes stop at the cap
instead of 30 s; 28 still run to 30 s in small but slow e-graphs, 17
still die at the memory limit).  What remains for the hopeless holes is
therefore a bound on rule work per round rather than on size, and a
memory check inside a statement (an allocator hook or egglog 3.0's
scheduler), not more caps of this kind.

### Ground `and`/`or` calls as unions (commit `fc3e2100`, from the egglog-3 branch)

`aci_call_rules` emitted, for every concrete `and`/`or` call of the step,
a rewrite whose left-hand side is the ground call itself: matched at most
once, searched on every iteration of the default ruleset, one rule per
call.  The egglog-3 work found it (there the search is a join and took
21 s per iteration on one hole; `wt-egglog/EGGLOG-ACI-GROUND-CALLS.md`)
and replaced it with a `(union lhs rhs)` at load time; on this branch the
groundness test is `Literal(_) => false` (the globals are unprefixed and
never occur inside a step's call).  Measured on four QF_UF proofs of the
`chk1200` run, same settings (8 workers, 1200 s, 60 s and 8 GB per hole,
guards and caps), against the run's own numbers:

| proof | chk1200 kept, pass s | union kept, pass s |
|---|---|---|
| gensys_icl072 | 19, 156 | 18, 34 |
| iso_icl054 | 18, 160 | 9, 27 |
| iso_icl942 | 14, 142 | 4, 10 |
| iso_icl946 | 13, 183 | 3, 11 |

Five to fifteen times faster passes on QG-classification (long `and`/`or`
chains), half to a quarter of the kept holes.  `chk1200` itself ran the
binary without it.

## 22. Fewer holes to check: hoist and prune, the verdict memo, reuse (2026-09-18)

`chk1200` (§21) was cancelled after QF_UF and half of QF_LIA.  Its QF_UF
numbers, final: 2,297,441 proved, 15,395 kept (31,762 in the full run), 921
skipped (15,865), 4,127 of 4,326 complete proofs fully checked.  QF_LIA at the
cancellation (2,162 complete proofs): 99.0% of the attempted holes proved but
349k skipped, 53 proofs hit the 1200 s budget and one job the 60 GB node.

The budget losses are a count problem, not an engine problem: cvc5's Alethe
printer expands the proof DAG once per subproof, so the same rewrite hole
appears many times.  On ten sample proofs 43–75% of the hole conclusions
repeat an earlier one.  Three measures, in the order they apply:

### Hoist and prune (commit `6364ff71`, from the coreAlethe work)

`--pipeline hoist prune`: every closed derivation that repeats (same digest,
holes included when `share_holes`, which the CLI always sets) is lifted once
to depth 0 and its copies become references; `prune` then drops what nothing
uses.  The context stack learned which anchors bind nothing, so derivations
under such anchors count as closed.  Holes on the ten samples:

| proof | holes | hoisted | pass s |
|---|---|---|---|
| MULTIPLIER_3 | 4,388 | 1,108 | 2 |
| RF-09 | 4,389 | 2,716 | 3 |
| c_inference | 2,143 | 822 | 1 |
| bofill | 2,715 | 1,453 | 2 |
| cut_lemma | 2,660 | 1,512 | 2 |
| FISCHER9 | 2,246 | 1,819 | 12 |
| ring | 4,457 | 1,027 | 3 |
| clock_synchro | 1,741 | 1,198 | 2 |
| vpm2 | 3,747 | 2,093 | 3 |

The hoisted proofs re-check with the same verdicts.  The runner's pass 0
(`run-holes.sh`, `HOIST_TIMEOUT` 300 s) writes the hoisted proof; the
checking passes see only that.

### Verdict memo (same commit)

In check-only mode `reconstruct_holes_in_parallel` keys each hole by
`(conclusion, sorted assumptions)` pointers; only representatives go to the
workers, duplicates copy the verdict (`hole memo: X of Y holes repeat an
earlier goal; Z distinct goals to check`).  It catches what hoisting cannot
merge (holes under differing anchors, holes in proofs that hoisting failed
on): MULTIPLIER_3 891 distinct goals among 3,374 holes, 173 s with 8 workers;
c_inference 822 of 2,143, 53 s (131 s baseline, 4 workers); vpm2 1,838 of
3,491, 127 s.

### Proved equalities as premises (commit `27e4b56c`, `--hole-reuse-proved`)

A later hole whose side terms occur in an equality already proved gets that
equality as an extra premise (table keyed by side pointer, at most 64 per
hole, only equalities whose assumptions are a subset of the hole's).  On
FISCHER9 hoisted: 17,391 equalities handed out for 1,697 holes, same
verdicts, 48 s against 40 s plain.  Whether it pays on other proofs is what
`chk1200h` measures.

### Run `chk1200h` (submitted 2026-09-18 01:15, arrays 29105879/80/81)

As `chk1200` (quad, one job per node, 8 workers, 60 s and 8 GB per hole,
guards, caps 3M/500k, binary `27e4b56c` with the ground-call union) but per
benchmark: cvc5 once, hoist and prune once, then the checking pass twice on
the hoisted proof, plain (`chk_*`, `ok`) and with `--hole-reuse-proved`
(`chkr_*`, `chkr_reused`, `okr`), 1200 s budget each; wall limit 3100 s.
Results `exp/results/egglog-holes/chk1200h`; `analyze.py` prints both passes
side by side.

### Distinct solver aborts (found in chk1200h2, fixed in the next commit after bb384366)

Six kept holes in QF_UF's `chk1200h2` results read "worker exited with status
1: ... Illegal merge attempted for function to_formula".  Reproduced with a
one-hole proof of `(= (distinct v n3 v) false)`; the same three proofs
(blocks.3, firewire_tree.1/.3) lost the hole in the full run and in
`chk1200`.  Cause: the base program's list re-association rewrites
(`(Args (Args t1 t2) t3)` <-> `(Args t1 (Args t2 t3))`, the encoding behind
RARE's `:list` variables) put nodes whose head is an improper sublist into
every argument list's class after the first `(run)`; in round 2 the
distinct-elimination rules bound such a sublist as an element, set a second
value for the same `to_formula` key, and egglog aborted -- every distinct
with three or more elements not proved in round 1, provable or not.  Fix:
element positions matched as `(Mk _)`.  The same investigation showed that
`(distinct a b a) = false` was unprovable even without the abort: the
compiled `distinct-false` rule needs non-empty segments before, between and
after the repeated element (segment variables cannot be empty), and the
`(and ...)` the solver builds is a list that never reaches the ACI set form
(the conversion exists only for the step's own calls).  The solver now marks
its conjunct lists and unions the conjunction with false when a list holds
false; restricted to those lists, the cost elsewhere is within noise
(gensys_icl072 hoisted, 1,395 holes: 26.7-28.4 s old vs 28.3-29.1 s new;
clocksynchro, 1,120 holes: 66.1-66.3 s vs 67.0-67.4 s).  Two engine tests
cover both cases.

### Run `chk1200h2`: results (2026-09-19)

Resubmission of `chk1200h` with the runner paging the binaries in before
timing (the first task on each node had paid ~0.2 s in its first checking
pass).  9,812 tasks, 344 node-hours.  Plain checking pass on the hoisted
proofs, against the full run (600 s budget, 30 s and 5 GB per hole, original
proofs) and `chk1200` (QF_UF only):

| | QF_UF | QF_LIA | QF_LRA |
|---|---|---|---|
| complete proofs | 4,325 | 2,543 | 537 |
| holes before / after hoisting | 2,420,688 / 2,348,353 (−3%) | 5,526,018 / 1,827,863 (−67%) | 4,395,839 / 1,691,984 (−62%) |
| proved | 2,233,232 | 1,274,199 | 702,767 |
| kept (full run) | 7,015 (31,762; chk1200 15,395) | 26,073 | 27,003 |
| skipped at the budget (full run) | 0 (15,865) | 523,268 (3.9 M) | 652,916 (3.7 M) |
| proved, % of attempted | 99.7 | 98.0 | 96.3 |
| proved, % of all holes | 95.1 | 69.7 (full ≈ 29) | 41.5 (full ≈ 15) |
| hole-free proofs (full run) | 1,599 = 37.0% (634 = 14.7%) | 1,698 = 66.8% (1,377 = 54.2%) | 236 = 43.9% (166 = 30.9%) |
| proofs hitting the budget | 0 | 100 | 128 |
| pass p50 / p90 / max, s | 10.9 / 19.7 / 852 | 2.1 / 228 / 1,303 | 144 / 1,208 / 1,300 |

Proofs whose upfront check fails (cvc5 proof defects: 198 QF_UF, 24 QF_LIA,
12 QF_LRA) also fail the hoist pass and are counted neither way, as before.
Kept-hole reasons, plain pass: QF_LIA 33,873 at the 60 s hole limit, 14,186
at the 8 GB limit, 4,045 unprovable, 2,041 at the pass budget; QF_LRA 26,107 /
22,932 / 1,290 / 2,392; QF_UF 810 / 446 / 12,681 / 32, plus the six distinct
aborts fixed above.  The remaining losses are the budget (the cut_lemma and
uart families: 23k–32k holes per proof, 3k–7k proved in 1,200 s) and the
arithmetic holes that exhaust 60 s or 8 GB.

Reuse of proved equalities as premises (`--hole-reuse-proved`, second pass on
the same hoisted proofs): a loss on every set -- QF_UF −4,559 holes, slower on
3,912 of 4,127 proofs (65,912 s vs 58,186 s); QF_LIA −35,864 holes, slower on
1,756 of 2,537; QF_LRA −45,753, slower on 397 of 530.  Why: a premise `l = r`
is a `(union l r)` plus `Avaliable` facts for every subterm of both sides, so
the normalizer and every other rule still fire on `l` (an e-graph union adds,
it never replaces) and additionally on `r`; the pair-equality seeding grows
with the square of the available terms; and the selection (any proved
equality with a side occurring in the goal, up to 64 per hole) is loose.
peg_solitaire.5: 46,042 equalities for 2,256 holes, 124 s -> 1,063 s, kept 11
-> 114.  The variant that would give the intended effect substitutes each
proved `l` by its normal form `r` in the goal before translation, so `l`
never enters the e-graph; not implemented.

## 23. Reuse across holes: substitution, and Carcara's normalizers as a preprocessor (2026-09-19)

### Why premise reuse lost

`chk1200h2` measured `--hole-reuse-proved` as a loss on every set.  A premise
`l = r` becomes `(union l r)` plus `Avaliable` facts for every subterm of
both sides; an e-graph union adds and never replaces, so the normalizer and
every other rule still fire on `l`, and additionally on `r`; the
pair-equality seeding grows with the square of the available terms; and the
selection (any proved equality with a side occurring in the goal, up to 64
per hole) is loose.  peg_solitaire.5: 46,042 equalities for 2,256 holes,
124 s -> 1,063 s.

### Substitution-based reuse (`--hole-reuse-subst`, check-only)

The variant that replaces instead of adding.  Every hole's compound subterms
are hashed structurally (`structural_hash`, the same in every process and
pool); the owner of a subterm is the smallest hole holding it and a hole
depends on the owners of its subterms; owners run first (smallest first),
the other holes keep the proof's order, and a worker takes the first hole
whose owners are done (window 512), else the first hole left.  After a
proved owner the child snapshots its e-graph, aligns the goal's compound
subterms with the encoded goal tree, and reports `nf <hash> <term>` for each
subterm whose class holds a strictly smaller decodable term (premise-only
variables rejected).  A later hole receives up to 64 such normal forms as
`(step nfK (cl (= t t)) :rule nf-hint :args (H))` lines in its input and the
child substitutes them into the goal (outermost first) before translation.
Interleaved measurement (plain / subst, two rounds each, 8 workers, 60 s and
8 GB per hole, hoisted proofs; the CPU throttles under sustained load, so
only back-to-back pairs compare):

| proof | plain s | subst s | substitutions |
|---|---|---|---|
| vpm2 | 114 / 110 | 100 / 105 | 2,179 |
| ring | 57 / 59 | 61 / 61 | 894 |
| c_inference | 39 / 39 | 41 / 41 | 197 |
| FISCHER9 (hole pass) | 37 / 38 | 40 / 41 | 63 |
| clock_synchro | 68 / 64 | 73 / 72 | 350 |
| MULTIPLIER_3 | 166 / 166 | 188 / 183 | 1,202 |

Verdicts unchanged (one more kept hole on cut_lemma in one run).  Gains only
where genuine normalization is shared (vpm2, −8%); 5–12% losses elsewhere:
after hoisting the holes share few subterms, the shared ones are constant
folds or sums already in cvc5's normal form, and the export snapshots cost
more than the substitutions save.  A double-negation hole over an
arithmetic atom takes 0.15 s in-process (0.11 s over a Boolean atom) while
RF-09 costs 0.47 s per hole in the isolated parallel run: the per-child
fixed cost (spawn, RARE load, prelude parse) dominates the cheap holes.  Kept
as an option, off by default.

### Carcara's normalizers first (`--hole-prenormalize`, check-only)

The trailing arguments of a hole are cvc5's (theory, method) ids: `3 7` and
`3 6` are the arithmetic rewriter's post- and pre-rewrites, `1 6`/`1 7` the
Boolean rewriter's, `2 7` UF's.  In the nine arithmetic samples 60–95% of the
holes are arithmetic rewrites, i.e. the rewriter's normal forms: polynomial
normalization, constant evaluation, canonical linear relations.  Carcara has
the decision procedures (`poly_simp`, `evaluate`, `aci_simp`) but not as
term normalizers, so `src/elaborator/prenorm.rs` is a bottom-up normalizer
in the proof's pool: constants evaluated; `not-not`; `and`/`or` flattened,
identity and absorbing elements and complementary pairs handled, arguments
sorted by pointer and deduplicated; `=>` to `or`; `ite` on constants and on
equal branches; `(= p true)`/`(= p false)`; `(= x x)`; symmetric `=` in one
order; `distinct` expanded to the pairwise disequalities (so a repeated
element gives false); `+ - * / to_real` to a canonical polynomial term
(monomials sorted, `(* c a1 .. an)`, constant last, `to_real` distributed);
relations `(op a b)` to `(op' P c)` with the difference polynomial scaled to
integral coefficients of gcd 1 (Int) or leading coefficient 1 (Real), a
positive leading coefficient with the relation flipped, the constant on the
right, Int bounds tightened (`>` to `>=` plus one, non-integer `=` false).
Before scheduling, both sides of every hole are normalized: equal sides
close the hole without egglog, otherwise the goal becomes the equality of
the normal forms.  Every step is an equivalence Carcara's rules justify
(`poly_simp`, `poly_simp_rel`, `evaluate`, `aci_simp`, `not_not`,
`distinct_elim`, `cong`), so certificates can cite them; only checking is
wired up.

Measurement (plain / prenorm, interleaved, same settings), pass time in s:

| proof | plain | prenorm | closed by normalization | kept plain -> prenorm |
|---|---|---|---|---|
| gensys_icl072 (QF_UF) | 29.3 | 0.04 | 1,395 / 1,395 | 18 -> 0 |
| RF-09 | 121.8 | 27.6 | 1,666 / 2,693 | 4 -> 0 |
| c_inference | 44.8 | 11.9 | 554 / 822 | 0 -> 0 |
| bofill ex4880 | 113.2 | 21.3 | 1,080 / 1,347 | 5 -> 0 |
| MULTIPLIER_3 | 220.0 | 2.9 | 802 / 891 | 0 -> 0 |
| cut_lemma_01_008 | 615.7 | 10.8 | 1,303 / 1,370 | 63 -> 0 |
| FISCHER9 | 47.7 | 12.4 | 1,394 / 1,697 | 0 -> 0 |
| ring | 70.5 | 3.3 | 830 / 911 | 0 -> 0 |
| clock_synchro | 68.3 | 0.8 | 1,054 / 1,120 | 1 -> 0 |
| vpm2 | 116.9 | 4.4 | 1,502 / 1,838 | 7 -> 0 |

Normalization itself takes 7–53 ms per proof.  Every hole egglog kept in
these proofs (98) is closed by normalization: the large `or`/`and` chains
of gensys, the arithmetic holes that exhausted 60 s in cut_lemma.  The
remaining holes reach egglog in normal form and prove quickly.  Soundness
checks: 27 equivalences and 5 non-equivalences as unit tests; a cross-check
of every closed hole against egglog's plain verdicts (no hole newly kept);
and an independent oracle, 60 random closed holes per proof sent to cvc5 as
the negation of the hole's equality over the benchmark's declarations
(`scratchpad/prenorm/oracle.py`): 600 of 600 unsat.

What is left for egglog after normalization is the RARE rewriting proper;
the guarantee the user asked about -- rewrites that never produce terms
needing further normalization -- would let the normalizer run once before
and once after egglog; today the engine's own normalizers cover the
in-between.  Next: the same measurement on the QF_UF families with kept
holes, then a cluster run with `--hole-prenormalize`.

## 24. Holes from another producer: folding veriT's rewrite derivations (2026-09-19)

The hole checking so far only sees cvc5 proofs, because only cvc5 prints
`TRUST_THEORY_REWRITE` holes.  veriT justifies the same rewrites with a
derivation: `*_simplify`, `ac_simp`, `la_rw_eq`, ... steps rewrite subterms
and `cong`, `trans`, `refl`, `symm` assemble them into the rewrite of the
term.  A new pass, `fold` (`src/elaborator/fold.rs`, `--pipeline fold`),
turns those derivations into cvc5-shaped holes so a veriT proof goes through
the same checking and elaboration.

**What is folded.**  A *rewrite derivation* is a closed sub-DAG of steps
whose rules are the 20 Alethe rewrite rules (`REWRITE_RULES`: the
`*_simplify` family, `ac_simp`, `la_rw_eq`, `distinct_elim`, `nary_elim`,
`connective_def`; quantifier rules, `ite_intro` and `bfun_elim` left out) or
the four glue rules, each concluding a unit `(= l r)` with no arguments, no
discharge and premises only inside the derivation.  Membership is decided
bottom-up; the roots -- members some outside step uses -- become
`(step id (cl (= l r)) :rule hole :args ("TRUST_THEORY_REWRITE" "<rules>"))`
with the same id, depth and clause, the second argument listing the rewrite
rules folded in (`ac_simp:3,and_simplify:1`); the other members are dropped
when nothing kept reaches them.  Glue-only derivations (a `cong` over
`refl`s) are left alone, and so is any `cong`/`trans` with a premise outside
a derivation -- an assumed equality, a congruence-closure argument -- which
is what keeps the pass from folding theory reasoning.

**Granularity.**  veriT rewrites a whole assertion in one derivation, a
`cong` at the top over the rewrites of every conjunct: on vpm2-0 (QF_LRA,
11,628 steps) unlimited folding gives 3 holes covering 9,052 steps, each an
equality of the entire assertion, and every one exhausts the 8 GB worker
limit.  `--fold-limit N` bounds the steps of a folded derivation (counted as
a tree): a step whose derivation would be larger is not a member, so it
stays and the derivations of its premises are folded instead.  On vpm2-0,
plain checking (8 workers, 60 s and 8 GB per hole, sort guards, growth
caps):

| limit | holes | steps folded | proof lines | proved | kept | pass time |
|---|---|---|---|---|---|---|
| 1 | 3,854 | 3,854 | 11,628 | 3,854 | 0 | 100 s |
| 10 | 3,547 | 9,641 | 6,938 | 3,547 | 0 | 201 s |
| 100 | 3,164 | 10,457 | 5,879 | 3,163 | 1 | 248 s |
| 1000 | 3,127 | 10,592 | 5,706 | 3,126 | 1 | 250 s |
| none | 3 | 9,052 | 2,580 | 0 | 3 (memory) | -- |

The hole count barely moves past limit 10 because most of veriT's rewrite
steps are leaves feeding a `cong` at the top; the kept hole at 100 and
above is a 49-summand `(* 1.0 x)` elimination that exhausts 60 s in egglog
(the prenormalizer closes it).  With `--hole-prenormalize` at limit 1: 2,960
of 3,854 holes closed by normalization, the 894 `la_rw_eq` goals rewritten
and proved, pass 34 s.

**Inputs.**  veriT 2026.05 (the tarball in the worktree, built copy from
wt-corealethe), `--proof-prune --proof-merge`.  Benchmarks are first
expanded with `cvc5 -o raw-benchmark --parse-only --dag-thresh=0`: a `let`
in the input makes veriT prove under `:=` anchors (`let` steps), the hole
checker does not apply anchor assignments, and Carcara's `let` checker
rejected the unexpanded proofs anyway (tgc_io-safe-6, step t2....t27).
Let-free veriT proofs check valid.  Corpus: 40 random unsat benchmarks under
400 KB per logic (QF_UF 40, QF_LIA 30 proved, QF_LRA 4 proved), in
`scratchpad/verit/corpus`; the runner `scratchpad/verit/corpus-run.sh`
folds (`fold hoist prune`, limit 100), checks the folded proof, then
hole-checks it plain and prenormalized.

**What the corpus shows so far** (26 of 106 proofs, smallest first per
logic, interleaved; binary d44e0c81 with the §23 normalizer):

| logic | proofs | steps before -> after | holes | plain proved / kept / skipped | plain hole-free | plain time | prenorm closed / proved / kept | prenorm hole-free | prenorm time |
|---|---|---|---|---|---|---|---|---|---|
| QF_UF | 9 | 10,025 -> 8,815 | 312 | 215 / 97 / 0 | 1 | 173 s | 312 / 312 / 0 | 9 | 0 s |
| QF_LIA | 9 | 288 -> 216 | 40 | 36 / 4 / 0 | 5 | 90 s | 23 / 40 / 0 | 9 | 1 s |
| QF_LRA | 8 | 948 -> 295 | 86 | 21 / 60 / 5 | 1 | 565 s | 19 / 39 / 47 | 5 | 404 s |

Every folded proof checks `holey` (the holes are the only unchecked
steps).  The plain engine does much worse on veriT's holes than on cvc5's,
for three reasons that are all about term shape, not rewrite content:

1. **`ac_simp` over nested binary `and`/`or`** (QF_UF, `iso_*`: 87 of 97
   kept in seconds): the flattening of a deep binary tree of `or`s inside
   `and`s hits the 500k growth cap.  cvc5 flattens in its own printer, so
   its holes never ask this.
2. **Relations under Boolean connectives** (QF_LRA `cbrt`, `Chua`): the
   engine's arithmetic normalization is a goal-level fallback, so
   `(* x (- 1.0))` = `(* (- 1.0) x)` proves as a relation or a negated
   relation (`scratchpad/verit/diag/d1`, 0.7 s each) but not one level
   down, inside an `and` (guard `arithRelBoolCanMatch` fails).  With
   `--fold-limit 1` such holes are leaves and prove.
3. **`bool_simplify` and buried `la_rw_eq`** (QF_LRA): a five-symbol
   `(not (=> A (=> B B)))` = `(and A B (not B))` exhausts 60 s or 8 GB in
   egglog (`diag/d2`), and a single `la_rw_eq` deep inside a 4 KB DNF
   (`windowreal-safe2-2`) exhausts 60 s: the Boolean rules explode on the
   surrounding term.

**Normalizer additions** (d72ba1bd), each an equivalence: negation normal
form; a negated bound is the opposite bound (Int tightened); two bounds on
one polynomial that make an equality (`(and (<= P c) (>= P c))` is
`(= P c)`) or, under `or`, a disequality are replaced by it -- the inverse
of `la_rw_eq`; and a conjunct that is a disjunction whose every member is
complemented among the conjuncts makes the conjunction false (dually for
`or`), which the flattening had hidden (`(not (=> (and A C) (=> (or B C)
(or B C))))` is false).  The dual-complement rule matters because NNF
pushes `not` through the compound literal the old complement test matched.
Unit tests: 41 equivalences, 9 non-equivalences.  With these, all three
`diag/d2` shapes, all 14 `windowreal-safe2-2` holes and all 3
`intersection-example` holes close without egglog.

**And on cvc5's holes: every one.**  Re-running the ten §23 sample proofs
with the final normalizer (`scratchpad/prenorm3`): 100% of the holes of
every proof are closed by normalization alone -- gensys 1,395/1,395, RF-09
2,693/2,693, 30_30_18 822/822, ex4880 1,347/1,347, MULTIPLIER_3 891/891,
cut_lemma 1,303 -> 1,370/1,370, FISCHER9 1,697/1,697, ring 911/911,
clock_synchro 1,120/1,120, vpm2 1,838/1,838 -- egglog is never called and
the passes take 0.01–0.04 s of hole time (0.3–3 s wall, 37 s for FISCHER9's
parse).  What was left to egglog before were negated bounds and
equality-to-bounds rewrites, which the additions cover.  The cross-check
(no hole newly kept; every hole egglog kept is closed) and the cvc5 oracle
(400 of 400 sampled closed holes unsat) both pass, as they did for the
NNF-only intermediate (`scratchpad/prenorm2`, same closed counts as §23).
The chk1200p run in progress uses the §23 normalizer; the natural next
cluster run is the same comparison with this one.

Pending: the rest of the corpus (the runner continues; its prenormalized
column is redone with the final binary by `scratchpad/verit/corpus-prenorm.sh`
once it ends), the same at `--fold-limit 1` for the granularity
comparison, and a cluster run over veriT proofs of the three sets.

**Bound-aware complements** (commit after d72ba1bd).  The negated-bound
normal form hid a complement: `(or (not (>= x 1)) (>= x 1))` became
`(or (<= x 0) (>= x 1))`, and a `comp_simplify` hole of RF-01 (QF_LIA)
went to egglog and failed.  The complement checks now reason about bounds
per polynomial: under `and`, bounds with no common value (or a point
outside a bound) are a complement pair and the tightest lower and upper
bound are the only ones kept; under `or`, bounds covering every value are
one and the weakest are kept; a member of a dual argument that is
complemented is dropped from it (`(or p (and (not p) q))` is `(or p q)`).
Unit tests 56 / 14.  The ten cvc5 sample proofs still close completely,
cross-check and oracle clean (`scratchpad/prenorm4`).

**Correction: the `let`s were never the obstacle.**  Two claims in the
"Inputs" paragraph above are wrong.  Carcara checks veriT's `let` proofs
valid as they are (tgc_io-safe-6, clock_synchro, FISCHER9, gensys: valid);
what failed was my own `--expand-let-bindings`, which expands the `let`
terms of the proof too, so the `let` rule had no `let` to match.  And the
rewrites do not depend on the anchor assignments: veriT's `let` subproofs
contain only `refl`, `cong` and the closing `let` (vpm2-0: 1,838 `refl`,
1,874 `cong`, 37 `let`, nothing else), while every `*_simplify`, `ac_simp`
and `la_rw_eq` step is at depth 0.  So `fold` applies to the original
proofs unchanged, the `let` subproofs stay as glue-only derivations, and
the holes are depth-0 and context-free.  On the original proofs at limit
100 (`scratchpad/verit/lets`): gensys 141 holes, clock_synchro 89,
tgc_io-safe-6 51, 30_30_18 30, FISCHER9 3,107, ring 26; every folded proof
checks `holey`, and the prenormalized pass closes every hole of every one
(hole time 0.000–0.022 s).  What the cvc5 round-trip had actually done for
vpm2-0 is unrelated to `let`: the original benchmark writes Real constants
as integer numerals, veriT then prints `(step t1602 (cl (= (- 1.0) (- 1)))
:rule unary_minus_simplify)`, and Carcara's parser rejects the mixed-sort
equality (`sort error: expected 'Real', got 'Int'`) even with
`--allow-int-real-subtyping`.  The corpus was run on the round-tripped
benchmarks, which is a valid experiment (the proofs differ only in the
absence of `let`s and in numeral spelling), but the plan is to run the
original benchmarks directly; `scratchpad/verit/gen-orig.sh` is producing
their veriT proofs and checking each, to count how many the numeral issue
affects.

## 25. The normalizer, exactly (2026-09-19)

**The normalizer, exactly** (`src/elaborator/prenorm.rs`, as of 9027d5ac).

*Driver.* With `--hole-prenormalize`, before any hole is scheduled, one `Normalizer` (one memo shared by all holes of the proof) normalizes both sides of every hole `(= l r)`. If the two normal forms are the same pooled term the hole is closed without egglog; otherwise the hole's clause becomes `(= nl nr)` and that is what egglog sees. The log line `hole prenorm: A of B holes closed by normalization, C goals rewritten` counts the two outcomes.

*Traversal.* Bottom-up and memoized per term (pointer identity in the term pool). An application `(f t1 .. tn)` gets its arguments normalized. An operator term gets its arguments normalized first, then one of the cases below applies to the already-normal arguments. Everything else is left as it is: constants, variables, and binders (`forall`, `exists`, `lambda`, `choice`, `let`), whose bodies are not entered.

*Operator cases.*

1. `not`: `(not (not p))` is `p`; `(not true)` is `false` and `(not false)` is `true`. `(not (rel P c))` for `rel` among `<`, `<=`, `>`, `>=` over Int or Real is the opposite relation, re-normalized as a relation (Int `(not (<= P c))` becomes `(>= P c+1)`, Real `(> P c)`). `(not (and a1 .. an))` is the `or` of the `(not ai)`, and `(not (or ..))` the `and` of them, each `(not ai)` going through this same case, then the connective through the `and`/`or` case: negation normal form. Any other `(not p)` stays (`(not (= a b))`, `(not (ite ..))`, `(not x)`).
2. `and`, `or`: the ACI procedure below.
3. `(=> a b)`: the `or` of `(not a)` (through case 1) and `b`, through the ACI procedure.
4. `ite`: `(ite true a b)` is `a`, `(ite false a b)` is `b`, `(ite c a a)` is `a`; otherwise kept.
5. `+`, `-`, `*`, `/`, `to_real` (term of sort Int or Real): the term is read as a polynomial and printed in canonical form. The polynomial has rational coefficients over *atoms*, the maximal subterms that are none of these operators: a numeral (also `(- 1)`) is a constant; `+` adds; unary `-` negates; n-ary `-` subtracts; `*` multiplies polynomials, so a product of atoms is a monomial and nonlinear terms are fine; `(/ p c)` with `c` a nonzero constant scales by `1/c`, any other division is an atom; `(to_real p)` is `p`'s polynomial with every atom wrapped in `to_real` and the constants converted. A monomial is the multiset of its atoms sorted by pointer. Canonical term: the monomials ordered by number of atoms, then by their atoms' pointers; each printed as the atom, `(* c a)` or `(* c a1 .. an)` with the coefficient omitted when it is 1; the constant last; a single monomial without the `+`; the zero of the sort when empty. Constants print as Int literals when the sort is Int and the value integral, else as Real literals (rationals).
6. Relations `<`, `<=`, `>`, `>=` with two arguments, and `=` with two arguments of sort Int or Real. The sort is Real as soon as one side is Real (Int numerals may stand on either side under subtyping), else Int. The difference `lhs - rhs` is taken as a polynomial. If it is constant, the relation is decided: `true` or `false`. Otherwise the constant moves right (`P + k op 0` is `P op -k`) and `P` is scaled: Int, by the lcm of the coefficients' denominators over the gcd of the resulting numerators, so the coefficients are integers with gcd 1; Real, by the reciprocal of the absolute leading coefficient (the first monomial in canonical order), so it is 1. A negative leading coefficient negates both sides and flips `<` with `>` and `<=` with `>=` (`=` stays). Int bounds are tightened: a non-integer bound is rounded, `>=` up, `<=` down, `>` becomes `>=` of the floor plus one, `<` becomes `<=` of the ceiling minus one, and `=` becomes `false`; an integer bound turns `>` into `>=` of the bound plus one and `<` into `<=` of the bound minus one. The result is `(op' P c)`.
7. `=` otherwise: `(= a a)` is `true`; `(= p true)` and `(= true p)` are `p`; `(= p false)` and `(= false p)` are `(not p)` through case 1; else the two sides are put in pointer order (one orientation per pair) and, when both are constants, evaluated.
8. `distinct`: with two arguments, `(not (= a b))` through cases 6/7 and 1; with more, the `and` of the pairwise `(not (= ai aj))`, `i < j`, through the ACI procedure, so a repeated element gives `false`.
9. Any other operator (`xor`, `div`, `mod`, `abs`, `select`, bit-vector operators, ...) is kept, evaluated when all its arguments are constants.

*The ACI procedure* for `(op a1 .. an)`, `op` being `and` (identity `true`, absorbing `false`) or `or` (identity `false`, absorbing `true`), with the `ai` already normal:

a. Arguments that are themselves `op` terms are flattened in (they are flat already, so one level suffices).
b. Identity elements are dropped; an absorbing element makes the result absorbing.
c. The rest is sorted by pointer and deduplicated.
d. Complements make the result absorbing: a negated argument `(not p)` with `p` also present, and `(not (= P c))` with a bound on the same polynomial `P` that excludes the point `c` under `and` or that covers it under `or`. "Excludes" and "covers" are the interval tests below.
e. An argument of the dual connective (an `or` inside an `and`, or the reverse) is examined member by member: a member is *complemented* if it has a literal complement among the arguments, or if it is a bound `(rel P c)` or a point `(= P c)` or `(not (= P c))` and some argument is a bound on the same `P` that excludes it (under `and`) or covers it (under `or`). If every member is complemented the result is absorbing; otherwise the complemented members are dropped from that argument (`(or p (and (not p) q))` is `(or p q)`), the argument is rebuilt through the ACI procedure for the dual connective, and the whole list is re-run through this procedure.
f. Bounds are merged per polynomial (same pooled `P`). Under `and`, only the tightest upper and the tightest lower bound stay (at equal value the strict one); if they have no common value the result is `false`; if they meet at one non-strict point they are replaced by `(= P c)`. Under `or`, only the weakest upper and lower stay (at equal value the non-strict one); if they cover every value the result is `true`; if they leave out exactly one point they are replaced by `(not (= P c))`: Int `low = up + 2` gives `(not (= P (up+1)))`, Real `low = up` with both strict gives `(not (= P c))`. Int bounds are never strict after case 6. If anything changed, the list is re-run through the procedure.
g. No argument left gives the identity, one gives that argument, more give `(op ..)` in pointer order.

*Interval tests* (upper `u` from `<=`/`<`, lower `l` from `>=`/`>`, Int bounds non-strict): two bounds exclude each other when `l > u`, or `l = u` and one is strict; a point `c` is excluded by `(<= P u)` when `u < c`, by `(< P u)` when `u <= c`, by `(>= P l)` when `l > c`, by `(> P l)` when `l >= c`, and by `(not (= P c))`. Two bounds cover everything when, Int, `l <= u + 1`, or, Real, `l < u`, or `l = u` and not both strict; a bound covers a disequality `(not (= P c))` when it is implied by `(= P c)`: `(<= P u)` with `u >= c`, `(< P u)` with `u > c`, `(>= P l)` with `l <= c`, `(> P l)` with `l < c`.

*What it is not.* No De Morgan below binders, no distribution of `and` over `or` (no DNF/CNF), no `ite` lifting, no reasoning across different polynomials, no theory reasoning beyond linear bounds on one polynomial. Canonical orders are pointer orders, so a normal form is canonical within one run's pool, which is all the check needs. Every step is an equivalence; the checker's rules that justify them (`poly_simp`, `poly_simp_rel`, `evaluate`, `aci_simp`, `not_not`, `distinct_elim`, plus the bound reasoning as `la_generic` instances) are what a certificate would cite, but only checking is wired up.

**Two fixes on the way** (f841cd24, 9027d5ac).  The parser fix from wt-diff
(92d8a42f) is ported: under `--allow-int-real-subtyping` the polymorphic
positions (`=`/`distinct` arguments, `ite` branches, uninterpreted function
arguments) accept an Int where a Real is expected, which is what rejected
the original vpm2-0 proof (`(= (- 1.0) (- 1))`).  With it the original
proof checks valid, folds to the same 3,164 holes as the round-tripped one
at limit 100, and -- after the normalizer takes a mixed Int/Real relation's
sort as Real rather than from its left side, which had kept
`(<= (- 300) P)` as an Int bound and `(<= P (- 300))` as a Real one -- every
one of them closes by normalization (hole time 0.047 s).

**Corpus complete** (106 proofs; 2 do not parse: `simple_startup_12nodes`
and `NEQ006_size5`, an undefined identifier on the last line of the veriT
output).  Plain checking, limit 100, 4 workers at 4 GB, 60 s per hole,
300 s per proof; the prenormalized column redone with 9027d5ac
(`scratchpad/verit/run100/results.txt`, `results-prenorm.txt`):

| logic | proofs | steps before -> after | holes | plain proved / kept / skipped | plain hole-free | plain time | prenorm closed / proved / kept | prenorm hole-free | prenorm time |
|---|---|---|---|---|---|---|---|---|---|
| QF_UF | 39 | 1,974,555 -> 1,663,096 | 2,401 | 2,012 / 389 / 0 | 2 | 683 s | 2,401 / 2,401 / 0 | 39 | 0 s |
| QF_LIA | 30 | 29,685 -> 11,376 | 8,169 | 8,159 / 10 / 0 | 20 | 1,289 s | 8,169 / 8,169 / 0 | 30 | 0 s |
| QF_LRA | 35 | 463,425 -> 363,685 | 10,254 | 812 / 1,496 / 7,946 | 2 | 7,805 s | 10,149 / 10,221 / 33 | 19 | 948 s |

Rules folded: QF_UF `ac_simp` 7,324, `or_simplify` 557, `and_simplify`
466, `eq_simplify` 193; QF_LIA `la_rw_eq` 10,403, `comp_simplify` 1,887,
`sum_simplify` 1,309; QF_LRA `la_rw_eq` 29,823, `ac_simp` 12,359,
`sum_simplify` 5,604, `prod_simplify` 5,552, `comp_simplify` 1,480, and
smaller counts of eleven others.  The 33 QF_LRA holes left are in 16
proofs, one to four each, and go to egglog after normalization and time
out there.  The original benchmarks' veriT proofs (`gen-orig.log`) check
valid with the subtyping port; the one `invalid` in that log was the
runner passing two benchmark paths for a repeated basename (`RF-01`).

This is the last measurement of the normalizer in this form: the design is
being redone as the composition of Carcara's own rule procedures
(`evaluate`, `poly_simp`/`poly_simp_rel`, `aci_simp`), so that elaboration
can emit the same steps, with everything else left to RARE rules.

## 26. The normalizer as four checker procedures, with certificates (2026-09-19)

The §23–25 normalizer was a general-purpose decision procedure for the
holes; that was not the point.  The point is one machinery for checking
and elaboration: normalization steps that are Carcara rule applications,
so that the same derivation that closes a hole in the checking pass is the
certificate that replaces it in the elaboration pass, and whatever the
normalizer does not reach is egglog's job through RARE rules (with a rule
file per producer, cvc5's and veriT's, as needed).

**What it is now** (`src/elaborator/prenorm.rs`, commit 013405c6).
Bottom-up and memoized; at each operator term, after the arguments, at
most one of the four procedures applies at the top, and its result is
normalized again (a `distinct` expands to equalities that `poly_simp_rel`
then canonicalizes, under an `and` that `aci_simp` then sorts):

- `evaluate`: a term whose arguments are all values is its value
  (`Term::evaluate`).
- `poly_simp`: `+`, `-`, `*`, `/`, `to_real` terms of sort Int or Real are
  printed as the canonical term of the checker's own polynomial
  (`checker::rules::polynomial::Polynomial`, now `pub(crate)`): monomials
  by size then atom pointers, `(* c a1 .. an)`, constant last, Int atoms
  in a Real polynomial wrapped in `to_real` (the checker's polynomial sees
  through it).  Bit-vectors not yet.
- `poly_simp_rel`: `(op x1 x2)` for `<`, `<=`, `>`, `>=`, `=` over Int/Real
  (Real when either side is) becomes `(op P c)`: the difference of the
  sides scaled by a positive factor (integral coefficients of gcd 1 for
  Int, leading coefficient of absolute value 1 for Real), constant on the
  right.  An equality is additionally oriented to a positive leading
  coefficient, which `poly_simp_rel` allows for `=` only.  No flipping of
  order relations and no Int tightening: those are RARE rules.  The step
  carries its `poly_simp` premise `(= (* s (- x1 x2)) (* 1 (- P c)))`.
- `aci_simp`: `and`, `or`, `bvand`, `bvor`, `bvxor`, `bvadd`, `bvmul`
  flattened, identity element removed, deduplicated when idempotent, sorted
  by pointer.  No absorbing element, no complements.
- `distinct_elim`: two arguments to `(not (= a b))`, more to the `and` of
  the pairwise disequalities in the checker's order, more than two
  Booleans to `false`.

Nothing else: NNF, negated bounds, bound merging, complements, absorbing
elements, `=>`, `ite`, `(= p true)`, `(= x x)` are gone.

**Certificates.**  Every step is one rule on one subterm, so the
derivation of a normal form is `cong` over the arguments' derivations,
the top step(s), the tail's derivation, joined by `trans`; a closed hole
`(= l r)` gets the two derivations joined by `symm` and `trans` (or
`refl`), a rewritten goal gets egglog's proof of `(= nl nr)` bridged to
`(= l r)` the same way.  `--hole-prenormalize` therefore works in the
elaboration pass too.  The unit tests check every certificate with the
checker (`certificates_check`).

**Two checker fixes on the way** (1d3cdec4): the evaluator compared an
Integer and a Real value structurally, so `evaluate` accepted
`(= (= 1.0 1) false)` under subtyping; and `aci_simp` deduplicated the
arguments of every associative operator, accepting `(= (+ a a) a)` and
`(= (* a a) a)`; deduplication is now confined to `and`, `or`, `bvand`,
`bvor`.

**Measured on the ten cvc5 sample proofs** (4 workers, 4 GB, 60 s per
hole; `scratchpad/prenorm5`, `scratchpad/elab5`):

| proof | holes | closed by normalization | rewritten for egglog | check-only: kept / pass | elaboration: justified / kept / pass | elaborated proof |
|---|---|---|---|---|---|---|
| gensys_icl072 | 1,395 | 462 | 6 | 0 / 8.5 s | 1,395 / 0 / 20 s | valid |
| RF-09 | 2,693 | 1,163 | 59 | 0 / 36 s | 2,693 / 0 / 72 s | holey (23 other holes) |
| 30_30_18 | 822 | 450 | 292 | 0 / 10 s | 822 / 0 / 24 s | valid |
| ex4880 | 1,347 | 911 | 252 | 0 / 22 s | 1,345 / 2 / 40 s | holey (108) |
| MULTIPLIER_3 | 891 | 766 | 36 | 0 / 3 s | 891 / 0 / 6 s | holey (217) |
| cut_lemma | 1,370 | 1,258 | 76 | 0 / 4 s | 1,370 / 0 / 8 s | holey (142) |
| FISCHER9 | 1,697 | 1,191 | 321 | 0 / 12 s | 1,697 / 0 / 22 s | holey (122) |
| ring | 911 | 747 | 95 | 0 / 6 s | 911 / 0 / 8 s | holey (116) |
| clock_synchro | 1,120 | 782 | 271 | 0 / 14 s | 1,119 / 1 / 22 s | holey (79) |
| vpm2 | 1,838 | 739 | 3 | 1 / 75 s | 1,837 / 1 / 82 s | holey (256) |

Normalization alone closes 33–92% of the holes per proof; the rest go to
egglog, either as rewritten goals or untouched (the Boolean shapes:
`(= p true)`, `not_not`, absorbing elements, complements, which are
`bool-*` RARE rules), and egglog proves all of them but one: `ho27` of
vpm2, a `(<= ...)` over a 49-summand sum whose sides normalize to
different relations (a flip), which egglog then cannot handle at that
size in 60 s.  Every hole the plain engine kept in §23 (98) is closed or
proved.  Pass times sit between the plain engine's (29–616 s) and the
§23 normalizer's (0.04–28 s).  Oracle: 400 of 400 sampled closed holes
unsat; cross-check: no hole newly kept.  In the elaboration pass every
certificate was accepted by the checker at insertion (no "checker
rejected" hole); the four kept holes are three egglog snapshots without
a certificate and the vpm2 timeout.  The "holey" verdicts of the
elaborated proofs are cvc5's other hole kinds (`ARITH_PRED_CAST_TYPE`,
`THEORY_INFERENCE_ARITH`, `THEORY_BV`), which were never in scope; gensys
and 30_30_18, which have none, come out valid.

**veriT.**  The corpus's prenormalized column is being redone with this
normalizer (`results-prenorm.txt`; the §24 column is kept as
`results-prenorm-old-normalizer.txt`).  What the old normalizer closed and
this one does not (veriT's `bool_simplify`, `la_rw_eq`, `comp_simplify`
shapes) is what a `verit.rare` file has to supply.

## 27. The residue: what egglog gave up on without a kill (2026-09-19)

The question was whether the rule set is enough: the holes egglog "could
not prove" after saturating (§19: 6,667 in the full run's checking pass)
are the only candidates for missing rules, and they were never classified.
`scratchpad/residue/residue.py` extracts them from a run's
`results.json.gz` and classifies the goals; `report.md` has the tables.

**chk1200h2 (growth caps, 60 s per hole).**  8,048 such holes in 2,863
proofs: QF_UF 6,440 (2,496 proofs, 6,339 from QG-classification), QF_LIA
1,101 (317), QF_LRA 507 (50).  Not one is a saturation: every one ends in
"the e-graph grew past the bound" (500k for the plain cap, 3M for
arithmetic), still growing when stopped, on goals of 100 to 8,000 nodes.
Structurally, 5,752 of the 8,048 have sides that coincide after sorting
and flattening `and`/`or`/`+` (5,552 of them QF_UF `or`/`and` chains) or
after deduplication or double negation; of the 2,296 whose sides really
differ, 794 QF_UF `or` goals differ by a `false` disjunct and 28 `and`
goals by a `true` conjunct, 20 are `(ite (not c) a b)` against
`(ite c b a)`, 12 are `(= s t)` against `true`, 8 `(ite false ..)`, and
the rest are arithmetic: `+` against `+` with more than ten differing
summands (656), sums that cancel to a constant (453), `<` against
`(not (>= ..))` (153), `<=`/`>=` flips and negations (90), `*` against
`+` (38).  No De Morgan shape, no `distinct`, nothing Boolean without UF
atoms.  A further 411 (90 LIA, 321 LRA) failed the relation fallback's
own key comparison (`arithRelBoolKeyOf`), i.e. relation goals whose
canonical keys differ: flips and tightenings again.

**The full run (no caps, 30 s per hole).**  The same reason is reported as
egglog's final check failing, `(= (goal_lhs) (goal_rhs))`: 6,591 holes
(QF_LIA 3,578 in 202 proofs, QF_UF 2,753 in 790, QF_LRA 260 in 56), plus
47 relation-key failures; those logs carry no goal text, but the proofs
are the same families that chk1200h2 stops at the cap.

**Conclusion.**  The residue is not evidence of missing rules.  It is the
e-graph blowing up on associativity and commutativity over long chains
and on polynomial arithmetic over many summands, on goals that the
§26 normalizer takes care of before egglog: `aci_simp` (flattening,
sorting, deduplication, the `false`/`true` units) and `poly_simp` (the
cancelling sums, the coefficient collection) cover about 7,700 of the 8,048
outright, and what remains after normalization for egglog is small: the
relation negations and flips (`<` vs `(not (>= ..))`, `<=` vs `>=`) and
the `ite` condition swap, which are single RARE rules on small goals.
The one structural gap found earlier, De Morgan (§19), does not occur in
the residue at all.  So the rule set, with the normalizer in front of it,
is sufficient for everything egglog was ever asked and failed to answer
by saturation; the unknown that remains is the never-attempted holes of
the budget-bound proofs, and the run with the §26 normalizer is what
measures those.

**In the checker too** (commit after 817c9516).  The normalizer had only
been wired into the elaborator's hole pass, for the historical reason that
the isolated workers and budgets live there.  `carcara check
--check-hole-rewrites --rare-file ...` now normalizes every
`TRUST_THEORY_REWRITE` hole before its in-process egglog call, logging
`closed by normalization` for the ones that need none; that path still has
no isolation and no hard per-hole limit (only the cooperative
`--rare-check-timeout`), which is why the evaluation keeps using the
elaborator's pass.  A plain `carcara check` without the flag leaves holes
as holes, as before.

## 28. Relations below the goal: the all-relations fallback (2026-09-19)

veriT's `la_rw_eq` rewrites an arithmetic equality into the conjunction of
its two bounds (`arith/LA-pre.c`, one of the preprocessing rules the
`fold` pass turns into holes), so a hole's goal is
`(= (= a b) (and (<= a b) (<= b a)))`.  Both the normalizer and egglog
failed on it, for the same reason: a relation and its mirror image have
the same content but different terms, and nothing identified them below
the goal.  The normalizer cannot: `poly_simp_rel` scales by a positive
factor (a negative one is allowed for `=` only), so `(<= a b)` and
`(<= b a)` become `(<= P c)` and `(<= -P -c)`.  egglog could not either:
`arithRelBoolKeyOf` is demanded for the goal's two sides only, so the
canonical keys were never computed for an atom inside an `and`.

**The fallback** (`arith_rel_all`/`arith_rel_merge` in
`arith_poly_norm_rel.egglog`, plan `arithRelAll` in the engine).  A third
goal fallback, tried only after the goal check and the two goal-level
arithmetic checks have failed: demand the key of every relation atom in
the e-graph (the nine shapes the key rules cover), run the guard and
`arith_poly` rulesets, union the atoms whose keys agree, then run the main
schedule once more and check the goal as it is.  A goal the earlier checks
prove never reaches it, so cvc5's holes pay nothing; the cost falls only on
goals that would otherwise be kept.

**Reconstruction.**  The unions the fallback makes are not rewrites, so the
certificate search had to learn them: a relation pair with equal keys is
one `poly_simp_rel` computation (`prove_by_arith`, in-class), and `and`/`or`
sides whose literal sets differ only in unioned literals are proved by
`aci_simp` on the matching literals plus in-class proofs of the pairs
(`prove_by_aci_modulo`, also a candidate edge of the path search).  The
computational strategies run after the rule search, so a checkable rule
path is still preferred.

**A soundness fix on the way.**  `rules_from_generated_program` stripped the
sort guards from the generated rules, so the search would ground
`arith-eq-elim-real` on an integer equality and emit a `rare_rewrite` step
the checker rejects ("trying to substitute term 's1' with a term of a
different sort"); the guards are now kept and checked when a rule is
grounded, with `encoded_sort` recomputing an encoded term's sort.

**Policy.**  In the elaboration pass the normalizer no longer rewrites the
goals it cannot close: the certificate search works on the e-graph of the
goal it was given, and on a normalized goal egglog proves more while the
reconstruction replays less (the `arith-eq-elim-int` instance it needs is
not a stored node, since the normalized sides are terms the rules were not
compiled around).  Closing a hole outright still applies, with the
normalizer's certificate.  Trying the normalized goal first and the
original on a reconstruction failure would get both, at one extra child run
per lost hole; not done.

**Measured** on the three `la_rw_eq` shapes (`scratchpad/verit/diag/d4`),
which were kept by both passes before: checking proves 3 of 3, elaboration
justifies 3 of 3, and the elaborated proof checks **valid** with no hole
left.  The unit tests cover the e-graph side
(`mirrored_inequalities_meet_inside_a_conjunction`) and the certificate
side end to end (`elaborates_mirrored_bounds_in_a_conjunction`).

## 29. `:list` parameters, and the complement rules that never fired (2026-09-19)

Probing the veriT corpus's kept holes turned up something that had been
distorting every measurement since §17.  A RARE rule's `:list` parameter
is compiled into **exactly one argument slot** of the `Args` chain (a bare
pattern variable, which the list re-association lets bind a *sublist*, but
never an empty one).  So a rule with k list parameters only matches when
all k lists are non-empty.  `bool-or-taut`, with three of them, proves

| goal | verdict |
|---|---|
| `(or a p b (not p) c)` | proved in 0.07 s |
| `(or a p (not p) c)` | kept |
| `(or a b p (not p))` | kept |
| `(or p (not p))` | kept |

and the kept ones are not merely unproved: an unreachable goal is what
triggers the quadratic pair seeding, so `(= (not (or (not A) A (not B)))
false)` with three-literal `A`, `B` exhausts 2 GB in 60 s
(`scratchpad/verit/diag/d3`).  The same holds for `bool-and-conf` and for
every other `:list` rule; Carcara's own `rare_rewrite` checker shares the
convention, substituting one term per parameter, so an empty list has no
form there either.

**The fix, on the set form.**  The ACI machinery converts every `and`/`or`
call into a set and already has set-level rules for the identity, the
singleton, idempotence and the absorbing element.  One more rule unions a
set that holds `w` and `(not w)` with the absorbing element, which finds
the pair whatever the arity and the positions
(`aci_norm.rs`, rule 9).  The reconstruction certifies it with a new
computation kind, `AciComplement`, whose Alethe step is
`or_simplify`/`and_simplify` -- Carcara's procedures for those rules
short-circuit on exactly this pair.

**Measured** on the six shapes of `scratchpad/verit/diag/d5`, all kept
before: checking proves 6 of 6 in under 0.1 s each, elaboration justifies
5 of 6 (the sixth has the pair under a `not`, where the search does not
chain the step onto `bool-not-true` yet).  Two tests cover it, at the
engine and end to end.

**The general fix** (commit ef1d4d8d) followed.  The compiler emits one
variant of a rule per subset of its `:list` parameters, with those dropped
from the argument chains; a variant that would leave an operator without
arguments is not emitted, and the count is capped at four list parameters.
For the three logics this turns 322 rules into 366.

Two things were needed for the certificates.  Every variant carries the
rule's name, so the verifier now accepts a certificate that *some* rule of
that name states rather than the first one found -- several sort
instantiations of a rule already shared a name, so this was a latent bug.
And a `rare_rewrite` step has no form for an absent argument, so an
instance whose list parameters were dropped is stated on the terms padded
with the connective's identity (`false` in an `or`, `true` in an `and`, `0`
in a sum, `1` in a product), which is exactly what the checker recomputes
from the rule's declaration, with an `aci_simp` step on each side bridging
the padding.  The padded terms come from instantiating the full variant's
pattern, so they agree with the checker by construction.

With the ACI set rule switched off, so that only this path can prove them,
the six complement shapes give 6 of 6 proved in checking and 5 of 6
justified in elaboration -- the same as the set rule, at about 1.4 times
the time and three steps per certificate instead of one.  Both are kept:
the set rule is the cheaper route for the shape that dominates, and the
variants cover every other list rule (`distinct-false`, the bit-vector and
string ones).  `tests/rare/list-empty.rare` holds a rule that only an
empty-list variant can apply, so the general path is pinned by a test of
its own rather than by the complement family.

**What is still open.**  A list parameter that binds *several* arguments
still cannot be written in a `rare_rewrite` step, so such an instance is
proved but not certified; that needs a form for a list argument in the
step's `:args`, which is a proof-format decision.

## 30. One rule on the set form, and the set form for every term (2026-09-19)

§29 left the `:list` gap closed by brute force: one compiled variant per
subset of a rule's list parameters, 2^k of them, capped at four.  The
variants are gone for the connectives.  A rule whose left-hand side is an
`and`/`or` over `:list` parameters is now compiled **once**, against the
ACI set form:

```
(rule ((= (@and (Assoc elements)) result)
       (set-contains elements (Mk w1))
       (set-contains elements (Mk (@not (Args (Mk w1) (Empty)))))
       (SortBool (Mk w1)))
      ((union result (Mk (Bool false)))) :ruleset list-ruleset)
```

The fixed arguments become membership conditions and the list parameters
disappear, because a set has no positions to fill: the rule fires whatever
the arity, wherever the fixed arguments sit, and with any of the lists
empty.  `set_form_rule` in `engine.rs` builds it, and a rule that gets one
emits no variants (`on_the_set_form`).  For the three logics the database
is 342 rules, against 322 with no empty-list handling at all and 366 with
the variants.  The hand-written complement rule of §29 is gone with them:
`bool-or-taut` and `bool-and-conf` are ordinary RARE rules again, and the
certificate cites them by name instead of an `AciComplement` computation.

**The set form has to exist for terms the rewriting derived**, not only
for the ground `and`/`or` calls the step spells out, or the compiled rule
has nothing to match.  `aci_norm::general_set_conversion` gives every
class of an `and`/`or` term its set form.  Its rules are declared with the
program but put in a ruleset of their own, `set-ruleset`, which no ordinary
round runs; the last **goal fallback plan**, `aciSets`, saturates that
ruleset and runs one more schedule round.  Three reasons, all measured:

- A goal the ordinary rules prove needs none of it and pays nothing.  On
  two cvc5 proofs with no kept holes (`dead_dnd014`, 624 holes;
  `prime_cone_unsat_20`, 398) the plan is invisible: 8.901 s against
  8.904 s and 18.610 s against 18.711 s with the plan removed entirely,
  same verdicts.  (Both are about 20% and 10% slower than the binary the
  cancelled `chk1200n` run used, which is the cost of everything on this
  branch since; moving the compiled set-form rules out of `list-ruleset`
  does not recover it and costs d3 and d5 a fallback round, so they stay.)
- The plans run in order on the *same* e-graph, so by the time the set
  conversion runs, the arithmetic plans have already added their relation
  rows.  A goal proved by the set form alone loses those, and the
  certificate search loses with them (d4 went 3 of 3 to 0 of 3 with the
  conversion first).
- Nothing else in the program depends on it, so it cannot slow down the
  rounds that do the ordinary work.

**A wrapper congruence was hiding the ACI and relation steps.**  The set
form merges an `and`/`or` term with its permutations, which makes
`Mk(@and(a,b))` and `Mk(@and(b,a))` congruence-compatible at the `Mk`
wrapper: same operator, one child, children in the same class.  The
candidate-graph builder preferred that edge, and justifying it pushed the
obligation one level down, onto the *unwrapped* applications -- where
`aci_modulo_pairs`, `aci_equal` and `arith_kind` all bail out, because
they read a term through `encoded_application`, which wants the wrapper.
The path then failed to justify, four bans later the search gave up, and a
hole that used to be justified was kept.  `expand_vertex` now offers the
ACI, ACI-modulo and relation edges *before* the congruence one; each is a
single step the checker replays, while the congruence edge between two
permuted n-ary applications is almost always a dead end.

**Measured** on the diagnostics, against the binary the cancelled
`chk1200n` run used:

| | before | after |
|---|---|---|
| d1 checking | 7/7, 0.52 s | 7/7, 0.50 s |
| d1 elaboration | 6/7, 60.0 s (one hole hit the 60 s cap) | **7/7, 0.56 s** |
| d2 checking | 2/3, 34.4 s | **3/3, 0.14 s** |
| d2 elaboration | 1/3, 33.5 s | 1/3, **0.60 s** |
| d4 | 3/3, 3/3 | 3/3, 3/3 |
| d5 | 6/6, 5/6 | 6/6, 5/6 |
| d3, d8, d9 | unchanged | unchanged |

d2's two kept holes and d3's one are not list-rule cases; they remain
open.  The full test suite passes, `tests/rare/list-empty.rare` included,
which is now pinned by the set-form path rather than by the variants.

**Both encodings are kept and selectable**, `--rare-list-encoding
set-form|chain` (default `set-form`; the isolated hole worker gets it
passed through, and the prepared database is keyed on it alongside the
seeding and the sort guards).  `chain` is the §29 compilation: the
argument chain plus one variant per subset of the list parameters.  It has
to stay, and not only for the comparison -- the set form is available only
because `and` and `or` are ACI, so the order-sensitive n-ary operators
(`str.++`, `re.++`, bv `concat`) and every other list rule go through the
chain path under either setting.  Measured side by side on the
diagnostics:

| | `set-form` | `chain` |
|---|---|---|
| d2 checking | 3/3, 0.17 s | 1/3, 60.2 s |
| d2 elaboration | 1/3, 0.85 s | 1/3, 60.2 s |
| d3 elaboration | 0/1, 0.16 s | 0/1, 2.85 s |
| d5 elaboration | 5/6, 0.26 s | 5/6, 0.48 s |
| d1, d4, d8, d9 | — | same verdicts, 5-100% slower |

`tests/rare/list-empty.rare` is checked under both.

**Still open**, unchanged from §29: a list parameter that binds several
arguments is proved but cannot be *cited*, since a `rare_rewrite` step has
no form for it.  Commit 18d43bf0 writes such an argument as a `rare-list`
term, which the parser and printer now round-trip, so the form exists in
Carcara; whether it belongs in Alethe is a proof-format decision.

## 31. What the encodings actually buy, and what cvc5's holes are blocked on (2026-09-20)

Both list encodings are now selectable (`--rare-list-encoding`), so the
question "does the set form help?" can be asked of a corpus rather than of
the diagnostics.  Two measurements, one of them the more useful for being
negative.

### cvc5's kept holes are not blocked on rules

Reading every `kept as trusted` line of the `chk1200h2` run (9,812
benchmarks, two checking passes, 120,841 kept-hole events):

| reason | events |
|---|---|
| per-hole time budget exhausted during egglog | 60,790 |
| worker killed: memory allocation failed (8 GB) | 37,564 |
| e-graph grew past the tuple cap | 17,079 |
| the proof's own hole budget ran out | 4,465 |
| every goal fallback failed (rounds exhausted) | 933 |

Every one of the 17,079 "egglog check failed" holes says *grew past the
bound*; **not one** says the goal was unreachable after the rounds.  So
0.8% of cvc5's kept holes are coverage misses and the rest are resource
kills.  A better rule encoding cannot move that corpus: no cvc5 hole is
waiting for a rule.  What would move it is saturation cost, and there the
set form is the wrong lever -- it *adds* to the e-graph rather than
replacing the chain.

The biggest identifiable family confirms it.  Of the cap kills, 10,446
have an `or` left-hand side and 2,343 an `and`; `Referendum-PT-1000/RF-06`
is typical, four holes that flatten a nested `or` over 1,000 literals.  At
the production cap (3M tuples) both encodings keep all four; at 30M both
prove all four, the chain in 58 s and the set form in 72 s.  The set form
is not what those holes need, and the cap is.

### veriT is where the list rules matter

The shapes that need an empty `:list` are veriT's, not cvc5's: the
diagnostics move from 2 of 3 to 3 of 3 on d2's checking (34.4 s to 0.14 s)
and the corpus run of §30 loses a quarter of its kept holes.  The corpus
A/B under one binary is running as this is written.

### The remaining diagnostic failures

d3 and d5's sixth shape -- the complementary pair under a `not` -- are
closed by commit be7d8658 (the constant intermediate).  d2's `bool_simplify`
holes are the one shape left, and they are a certificate-search failure,
not an engine one: checking proves them in 0.2 s, the reconstruction gives
up in the same time.  It is not a budget (256, 1024, 4096 and 16384 states
all fail identically, and so do 4, 32 and 256 rejustification attempts) and
not a verification rejection (nothing is logged as a rejected step).  The
path simply is not in the candidate graph: the derivation rewrites *inside*
a nested implication, so no rule instance grounds at the root, and the only
way to walk to a class-mate that differs deep inside is to substitute a
subterm.  Two widenings were tried and neither moves it.  Substituting an
arbitrary class-mate rather than a constant changes nothing: grounding the
alternative's children goes through the preferred representatives, which
are the goal's own subterms.  Counting only *wrapped* positions against the
substitution bound -- the encoding spends six nodes on a variable, so 32 raw
positions cover barely two arguments of a real term -- reaches deeper but
also changes nothing, and costs 2 to 3 times the elaboration time on the
small proofs, so it was dropped.

The diagnosis that remains is that the intermediate terms never become
vertices at all.  `ground` binds every pattern variable to
`self.representative(class)`, so a rule instance is spelled with the goal's
own subterms; a derivation that rewrites inside a nested implication
produces no instance anchored at the root, and the root enode itself never
changes, since rewriting merges the inner class rather than replacing it.
Grounding a match through the matched enode's own children, instead of the
class's preferred representative, is the change that would give the search
those vertices.

## 32. The cancelled run, read (2026-09-20)

§31's taxonomy came from `chk1200h2`, which is complete but runs neither
the normalizer nor the elaboration pass.  `chk1200n` does both; it was
cancelled after QF_UF, and its partial `results.json.gz` covers **951
proofs**, which is enough to say what the current pipeline actually leaves
behind.

| | holes |
|---|---|
| after hoisting | 513,596 |
| plain checking pass: proved / kept | 510,626 / 2,970 |
| normalized pass: proved / kept | 512,953 / **643** |
| closed by the normalizer alone, no egglog | 162,605 (31.7%) |
| remaining in the elaborated proof | **5,346** (1.0%) |

The elaborated proofs re-check: **390 valid**, 532 holey, 2 error, 10 with
no cvc5 proof, 17 tasks cut off.  Of the 532 holey ones, 23 are one hole
short of valid and 439 are within five.  Elaboration cost 15,298 s of wall
across the 951 proofs and the re-check 2,202 s.

The normalizer is worth more than any cap: it closes a third of all holes
outright and cuts the checking pass's kept holes by 78%.  §31's conclusion
stands but its emphasis was wrong -- cvc5's holes are not blocked on rules,
and the largest slice of what `chk1200h2` called a cap kill never reaches
egglog at all once the normalizer runs (`Referendum-PT-1000/RF-06`: four
holes, 50 s to fail at the production cap, 72 s to succeed at ten times it,
**0.003 s** to close under `--hole-prenormalize`).

What the residue is made of, across both passes:

| reason | holes |
|---|---|
| e-graph grew past the tuple cap | 2,507 |
| no certificate found (the search) | 2,214 |
| per-hole time budget | 1,240 |
| the reconstructed steps were rejected by the checker | 517 |
| memory | 430 |
| the proof's hole budget | 16 |

So the certificate search, not the engine, is now the largest addressable
class: 2,214 + 517 against 2,507 cap kills.  And all 517 rejections are one
bug, fixed in 1feffecc: the reconstruction emitted `(ite true t u) = t` as
an `evaluate` step, and Carcara's evaluator decides an application of
interpreted operators to *values* -- it needs every argument to evaluate,
so an `ite` with arbitrary branches is not one of those.  It is the first
case of `ite_simplify`, which is what the step now cites.

## 33. The encodings, side by side (2026-09-20)

### veriT, one binary, 98 proofs, normalizer on in both arms

| | holes | proved | kept | skipped | time |
|---|---|---|---|---|---|
| `set-form` | 17,067 | **10,761** | **1,370** | **4,936** | 9,893 s |
| `chain` | 17,067 | 5,866 | 1,558 | 9,643 | 10,606 s |

Same binary, same folded proofs, same budgets, the two arms run one after
the other so they never shared the machine.  The set form proves 83% more
holes, keeps 12% fewer, and -- the number that explains the other two --
skips half as many.  Both arms are budget-bound at 300 s per proof, so the
proof runs out of budget with two thirds of its holes untried.  Per proof
the set form keeps fewer holes on 39 and more on 10, and is more than 10%
faster on 35 against 1.

**This is a throughput win, not a coverage win.**  The residue reasons of
the two arms contain *no* "goal not reached" at all: on the holes each arm
got to, `chain` -- with its empty-list variants -- reaches the same goals
the set form reaches.  What it does not do is reach them as cheaply.  The
cost is where the two encodings differ: a rule with a `:list` parameter
compiles to one set-form rule but to 2^k-1 chain variants, and on an n-ary
`and`/`or` a list parameter has to bind a *segment*, which the chain can
only produce by re-associating the argument chain.  That is why the gap
shows up on veriT and not on cvc5: measured per hole, 59% of the folded
veriT holes contain an `and`/`or` of arity 3 or more, against 3% of cvc5's
theory-rewrite holes, 76% of which contain no `and`/`or` at all.  The
earlier reading of this table -- that `chain` loses on the empty-list case,
and a depth-based reading of the same difference -- are both wrong.

### cvc5, the cap-kill sample

Three proofs whose `chk1200h2` residue was entirely growth-cap kills, at
the production cap and at ten times it, with and without the normalizer:

| proof (holes) | plain, 3M | normalizer, 3M | normalizer, 30M | normalizer, 3M, `chain` |
|---|---|---|---|---|
| RC-06 (76) | 66 proved, 10 kept, 283 s | 73, 3, 240 s | 73, 3, 240 s | 73, 3, **159 s** |
| v25_problem_2__029 (108) | 106, 2, 81 s | 108, 0, 17 s | 108, 0, 19 s | 108, 0, 18 s |
| problem__006 (102) | 100, 2, 60 s | 102, 0, 60 s→4 s | 102, 0, 4 s | 102, 0, 4 s |

Three readings.  The normalizer removes the residue and cuts the pass by
3 to 15 times.  **The ten-times cap adds nothing once the normalizer is
on** -- identical verdicts, identical time -- so the 17,079 cap kills of
§31 are not a cap problem.  And `chain` is no worse than the set form here
and sometimes faster (RC-06, 159 s against 240 s), which is the same
conclusion §31 reached from `RF-06`: cvc5 does not need the set form.

So the two producers want different things, and the run submitted as
`enc4` measures exactly that on cvc5 at scale, four configurations over one
hoisted proof per benchmark.

## 34. Coarse holes from the producer: veriT's preprocessing (2026-09-20)

The folded veriT holes of §33 are made by Carcara: `--pipeline fold` glues a
chain of `*_simplify`/`ac_simp` steps back together after veriT has already
spelled it out.  veriT can print the hole itself, which is both cheaper and
honest about where the granularity comes from.  The vendored copy in
`verit-2026.05/` now has

```
--proof-coarse-preprocessing
```

Its patch, against the 2026.05 sources, is kept in
`~/exp/egglog-holes/verit-coarse-preprocessing.patch`.

### What it does

`src/pre/pre.c` has two parallel pipelines, `pre_process` (no proof) and
`pre_process_array_proof` (proof).  The option does not switch between them.
Each stage of the proof pipeline still runs, unchanged, but inside a
subproof whose steps are thrown away (`proof_subproof_begin` ...
`proof_subproof_remove`), and what is logged in its place is one step

```
(step tN (cl (= F G)) :rule hole :args ("preprocessing" "<stage>"))
```

followed by the same `equiv_pos2` + resolution the detailed pipeline ends
with.  So the transformation, the formula it produces, and the search that
follows are bit for bit what they are without the option; only the
justification changes.  The stages that get a hole are `lang_red` (n-ary
and distinct elimination), `simplify_formula` (every call site, including
the ones inside `pre_ite_proof` and `pre_quant_ite_proof` and the one in
instance preprocessing) and `eq_rewrite`.  `bfun_elim`, `ite_intro` and
skolemization already log one step each and are left alone, and **let
elimination keeps its derivation**: its equivalence is a substitution, not a
rewrite any RARE rule states, and its `let` step is one Carcara checks
natively, so a hole there can only lose.

The `hole` rule is new on the veriT side (`ps_type_hole`), carries no
premises, and prints a tag Carcara matches on.  `"preprocessing"` joins
`THEORY_REWRITE_TAGS`, so the whole existing pipeline -- `--hole-check-only`,
elaboration, `hoist` -- treats these holes exactly like cvc5's.

### That the search is untouched, measured

`gensys_icl328` (QF_UF, QG-classification), same binary, `--proof-prune
--proof-merge`, rule histograms of the two proofs:

| | detailed | coarse |
|---|---|---|
| `resolution` | 6043 | 6043 |
| `and_pos` / `and` / `or` / `not_and` / `not_not` | 733 / 200 / 98 / 110 / 110 | identical |
| `eq_transitive` / `eq_congruent` / `eq_reflexive` / `contraction` | 1381 / 113 / 30 / 94 | identical |
| `cong` + `refl` + `trans` + `ac_simp` + `*_simplify` + `let` | 4454 | 0 |
| `hole` | 0 | 135 |
| steps | 15,059 | 10,731 |

Every search-level count is the same; 4,454 preprocessing steps become 135
holes.

### What the holes are worth

Checked through the RARE/egglog pipeline (8 workers, 20 s per hole, the
production caps), `gensys_icl328`: **123 of 135 holes proved in 6.8 s**.
The 12 kept split 6 `let_elim` and 6 `simplify_formula`, all of them the
large ones -- a `let_elim` hole is a substitution over a whole assertion,
which is not a rewrite any RARE rule states.

Over 40 benchmarks -- a slice of QG-classification plus the QF_UF, QF_LIA
and QF_LRA eval sets -- 32 give an unsat proof and **528 holes, 456 proved
(86%), 72 kept, none skipped** (with let elimination left detailed; when it
was a hole too the same set gave 578 holes, 469 proved, 81%, and 24 of the
109 kept were `let_elim` -- dropping it removes 50 holes and 37 of the
residue).  The shape is uneven and worth keeping in view:

- whole proofs close: `BART-PT-020__RC-00` 144/144, `BART-PT-050__RC-05`
  49/49, the Bromberger slack benchmark 11/11, `gensys_icl328` 119/125,
  `gensys_icl077` 125/133;
- the QF_UF hwbench family produces **no holes at all** -- veriT's
  preprocessing does nothing there, so there is nothing to make coarse;
- the residue concentrates in QF_LRA/QF_LIA with heavy arithmetic
  preprocessing: `clocksynchro_*.induct` 0/2,
  `ReachSafety-Loops__deep-nested-O0` 1/7, the two Heizmann proofs 11/25
  and 17/28.

The residue is 37 `simplify_formula` and 5 `eq_rewrite`, plus per-hole
budget kills at 20 s on the large ones.  There is one cause, not two: a hole
that covers a whole assertion is too big for one attempt, either past the
growth cap or past the budget.  A per-assertion `simplify_formula` hole is
much coarser than a cvc5 theory-rewrite hole, and the natural next knob is a
bound on how much a single hole may cover -- the analogue of the fold pass's
`--fold-limit`, but at the point the derivation is made.

### Bounding how much one hole covers

A hole per stage per assertion is very coarse, and the residue above is
entirely holes that are too big for one attempt.  `--proof-hole-size=N`
bounds it, in DAG nodes:

```
--proof-coarse-preprocessing --proof-hole-size=50
```

The stage still runs once, on the whole assertion, so the result is
unchanged.  What changes is how its equivalence is written down:
`pre_hole_equiv` walks `src` and `dest` in parallel and, while the two have
the same top symbol and arity and the pair is bigger than the bound,
descends into the arguments that differ and puts the pieces back together
with one `cong` step.  A hole is emitted where the pair is small enough, or
where the two sides stop having the same shape -- which is as far as
congruence can go.  Binders are never entered (that would need `bind`).

```
(step t3 (cl (= (or false (f A) (f A)) (f A)))   :rule hole ...)
(step t4 (cl (= (or (g A) (g A) false) (g A)))   :rule hole ...)
(step t5 (cl (= (and true (h A)) (h A)))         :rule hole ...)
(step t6 (cl (= (and (or false (f A) (f A)) ...) (and (f A) (g A) (h A))))
     :rule cong :premises (t3 t4 t5))
```

Over the same 40 benchmarks, at `N = 50`, leaving out one outlier treated
below (31 proofs):

| | holes | proved | kept | time |
|---|---|---|---|---|
| `N = 0` | 521 | 455 (87.3%) | 66 | 571 s |
| `N = 50` | 1,804 | **1,729 (95.8%)** | 75 | **500 s** |
| `N = 50` + normalizer | 1,804 | **1,745 (96.7%)** | 59 | **281 s** |

Bounding the hole buys 8.5 points of closure and costs *less* wall-clock,
because what it removes is the 20 s each impossible whole-assertion hole was
burning.  On the two worst proofs:

| proof | holes, N=0 | proved | holes, N=50 | proved |
|---|---|---|---|---|
| `clocksynchro_7clocks.induct` | 2 | **0** | 52 | **51** |
| Heizmann `bubblesort` | 25 | 11 (44%) | 900 | **851 (95%)** |

It is not free: the `cong` glue is steps (Heizmann 2,562 -> 3,575), and on a
proof with many rewrites the many small holes cost more wall-clock in total
than a few impossible ones (Heizmann 34 s -> 228 s).  But it is time spent
on goals that close.

**The outlier, and what it says about the knob.**
`ReachSafety-Loops__deep-nested-O0` goes from 7 holes to **16,236**, and the
300 s per-proof budget gets through 5,497 of them -- 18 kept, the other
10,721 never attempted.  The bound is not what produces that number: at
`N = 200` and at `N = 1000` the count is the same 16,227, because the
formula is a deep spine with a separate small rewrite hanging off nearly
every level.  Descending the spine, each differing child is already far
below the bound, so the bound never gets to bundle anything.  Its holes do
not fail, there are simply too many of them for the budget: for this shape
the knob to turn is the budget, not the granularity.

**What it cannot split.**  When the stage rewrites the *root* into a
different shape, congruence has no footing.  The one hole left in
`clocksynchro_7clocks.induct` is `ac_simp` flattening a left-nested binary
`and` chain into a flat 159-ary one: arity 2 against arity 159 at the root,
so the split stops immediately and the hole is the whole assertion.  egglog
dies on it either way (38,215,762 tuples against a 3M cap at 180 s).  The
hole normalizer closes it in 0.02 s -- it is exactly an `aci_simp` -- so
with `--hole-prenormalize` that proof goes **52 of 52**.

### `--expand-let-bindings` is a cvc5 flag

Checking these proofs with `--expand-let-bindings`, as the cvc5 runners do,
makes veriT proofs that contain `let` steps come out `invalid`: the flag
expands the very `(let ...)` term the `let` rule is about, and the rule then
reports the premise is "of the wrong form, expected `(let ...)`".  Dropped,
the same proofs are `valid`.  Nothing to do with veriT or with this option;
a veriT runner must not pass it.

### The `eq_rewrite` residue is a cap kill, not a missing rule

`eq_rewrite` is veriT's `pre_eq`, on in QF_IDL/RDL/LRA/LIA/LIRA: it replaces
every arithmetic equality by a conjunction of two inequalities, which
veriT justifies with `la_rw_eq`, `(= (= t u) (and (<= t u) (<= u t)))`.
RARE states the same rewrite the other way round -- `arith-eq-elim-int` and
`arith-eq-elim-real` give `(and (>= t s) (<= t s))` -- and `arith-elim-leq`,
`(= (<= t s) (>= s t))`, bridges the two orientations, so the engine does
have what it needs.  A minimal hole `(= (= x y) (and (<= x y) (<= y x)))`
over two reals is proved in **0.19 s**.

What fails is the size.  An `eq_rewrite` hole is a whole assertion: on
`clocksynchro_7clocks.induct` it is 33 KB of arithmetic in which every
equality splits at once, and the run ends "the e-graph grew past the bound
(14,157,290 tuples, cap 3,000,000)".  The same proof's `lang_red` and
`simplify_formula` holes, also whole assertions, are killed by the 20 s
per-hole budget.  So the arithmetic residue here is the granularity, not the
rule set -- the same conclusion §31 reached about cvc5's cap kills, arrived
at from the other side.
