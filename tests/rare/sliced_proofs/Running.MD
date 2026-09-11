# Running examples

## Elaborating a full cvc5 proof

`carcara elaborate --elaborate-hole-rewrites` replaces every `hole` step
marked `TRUST_THEORY_REWRITE` by a checked subproof: the egglog engine
proves the rewrite, a certificate is reconstructed from its saturated
e-graph, and the certificate's Alethe steps are checked against the RARE
database before being inserted. For instance, on a cvc5 QF_LIA proof with
two trust holes:

    carcara elaborate tests/rare/elaborate/RF-12.smt2.alethe tests/rare/elaborate/RF-12.smt2 \
      --rare-file tests/rare/big.rare --elaborate-hole-rewrites --pipeline hole \
      --expand-let-bindings --allow-int-real-subtyping --parse-hole-args --no-print-with-sharing

The printed proof contains no `TRUST_THEORY_REWRITE` hole, and checks as
`valid` without `--check-hole-rewrites`:

    carcara check <elaborated.alethe> tests/rare/elaborate/RF-12.smt2 --rare-file tests/rare/big.rare \
      --expand-let-bindings --allow-int-real-subtyping --parse-hole-args

The egglog options of the checking flags (`--continuous-saturation`,
`--rare-check-timeout`, `--print-egglog`) apply to the elaboration runs too.

## The slices in this directory

Each `<problem>__from-<step>.smt2.alethe` file is a proof fragment ending
at one trust hole, not a refutation, so `carcara elaborate` rejects it at
the checking stage (the proof does not conclude the empty clause). They
are exercised by the `egglog_egraph_reconstruction` integration test,
which drives the same pipeline hole by hole:

    BENCH_LIST=<tsv: alethe, smt2, hole id> BENCH_RARE=tests/rare/big.rare BENCH_OUT=<dir> \
      cargo test --test egglog_egraph_reconstruction -- --ignored reconstructs_benchmark_corpus --nocapture

writing one elaborated proof per hole into `BENCH_OUT`.
