# Running examples

Choose one example, for instance:

If you choose:
tests/rare/sliced_proofs/Examples/mathsat/EufLaArithmetic/medium/medium11/medium11__from-t24.smt2.alethe

carcara elaborate tests/rare/sliced_proofs/Examples/mathsat/EufLaArithmetic/medium/medium11/medium11__from-t24.smt2.alethe tests/rare/sliced_proofs/Examples/mathsat/EufLaArithmetic/medium/medium11/medium11.smt2  --rare-file tests/rare/big.rare   --hole-solver rare_rewrite   --pipeline polyeq lia-generic local uncrowd reordering hole local   --expand-let-bindings   --allow-int-real-subtyping   --parse-hole-args   --no-print-with-sharing

You should see something like:

```
Running goal check schedule round 1...
Elaboration succeeded in 0.110811s
holey
(step t24.t1 (cl (= (or (or (or (or (or (or (or (or (or (or (or (= y 0) (= y 1)) (= y 2)) (= y 3)) (= y 4)) (= y 5)) (= y 6)) (= y 7)) (= y 8)) (= y 9)) (= y 10)) (= y 11)) (or (= y 11) (= y 10) (= y 9) (= y 8) (= y 7) (= y 6) (= y 5) (= y 4) (= y 3) (= y 2) (= y 0) (= y 1)))) :rule hole :args ("TRUST_THEORY_REWRITE"))
caotic@tiago:~/Workspace/carcara$ 
```