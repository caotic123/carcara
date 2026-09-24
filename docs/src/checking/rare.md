# Checking Rare rewrites

SMT solvers can produce proofs that may depend on rare rules. In general, rare rules have the following format:

```
(declare-rare-rule bool-implies-de-morgan ((x1 Bool) (y1 Bool))
  :args (x1 y1)
  :conclusion (= (not (=> x1 y1)) (and x1 (not y1)))
)
```

First, we have a set of arguments and a conclusion. We can substitute the arguments into the conclusion. The substitution can be any first-order term available in the Alethe context.

```
(step st191.t1 
  (cl (= (not (=> (not (member$ ?v0 ?v1)) (= ?v0 ?v2)))
         (and (not (member$ ?v0 ?v1)) (not (= ?v0 ?v2)))))
  :rule rare_rewrite
  :args ("bool-implies-de-morgan" (not (member$ ?v0 ?v1)) (= ?v0 ?v2)))
```

Arguments can also be polymorphic:

```lisp
(declare-rare-rule eq-refl ((@T0 Type) (t1 @T0))
  :args (t1)
  :premises ()
  :conclusion (= (= t1 t1) true))
```

We use `@Type` to denote an argument that is a polymorphic type. Polymorphic arguments are not passed in the `:args` field of the step statement:

```lisp
(step t264
  (cl (= (= (op e3 e3) (op e3 e3)) true))
  :rule rare_rewrite
  :args ("eq-refl" (op e3 e3)))
```

## Flags

We use the `--rare-file` flag to pass the rare file, for example:

```bash
carcara check your_file.smt2.alethe your_file.smt2 --rare-file your_rare_file.rare
```

Note that Carcara will only be able to check your proofs if every rewrite rule mentioned in the Alethe file is also present in your rare file.

## Translating RARE rules to Eunoia

`translate eunoia` compiles the definitions supplied with `--rare-file` into
the output proof, before translating their uses:

```bash
carcara translate eunoia \
  --eunoia-mech /path/to/AletheInEunoia/signature \
  --rare-file rules.rare proof.alethe problem.smt2 > proof.eo
ethos proof.eo
```

The signature must provide `$normalize_eo_list` and `$normalize_eo_pairwise`
in `programs/lists.eo` (tested with Ethos 0.2.4). There is no separate RARE
support file.

Every definition in the supplied database is emitted, in declaration order,
under generated `@rare.rule.N` names. Rule compilation is independent of the
proof. Proof references and argument shapes are validated separately. A missing
definition is an error; translation does not load a fixed `rules/rare_rules.eo`
file. An unsupported definition is an error even when the proof does not use it.

List arguments remain sequences: bare `rare-list` becomes `eo::List::nil`,
and `(rare-list a b)` becomes `(eo::List::cons a b)`. A parameter declared
`(xs Bool :list)` becomes `(xs eo::List :list)` in the generated rule. Each
associative application assembles its operands and invokes:
`($normalize_eo_list ElementType ResultType operator sequence)`.
Consequently, the same `xs` may occur under both `and`
and `or`: an empty sequence is interpreted as `true` and `false`, respectively.
The normalizer uses the two nil/cons cases to build a full operator spine.
Carcara wraps that result in `eo::list_singleton_elim`, so singleton elimination
happens only after the complete application is assembled.
Ordinary nested formulas remain individual operands.

The compiler currently handles list occurrences in `and`, `or`, homogeneous
`+` and `*`, and pairwise `distinct`. Pairwise comparisons are generated after
all sequence fragments are concatenated. Carcara's `Distinct` case dispatches
to `($normalize_eo_pairwise ElementType distinct sequence eo::List::nil)` and
applies `eo::list_singleton_elim and` to its result. The pairwise program accepts
the comparison operator as a parameter; it does not match on `distinct`.
Its last argument starts empty and internally holds the left operand of a
comparison row.

List element types are checked by generated requirements using
`$normalize_eo_list` with `eo::List::cons`, which preserves the carrier and
validates its elements, including unused list parameters. Polymorphic element
types are recovered using `eo::typeof` on a scalar argument of that type.

Premises are bound as formulas and checked against their computed RARE
templates using `:requires`. Conclusions use `:conclusion`, since
`:conclusion-explicit` cannot match an evaluatable normalizer expression.

Unsupported constructs produce a diagnostic before any Eunoia output is
printed. These currently include list splicing into other operators or
arbitrary functions, mixed numeric sorts within an associative application,
binders, bitvector/string sorts, and value parameters that must be inferred
only from premises. A polymorphic type must be an explicit argument or have
a scalar argument from which it can be recovered.

### Regression checks

The ordinary Rust suite checks declaration generation and error handling.
The integration test invokes both the Carcara CLI and Ethos on generated
proofs, including empty/singleton/nonempty sequences, shared `and`/`or`
parameters, nested operands, computed premises, arithmetic, and polymorphic
pairwise rules. It also checks rejection of incorrect conclusions and types:

```bash
ALETHE_EUNOIA_SIGNATURE=/path/to/AletheInEunoia/signature \
ETHOS=ethos \
cargo test --test test_eunoia_rare generated_rules_check_in_ethos -- --ignored --nocapture
```
