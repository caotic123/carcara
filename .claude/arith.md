# Arithmetic Normalization in RARE

This note explains how the arithmetic normalization pipeline works today.

The implementation is split across:

- `arith_poly_norm.egglog`: numeric polynomial normalization
- `arith_poly_norm_rel.egglog`: arithmetic relation normalization
- `arith_poly_norm.rs`: program-level gating and goal fallback setup
- `arith_poly_norm_rel.rs`: relation-bool fallback setup
- `engine.rs`: goal scheduling, fallback ordering, and source-shape injection

The important idea is:

- numeric arithmetic terms are normalized to `PolyN`
- arithmetic relation terms are normalized to canonical keys built from normalized `PolyN`
- goal equality is proved by comparing those canonical forms, not by replaying surface rewrites

## 1. When the Arithmetic Machinery Exists

The arithmetic machinery is not emitted for every problem.

`arith_poly_norm::uses_arith_machinery` enables it only when the problem-wide function inventory contains arithmetic-relevant syntax:

- arithmetic operators: `+`, `-`, `*`, `/`, `/_total`, `to_real`
- arithmetic relations: `<`, `<=`, `>`, `>=`
- numeric uninterpreted functions

That keeps non-arithmetic problems from paying for the extra ruleset.

## 2. What Triggers It

Goal checking in the engine runs in this order:

1. run the ordinary schedule
2. check raw equality `goal_lhs = goal_rhs`
3. if that fails and arithmetic is enabled, try numeric normalization
4. if that fails, try relation-bool normalization

So the arithmetic pipeline is a fallback, not the first mechanism.

There are two goal-facing entry points:

- `arithGoalPolyNfOf-demand` for numeric equality
- `arithRelBoolKeyOf-demand` for boolean equalities over arithmetic relations

The engine always injects both fallback plans when arithmetic support is enabled. Egglog decides whether the goal actually matches.

## 3. Why We Keep the Raw Term and Also Emit a Shape

This is the most subtle part.

The e-graph still stores the original SMT term, for example:

- `Mk (@+ args)`
- `Mk (@- args)`

But for `+` and `-` we also emit an arity-safe arithmetic view through:

- `arithSyntaxOf : Term -> Term`

Examples:

- `(+ a b c)` stays in the graph as raw `@+`, but gets
  `arithSyntaxOf(raw) = Mk (@arith_add2 (Args (Mk (@arith_add2 (Args a (Args b (Empty))))) (Args c (Empty))))`
- `(- a)` gets
  `arithSyntaxOf(raw) = Mk (@arith_neg1 (Args a (Empty)))`
- `(- a b c)` gets
  `arithSyntaxOf(raw) = Mk (@arith_sub2 (Args (Mk (@arith_sub2 (Args a (Args b (Empty))))) (Args c (Empty))))`

Why both?

- the rest of the rewrite system still expects the original SMT constructors
- `arith_poly_norm` should not infer operator arity from raw `Args`
- only the arithmetic normalizer consumes the arity-safe view

This is exactly what avoids the old unary-vs-binary ambiguity for `+` and `-`.

## 4. Data Model

### `MonN`

`MonN` is a sorted monomial:

- `MOne`: the constant monomial
- `MCons i64 MonN`: one hashed atom times the tail monomial

Atoms are identified by `arith_poly_atom_hash`.

### `PolyN`

`PolyN` is a sorted sparse polynomial:

- `PZero`
- `PCons MonN BigRat PolyN`

Each node is one monomial/coefficient pair followed by the rest of the polynomial.

The representation invariant is:

- monomials are kept in sorted order
- zero coefficients are removed
- equal monomials are merged by addition

## 5. Demand-Driven Structure

Almost every computed object uses the same pattern:

- a function `F`
- a relation `F-demand`
- rules that, when demand appears, recursively demand dependencies
- rules that `set` the function once the dependencies exist

This keeps the arithmetic rules lazy.

Typical pattern:

1. `F-demand x` appears
2. rules request the sub-results needed for `x`
3. once the sub-results exist, a `set (F x) value` rule fires

That is why there are many paired names like:

- `addPolyN` / `addPolyN-demand`
- `canonGeqPolyN` / `canonGeqPolyN-demand`
- `arithRelBoolKeyOf` / `arithRelBoolKeyOf-demand`

## 6. Core Numeric Functions

### `atomMonN`

Maps an opaque arithmetic atom to a one-atom monomial.

Flow:

1. `atomMonN-demand t`
2. hash `t` with `arith_poly_atom_hash`
3. produce `MCons hash MOne`

### `atomPolyN`

Lifts an atom into a one-term polynomial with coefficient `1`.

Flow:

1. `atomPolyN-demand t`
2. demand `atomMonN t`
3. return `PCons mon 1 PZero`

### `cmpMonN`

Lexicographic order on monomials.

Used by:

- `addPolyN` to merge sorted terms
- `mulMonN` to preserve canonical monomial order

### `mulMonN`

Sorted merge of two monomials.

Flow:

1. compare leading atom hashes
2. keep the smaller one first
3. recurse
4. duplicate hashes are preserved, so exponent is encoded by repetition

### `scalePolyN`

Multiply every coefficient by a rational constant.

Special cases:

- multiplying by `0` returns `PZero`
- multiplying by `1` is identity
- zero coefficients are dropped

### `addPolyN`

Merge-addition of two sorted sparse polynomials.

Flow:

1. compare leading monomials with `cmpMonN`
2. if equal, add coefficients
3. if the coefficient sum is zero, drop the term
4. otherwise keep the smaller leading monomial and recurse

### `mulMonIntoPolyN`

Multiply one monomial/coefficient pair into a polynomial.

It is a helper used by `mulPolyN`.

### `mulPolyN`

Distributes one polynomial over another.

Flow:

1. multiply the head term into the other polynomial
2. recurse on the tail
3. add the two partial products with `addPolyN`

### `polyIsConstN` and `polyConstN`

Recognize a constant polynomial and extract its rational value.

These are used mainly by `/` and `/_total`, where only constant denominators are scaled through. Non-constant denominators stay opaque.

## 7. `arithPolyNfOf`: Numeric Normalization

`arithPolyNfOf` is the main numeric normal form function.

Important detail:

- it is declared `:no-merge`

So for a given `Term` e-class, egglog is not allowed to derive two different `PolyN` values. That is a safety property, not just an optimization.

### Base cases

It directly normalizes:

- integer literals
- real/rational literals
- variables
- numeric uninterpreted functions through `declare_opaque_arith_poly_rules`

### `+` and `-`

These do not normalize from raw `@+` and `@-` shape anymore. They normalize from the arity-safe helper terms:

- `@arith_pos1`
- `@arith_add2`
- `@arith_neg1`
- `@arith_sub2`

Raw source `+` and `-` first go through:

1. `arithPolyNfOf-demand raw`
2. look up `arithSyntaxOf raw`
3. demand the safe helper term
4. copy the helper term normal form back to the raw term

That is what keeps arity stable inside the polynomial layer.

### `*`

`*` still uses raw SMT shape because it does not have the unary-vs-binary ambiguity problem here.

Flow:

1. n-ary `*` is left-associated on demand
2. binary `*` normalizes both sides
3. multiply polynomials with `mulPolyN`

### `/` and `/_total`

Flow:

1. n-ary forms are left-associated on demand
2. normalize numerator and denominator
3. if denominator is a nonzero constant polynomial, scale numerator by its inverse
4. if denominator is zero for `/_total`, return `0`
5. otherwise keep the whole division term opaque via `atomPolyN`

### `to_real`

`to_real` is erased at the polynomial level:

1. demand the child
2. return the same `PolyN`

That is sound because coefficients are already rationals.

## 8. Goal-Facing Numeric Wrapper

The engine does not compare `arithPolyNfOf(goal_lhs)` directly.

Instead it uses:

- `arithGoalPolyCanMatch`
- `arithGoalPolyNfOf`

Purpose:

- guard the fallback so non-numeric goals do not pretend to be numeric
- keep goal-side checks separate from internal normalization

Flow:

1. demand `arithGoalPolyNfOf goal_lhs`
2. run `arith_poly_guard`
3. check `arithGoalPolyCanMatch goal_lhs = true`
4. demand both goal sides
5. saturate `arith_poly`
6. compare `arithGoalPolyNfOf goal_lhs` and `arithGoalPolyNfOf goal_rhs`

## 9. Relation Normalization

`arith_poly_norm_rel.egglog` handles arithmetic comparisons and boolean equalities between them.

The main idea is:

- convert a relation into a normalized difference polynomial
- canonicalize that polynomial depending on relation kind
- wrap it in a relation key

### Difference extraction

The relation path uses:

- `@arith_sub2(x1, x2)`
- optionally `to_real(@arith_sub2(...))`

through `arithPolyNormRelDiff`.

This keeps relation normalization aligned with the same safe subtraction notation used by the numeric layer.

### Integer-sensitive helpers

Subtle but important helpers:

- `atomHashIsInt`
- `monIsIntN`
- `polyIsIntExprN`

These track whether an expression is integer-valued after normalization, which matters for tightening strict-vs-nonstrict inequalities.

### Structural helpers

- `relConstN`: constant part of a relation polynomial
- `relRestN`: non-constant part
- `relScaleAbsN`: absolute leading scale used for canonicalization

### Canonicalizers

`canonRelPolyN`

- normalizes up to positive scaling
- used for strict order keys

`canonGeqPolyN`

- canonical form specialized for `>=`
- contains the integer-tightening behavior
- for integer expressions, it can absorb a negative constant offset into the threshold

`canonEqPolyN`

- canonical form for equality
- normalizes up to sign

## 10. Relation Keys

Once the relation polynomial is canonicalized, the relation becomes a key:

- `EqRelKey`
- `GeqKey`
- `GtKey`
- `LeqKey`
- `LtKey`

Those keys are what the goal fallback compares, not the original formulas.

This means formulas such as:

- `(>= a b)`
- `(<= b a)`

can converge to the same key even if the surface syntax differs.

## 11. `arithRelBoolKeyOf`: Boolean Equality over Relations

This is the second fallback path.

It covers boolean formulas of the forms:

- `(= x y)` where `x` and `y` are arithmetic expressions
- `<`, `<=`, `>`, `>=`
- `not` around those relation atoms

Flow:

1. `arithRelBoolKeyOf-demand goal_lhs`
2. `arith_poly_guard` proves the lhs is a supported relation-shaped boolean
3. `arithRelBoolKeyOf-demand` on both sides
4. relation rules derive canonical keys
5. compare `arithRelBoolKeyOf goal_lhs` and `arithRelBoolKeyOf goal_rhs`

Strict inequalities use `strictOrderBoolKeyN`, which is where integer-valued expressions are shifted so that:

- strict integer order can be reduced to a non-strict canonical form

That is why examples like:

- `(> x y)`
- `(not (>= y x))`

can normalize to the same key.

## 12. Equality by Normalization

There are two equality-by-normalization modes.

### Numeric equality

Used when both sides are arithmetic expressions.

Proof condition:

- `arithGoalPolyNfOf(lhs) = arithGoalPolyNfOf(rhs)`

### Relation-boolean equality

Used when both sides are boolean arithmetic relations.

Proof condition:

- `arithRelBoolKeyOf(lhs) = arithRelBoolKeyOf(rhs)`

This is stronger than textual rewriting and weaker than arbitrary boolean reasoning. It is intentionally specialized.

## 13. Subtle Details and Design Constraints

### `:no-merge` vs `:merge old`

Use `:no-merge` for semantic normal forms:

- `arithPolyNfOf`
- `addPolyN`
- `mulPolyN`
- `canonGeqPolyN`

If two different values are derived there, something is wrong.

Use `:merge old` for memo-like views or keys that may be derived from several equivalent presentations:

- `arithSyntaxOf`
- `relPolyOf`
- `eqRelPolyOf`
- `arithRelBoolKeyOf`

### Why only `+` and `-` get source-shape lowering

That is the smallest useful fix.

- they define the polynomial structure
- they are the operators whose arity can be confused by raw `Args` equalities
- `*`, `/`, `/_total`, and `to_real` do not create the same unary-vs-binary ambiguity here

### Why raw terms stay in the graph

The general rewrite system still wants the original SMT constructors.

So we do not replace raw syntax with helper syntax globally. We only give the arithmetic normalizer a second, safer view.

### Why demand relations exist everywhere

Without demands, the arithmetic ruleset would eagerly normalize every reachable arithmetic subterm and relation. That would be much more expensive.

Demand relations make normalization happen only when:

- a goal fallback needs it
- a dependent arithmetic or relation rule explicitly asks for it

## 14. Practical Mental Model

If a goal looks numeric:

1. normalize both sides to `PolyN`
2. compare the resulting polynomials

If a goal looks like equality between arithmetic relations:

1. turn each relation into a canonical relation key
2. compare the resulting keys

If neither path matches:

- arithmetic normalization does nothing
- the goal must be solved by ordinary rewriting or another subsystem
