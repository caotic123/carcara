# Evaluate Rules — Expected Results

## Boolean Operations ✅

| Input | Expected Result | Status |
|-------|-----------------|--------|
| `(not b)` | `¬eval(b)` | ✅ |
| `(ite b x y)` | `eval(b) ? eval(x) : eval(y)` | ✅ |
| `(or b bs)` | `eval(b) ∨ eval(bs)` | ✅ |
| `(=> b b2)` | `¬eval(b) ∨ eval(b2)` | ✅ |
| `(and b bs)` | `eval(b) ∧ eval(bs)` | ✅ |
| `(xor b b2)` | `eval(b) ⊕ eval(b2)` | ✅ |

## Equality ✅

Note: Equality uses `:when` conditions since egglog's `=` is not decidable in RHS.

| Input | Condition | Expected Result | Status |
|-------|-----------|-----------------|--------|
| `(= x y)` | both rationals | `:when ((= (* n1 d2) (* n2 d1)))` → `true`/`false` | ✅ |
| `(= x y)` | both integers | `:when ((= x y))` → `true`/`false` | ✅ |
| `(= x y)` | both booleans | `:when ((= x y))` → `true`/`false` | ✅ |

## Arithmetic Comparisons ✅

| Input | Expected Result | Status |
|-------|-----------------|--------|
| `(< x z)` | `eval(x) - eval(z) < 0` → `true`/`false` | ✅ |
| `(<= x z)` | `eval(x) - eval(z) ≤ 0` → `true`/`false` | ✅ |
| `(> x z)` | `eval(z) - eval(x) < 0` → `true`/`false` | ✅ |
| `(>= x z)` | `eval(z) - eval(x) ≤ 0` → `true`/`false` | ✅ |

## Arithmetic Operations ✅

| Input | Expected Result | Status |
|-------|-----------------|--------|
| `(+ x ys)` | `eval(x) + eval(ys)` (Int or Real preserved) | ✅ |
| `(- x z)` | `eval(x) - eval(z)` (Int or Real preserved) | ✅ |
| `(- x)` | `-eval(x)` | ✅ |
| `(* x ys)` | `eval(x) × eval(ys)` (Int or Real preserved) | ✅ |
| `(/ x y)` | `toQ(eval(x)) / toQ(eval(y))` → Rational | ✅ |
| `(/_total x y)` | `y = 0 ? 0/1 : toQ(eval(x)) / toQ(eval(y))` | ✅ |
| `(div i1 i2)` | `⌊eval(i1) / eval(i2)⌋` → Integer | ✅ |
| `(div_total i1 i2)` | `i2 = 0 ? 0 : ⌊eval(i1) / eval(i2)⌋` | N/A (not standard SMT-LIB) |
| `(mod i1 i2)` | `eval(i1) mod eval(i2)` → Integer | ✅ |
| `(mod_total i1 i2)` | `i2 = 0 ? eval(i1) : eval(i1) mod eval(i2)` | N/A (not standard SMT-LIB) |

## Arithmetic Conversions & Predicates ✅

| Input | Expected Result | Status |
|-------|-----------------|--------|
| `(to_real x)` | `eval(x)` as Rational (e.g., `5` → `5/1`) | ✅ |
| `(to_int x)` | `⌊eval(x)⌋` as Integer | ✅ |
| `(is_int x)` | `⌊eval(x)⌋ = eval(x)` → `true`/`false` | ✅ |
| `(abs x)` | `eval(x) < 0 ? -eval(x) : eval(x)` | ✅ |
| `(int.log2 i)` | `⌊log₂(eval(i))⌋` for positive integers | N/A (not standard SMT-LIB) |
| `(int.pow2 i)` | `2^eval(i)` | N/A (not standard SMT-LIB) |
| `(int.ispow2 i)` | `∃k. eval(i) = 2^k` → `true`/`false` | N/A (not standard SMT-LIB) |
