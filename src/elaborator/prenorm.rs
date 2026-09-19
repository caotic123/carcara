//! Normalizing a hole's goal with Carcara's own normal forms before the
//! egglog engine sees it.
//!
//! cvc5's theory-rewrite holes are, for the most part, the arithmetic
//! rewriter's and the Boolean rewriter's normal forms: polynomial
//! normalization, constant evaluation, flattening of `and`/`or`, and the
//! canonical shape of linear relations.  Carcara already has decision
//! procedures for those (`poly_simp`, `evaluate`, `aci_simp`); this module
//! turns them into a normalizer that rewrites every subterm of a goal into a
//! canonical form.  A hole whose two sides normalize to the same term is
//! proved without egglog; the others reach egglog as the equality of the two
//! normal forms, with nothing left to normalize.
//!
//! Every step is an equivalence Carcara's checker can justify (`poly_simp`
//! and `poly_simp_rel` for the polynomial and relation forms, `evaluate`
//! for constants, `aci_simp` and `not_not` for the Boolean shapes), so a
//! certificate can cite them; only the checking use is wired up here.
use crate::ast::{
    Operator, Rc, Sort, Term,
    pool::{PrimitivePool, TermPool},
};
use indexmap::IndexMap;
use rug::{Integer, Rational};
use std::collections::HashMap;

/// A monomial: the atoms multiplied, sorted by pointer (one order per pool).
#[derive(Clone, Hash, PartialEq, Eq, Debug)]
struct Monomial(Vec<Rc<Term>>);

impl Monomial {
    fn one() -> Self {
        Self(Vec::new())
    }

    fn mul(&self, other: &Self) -> Self {
        let mut atoms = self.0.clone();
        atoms.extend(other.0.iter().cloned());
        atoms.sort_unstable_by_key(Rc::as_ptr);
        Self(atoms)
    }
}

/// A polynomial with rational coefficients over atoms (subterms that are
/// not arithmetic operations): monomials with their coefficients, in
/// insertion order.
#[derive(Clone, Debug, Default)]
struct Polynomial(IndexMap<Monomial, Rational>);

impl Polynomial {
    fn constant(value: Rational) -> Self {
        let mut poly = Self::default();
        poly.add_monomial(Monomial::one(), value);
        poly
    }

    fn atom(term: Rc<Term>) -> Self {
        let mut poly = Self::default();
        poly.add_monomial(Monomial(vec![term]), Rational::from(1));
        poly
    }

    fn add_monomial(&mut self, monomial: Monomial, coefficient: Rational) {
        if coefficient == 0 {
            return;
        }
        let entry = self.0.entry(monomial).or_insert_with(Rational::new);
        *entry += coefficient;
        if *entry == 0 {
            self.0.retain(|_, c| *c != 0);
        }
    }

    fn add(&mut self, other: &Self) {
        for (monomial, coefficient) in &other.0 {
            self.add_monomial(monomial.clone(), coefficient.clone());
        }
    }

    fn scale(&mut self, factor: &Rational) {
        if *factor == 0 {
            self.0.clear();
            return;
        }
        for coefficient in self.0.values_mut() {
            *coefficient *= factor;
        }
    }

    fn mul(&self, other: &Self) -> Self {
        let mut result = Self::default();
        for (m1, c1) in &self.0 {
            for (m2, c2) in &other.0 {
                result.add_monomial(m1.mul(m2), Rational::from(c1 * c2));
            }
        }
        result
    }

    fn constant_part(&self) -> Rational {
        self.0.get(&Monomial::one()).cloned().unwrap_or_default()
    }

    fn is_constant(&self) -> bool {
        self.0.keys().all(|m| m.0.is_empty())
    }

    /// The monomials in the canonical order: fewer atoms first, then by
    /// the atoms' pointers.
    fn sorted(&self) -> Vec<(&Monomial, &Rational)> {
        let mut entries: Vec<_> = self.0.iter().collect();
        entries.sort_by(|(a, _), (b, _)| {
            a.0.len().cmp(&b.0.len()).then_with(|| {
                a.0.iter()
                    .map(Rc::as_ptr)
                    .cmp(b.0.iter().map(Rc::as_ptr))
            })
        });
        entries
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ArithSort {
    Int,
    Real,
}

pub struct Normalizer {
    cache: HashMap<Rc<Term>, Rc<Term>>,
    /// How many subterms changed under normalization.
    pub rewritten: usize,
}

impl Default for Normalizer {
    fn default() -> Self {
        Self::new()
    }
}

/// A bound `(rel P c)` or a point `(= P c)` in normal form, as its relation, polynomial and
/// constant.
fn bound_parts(term: &Rc<Term>) -> Option<(Operator, &Rc<Term>, Rational)> {
    use Operator::*;
    match term.as_ref() {
        Term::Op(rel @ (LessThan | LessEq | GreaterThan | GreaterEq | Equals), args)
            if args.len() == 2 =>
        {
            Some((*rel, &args[0], args[1].as_signed_number()?))
        }
        _ => None,
    }
}

/// Whether `(x P a)` and `(y P b)` have no common solution; `Distinct` stands for `(not (= P a))`.
fn bounds_exclude(integer: bool, x: Operator, a: &Rational, y: Operator, b: &Rational) -> bool {
    use Operator::*;
    match (x, y) {
        (Equals, Equals) => a != b,
        (Equals, Distinct) | (Distinct, Equals) => a == b,
        (Equals, LessEq) | (LessEq, Equals) => if x == Equals { b < a } else { a < b },
        (Equals, LessThan) | (LessThan, Equals) => if x == Equals { b <= a } else { a <= b },
        (Equals, GreaterEq) | (GreaterEq, Equals) => if x == Equals { b > a } else { a > b },
        (Equals, GreaterThan) | (GreaterThan, Equals) => if x == Equals { b >= a } else { a >= b },
        (LessEq | LessThan, GreaterEq | GreaterThan) => {
            // upper a, lower b
            b > a || (b == a && (x == LessThan || y == GreaterThan)) || (integer && b > a)
        }
        (GreaterEq | GreaterThan, LessEq | LessThan) => bounds_exclude(integer, y, b, x, a),
        _ => false,
    }
}

/// Whether `(x P a)` or `(y P b)` holds for every value; `Distinct` stands for `(not (= P a))`.
fn bounds_cover(integer: bool, x: Operator, a: &Rational, y: Operator, b: &Rational) -> bool {
    use Operator::*;
    match (x, y) {
        (Distinct, Distinct) => a != b,
        (Distinct, LessEq) | (LessEq, Distinct) => if x == Distinct { b >= a } else { a >= b },
        (Distinct, LessThan) | (LessThan, Distinct) => if x == Distinct { b > a } else { a > b },
        (Distinct, GreaterEq) | (GreaterEq, Distinct) => if x == Distinct { b <= a } else { a <= b },
        (Distinct, GreaterThan) | (GreaterThan, Distinct) => if x == Distinct { b < a } else { a < b },
        (LessEq | LessThan, GreaterEq | GreaterThan) => {
            // upper a, lower b
            if integer {
                *b <= a.clone() + Rational::from(1)
            } else {
                b < a || (b == a && !(x == LessThan && y == GreaterThan))
            }
        }
        (GreaterEq | GreaterThan, LessEq | LessThan) => bounds_cover(integer, y, b, x, a),
        _ => false,
    }
}

impl Normalizer {
    pub fn new() -> Self {
        Self { cache: HashMap::new(), rewritten: 0 }
    }

    /// `term` in normal form.
    pub fn normalize(&mut self, pool: &mut PrimitivePool, term: &Rc<Term>) -> Rc<Term> {
        if let Some(known) = self.cache.get(term) {
            return known.clone();
        }
        let result = self.normalize_uncached(pool, term);
        if result != *term {
            self.rewritten += 1;
        }
        self.cache.insert(term.clone(), result.clone());
        result
    }

    fn normalize_uncached(&mut self, pool: &mut PrimitivePool, term: &Rc<Term>) -> Rc<Term> {
        match term.as_ref() {
            Term::Op(op, args) => {
                let args: Vec<Rc<Term>> =
                    args.iter().map(|arg| self.normalize(pool, arg)).collect();
                self.normalize_op(pool, term, *op, args)
            }
            Term::App(function, args) => {
                let function = self.normalize(pool, function);
                let args: Vec<Rc<Term>> =
                    args.iter().map(|arg| self.normalize(pool, arg)).collect();
                pool.add(Term::App(function, args))
            }
            _ => term.clone(),
        }
    }

    fn normalize_op(
        &mut self,
        pool: &mut PrimitivePool,
        original: &Rc<Term>,
        op: Operator,
        args: Vec<Rc<Term>>,
    ) -> Rc<Term> {
        use Operator::*;
        match op {
            Not => {
                let arg = &args[0];
                if let Term::Op(Not, inner) = arg.as_ref() {
                    return inner[0].clone();
                }
                if arg.is_bool_true() {
                    return pool.add(Term::new_bool(false));
                }
                if arg.is_bool_false() {
                    return pool.add(Term::new_bool(true));
                }
                // A negated bound is the opposite bound.
                if let Term::Op(rel @ (LessThan | LessEq | GreaterThan | GreaterEq), rel_args) =
                    arg.as_ref()
                {
                    if rel_args.len() == 2 {
                        if let Some(sort) = self.arith_sort(pool, &rel_args[0]) {
                            let negated = match rel {
                                LessThan => GreaterEq,
                                LessEq => GreaterThan,
                                GreaterThan => LessEq,
                                _ => LessThan,
                            };
                            let (lhs, rhs) = (rel_args[0].clone(), rel_args[1].clone());
                            return self.normalize_relation(pool, negated, &lhs, &rhs, sort);
                        }
                    }
                }
                // Negation normal form: a negated conjunction or disjunction is
                // the dual connective over the negated arguments.
                if let Term::Op(inner_op @ (And | Or), inner) = arg.as_ref() {
                    let dual = if *inner_op == And { Or } else { And };
                    let inner = inner.clone();
                    let negated: Vec<Rc<Term>> = inner
                        .iter()
                        .map(|x| self.normalize_op(pool, original, Not, vec![x.clone()]))
                        .collect();
                    return self.normalize_aci(pool, dual, negated);
                }
                pool.add(Term::Op(Not, args))
            }
            And | Or => self.normalize_aci(pool, op, args),
            Implies if args.len() == 2 => {
                let negated = self.normalize_op(pool, original, Not, vec![args[0].clone()]);
                self.normalize_aci(pool, Or, vec![negated, args[1].clone()])
            }
            Ite if args.len() == 3 => {
                if args[0].is_bool_true() {
                    return args[1].clone();
                }
                if args[0].is_bool_false() {
                    return args[2].clone();
                }
                if args[1] == args[2] {
                    return args[1].clone();
                }
                pool.add(Term::Op(Ite, args))
            }
            Add | Sub | Mult | RealDiv | ToReal => {
                let sort = match self.arith_sort(pool, original) {
                    Some(sort) => sort,
                    None => return self.evaluated(pool, Term::Op(op, args)),
                };
                let candidate = pool.add(Term::Op(op, args));
                let poly = self.polynomial(pool, &candidate);
                self.term_of_polynomial(pool, &poly, sort)
            }
            LessThan | LessEq | GreaterThan | GreaterEq if args.len() == 2 => {
                match self.relation_sort(pool, &args[0], &args[1]) {
                    Some(sort) => self.normalize_relation(pool, op, &args[0], &args[1], sort),
                    None => self.evaluated(pool, Term::Op(op, args)),
                }
            }
            Equals if args.len() == 2 => {
                if args[0] == args[1] {
                    return pool.add(Term::new_bool(true));
                }
                if let Some(sort) = self.relation_sort(pool, &args[0], &args[1]) {
                    return self.normalize_relation(pool, Equals, &args[0], &args[1], sort);
                }
                // `(= p true)` is `p`, `(= p false)` is `(not p)`.
                for (index, other) in [(0, 1), (1, 0)] {
                    if args[index].is_bool_true() {
                        return args[other].clone();
                    }
                    if args[index].is_bool_false() {
                        return self.normalize_op(pool, original, Not, vec![args[other].clone()]);
                    }
                }
                // Symmetric: one order per pair.
                let mut args = args;
                if Rc::as_ptr(&args[0]) > Rc::as_ptr(&args[1]) {
                    args.swap(0, 1);
                }
                self.evaluated(pool, Term::Op(Equals, args))
            }
            Distinct if args.len() == 2 => {
                let equality = self.normalize_op(pool, original, Equals, args);
                self.normalize_op(pool, original, Not, vec![equality])
            }
            // A distinct is the conjunction of the pairwise disequalities
            // (Alethe's `distinct_elim`); as a conjunction it meets cvc5's
            // expansion of it and a repeated element makes it false.
            Distinct => {
                let mut conjuncts = Vec::with_capacity(args.len() * (args.len() - 1) / 2);
                for i in 0..args.len() {
                    for j in i + 1..args.len() {
                        let equality = self.normalize_op(
                            pool,
                            original,
                            Equals,
                            vec![args[i].clone(), args[j].clone()],
                        );
                        conjuncts.push(self.normalize_op(pool, original, Not, vec![equality]));
                    }
                }
                self.normalize_aci(pool, And, conjuncts)
            }
            _ => self.evaluated(pool, Term::Op(op, args)),
        }
    }

    /// The term, evaluated when it is ground.
    fn evaluated(&mut self, pool: &mut PrimitivePool, term: Term) -> Rc<Term> {
        let term = pool.add(term);
        if let Term::Op(_, args) = term.as_ref() {
            if args.iter().all(|arg| matches!(arg.as_ref(), Term::Const(_))) {
                return term.evaluate(pool);
            }
        }
        term
    }

    fn normalize_aci(&mut self, pool: &mut PrimitivePool, op: Operator, args: Vec<Rc<Term>>) -> Rc<Term> {
        let (identity, absorbing) = match op {
            Operator::And => (true, false),
            _ => (false, true),
        };
        let mut flat: Vec<Rc<Term>> = Vec::new();
        for arg in args {
            match arg.as_ref() {
                Term::Op(inner, inner_args) if *inner == op => flat.extend(inner_args.iter().cloned()),
                _ => flat.push(arg),
            }
        }
        let mut kept: Vec<Rc<Term>> = Vec::new();
        for arg in flat {
            if arg.is_bool_true() == identity && (arg.is_bool_true() || arg.is_bool_false()) {
                continue;
            }
            if arg.is_bool_true() == absorbing && (arg.is_bool_true() || arg.is_bool_false()) {
                return pool.add(Term::new_bool(absorbing));
            }
            kept.push(arg);
        }
        kept.sort_unstable_by_key(Rc::as_ptr);
        kept.dedup();
        // `p` and `(not p)` together make the absorbing element, and so do
        // two bounds on one polynomial that are inconsistent (under `and`) or
        // that cover every value (under `or`).
        let negated: std::collections::HashSet<usize> = kept
            .iter()
            .filter_map(|arg| match arg.as_ref() {
                Term::Op(Operator::Not, inner) => Some(Rc::as_ptr(&inner[0]) as *const () as usize),
                _ => None,
            })
            .collect();
        let mut bounds: HashMap<usize, (bool, Vec<(Operator, Rational)>)> = HashMap::new();
        for arg in &kept {
            if let Some((rel, poly, value)) = bound_parts(arg) {
                let key = Rc::as_ptr(poly) as *const () as usize;
                let entry = match bounds.get_mut(&key) {
                    Some(entry) => entry,
                    None => {
                        let integer = self.arith_sort(pool, poly) == Some(ArithSort::Int);
                        bounds.entry(key).or_insert((integer, Vec::new()))
                    }
                };
                entry.1.push((rel, value));
            }
        }
        let under_and = op == Operator::And;
        let complemented = |x: &Rc<Term>| -> bool {
            let literal = match x.as_ref() {
                Term::Op(Operator::Not, inner) => {
                    kept.binary_search_by_key(&Rc::as_ptr(&inner[0]), Rc::as_ptr).is_ok()
                }
                _ => negated.contains(&(Rc::as_ptr(x) as *const () as usize)),
            };
            if literal {
                return true;
            }
            // A bound or a point against the bounds kept on its polynomial.
            let (rel, poly, value) = match x.as_ref() {
                Term::Op(Operator::Not, inner) => match bound_parts(&inner[0]) {
                    Some((Operator::Equals, poly, value)) => (Operator::Distinct, poly, value),
                    _ => return false,
                },
                _ => match bound_parts(x) {
                    Some(parts) => parts,
                    None => return false,
                },
            };
            let Some((integer, others)) = bounds.get(&(Rc::as_ptr(poly) as *const () as usize))
            else {
                return false;
            };
            others.iter().any(|(other, bound)| {
                if under_and {
                    bounds_exclude(*integer, rel, &value, *other, bound)
                } else {
                    bounds_cover(*integer, rel, &value, *other, bound)
                }
            })
        };
        if kept.iter().any(|arg| {
            matches!(arg.as_ref(), Term::Op(Operator::Not, _)) && complemented(arg)
        }) {
            return pool.add(Term::new_bool(absorbing));
        }
        // So does an argument of the dual connective whose every argument is
        // complemented here: `(and (or p q) (not p) (not q))` is false.
        let dual = if op == Operator::And { Operator::Or } else { Operator::And };
        if kept.iter().any(|arg| match arg.as_ref() {
            Term::Op(inner_op, inner) if *inner_op == dual => inner.iter().all(complemented),
            _ => false,
        }) {
            return pool.add(Term::new_bool(absorbing));
        }
        // A member of such an argument that is complemented here is redundant
        // in it: `(or p (and (not p) q))` is `(or p q)`.
        let filtered: Vec<Option<Vec<Rc<Term>>>> = kept
            .iter()
            .map(|arg| match arg.as_ref() {
                Term::Op(inner_op, inner) if *inner_op == dual => {
                    let rest: Vec<Rc<Term>> =
                        inner.iter().filter(|m| !complemented(m)).cloned().collect();
                    (rest.len() < inner.len()).then_some(rest)
                }
                _ => None,
            })
            .collect();
        if filtered.iter().any(Option::is_some) {
            let mut rebuilt = Vec::with_capacity(kept.len());
            for (arg, rest) in kept.iter().zip(filtered) {
                match rest {
                    Some(rest) => rebuilt.push(self.normalize_aci(pool, dual, rest)),
                    None => rebuilt.push(arg.clone()),
                }
            }
            return self.normalize_aci(pool, op, rebuilt);
        }
        // Two bounds on one polynomial that make an equality (or, in a
        // disjunction, a disequality) are that: `(and (<= P c) (>= P c))` is
        // `(= P c)`, which meets veriT's `la_rw_eq` from the other side.
        if let Some(merged) = self.merge_bounds(pool, op, &kept) {
            return self.normalize_aci(pool, op, merged);
        }
        match kept.len() {
            0 => pool.add(Term::new_bool(identity)),
            1 => kept.pop().unwrap(),
            _ => pool.add(Term::Op(op, kept)),
        }
    }

    /// `args` with the bounds on each polynomial combined: under `and` only the
    /// tightest lower and upper bound stay, an empty interval is `false` and a
    /// point interval is the equality; under `or` only the weakest of each
    /// stay, two half-lines that cover everything are `true` and two that
    /// leave out one point are its disequality (the inverse of veriT's
    /// `la_rw_eq`).  `None` when nothing changes.  Bounds are in normal form,
    /// `(rel P c)` with `c` a constant; Int bounds are never strict.
    fn merge_bounds(
        &mut self,
        pool: &mut PrimitivePool,
        op: Operator,
        args: &[Rc<Term>],
    ) -> Option<Vec<Rc<Term>>> {
        use Operator::*;
        // (index, strict, value)
        type Bound = (usize, bool, Rational);
        struct Bounds {
            poly: Rc<Term>,
            lower: Vec<Bound>,
            upper: Vec<Bound>,
        }
        let mut by_poly: IndexMap<usize, Bounds> = IndexMap::new();
        for (index, arg) in args.iter().enumerate() {
            let Term::Op(rel @ (LessThan | LessEq | GreaterThan | GreaterEq), rel_args) =
                arg.as_ref()
            else {
                continue;
            };
            if rel_args.len() != 2 {
                continue;
            }
            let Some(value) = rel_args[1].as_signed_number() else { continue };
            let entry = by_poly
                .entry(Rc::as_ptr(&rel_args[0]) as *const () as usize)
                .or_insert_with(|| Bounds {
                    poly: rel_args[0].clone(),
                    lower: Vec::new(),
                    upper: Vec::new(),
                });
            let strict = matches!(rel, LessThan | GreaterThan);
            match rel {
                LessThan | LessEq => entry.upper.push((index, strict, value)),
                _ => entry.lower.push((index, strict, value)),
            }
        }
        let mut removed = vec![false; args.len()];
        let mut added: Vec<Rc<Term>> = Vec::new();
        let mut changed = false;
        for bounds in by_poly.into_values() {
            if bounds.lower.len() + bounds.upper.len() < 2 {
                continue;
            }
            let Some(sort) = self.arith_sort(pool, &bounds.poly) else { continue };
            let integer = sort == ArithSort::Int;
            // Under `and` the tightest bounds: the least upper (strict first at
            // a tie) and the greatest lower; under `or` the weakest: the
            // greatest upper (non-strict first) and the least lower.
            let tighter = |a: &Bound, b: &Bound, upper: bool| -> bool {
                let (av, bv) = (&a.2, &b.2);
                if av != bv {
                    (av < bv) == upper
                } else {
                    a.1 && !b.1
                }
            };
            let pick = |list: &[Bound], upper: bool| -> Option<Bound> {
                let mut best: Option<&Bound> = None;
                for bound in list {
                    let better = match best {
                        None => true,
                        Some(current) => {
                            let a_tighter = tighter(bound, current, upper);
                            if op == And { a_tighter } else { !a_tighter && (bound.2 != current.2 || bound.1 != current.1) }
                        }
                    };
                    if better {
                        best = Some(bound);
                    }
                }
                best.cloned()
            };
            let upper = pick(&bounds.upper, true);
            let lower = pick(&bounds.lower, false);
            let keep: Vec<usize> = upper.iter().chain(lower.iter()).map(|b| b.0).collect();
            for bound in bounds.upper.iter().chain(bounds.lower.iter()) {
                if !keep.contains(&bound.0) {
                    removed[bound.0] = true;
                    changed = true;
                }
            }
            let (Some(upper), Some(lower)) = (upper, lower) else { continue };
            let (up, low) = (&upper.2, &lower.2);
            let point = |this: &Self, pool: &mut PrimitivePool, c: &Rational| {
                let constant = this.constant_term(pool, c, sort);
                pool.add(Term::Op(Equals, vec![bounds.poly.clone(), constant]))
            };
            let replacement = if op == And {
                // `P <= up` and `P >= low`
                if low > up || (low == up && (upper.1 || lower.1)) {
                    Some(pool.add(Term::new_bool(false)))
                } else if low == up {
                    Some(point(self, pool, low))
                } else {
                    None
                }
            } else {
                // `P <= up` or `P >= low`: everything when the half-lines meet
                let covers = if integer {
                    *low <= up.clone() + Rational::from(1)
                } else {
                    low < up || (low == up && !(upper.1 && lower.1))
                };
                if covers {
                    Some(pool.add(Term::new_bool(true)))
                } else if integer && *low == up.clone() + Rational::from(2) {
                    let equality = point(self, pool, &(up.clone() + Rational::from(1)));
                    Some(pool.add(Term::Op(Not, vec![equality])))
                } else if !integer && low == up {
                    let equality = point(self, pool, low);
                    Some(pool.add(Term::Op(Not, vec![equality])))
                } else {
                    None
                }
            };
            if let Some(term) = replacement {
                removed[upper.0] = true;
                removed[lower.0] = true;
                added.push(term);
                changed = true;
            }
        }
        if !changed {
            return None;
        }
        let mut result: Vec<Rc<Term>> = args
            .iter()
            .enumerate()
            .filter(|(index, _)| !removed[*index])
            .map(|(_, arg)| arg.clone())
            .collect();
        result.extend(added);
        Some(result)
    }

    /// The sort a relation between `a` and `b` is normalized in: Real as soon as one side is
    /// Real, since under Int/Real subtyping an integer numeral may stand on either side.
    fn relation_sort(
        &self,
        pool: &mut PrimitivePool,
        a: &Rc<Term>,
        b: &Rc<Term>,
    ) -> Option<ArithSort> {
        match (self.arith_sort(pool, a)?, self.arith_sort(pool, b)?) {
            (ArithSort::Int, ArithSort::Int) => Some(ArithSort::Int),
            _ => Some(ArithSort::Real),
        }
    }

    fn arith_sort(&self, pool: &mut PrimitivePool, term: &Rc<Term>) -> Option<ArithSort> {
        match pool.sort(term).as_ref() {
            Sort::Int => Some(ArithSort::Int),
            Sort::Real => Some(ArithSort::Real),
            _ => None,
        }
    }

    /// The polynomial of an arithmetic term whose subterms are already in
    /// normal form.
    fn polynomial(&mut self, pool: &mut PrimitivePool, term: &Rc<Term>) -> Polynomial {
        if let Some(value) = term.as_signed_number() {
            return Polynomial::constant(value);
        }
        match term.as_ref() {
            Term::Op(Operator::Add, args) => {
                let mut sum = Polynomial::default();
                for arg in args {
                    sum.add(&self.polynomial(pool, arg));
                }
                sum
            }
            Term::Op(Operator::Sub, args) if args.len() == 1 => {
                let mut poly = self.polynomial(pool, &args[0]);
                poly.scale(&Rational::from(-1));
                poly
            }
            Term::Op(Operator::Sub, args) => {
                let mut result = self.polynomial(pool, &args[0]);
                for arg in &args[1..] {
                    let mut poly = self.polynomial(pool, arg);
                    poly.scale(&Rational::from(-1));
                    result.add(&poly);
                }
                result
            }
            Term::Op(Operator::Mult, args) => {
                let mut product = Polynomial::constant(Rational::from(1));
                for arg in args {
                    product = product.mul(&self.polynomial(pool, arg));
                }
                product
            }
            Term::Op(Operator::RealDiv, args) if args.len() == 2 => {
                match args[1].as_signed_number() {
                    Some(divisor) if divisor != 0 => {
                        let mut poly = self.polynomial(pool, &args[0]);
                        poly.scale(&(Rational::from(1) / divisor));
                        poly
                    }
                    _ => Polynomial::atom(term.clone()),
                }
            }
            Term::Op(Operator::ToReal, args) if args.len() == 1 => {
                // `to_real` distributes over the sum: constants convert,
                // atoms are wrapped.
                let inner = self.polynomial(pool, &args[0]);
                let mut result = Polynomial::default();
                for (monomial, coefficient) in &inner.0 {
                    let atoms: Vec<Rc<Term>> = monomial
                        .0
                        .iter()
                        .map(|atom| pool.add(Term::Op(Operator::ToReal, vec![atom.clone()])))
                        .collect();
                    let mut atoms = atoms;
                    atoms.sort_unstable_by_key(Rc::as_ptr);
                    result.add_monomial(Monomial(atoms), coefficient.clone());
                }
                result
            }
            _ => Polynomial::atom(term.clone()),
        }
    }

    fn constant_term(&self, pool: &mut PrimitivePool, value: &Rational, sort: ArithSort) -> Rc<Term> {
        match sort {
            ArithSort::Int if value.is_integer() => pool.add(Term::new_int(value.numer().clone())),
            _ => pool.add(Term::new_real(value.clone())),
        }
    }

    /// The canonical term of a polynomial: the monomials in order, each a
    /// constant, an atom or a product `(* c a1 ... an)`, summed.
    fn term_of_polynomial(&self, pool: &mut PrimitivePool, poly: &Polynomial, sort: ArithSort) -> Rc<Term> {
        let mut terms: Vec<Rc<Term>> = Vec::new();
        let mut constant: Option<Rational> = None;
        for (monomial, coefficient) in poly.sorted() {
            if monomial.0.is_empty() {
                constant = Some(coefficient.clone());
                continue;
            }
            let mut factors: Vec<Rc<Term>> = Vec::new();
            if *coefficient != 1 {
                factors.push(self.constant_term(pool, coefficient, sort));
            }
            factors.extend(monomial.0.iter().cloned());
            terms.push(if factors.len() == 1 {
                factors.pop().unwrap()
            } else {
                pool.add(Term::Op(Operator::Mult, factors))
            });
        }
        if let Some(constant) = constant {
            terms.push(self.constant_term(pool, &constant, sort));
        }
        match terms.len() {
            0 => self.constant_term(pool, &Rational::new(), sort),
            1 => terms.pop().unwrap(),
            _ => pool.add(Term::Op(Operator::Add, terms)),
        }
    }

    /// `(op lhs rhs)` over arithmetic terms as `(op' P c)`: the difference of
    /// the sides as a polynomial with integral coefficients of gcd 1 (Int) or
    /// a leading coefficient of 1 (Real), positive leading coefficient, the
    /// constant on the right, tightened to an integer for Int.
    fn normalize_relation(
        &mut self,
        pool: &mut PrimitivePool,
        op: Operator,
        lhs: &Rc<Term>,
        rhs: &Rc<Term>,
        sort: ArithSort,
    ) -> Rc<Term> {
        use Operator::*;
        let mut difference = self.polynomial(pool, lhs);
        let mut right = self.polynomial(pool, rhs);
        right.scale(&Rational::from(-1));
        difference.add(&right);
        if difference.is_constant() {
            let value = difference.constant_part();
            let holds = match op {
                LessThan => value < 0,
                LessEq => value <= 0,
                GreaterThan => value > 0,
                GreaterEq => value >= 0,
                _ => value == 0,
            };
            return pool.add(Term::new_bool(holds));
        }
        let mut op = op;
        let constant = difference.constant_part();
        difference.add_monomial(Monomial::one(), -constant.clone());
        let sorted = difference.sorted();
        let leading = sorted[0].1.clone();
        let scale = match sort {
            ArithSort::Int => {
                let mut lcm = Integer::from(1);
                for (_, c) in &sorted {
                    lcm.lcm_mut(c.denom());
                }
                let mut gcd = Integer::from(0);
                for (_, c) in &sorted {
                    let scaled = Rational::from(c.clone() * Rational::from(&lcm));
                    gcd.gcd_mut(scaled.numer());
                }
                Rational::from((lcm, gcd))
            }
            ArithSort::Real => Rational::from(1) / leading.clone().abs(),
        };
        let scale = if leading < 0 { -scale } else { scale };
        if leading < 0 {
            op = match op {
                LessThan => GreaterThan,
                LessEq => GreaterEq,
                GreaterThan => LessThan,
                GreaterEq => LessEq,
                other => other,
            };
        }
        difference.scale(&scale);
        // `P + k op 0` is `P op -k`.
        let mut bound = Rational::from(-constant * &scale);
        if sort == ArithSort::Int && !bound.is_integer() {
            match op {
                GreaterEq => bound = bound.ceil(),
                LessEq => bound = bound.floor(),
                GreaterThan => {
                    op = GreaterEq;
                    bound = bound.floor() + 1;
                }
                LessThan => {
                    op = LessEq;
                    bound = bound.ceil() - 1;
                }
                _ => return pool.add(Term::new_bool(false)),
            }
        } else if sort == ArithSort::Int {
            match op {
                GreaterThan => {
                    op = GreaterEq;
                    bound += 1;
                }
                LessThan => {
                    op = LessEq;
                    bound -= 1;
                }
                _ => {}
            }
        }
        let left = self.term_of_polynomial(pool, &difference, sort);
        let right = self.constant_term(pool, &bound, sort);
        pool.add(Term::Op(op, vec![left, right]))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser;

    /// Normalizes `lhs` and `rhs` parsed against `problem`, returning
    /// whether they coincide and their printed normal forms.
    fn same(problem: &str, lhs: &str, rhs: &str) -> (bool, String, String) {
        let problem_text = format!("{problem}\n(assert (= {lhs} {rhs}))\n");
        let proof = format!("(assume h0 (= {lhs} {rhs}))\n");
        let (_, proof, _, mut pool) = parser::parse_instance(
            parser::Source::new(std::path::Path::new("<p>"), &problem_text),
            parser::Source::new(std::path::Path::new("<a>"), &proof),
            None,
            parser::Config::new().allow_int_real_subtyping(true),
        )
        .expect("parses");
        let crate::ast::ProofCommand::Assume { term, .. } = &proof.commands[0] else {
            panic!("expected an assume");
        };
        let (_, l, r) = crate::rare::util::get_equational_terms(term).expect("equality");
        let (l, r) = (l.clone(), r.clone());
        let mut normalizer = Normalizer::new();
        let nl = normalizer.normalize(&mut pool, &l);
        let nr = normalizer.normalize(&mut pool, &r);
        (nl == nr, format!("{nl:#}"), format!("{nr:#}"))
    }

    const INTS: &str = "(declare-const x Int) (declare-const y Int) (declare-const z Int) (declare-const p Bool) (declare-const q Bool) (declare-const z_bool Bool)";
    const REALS: &str = "(declare-const a Real) (declare-const b Real) (declare-const x Int)";

    #[test]
    fn equivalent_sides_coincide() {
        for (problem, lhs, rhs) in [
            (INTS, "(not (not (>= (+ x (* -1 y)) 1)))", "(>= (+ x (* -1 y)) 1)"),
            (INTS, "(* 4 256)", "1024"),
            (INTS, "(+ 0 1536 -1024 -1024 -512 -512 512 512 512)", "0"),
            (INTS, "(+ x y x)", "(+ (* 2 x) y)"),
            (INTS, "(- x y)", "(+ x (* (- 1) y))"),
            (INTS, "(* (+ x 1) (+ x 1))", "(+ (* x x) (* 2 x) 1)"),
            (INTS, "(< x y)", "(>= (+ y (* -1 x)) 1)"),
            (INTS, "(> (* 2 x) 3)", "(>= x 2)"),
            (INTS, "(<= (* 2 x) 3)", "(<= x 1)"),
            (INTS, "(= (* 2 x) 3)", "false"),
            (INTS, "(>= (* -2 x) (* -4 y))", "(<= (+ x (* -2 y)) 0)"),
            (INTS, "(and p true q p)", "(and q p)"),
            (INTS, "(or p (not p))", "true"),
            (INTS, "(and p (not p))", "false"),
            (INTS, "(=> p q)", "(or (not p) q)"),
            (INTS, "(ite true x y)", "x"),
            (INTS, "(= x x)", "true"),
            (INTS, "(distinct x y)", "(not (= x y))"),
            (INTS, "(distinct x y z)", "(and (not (= y x)) (not (= z x)) (not (= z y)))"),
            (INTS, "(distinct x y x)", "false"),
            (INTS, "(= p true)", "p"),
            (INTS, "(= false p)", "(not p)"),
            (INTS, "(not (=> p q))", "(and p (not q))"),
            (INTS, "(not (and p (not q)))", "(or (not p) q)"),
            (INTS, "(not (=> (and p q) (=> (or p q) (or p q))))", "false"),
            (INTS, "(and (or p q) (not p) (not q))", "false"),
            (INTS, "(or (and p q) (not p) (not q))", "true"),
            (INTS, "(not (<= x 3))", "(>= x 4)"),
            (INTS, "(not (< x y))", "(>= x y)"),
            (REALS, "(not (<= a 3.0))", "(> a 3.0)"),
            (INTS, "(and (<= x y) (<= y x))", "(= x y)"),
            (INTS, "(and p (<= (+ x 1) y) (<= y (+ x 1)) q)", "(and p q (= y (+ x 1)))"),
            (INTS, "(or (< x y) (< y x))", "(not (= x y))"),
            (INTS, "(not (and (<= x y) (<= y x)))", "(distinct x y)"),
            (REALS, "(and (<= a (* 2.0 b)) (<= (* 2.0 b) a))", "(= a (* 2.0 b))"),
            (REALS, "(or (not (<= a b)) (not (<= b a)))", "(not (= a b))"),
            (INTS, "(or (<= x 0) (>= x 1))", "true"),
            (INTS, "(or (not (>= x 1)) (>= x 1) p)", "true"),
            (INTS, "(and (<= x 0) (>= x 1))", "false"),
            (INTS, "(and (<= x 3) (<= x 5) (>= x 1))", "(and (<= x 3) (>= x 1))"),
            (INTS, "(not (or (not (and (>= x 1) (>= y 1))) (and (>= x 1) (>= y 1)) (not (>= z 1))))", "false"),
            (REALS, "(or (< a 1.0) (>= a 1.0))", "true"),
            (INTS, "(and (>= x 1) (or (<= x 0) p) (not p))", "false"),
            (INTS, "(and (= x 2) (or (<= x 1) (>= x 3)))", "false"),
            (INTS, "(or (not (= x 2)) (and (<= x 2) (>= x 2)))", "true"),
            (INTS, "(or p (and (not p) q))", "(or p q)"),
            (INTS, "(and p (or (not p) q) (or (not q) (not p) z_bool))", "(and p q z_bool)"),
            (INTS, "(or (<= x 1) (and (>= x 5) (>= x 7)))", "(or (<= x 1) (>= x 7))"),
            (REALS, "(or (< a 1.0) (and (>= a 1.0) (>= b 1.0)))", "(or (< a 1.0) (>= b 1.0))"),
            (REALS, "(and (< a 1.0) (>= a 1.0))", "false"),
            (REALS, "(and (<= a 1.0) (< a 2.0))", "(<= a 1.0)"),
            (REALS, "(or (<= a 1.0) (< a 2.0))", "(< a 2.0)"),
            (REALS, "(>= 0.0 (/ (- 1) 1024))", "true"),
            (REALS, "(* (/ 1 2) (to_real (+ x (* 2 x))))", "(* (/ 3 2) (to_real x))"),
            (REALS, "(< (* 2.0 a) b)", "(> (+ b (* (- 2.0) a)) 0.0)"),
            (REALS, "(= a b)", "(= (+ a (* (- 1.0) b)) 0.0)"),
            (REALS, "(= (- 1.0) (- 1))", "true"),
            (REALS, "(= (+ (* 500.0 a) (* (- 1) b)) (- 300))", "(and (<= (+ (* 500.0 a) (* (- 1) b)) (- 300)) (<= (- 300) (+ (* 500.0 a) (* (- 1) b))))"),
            (REALS, "(<= 1 a)", "(>= a 1.0)"),
        ] {
            let (equal, nl, nr) = same(problem, lhs, rhs);
            assert!(equal, "{lhs} and {rhs} normalize to {nl} and {nr}");
        }
    }

    #[test]
    fn different_sides_stay_apart() {
        for (problem, lhs, rhs) in [
            (INTS, "(>= x 1)", "(>= x 2)"),
            (INTS, "(+ x y)", "(+ x z)"),
            (INTS, "(and p q)", "(or p q)"),
            (INTS, "(* x y)", "(* x x)"),
            (REALS, "(>= a 1.0)", "(> a 1.0)"),
            (INTS, "(and (or p q) (not p))", "false"),
            (INTS, "(not (and p q))", "(and (not p) (not q))"),
            (INTS, "(and (<= x y) (<= y (+ x 1)))", "(= x y)"),
            (INTS, "(or (<= x 2) (>= x 3))", "(not (= x 3))"),
            (INTS, "(or (<= x 0) (>= x 2))", "true"),
            (REALS, "(and (<= a 1.0) (< a 2.0))", "(< a 2.0)"),
            (REALS, "(or (< a 1.0) (> a 1.0))", "true"),
            (INTS, "(and (>= x 1) (or (<= x 1) p) (not p))", "false"),
            (REALS, "(or (< a 1.0) (and (> a 1.0) (>= b 1.0)))", "(or (< a 1.0) (>= b 1.0))"),
        ] {
            let (equal, nl, nr) = same(problem, lhs, rhs);
            assert!(!equal, "{lhs} and {rhs} both normalize to {nl}, {nr}");
        }
    }
}
