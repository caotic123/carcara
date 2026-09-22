//! Normalizing a hole's goal with the procedures behind four of Carcara's
//! own rules, before the egglog engine sees it.
//!
//! The normalizer is the bottom-up composition of exactly the procedures
//! that check `evaluate`, `poly_simp` (with `poly_simp_rel` for relations),
//! `aci_simp`, `distinct_elim` and `la_rw_eq`: a ground term is evaluated, an arithmetic
//! term is printed as its canonical polynomial, a relation is put in the
//! form `(op P c)` with `P` the scaled difference of its sides, an `and`/`or`
//! (and the associative bit-vector operators) is flattened, freed of its
//! identity element, deduplicated when idempotent and sorted, a
//! `distinct` is expanded to its pairwise disequalities, and a pair of
//! opposite bounds between the same two terms, `(and (<= t u) (<= u t))`
//! or with either bound written as a `>=`, is the equality `(= t u)`
//! (`la_rw_eq`, read on the term as written, before its bounds are
//! normalized apart; a `>=` bound is first turned round by `la_generic`,
//! `equiv_neg1`, `equiv_neg2` and `resolution`, so the certificate stays
//! within Alethe without a `*_simplify` rule).  Nothing else: what these
//! five do not reach is left to the RARE rules in egglog.
//!
//! Because each step is one of those rules applied to one subterm, the
//! derivation of a normal form is a certificate of `cong`, `trans` and rule
//! steps that the checker verifies, so the same normalization serves the
//! checking pass (a hole whose sides have the same normal form is closed)
//! and the elaboration pass (the certificate replaces the hole, or bridges
//! the hole's sides to the normal forms egglog proves equal).
//!
//! The polynomial is the checker's own (`checker::rules::polynomial`), so a
//! `poly_simp` step the normalizer emits is one the checker accepts by
//! construction.
use crate::ast::{Operator, Rc, Sort, Term, Value, pool::TermPool};
use crate::checker::rules::polynomial::{Monomial, Polynomial};
use indexmap::IndexSet;
use rug::{Integer, Rational};
use std::collections::HashMap;

/// A premise a top step's certificate needs: the `poly_simp` equality a
/// `poly_simp_rel` step is stated on, or the equality of a `>=` bound with
/// its `<=` mirror image, `(= (>= x y) (<= y x))`, proved from `la_generic`
/// and the `equiv_neg` tautologies by resolution.
#[derive(Clone)]
enum Premise {
    PolySimp(Rc<Term>, Rc<Term>),
    BoundFlip(Rc<Term>, Rc<Term>),
}

/// One rule application at the top of a term: `(= from to)` by `rule`, with
/// the premises its certificate needs.  A `flipped` step is one whose rule
/// concludes `(= to from)` (`la_rw_eq` states the equality as the pair of
/// bounds); its certificate adds a `symm`.
#[derive(Clone)]
struct TopStep {
    rule: &'static str,
    from: Rc<Term>,
    to: Rc<Term>,
    premises: Vec<Premise>,
    flipped: bool,
}

/// How a term's normal form is derived: the arguments' normal forms under
/// `cong`, then rule applications at the top, then the derivation of the
/// last top step's result (whose own arguments may need normalizing again).
#[derive(Clone)]
struct Derivation {
    /// The term with its arguments replaced by their normal forms, when any
    /// changed.
    cong: Option<Rc<Term>>,
    tops: Vec<TopStep>,
    /// The term the top steps end at, when it is not yet normal.
    tail: Option<Rc<Term>>,
    result: Rc<Term>,
}

pub struct Normalizer {
    derivations: HashMap<Rc<Term>, Derivation>,
    /// How many subterms changed under normalization.
    pub rewritten: usize,
}

impl Default for Normalizer {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ArithSort {
    Int,
    Real,
}

fn arith_sort(pool: &mut dyn TermPool, term: &Rc<Term>) -> Option<ArithSort> {
    match pool.sort(term).as_ref() {
        Sort::Int => Some(ArithSort::Int),
        Sort::Real => Some(ArithSort::Real),
        _ => None,
    }
}

/// Whether every argument of `op` may be dropped when repeated.
fn is_idempotent(op: Operator) -> bool {
    matches!(
        op,
        Operator::And | Operator::Or | Operator::BvAnd | Operator::BvOr
    )
}

/// The operators the `aci_simp` component handles: associative and
/// commutative, with an identity element.  `+` and `*` go through
/// `poly_simp` instead.
fn is_aci(op: Operator) -> bool {
    matches!(
        op,
        Operator::And
            | Operator::Or
            | Operator::BvAnd
            | Operator::BvOr
            | Operator::BvXor
            | Operator::BvAdd
            | Operator::BvMul
    )
}

fn identity_of(pool: &mut dyn TermPool, op: Operator, sample: &Rc<Term>) -> Option<Rc<Term>> {
    let term = match op {
        Operator::And => Term::new_bool(true),
        Operator::Or => Term::new_bool(false),
        Operator::BvAdd | Operator::BvOr | Operator::BvXor | Operator::BvMul | Operator::BvAnd => {
            let &Sort::BitVec(width) = pool.sort(sample).as_ref() else {
                return None;
            };
            match op {
                Operator::BvMul => Term::new_bv(Integer::from(1), width),
                Operator::BvAnd => Term::new_bv((Integer::from(1) << width) - 1, width),
                _ => Term::new_bv(Integer::from(0), width),
            }
        }
        _ => return None,
    };
    Some(pool.add(term))
}

impl Normalizer {
    pub fn new() -> Self {
        Self {
            derivations: HashMap::new(),
            rewritten: 0,
        }
    }

    /// `term` in normal form.
    pub fn normalize(&mut self, pool: &mut dyn TermPool, term: &Rc<Term>) -> Rc<Term> {
        if let Some(known) = self.derivations.get(term) {
            return known.result.clone();
        }
        let derivation = self.derive(pool, term);
        if derivation.result != *term {
            self.rewritten += 1;
        }
        let result = derivation.result.clone();
        self.derivations.insert(term.clone(), derivation);
        result
    }

    fn derive(&mut self, pool: &mut dyn TermPool, term: &Rc<Term>) -> Derivation {
        let same = |t: &Rc<Term>| Derivation {
            cong: None,
            tops: Vec::new(),
            tail: None,
            result: t.clone(),
        };
        // 0. `la_rw_eq`, on the term as written: `(and (<= t u) (<= u t))`,
        //    either bound possibly a `>=`, is `(= t u)`.  This comes before
        //    the arguments are normalized because afterwards the two bounds
        //    are `(<= P c)` and `(<= -P -c)` and no longer mirror each
        //    other.  The equality is then normalized like any other.
        if let Some(tops) = self.la_rw_eq_steps(pool, term) {
            let equality = tops.last().expect("at least the la_rw_eq step").to.clone();
            let result = self.normalize(pool, &equality);
            let tail = (result != equality).then(|| equality.clone());
            return Derivation { cong: None, tops, tail, result };
        }
        // 1. The arguments, under `cong`.
        let current = match term.as_ref() {
            Term::Op(op, args) => {
                let normal: Vec<Rc<Term>> = args.iter().map(|a| self.normalize(pool, a)).collect();
                if normal == *args {
                    term.clone()
                } else {
                    pool.add(Term::Op(*op, normal))
                }
            }
            Term::App(function, args) => {
                let normal: Vec<Rc<Term>> = args.iter().map(|a| self.normalize(pool, a)).collect();
                if normal == *args {
                    term.clone()
                } else {
                    pool.add(Term::App(function.clone(), normal))
                }
            }
            _ => return same(term),
        };
        let cong = (current != *term).then(|| current.clone());
        // 2. Rule applications at the top, each on the previous one's result.
        let mut tops = Vec::new();
        let mut at = current;
        while let Some(step) = self.top_step(pool, &at) {
            at = step.to.clone();
            tops.push(step);
            if tops.len() > 16 {
                break;
            }
        }
        // 3. The result of a top step may have arguments that are not normal
        //    (a `distinct` expands to equalities), so it is normalized again.
        let (tail, result) = if tops.is_empty() {
            (None, at)
        } else {
            let normal = self.normalize(pool, &at);
            if normal == at {
                (None, at)
            } else {
                (Some(at), normal)
            }
        };
        Derivation { cong, tops, tail, result }
    }

    /// `la_rw_eq` read backwards: `(and (<= t u) (<= u t))`, with `t` and
    /// `u` the same terms in both bounds, to `(= t u)`.  A bound written as
    /// `(>= u t)` or `(>= t u)` is accepted too; the certificate then first
    /// turns it round under `cong`, so the pair matches the rule as stated.
    fn la_rw_eq_steps(&mut self, pool: &mut dyn TermPool, term: &Rc<Term>) -> Option<Vec<TopStep>> {
        // A bound as "x is at most y", and whether it is written as a `>=`.
        fn at_most(bound: &Rc<Term>) -> Option<(&Rc<Term>, &Rc<Term>, bool)> {
            match bound.as_ref() {
                Term::Op(Operator::LessEq, args) if args.len() == 2 => {
                    Some((&args[0], &args[1], false))
                }
                Term::Op(Operator::GreaterEq, args) if args.len() == 2 => {
                    Some((&args[1], &args[0], true))
                }
                _ => None,
            }
        }
        let Term::Op(Operator::And, args) = term.as_ref() else {
            return None;
        };
        let [first, second] = args.as_slice() else {
            return None;
        };
        let (t, u, first_flipped) = at_most(first)?;
        let (u2, t2, second_flipped) = at_most(second)?;
        if t != t2 || u != u2 || arith_sort(pool, t).is_none() {
            return None;
        }
        let (t, u) = (t.clone(), u.clone());
        let lower = pool.add(Term::Op(Operator::LessEq, vec![t.clone(), u.clone()]));
        let upper = pool.add(Term::Op(Operator::LessEq, vec![u.clone(), t.clone()]));
        let stated = pool.add(Term::Op(Operator::And, vec![lower.clone(), upper.clone()]));
        let mut tops = Vec::new();
        if stated != *term {
            let mut premises = Vec::new();
            if first_flipped {
                premises.push(Premise::BoundFlip(first.clone(), lower));
            }
            if second_flipped {
                premises.push(Premise::BoundFlip(second.clone(), upper));
            }
            tops.push(TopStep {
                rule: "cong",
                from: term.clone(),
                to: stated.clone(),
                premises,
                flipped: false,
            });
        }
        let to = pool.add(Term::Op(Operator::Equals, vec![t, u]));
        tops.push(TopStep {
            rule: "la_rw_eq",
            from: stated,
            to,
            premises: Vec::new(),
            flipped: true,
        });
        Some(tops)
    }

    /// One rule applied at the top of `term`, whose arguments are normal.
    fn top_step(&mut self, pool: &mut dyn TermPool, term: &Rc<Term>) -> Option<TopStep> {
        use Operator::*;
        let Term::Op(op, args) = term.as_ref() else {
            return None;
        };
        let step = |rule, to: Rc<Term>| {
            (to != *term).then(|| TopStep {
                rule,
                from: term.clone(),
                to,
                premises: Vec::new(),
                flipped: false,
            })
        };
        // `evaluate`: a ground term is its value.
        if args.iter().all(|a| Value::from_term(a).is_some()) {
            let value = term.evaluate(pool);
            if value != *term {
                return step("evaluate", value);
            }
        }
        match op {
            Add | Sub | Mult | RealDiv | ToReal => {
                let sort = arith_sort(pool, term)?;
                let poly = Polynomial::from_term(term);
                let canonical = self.term_of_polynomial(pool, &poly, sort);
                step("poly_simp", canonical)
            }
            LessThan | LessEq | GreaterThan | GreaterEq | Equals if args.len() == 2 => {
                let sort = match (arith_sort(pool, &args[0])?, arith_sort(pool, &args[1])?) {
                    (ArithSort::Int, ArithSort::Int) => ArithSort::Int,
                    _ => ArithSort::Real,
                };
                self.relation_step(pool, term, *op, &args[0], &args[1], sort)
            }
            Distinct => step("distinct_elim", self.distinct_expansion(pool, args)),
            _ if is_aci(*op) => step("aci_simp", self.aci_canonical(pool, *op, args)),
            _ => None,
        }
    }

    /// `(op x1 x2)` as `(op P c)`: the difference of the sides scaled by a
    /// positive factor (integral coefficients of gcd 1 for Int, leading
    /// coefficient of absolute value 1 for Real), its constant moved to the
    /// right.  The `poly_simp` premise `(= (* s (- x1 x2)) (* 1 (- P c)))`
    /// is what `poly_simp_rel` needs.
    fn relation_step(
        &mut self,
        pool: &mut dyn TermPool,
        term: &Rc<Term>,
        op: Operator,
        x1: &Rc<Term>,
        x2: &Rc<Term>,
        sort: ArithSort,
    ) -> Option<TopStep> {
        let difference = Polynomial::from_term(x1).sub(Polynomial::from_term(x2));
        let constant = difference.1.clone();
        let mut poly = difference;
        poly.1 = Rational::new();
        let scale = if poly.0.is_empty() {
            Rational::from(1)
        } else {
            match sort {
                ArithSort::Int => {
                    let mut lcm = Integer::from(1);
                    for c in poly.0.values() {
                        lcm.lcm_mut(c.denom());
                    }
                    let mut gcd = Integer::from(0);
                    for c in poly.0.values() {
                        let scaled = Rational::from(c.clone() * Rational::from(&lcm));
                        gcd.gcd_mut(scaled.numer());
                    }
                    Rational::from((lcm, gcd))
                }
                ArithSort::Real => {
                    let (_, leading) = Self::sorted_monomials(&poly)[0];
                    Rational::from(1) / leading.clone().abs()
                }
            }
        };
        // An equality may be scaled by a negative factor (`poly_simp_rel`
        // allows it for `=` only), which fixes its orientation: a positive
        // leading coefficient.
        let scale = if op == Operator::Equals
            && !poly.0.is_empty()
            && *Self::sorted_monomials(&poly)[0].1 < 0
        {
            -scale
        } else {
            scale
        };
        for c in poly.0.values_mut() {
            *c *= &scale;
        }
        let y1 = self.term_of_polynomial(pool, &poly, sort);
        let y2 = self.constant_term(pool, &Rational::from(-constant * &scale), sort);
        if y1 == *x1 && y2 == *x2 {
            return None;
        }
        let to = pool.add(Term::Op(op, vec![y1.clone(), y2.clone()]));
        // the premise's sides, `(* s (- x1 x2))` and `(* 1 (- y1 y2))`
        let s = self.constant_term(pool, &scale, sort);
        let one = self.constant_term(pool, &Rational::from(1), sort);
        let left = pool.add(Term::Op(Operator::Sub, vec![x1.clone(), x2.clone()]));
        let left = pool.add(Term::Op(Operator::Mult, vec![s, left]));
        let right = pool.add(Term::Op(Operator::Sub, vec![y1, y2]));
        let right = pool.add(Term::Op(Operator::Mult, vec![one, right]));
        Some(TopStep {
            rule: "poly_simp_rel",
            from: term.clone(),
            to,
            premises: vec![Premise::PolySimp(left, right)],
            flipped: false,
        })
    }

    /// `distinct_elim`'s expansion: the disequality of two arguments, the
    /// conjunction of the pairwise disequalities of more (`false` for more
    /// than two Booleans).
    fn distinct_expansion(&mut self, pool: &mut dyn TermPool, args: &[Rc<Term>]) -> Rc<Term> {
        let disequality = |pool: &mut dyn TermPool, a: &Rc<Term>, b: &Rc<Term>| {
            let equality = pool.add(Term::Op(Operator::Equals, vec![a.clone(), b.clone()]));
            pool.add(Term::Op(Operator::Not, vec![equality]))
        };
        match args {
            [a, b] => disequality(pool, a, b),
            _ if pool.sort(&args[0]).as_ref() == &Sort::Bool => pool.add(Term::new_bool(false)),
            _ => {
                let mut conjuncts = Vec::with_capacity(args.len() * (args.len() - 1) / 2);
                for i in 0..args.len() {
                    for j in i + 1..args.len() {
                        conjuncts.push(disequality(pool, &args[i], &args[j]));
                    }
                }
                pool.add(Term::Op(Operator::And, conjuncts))
            }
        }
    }

    /// `aci_simp`'s canonical form: flattened, without the identity element,
    /// deduplicated when the operator is idempotent, in pointer order.
    fn aci_canonical(
        &mut self,
        pool: &mut dyn TermPool,
        op: Operator,
        args: &[Rc<Term>],
    ) -> Rc<Term> {
        let identity = identity_of(pool, op, &args[0]);
        let mut flat: Vec<Rc<Term>> = Vec::new();
        for arg in args {
            match arg.as_ref() {
                Term::Op(inner, inner_args) if *inner == op => {
                    flat.extend(inner_args.iter().cloned())
                }
                _ => flat.push(arg.clone()),
            }
        }
        if let Some(identity) = &identity {
            flat.retain(|a| a != identity);
        }
        if is_idempotent(op) {
            let set: IndexSet<Rc<Term>> = flat.into_iter().collect();
            flat = set.into_iter().collect();
        }
        flat.sort_by_key(Rc::as_ptr);
        match flat.len() {
            0 => identity.unwrap_or_else(|| pool.add(Term::Op(op, Vec::new()))),
            1 => flat.pop().unwrap(),
            _ => pool.add(Term::Op(op, flat)),
        }
    }

    /// The monomials in canonical order: fewer atoms first, then by the
    /// atoms' pointers.
    fn sorted_monomials(poly: &Polynomial) -> Vec<(&Monomial, &Rational)> {
        let mut entries: Vec<_> = poly.0.iter().collect();
        entries.sort_by(|(a, _), (b, _)| {
            a.0.len()
                .cmp(&b.0.len())
                .then_with(|| a.0.iter().map(Rc::as_ptr).cmp(b.0.iter().map(Rc::as_ptr)))
        });
        entries
    }

    fn constant_term(
        &self,
        pool: &mut dyn TermPool,
        value: &Rational,
        sort: ArithSort,
    ) -> Rc<Term> {
        match sort {
            ArithSort::Int if value.is_integer() => pool.add(Term::new_int(value.numer().clone())),
            _ => pool.add(Term::new_real(value.clone())),
        }
    }

    /// The canonical term of a polynomial: the monomials in order, each an
    /// atom or a product `(* c a1 ... an)`, summed, the constant last.  In a
    /// Real polynomial an Int atom is wrapped in `to_real`, which the
    /// checker's polynomial sees through.
    fn term_of_polynomial(
        &self,
        pool: &mut dyn TermPool,
        poly: &Polynomial,
        sort: ArithSort,
    ) -> Rc<Term> {
        let mut terms: Vec<Rc<Term>> = Vec::new();
        for (monomial, coefficient) in Self::sorted_monomials(poly) {
            let mut factors: Vec<Rc<Term>> = Vec::new();
            if *coefficient != 1 {
                factors.push(self.constant_term(pool, coefficient, sort));
            }
            for atom in &monomial.0 {
                let atom =
                    if sort == ArithSort::Real && arith_sort(pool, atom) == Some(ArithSort::Int) {
                        pool.add(Term::Op(Operator::ToReal, vec![atom.clone()]))
                    } else {
                        atom.clone()
                    };
                factors.push(atom);
            }
            terms.push(if factors.len() == 1 {
                factors.pop().unwrap()
            } else {
                pool.add(Term::Op(Operator::Mult, factors))
            });
        }
        if poly.1 != 0 || terms.is_empty() {
            terms.push(self.constant_term(pool, &poly.1, sort));
        }
        match terms.len() {
            1 => terms.pop().unwrap(),
            _ => pool.add(Term::Op(Operator::Add, terms)),
        }
    }

    /// The certificate of `(= lhs rhs)` for a hole whose sides have the same
    /// normal form: Alethe steps numbered `{id}.1`, `{id}.2`, ... whose last
    /// step concludes the equality.  `None` when the sides differ.
    pub fn certificate(
        &mut self,
        pool: &mut dyn TermPool,
        id: &str,
        lhs: &Rc<Term>,
        rhs: &Rc<Term>,
    ) -> Option<Vec<String>> {
        let left = self.normalize(pool, lhs);
        let right = self.normalize(pool, rhs);
        if left != right {
            return None;
        }
        let mut emitter = Emitter {
            prefix: id.to_owned(),
            steps: Vec::new(),
            memo: HashMap::new(),
        };
        let left_step = self.emit(pool, &mut emitter, lhs);
        let right_step = self.emit(pool, &mut emitter, rhs);
        match (left_step, right_step) {
            (None, None) => {
                emitter.emit(pool, lhs, rhs, "refl", &[]);
            }
            (Some(_), None) => {}
            (None, Some(r)) => {
                emitter.emit(pool, lhs, rhs, "symm", &[r]);
            }
            (Some(l), Some(r)) => {
                let flipped = emitter.emit(pool, &left, rhs, "symm", &[r]);
                emitter.emit(pool, lhs, rhs, "trans", &[l, flipped]);
            }
        }
        Some(emitter.steps)
    }

    /// The steps bridging `lhs` and `rhs` to their normal forms and egglog's
    /// proof of the normal forms' equality (`inner`, steps concluding
    /// `(= left right)` numbered from `{id}.1`): the combined certificate,
    /// concluding `(= lhs rhs)`.
    pub fn bridge(
        &mut self,
        pool: &mut dyn TermPool,
        id: &str,
        lhs: &Rc<Term>,
        rhs: &Rc<Term>,
        inner: Vec<String>,
    ) -> Vec<String> {
        let left = self.normalize(pool, lhs);
        let right = self.normalize(pool, rhs);
        let inner_last = format!("{id}.{}", inner.len());
        let mut emitter = Emitter {
            prefix: id.to_owned(),
            steps: inner,
            memo: HashMap::new(),
        };
        let mut chain: Vec<String> = Vec::new();
        if let Some(l) = self.emit(pool, &mut emitter, lhs) {
            chain.push(l);
        }
        chain.push(inner_last);
        if let Some(r) = self.emit(pool, &mut emitter, rhs) {
            chain.push(emitter.emit(pool, &right, rhs, "symm", &[r]));
        }
        if chain.len() > 1 {
            emitter.emit(pool, lhs, rhs, "trans", &chain);
        }
        let _ = left;
        emitter.steps
    }

    /// Emits the derivation of `term`'s normal form and returns the id of
    /// the step concluding `(= term normal)`, or `None` when it is normal.
    fn emit(
        &mut self,
        pool: &mut dyn TermPool,
        emitter: &mut Emitter,
        term: &Rc<Term>,
    ) -> Option<String> {
        if let Some(known) = emitter.memo.get(term) {
            return known.clone();
        }
        let derivation = match self.derivations.get(term) {
            Some(d) => d.clone(),
            None => {
                self.normalize(pool, term);
                self.derivations[term].clone()
            }
        };
        let result = derivation.result.clone();
        let step = if result == *term {
            None
        } else {
            let mut chain: Vec<String> = Vec::new();
            let mut at = term.clone();
            if let Some(congruent) = &derivation.cong {
                let (Term::Op(_, args) | Term::App(_, args)) = term.as_ref() else {
                    unreachable!("a cong derivation is over an application")
                };
                let (Term::Op(_, normal) | Term::App(_, normal)) = congruent.as_ref() else {
                    unreachable!()
                };
                let mut premises = Vec::new();
                for (arg, its_normal) in args.iter().zip(normal.iter()) {
                    if arg != its_normal {
                        premises.push(
                            self.emit(pool, emitter, arg)
                                .expect("a changed argument has a derivation"),
                        );
                    }
                }
                chain.push(emitter.emit(pool, term, congruent, "cong", &premises));
                at = congruent.clone();
            }
            for top in &derivation.tops {
                let premises: Vec<String> = top
                    .premises
                    .iter()
                    .map(|premise| match premise {
                        Premise::PolySimp(left, right) => {
                            emitter.emit(pool, left, right, "poly_simp", &[])
                        }
                        Premise::BoundFlip(from, to) => emitter.emit_bound_flip(pool, from, to),
                    })
                    .collect();
                let id = if top.flipped {
                    let stated = emitter.emit(pool, &top.to, &top.from, top.rule, &premises);
                    emitter.emit(pool, &top.from, &top.to, "symm", &[stated])
                } else {
                    emitter.emit(pool, &top.from, &top.to, top.rule, &premises)
                };
                chain.push(id);
                at = top.to.clone();
            }
            if let Some(tail) = &derivation.tail {
                if let Some(id) = self.emit(pool, emitter, tail) {
                    chain.push(id);
                }
            }
            let _ = at;
            Some(if chain.len() == 1 {
                chain.pop().unwrap()
            } else {
                emitter.emit(pool, term, &result, "trans", &chain)
            })
        };
        emitter.memo.insert(term.clone(), step.clone());
        step
    }
}

/// Numbered Alethe steps under a hole's id.
struct Emitter {
    prefix: String,
    steps: Vec<String>,
    memo: HashMap<Rc<Term>, Option<String>>,
}

impl Emitter {
    fn emit(
        &mut self,
        _pool: &mut dyn TermPool,
        lhs: &Rc<Term>,
        rhs: &Rc<Term>,
        rule: &str,
        premises: &[String],
    ) -> String {
        let id = format!("{}.{}", self.prefix, self.steps.len() + 1);
        let premises = if premises.is_empty() {
            String::new()
        } else {
            format!(" :premises ({})", premises.join(" "))
        };
        self.steps.push(format!(
            "(step {id} (cl (= {lhs:#} {rhs:#})) :rule {rule}{premises})"
        ));
        id
    }

    fn emit_clause(
        &mut self,
        literals: &str,
        rule: &str,
        premises: &[String],
        args: &str,
    ) -> String {
        let id = format!("{}.{}", self.prefix, self.steps.len() + 1);
        let premises = if premises.is_empty() {
            String::new()
        } else {
            format!(" :premises ({})", premises.join(" "))
        };
        let args = if args.is_empty() {
            String::new()
        } else {
            format!(" :args ({args})")
        };
        self.steps.push(format!(
            "(step {id} (cl {literals}) :rule {rule}{premises}{args})"
        ));
        id
    }

    /// `(= a b)` for a bound `a` and its mirror image `b` (`(>= x y)` and
    /// `(<= y x)`, or the reverse): each implies the other by `la_generic`,
    /// and the two implications make the equivalence through the
    /// `equiv_neg` tautologies and resolution.  Returns the last step's id.
    fn emit_bound_flip(&mut self, pool: &mut dyn TermPool, a: &Rc<Term>, b: &Rc<Term>) -> String {
        let a_implies_b =
            self.emit_clause(&format!("(not {a:#}) {b:#}"), "la_generic", &[], "1.0 1.0");
        let b_implies_a =
            self.emit_clause(&format!("(not {b:#}) {a:#}"), "la_generic", &[], "1.0 1.0");
        let neg2 = self.emit_clause(
            &format!("(= {a:#} {b:#}) {a:#} {b:#}"),
            "equiv_neg2",
            &[],
            "",
        );
        let with_b = self.emit_clause(
            &format!("(= {a:#} {b:#}) {b:#}"),
            "resolution",
            &[neg2, a_implies_b],
            "",
        );
        let neg1 = self.emit_clause(
            &format!("(= {a:#} {b:#}) (not {a:#}) (not {b:#})"),
            "equiv_neg1",
            &[],
            "",
        );
        let with_not_b = self.emit_clause(
            &format!("(= {a:#} {b:#}) (not {b:#})"),
            "resolution",
            &[neg1, b_implies_a],
            "",
        );
        let _ = pool;
        self.emit(pool, a, b, "resolution", &[with_b, with_not_b])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser;

    const INTS: &str = "(declare-const x Int) (declare-const y Int) (declare-const z Int) (declare-const p Bool) (declare-const q Bool) (declare-fun f (Int) Int)";
    const REALS: &str = "(declare-const a Real) (declare-const b Real) (declare-const x Int)";

    fn parse(
        problem: &str,
        lhs: &str,
        rhs: &str,
    ) -> (
        crate::ast::Problem,
        Rc<Term>,
        Rc<Term>,
        crate::ast::pool::PrimitivePool,
    ) {
        let problem_text = format!("{problem}\n(assert (= {lhs} {rhs}))\n");
        let proof = format!("(assume h0 (= {lhs} {rhs}))\n");
        let (problem, proof, _, pool) = parser::parse_instance(
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
        (problem, l.clone(), r.clone(), pool)
    }

    /// Normalizes `lhs` and `rhs` parsed against `problem`, returning
    /// whether they coincide and their printed normal forms.
    fn same(problem: &str, lhs: &str, rhs: &str) -> (bool, String, String) {
        let (_, l, r, mut pool) = parse(problem, lhs, rhs);
        let mut normalizer = Normalizer::new();
        let nl = normalizer.normalize(&mut pool, &l);
        let nr = normalizer.normalize(&mut pool, &r);
        (nl == nr, format!("{nl:#}"), format!("{nr:#}"))
    }

    /// The certificate of `(= lhs rhs)`, checked by the checker.
    fn certified(problem: &str, lhs: &str, rhs: &str) -> Result<usize, String> {
        let (problem_ast, l, r, mut pool) = parse(problem, lhs, rhs);
        let mut normalizer = Normalizer::new();
        let steps = normalizer
            .certificate(&mut pool, "t1", &l, &r)
            .ok_or_else(|| "sides differ".to_owned())?;
        let negated = format!("(not (= {lhs} {rhs}))");
        let proof = format!(
            "(assume t1.h {negated})\n{}\n(step t1.{} (cl) :rule resolution :premises (t1.{} t1.h))\n",
            steps.join("\n"),
            steps.len() + 1,
            steps.len()
        );
        let problem_text = format!("{problem}\n(assert {negated})\n");
        let (problem_parsed, proof_parsed, _) = parser::parse_instance_with_pool(
            parser::Source::new(std::path::Path::new("<p>"), &problem_text),
            parser::Source::new(std::path::Path::new("<c>"), &proof),
            None,
            parser::Config::new().allow_int_real_subtyping(true),
            &mut pool,
        )
        .map_err(|e| format!("certificate does not parse: {e}\n{proof}"))?;
        let _ = problem_ast;
        let rules = crate::ast::rare_rules::Rules::default();
        let mut checker =
            crate::checker::ProofChecker::new(&mut pool, &rules, crate::checker::Config::new());
        match checker.check(&problem_parsed, &proof_parsed) {
            Ok(_) => Ok(steps.len()),
            Err(e) => Err(format!("certificate rejected: {e}\n{proof}")),
        }
    }

    #[test]
    fn equivalent_sides_coincide() {
        for (problem, lhs, rhs) in [
            (INTS, "(* 4 256)", "1024"),
            (INTS, "(+ 0 1536 -1024 -1024 -512 -512 512 512 512)", "0"),
            (INTS, "(+ x y x)", "(+ (* 2 x) y)"),
            (INTS, "(- x y)", "(+ x (* (- 1) y))"),
            (INTS, "(* (+ x 1) (+ x 1))", "(+ (* x x) (* 2 x) 1)"),
            (INTS, "(< x y)", "(< (- x y) 0)"),
            (INTS, "(> (* 2 x) 3)", "(> (* 2 x) 3)"),
            (
                INTS,
                "(>= (* -2 x) (* -4 y))",
                "(>= (+ (* -1 x) (* 2 y)) 0)",
            ),
            (INTS, "(= x y)", "(= (- y x) 0)"),
            (INTS, "(and p true q p)", "(and q p)"),
            (INTS, "(or p (or q p) false)", "(or q p)"),
            (INTS, "(and (and p q) (and q p))", "(and p q)"),
            (INTS, "(distinct x y)", "(not (= x y))"),
            (
                INTS,
                "(distinct x y z)",
                "(and (not (= y x)) (not (= z x)) (not (= z y)))",
            ),
            (INTS, "(f (+ x 0))", "(f x)"),
            (INTS, "(<= 2 3)", "true"),
            (INTS, "(and p (<= x x))", "p"),
            (REALS, "(>= 0.0 (/ (- 1) 1024))", "true"),
            (
                REALS,
                "(* (/ 1 2) (to_real (+ x (* 2 x))))",
                "(* (/ 3 2) (to_real x))",
            ),
            (REALS, "(< (* 2.0 a) b)", "(< (+ a (* (- 0.5) b)) 0.0)"),
            (REALS, "(= (- 1.0) (- 1))", "true"),
            (REALS, "(<= 1 a)", "(<= (- a) (- 1.0))"),
            // veriT's `la_rw_eq` shapes
            (INTS, "(and (<= x y) (<= y x))", "(= x y)"),
            (INTS, "(and (<= y x) (<= x y))", "(= x y)"),
            (INTS, "(and p (= 0 x))", "(and p (and (<= 0 x) (<= x 0)))"),
            (INTS, "(not (= x y))", "(not (and (<= x y) (<= y x)))"),
            (
                INTS,
                "(ite p (= 1 x) (= 0 x))",
                "(ite p (and (<= 1 x) (<= x 1)) (and (<= 0 x) (<= x 0)))",
            ),
            (
                INTS,
                "(and p q (= 0 (+ x (* (- 2) y))))",
                "(and p q (and (<= 0 (+ x (* (- 2) y))) (<= (+ x (* (- 2) y)) 0)))",
            ),
            (REALS, "(and (<= a b) (<= b a))", "(= (- a b) 0.0)"),
            // cvc5's `arith-eq-elim` shape, and the other ways round
            (INTS, "(and (>= x y) (<= x y))", "(= x y)"),
            (INTS, "(and (<= x y) (>= x y))", "(= x y)"),
            (INTS, "(and (>= y x) (>= x y))", "(= x y)"),
            (INTS, "(and p (= 0 x))", "(and p (and (>= x 0) (<= x 0)))"),
            (REALS, "(and (>= a b) (<= a b))", "(= (- a b) 0.0)"),
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
            (INTS, "(and p (not p))", "false"),
            (INTS, "(=> p q)", "(or (not p) q)"),
            (INTS, "(not (not p))", "p"),
            (INTS, "(= p true)", "p"),
            (INTS, "(not (<= x 3))", "(>= x 4)"),
            (INTS, "(and (<= x y) (<= y z))", "(= x y)"),
            (INTS, "(and (<= x y) (< y x))", "(= x y)"),
            (INTS, "(and (>= x y) (>= x y))", "(= x y)"),
            (INTS, "(and (>= x y) (<= y x))", "(= x y)"),
            (INTS, "(and p (<= x y) (<= y x))", "(and p (= x y))"),
            (REALS, "(>= a 1.0)", "(> a 1.0)"),
        ] {
            let (equal, nl, nr) = same(problem, lhs, rhs);
            assert!(!equal, "{lhs} and {rhs} both normalize to {nl}, {nr}");
        }
    }

    #[test]
    fn certificates_check() {
        for (problem, lhs, rhs) in [
            (INTS, "(* 4 256)", "1024"),
            (INTS, "(+ x y x)", "(+ (* 2 x) y)"),
            (INTS, "(< x y)", "(< (- x y) 0)"),
            (
                INTS,
                "(>= (* -2 x) (* -4 y))",
                "(>= (+ (* -1 x) (* 2 y)) 0)",
            ),
            (INTS, "(= x y)", "(= (- y x) 0)"),
            (INTS, "(and p true q p)", "(and q p)"),
            (INTS, "(and (and p q) (and q p))", "(and p q)"),
            (
                INTS,
                "(distinct x y z)",
                "(and (not (= y x)) (not (= z x)) (not (= z y)))",
            ),
            (INTS, "(f (+ x 0))", "(f x)"),
            (INTS, "(and p (<= x x))", "p"),
            (
                INTS,
                "(or (distinct x (+ y 0)) (= (f (* 1 x)) 0))",
                "(or (not (= x y)) (= (f x) 0))",
            ),
            (INTS, "x", "x"),
            (
                REALS,
                "(* (/ 1 2) (to_real (+ x (* 2 x))))",
                "(* (/ 3 2) (to_real x))",
            ),
            (REALS, "(< (* 2.0 a) b)", "(< (+ a (* (- 0.5) b)) 0.0)"),
            (REALS, "(<= 1 a)", "(<= (- a) (- 1.0))"),
            (INTS, "(and (<= x y) (<= y x))", "(= x y)"),
            (INTS, "(and p (= 0 x))", "(and p (and (<= 0 x) (<= x 0)))"),
            (INTS, "(not (= x y))", "(not (and (<= x y) (<= y x)))"),
            (
                INTS,
                "(ite p (= 1 x) (= 0 x))",
                "(ite p (and (<= 1 x) (<= x 1)) (and (<= 0 x) (<= x 0)))",
            ),
            (
                INTS,
                "(and p q (= 0 (+ x (* (- 2) y))))",
                "(and p q (and (<= 0 (+ x (* (- 2) y))) (<= (+ x (* (- 2) y)) 0)))",
            ),
            (REALS, "(and (<= a b) (<= b a))", "(= (- a b) 0.0)"),
            (INTS, "(and (>= x y) (<= x y))", "(= x y)"),
            (INTS, "(and (<= x y) (>= x y))", "(= x y)"),
            (INTS, "(and (>= y x) (>= x y))", "(= x y)"),
            (INTS, "(and p (= 0 x))", "(and p (and (>= x 0) (<= x 0)))"),
            (
                INTS,
                "(not (= 0 (+ x (* (- 2) y))))",
                "(not (and (>= (+ x (* (- 2) y)) 0) (<= (+ x (* (- 2) y)) 0)))",
            ),
            (REALS, "(and (>= a b) (<= a b))", "(= (- a b) 0.0)"),
        ] {
            match certified(problem, lhs, rhs) {
                Ok(_) => {}
                Err(e) => panic!("{lhs} = {rhs}: {e}"),
            }
        }
    }
}
