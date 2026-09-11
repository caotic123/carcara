//! Checker-side recomputation of the egglog solvers' computational unions.
use std::{cmp::Ordering, collections::{BTreeMap, HashSet}};
use rug::{Integer, Rational};
use egglog::ast::{Action as EgglogAction, Command as EgglogCommand, GenericExpr, Literal as EgglogLiteral};
use super::*;

/// The computational egglog solvers whose unions carry no rewrite witness.
/// Each is a deterministic function on terms, so a certificate step is
/// verified by recomputing it — never by consulting the e-graph, whose
/// intermediate solver state (`to_formula` rows, partial lists) is not
/// evidence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Computation {
    DistinctElim,
    Evaluation,
    AciNorm,
    /// Polynomial normal forms agree (cvc5's ARITH_POLY_NORM).
    ArithPolyNorm,
    /// Canonical relation keys agree (cvc5's ARITH_POLY_NORM_REL).
    ArithPolyNormRel,
}

/// The term-to-term solvers, proposed as edges by the in-class search.
/// The arithmetic kinds judge both sides at once and are proposed by the
/// cross-class strategy instead.
pub const COMPUTATIONS: [Computation; 3] = [
    Computation::DistinctElim,
    Computation::Evaluation,
    Computation::AciNorm,
];

/// Flatten a term through an ACI operator: nested same-operator
/// applications are inlined and the operator's identity is dropped.
pub fn flatten_aci(term: &Term, operator: &str, identity: bool, out: &mut Vec<Term>) {
    if let Some((op, elements)) = encoded_application(term) {
        if op == operator {
            for element in &elements {
                flatten_aci(element, operator, identity, out);
            }
            return;
        }
    }
    if bool_value(term) == Some(identity) {
        return;
    }
    out.push(term.clone());
}

/// Associative-commutative-idempotent equality for `and`/`or`: both sides
/// flatten to the same non-empty set of literals.  Purely syntactic — the
/// e-graph is never consulted, so this is decidable checker-side.
pub fn aci_equal(lhs: &Term, rhs: &Term) -> bool {
    let operator = [lhs, rhs].iter().find_map(|term| {
        match encoded_application(term) {
            Some(("@and", _)) => Some(("@and", true)),
            Some(("@or", _)) => Some(("@or", false)),
            _ => None,
        }
    });
    let Some((operator, identity)) = operator else {
        return false;
    };
    let mut left = Vec::new();
    let mut right = Vec::new();
    flatten_aci(lhs, operator, identity, &mut left);
    flatten_aci(rhs, operator, identity, &mut right);
    let left: HashSet<_> = left.into_iter().collect();
    let right: HashSet<_> = right.into_iter().collect();
    !left.is_empty() && left == right
}

// ---------------------------------------------------------------------
// Arithmetic: polynomial normal forms (arith_poly_norm) and canonical
// relation keys (arith_poly_norm_rel), recomputed checker-side.  The
// solver proves these goals by comparing normal forms of the two sides
// rather than by union, so they never share an e-class.
// ---------------------------------------------------------------------

/// Sort facts the arithmetic checkers need: which uninterpreted functions
/// are integer- or real-valued.  Read off the generated program's opaque
/// atom rules — problem signature, never e-graph state.
#[derive(Clone, Debug, Default)]
pub struct ArithSorts {
    pub int_functions: HashSet<String>,
    pub real_functions: HashSet<String>,
}

impl ArithSorts {
    pub fn from_generated_program(program: &str) -> Self {
        let commands = egglog::ast::Parser::default()
            .get_program_from_string(None, program)
            .expect("Carcara's generated egglog program should parse");
        let mut sorts = Self::default();
        for command in commands {
            let EgglogCommand::Rule { rule, .. } = command else {
                continue;
            };
            for action in &rule.head.0 {
                let EgglogAction::Set(_, head, arguments, value) = action else {
                    continue;
                };
                if head.to_string() != "arithCopyOf" {
                    continue;
                }
                let Some(GenericExpr::Call(_, wrapper, wrapped)) = arguments.first() else {
                    continue;
                };
                let Some(GenericExpr::Call(_, function, _)) = wrapped.first() else {
                    continue;
                };
                let GenericExpr::Call(_, atom, atom_arguments) = value else {
                    continue;
                };
                if wrapper.to_string() != "Mk" || atom.to_string() != "AAtom" {
                    continue;
                }
                let Some(GenericExpr::Lit(_, EgglogLiteral::Bool(is_int))) =
                    atom_arguments.get(1)
                else {
                    continue;
                };
                let set = if *is_int {
                    &mut sorts.int_functions
                } else {
                    &mut sorts.real_functions
                };
                set.insert(function.to_string());
            }
        }
        sorts
    }

    /// `Some(true)` for integer-valued atoms, `Some(false)` for real-valued
    /// ones, `None` when the sort is not numeric or unknown — which the
    /// checkers treat conservatively, never as integer.
    pub fn atom_is_int(&self, atom: &Term) -> Option<bool> {
        let ("Mk", [inner]) = (atom.op.as_str(), atom.children.as_slice()) else {
            return None;
        };
        match (inner.op.as_str(), inner.children.as_slice()) {
            ("Var", [_, sort]) => match sort_name(sort)? {
                "Int" => Some(true),
                "Real" => Some(false),
                _ => None,
            },
            // Opaque divisions are real-valued for the solver.
            ("@/" | "@/_total", [_]) => Some(false),
            (function, [_]) if self.int_functions.contains(function) => Some(true),
            (function, [_]) if self.real_functions.contains(function) => Some(false),
            _ => None,
        }
    }
}

pub fn sort_name(sort: &Term) -> Option<&str> {
    let inner = match (sort.op.as_str(), sort.children.as_slice()) {
        ("Sort", [inner]) => inner,
        _ => sort,
    };
    let ("Const", [name]) = (inner.op.as_str(), inner.children.as_slice()) else {
        return None;
    };
    Some(name.op.trim_matches('"'))
}

/// A monomial: atom -> exponent, in canonical (sorted) order.
pub type Monomial = BTreeMap<Term, u32>;

/// A polynomial in canonical form: monomial -> nonzero rational
/// coefficient.  The empty monomial is the constant term, and sorts first.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Poly(BTreeMap<Monomial, Rational>);

impl Poly {
    pub fn constant(value: Rational) -> Self {
        let mut poly = Self::default();
        poly.add_term(Monomial::new(), value);
        poly
    }

    pub fn atom(term: Term) -> Self {
        let mut poly = Self::default();
        poly.add_term(Monomial::from([(term, 1)]), Rational::from(1));
        poly
    }

    pub fn add_term(&mut self, monomial: Monomial, coefficient: Rational) {
        let sum = match self.0.remove(&monomial) {
            Some(existing) => existing + coefficient,
            None => coefficient,
        };
        if sum != 0 {
            self.0.insert(monomial, sum);
        }
    }

    pub fn add(&self, other: &Self) -> Self {
        let mut out = self.clone();
        for (monomial, coefficient) in &other.0 {
            out.add_term(monomial.clone(), coefficient.clone());
        }
        out
    }

    pub fn scale(&self, factor: &Rational) -> Self {
        let mut out = Self::default();
        for (monomial, coefficient) in &self.0 {
            out.add_term(monomial.clone(), Rational::from(coefficient * factor));
        }
        out
    }

    pub fn sub(&self, other: &Self) -> Self {
        self.add(&other.scale(&Rational::from(-1)))
    }

    pub fn mul(&self, other: &Self) -> Self {
        let mut out = Self::default();
        for (left, c1) in &self.0 {
            for (right, c2) in &other.0 {
                let mut monomial = left.clone();
                for (atom, power) in right {
                    *monomial.entry(atom.clone()).or_insert(0) += power;
                }
                out.add_term(monomial, Rational::from(c1 * c2));
            }
        }
        out
    }

    pub fn as_constant(&self) -> Option<Rational> {
        match self.0.len() {
            0 => Some(Rational::new()),
            1 => self.0.get(&Monomial::new()).cloned(),
            _ => None,
        }
    }

    pub fn constant_term(&self) -> Rational {
        self.0.get(&Monomial::new()).cloned().unwrap_or_default()
    }

    pub fn without_constant(&self) -> Self {
        let mut out = self.clone();
        out.0.remove(&Monomial::new());
        out
    }

    /// The solver's scaling pivot: the absolute coefficient of the first
    /// non-constant monomial, or of the constant when there is none.
    pub fn pivot(&self) -> Option<Rational> {
        self.0
            .iter()
            .find(|(monomial, _)| !monomial.is_empty())
            .or_else(|| self.0.iter().next())
            .map(|(_, coefficient)| coefficient.clone().abs())
    }

    pub fn head_is_nonnegative(&self) -> bool {
        self.0
            .values()
            .next()
            .map_or(true, |coefficient| coefficient.cmp0() != Ordering::Less)
    }

    /// Integer-valued under every integer assignment of its atoms: integer
    /// coefficients over integer atoms.  The constant term only counts when
    /// asked for.
    pub fn is_int_valued(&self, sorts: &ArithSorts, include_constant: bool) -> bool {
        self.0.iter().all(|(monomial, coefficient)| {
            if monomial.is_empty() {
                !include_constant || coefficient.is_integer()
            } else {
                coefficient.is_integer()
                    && monomial
                        .keys()
                        .all(|atom| sorts.atom_is_int(atom) == Some(true))
            }
        })
    }

    pub fn atoms_are_numeric(&self, sorts: &ArithSorts) -> bool {
        self.0
            .keys()
            .flat_map(|monomial| monomial.keys())
            .all(|atom| sorts.atom_is_int(atom).is_some())
    }
}

pub const ARITH_OPS: [&str; 10] = [
    "@+",
    "@-",
    "@*",
    "@/",
    "@/_total",
    "@to_real",
    "@arith_pos1",
    "@arith_neg1",
    "@arith_add2",
    "@arith_sub2",
];

/// Polynomial normal form of an encoded numeric term, mirroring the
/// solver's `arithCopyOf`/`arithPolyNfOf`: n-ary operators fold left,
/// `to_real` is erased, division scales by a nonzero constant denominator
/// and is otherwise an opaque atom, and any non-arithmetic term is an
/// opaque atom.
pub fn poly_of(term: &Term) -> Option<Poly> {
    let ("Mk", [inner]) = (term.op.as_str(), term.children.as_slice()) else {
        return None;
    };
    match (inner.op.as_str(), inner.children.as_slice()) {
        ("Num", [value]) => Some(Poly::constant(value.op.parse::<Integer>().ok()?.into())),
        ("Real", [numer, denom]) => Some(Poly::constant(rational_from_leaves(numer, denom)?)),
        ("RatConst", [literal]) => Some(Poly::constant(bigrat_literal(&literal.op)?)),
        (operator, [arguments]) if ARITH_OPS.contains(&operator) => {
            let elements = list_elements(arguments)?;
            let polys = elements.iter().map(poly_of).collect::<Option<Vec<_>>>()?;
            fold_arith(operator, &elements, &polys)
        }
        _ => Some(Poly::atom(term.clone())),
    }
}

pub fn fold_arith(operator: &str, elements: &[Term], polys: &[Poly]) -> Option<Poly> {
    let (first, rest) = polys.split_first()?;
    match operator {
        "@+" | "@arith_pos1" | "@arith_add2" => {
            Some(rest.iter().fold(first.clone(), |acc, poly| acc.add(poly)))
        }
        "@-" | "@arith_neg1" | "@arith_sub2" => Some(if rest.is_empty() {
            first.scale(&Rational::from(-1))
        } else {
            rest.iter().fold(first.clone(), |acc, poly| acc.sub(poly))
        }),
        "@*" => Some(rest.iter().fold(first.clone(), |acc, poly| acc.mul(poly))),
        "@to_real" if rest.is_empty() => Some(first.clone()),
        "@/" | "@/_total" => {
            let mut acc = first.clone();
            let mut acc_term = elements[0].clone();
            for (poly, element) in rest.iter().zip(&elements[1..]) {
                acc_term = encoded_app(operator, vec![acc_term, element.clone()]);
                acc = match poly.as_constant() {
                    Some(k) if k != 0 => acc.scale(&Rational::from(k.recip_ref())),
                    _ => Poly::atom(acc_term.clone()),
                };
            }
            Some(acc)
        }
        _ => None,
    }
}

/// Both sides have the same polynomial normal form.
pub fn poly_equal(lhs: &Term, rhs: &Term) -> bool {
    matches!((poly_of(lhs), poly_of(rhs)), (Some(l), Some(r)) if l == r)
}

/// Canonical key of an arithmetic relation: `p` in `p = 0`, `p >= 0` or
/// `p > 0`, normalized so equivalent relations share one key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RelKey {
    Eq(Poly),
    Geq(Poly),
    Gt(Poly),
}

/// Positive scaling by the pivot coefficient.
pub fn canon_rel(poly: &Poly) -> Poly {
    match poly.pivot() {
        Some(k) if k != 0 => poly.scale(&Rational::from(k.recip_ref())),
        _ => poly.clone(),
    }
}

/// Scaling by any nonzero constant: pivot magnitude, head sign nonnegative.
pub fn canon_eq(poly: &Poly) -> Poly {
    let scaled = canon_rel(poly);
    if scaled.head_is_nonnegative() {
        scaled
    } else {
        scaled.scale(&Rational::from(-1))
    }
}

/// `p >= 0`: when the non-constant part is integer-valued, the constant
/// tightens to its floor (`q + k >= 0` iff `q + floor(k) >= 0`).
pub fn canon_geq(poly: &Poly, sorts: &ArithSorts) -> Poly {
    let scaled = canon_rel(poly);
    let rest = scaled.without_constant();
    if rest.is_int_valued(sorts, false) {
        let floor = Integer::from(scaled.constant_term().floor_ref());
        rest.add(&Poly::constant(Rational::from(floor)))
    } else {
        scaled
    }
}

/// `p > 0`: a strict key over the reals; over an integer-valued `p` it is
/// `p - 1 >= 0`.  The constant must be an integer for that shift to be
/// valid (`x > 1/2` is `x >= 1`, not `x >= 2`), so unlike the solver's
/// own key this one checks it.
pub fn canon_strict(poly: &Poly, sorts: &ArithSorts) -> RelKey {
    if poly.is_int_valued(sorts, true) {
        RelKey::Geq(canon_geq(&poly.sub(&Poly::constant(Rational::from(1))), sorts))
    } else {
        RelKey::Gt(canon_rel(poly))
    }
}

pub fn rel_key(term: &Term, sorts: &ArithSorts) -> Option<RelKey> {
    let diff = |a: &Term, b: &Term| Some(poly_of(a)?.sub(&poly_of(b)?));
    let (operator, elements) = encoded_application(term)?;
    match (operator, elements.as_slice()) {
        ("@=", [a, b]) => {
            let (left, right) = (poly_of(a)?, poly_of(b)?);
            (left.atoms_are_numeric(sorts) && right.atoms_are_numeric(sorts))
                .then(|| RelKey::Eq(canon_eq(&left.sub(&right))))
        }
        ("@>=", [a, b]) => Some(RelKey::Geq(canon_geq(&diff(a, b)?, sorts))),
        ("@<=", [a, b]) => Some(RelKey::Geq(canon_geq(&diff(b, a)?, sorts))),
        ("@>", [a, b]) => Some(canon_strict(&diff(a, b)?, sorts)),
        ("@<", [a, b]) => Some(canon_strict(&diff(b, a)?, sorts)),
        ("@not", [negated]) => {
            let (operator, elements) = encoded_application(negated)?;
            match (operator, elements.as_slice()) {
                ("@>=", [a, b]) => Some(canon_strict(&diff(b, a)?, sorts)),
                ("@<=", [a, b]) => Some(canon_strict(&diff(a, b)?, sorts)),
                ("@>", [a, b]) => Some(RelKey::Geq(canon_geq(&diff(b, a)?, sorts))),
                ("@<", [a, b]) => Some(RelKey::Geq(canon_geq(&diff(a, b)?, sorts))),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Both sides are arithmetic relations with the same canonical key.
pub fn rel_equal(lhs: &Term, rhs: &Term, sorts: &ArithSorts) -> bool {
    matches!((rel_key(lhs, sorts), rel_key(rhs, sorts)), (Some(l), Some(r)) if l == r)
}

/// The arithmetic computation, if any, that justifies `lhs = rhs` outright.
pub fn arith_kind(lhs: &Term, rhs: &Term, sorts: &ArithSorts) -> Option<Computation> {
    if poly_equal(lhs, rhs) {
        Some(Computation::ArithPolyNorm)
    } else if rel_equal(lhs, rhs, sorts) {
        Some(Computation::ArithPolyNormRel)
    } else {
        None
    }
}

impl Computation {
    /// Checker-side recomputation mirroring the egglog solver exactly.
    /// Computations are stated on formula positions; an obligation that
    /// descended through the `Mk` wrapper by congruence is served by
    /// wrapping, computing, and unwrapping again.
    pub fn apply(self, term: &Term) -> Option<Term> {
        if term.op == "Mk" {
            return self.apply_wrapped(term);
        }
        let result = self.apply_wrapped(&Term::new("Mk", vec![term.clone()]))?;
        match (result.op.as_str(), result.children.as_slice()) {
            ("Mk", [inner]) => Some(inner.clone()),
            _ => None,
        }
    }

    pub fn apply_wrapped(self, term: &Term) -> Option<Term> {
        match self {
            // Judged on both sides at once (`poly_equal` / `rel_equal`); no
            // term-to-term form.
            Self::ArithPolyNorm | Self::ArithPolyNormRel => None,
            Self::Evaluation => evaluate(term),
            // distinct(t1..tn) = and of pairwise (not (= ti tj)), i < j, in
            // the solver's row-major order.
            Self::DistinctElim => {
                let (operator, elements) = encoded_application(term)?;
                if operator != "@distinct" || elements.len() < 2 {
                    return None;
                }
                let mut conjuncts = Vec::new();
                for i in 0..elements.len() {
                    for j in i + 1..elements.len() {
                        let equality =
                            encoded_app("@=", vec![elements[i].clone(), elements[j].clone()]);
                        conjuncts.push(encoded_app("@not", vec![equality]));
                    }
                }
                Some(encoded_app("@and", conjuncts))
            }
            // ACI cleanups for and/or, mirroring aci_norm's term-level
            // rewrites: singleton and idempotency collapse, identity
            // elimination (identity as the second element, as the rule has
            // it).
            Self::AciNorm => {
                let (operator, elements) = encoded_application(term)?;
                let identity = match operator {
                    "@and" => true,
                    "@or" => false,
                    _ => return None,
                };
                match elements.as_slice() {
                    [x] if x.op == "Mk" => Some(x.clone()),
                    [x, y] if x == y && x.op == "Mk" => Some(x.clone()),
                    [x, y] if x.op == "Mk" && bool_value(y) == Some(identity) => Some(x.clone()),
                    _ => None,
                }
            }
        }
    }
}

/// SMT-LIB integer division and modulo: the remainder is never negative.
pub fn euclidean_div_mod(x: i64, y: i64) -> Option<(i64, i64)> {
    if y == 0 {
        return None;
    }
    let remainder = x.checked_rem_euclid(y)?;
    let quotient = x.checked_sub(remainder)?.checked_div(y)?;
    Some((quotient, remainder))
}

/// Constant folding, mirroring evaluation.egglog: Boolean connectives and
/// `ite`, comparisons, integer and rational arithmetic, conversions.  Real
/// literals normalize to `RatConst`, the solver's own rewrite.  Integer
/// `div`/`mod` follow SMT-LIB (Euclidean) semantics; where the solver
/// would compute something else the recomputed term is simply absent
/// from the e-graph, and no step is proposed.
pub fn evaluate(term: &Term) -> Option<Term> {
    if let ("Mk", [inner]) = (term.op.as_str(), term.children.as_slice()) {
        if inner.op == "Real" {
            return rational_of(term).map(|value| encoded_rational(&value));
        }
    }
    let (operator, elements) = encoded_application(term)?;
    let ints = |x: &Term, y: &Term| Some((integer_of(x)?, integer_of(y)?));
    let rats = |x: &Term, y: &Term| Some((rational_of(x)?, rational_of(y)?));
    match (operator, elements.as_slice()) {
        ("@not", [x]) => Some(encoded_bool(!bool_value(x)?)),
        ("@and", [x, y]) => Some(encoded_bool(bool_value(x)? && bool_value(y)?)),
        ("@or", [x, y]) => Some(encoded_bool(bool_value(x)? || bool_value(y)?)),
        ("@xor", [x, y]) => Some(encoded_bool(bool_value(x)? ^ bool_value(y)?)),
        ("@=>", [x, y]) => Some(encoded_bool(!bool_value(x)? || bool_value(y)?)),
        ("@ite", [condition, x, y]) => Some(if bool_value(condition)? {
            x.clone()
        } else {
            y.clone()
        }),
        ("@=", [x, y]) => {
            let equal = if let (Some(a), Some(b)) = (bool_value(x), bool_value(y)) {
                a == b
            } else if let Some((a, b)) = ints(x, y) {
                a == b
            } else {
                let (a, b) = rats(x, y)?;
                a == b
            };
            Some(encoded_bool(equal))
        }
        ("@<" | "@<=" | "@>" | "@>=", [x, y]) => {
            let ordering = match ints(x, y) {
                Some((a, b)) => a.cmp(&b),
                None => {
                    let (a, b) = rats(x, y)?;
                    a.cmp(&b)
                }
            };
            Some(encoded_bool(match operator {
                "@<" => ordering == Ordering::Less,
                "@<=" => ordering != Ordering::Greater,
                "@>" => ordering == Ordering::Greater,
                _ => ordering != Ordering::Less,
            }))
        }
        ("@+" | "@-" | "@*", [x, y]) => {
            if let Some((a, b)) = ints(x, y) {
                let value = match operator {
                    "@+" => a.checked_add(b)?,
                    "@-" => a.checked_sub(b)?,
                    _ => a.checked_mul(b)?,
                };
                Some(encoded_num(value))
            } else {
                let (a, b) = rats(x, y)?;
                let value = match operator {
                    "@+" => a + b,
                    "@-" => a - b,
                    _ => a * b,
                };
                Some(encoded_rational(&value))
            }
        }
        ("@-", [x]) => match integer_of(x) {
            Some(a) => Some(encoded_num(a.checked_neg()?)),
            None => Some(encoded_rational(&(-rational_of(x)?))),
        },
        ("@/" | "@/_total", [x, y]) => {
            let (a, b) = match ints(x, y) {
                Some((a, b)) => (Rational::from(a), Rational::from(b)),
                None => rats(x, y)?,
            };
            let value = if b != 0 {
                a / b
            } else if operator == "@/_total" {
                Rational::new()
            } else {
                return None;
            };
            Some(encoded_rational(&value))
        }
        ("@div", [x, y]) => {
            let (a, b) = ints(x, y)?;
            Some(encoded_num(euclidean_div_mod(a, b)?.0))
        }
        ("@mod", [x, y]) => {
            let (a, b) = ints(x, y)?;
            Some(encoded_num(euclidean_div_mod(a, b)?.1))
        }
        ("@to_real", [x]) => {
            let value = match integer_of(x) {
                Some(a) => Rational::from(a),
                None => rational_of(x)?,
            };
            Some(encoded_rational(&value))
        }
        ("@to_int", [x]) => match integer_of(x) {
            Some(a) => Some(encoded_num(a)),
            None => Some(encoded_num(
                Integer::from(rational_of(x)?.floor_ref()).to_i64()?,
            )),
        },
        ("@is_int", [x]) => Some(encoded_bool(
            integer_of(x).is_some() || rational_of(x)?.is_integer(),
        )),
        ("@abs", [x]) => match integer_of(x) {
            Some(a) => Some(encoded_num(a.checked_abs()?)),
            None => Some(encoded_rational(&rational_of(x)?.abs())),
        },
        _ => None,
    }
}
