use std::{
    cmp::Ordering,
    collections::{BTreeMap, HashMap, HashSet},
    fs::File,
    io::BufReader,
    path::{Path, PathBuf},
    rc::Rc,
    time::{Duration, Instant},
};

use carcara::{
    ast::ProofNode,
    parser,
    rare::engine::{RunEgglogOptions, run_egglog},
};
use egglog::{
    EGraph as ProductionEGraph, SerializeConfig as ProductionSerializeConfig,
    ast::{Action as EgglogAction, Command as EgglogCommand, Expr as EgglogExpr, GenericExpr},
};
use egglog_proofs::{
    CommandOutput, EGraph as ProofEGraph, SerializeConfig as ProofSerializeConfig,
};

use egglog::ast::Literal as EgglogLiteral;
use rug::{Integer, Rational};

const PROGRAM: &str = include_str!("fixtures/raw_rare_posthoc.egg");

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Term {
    op: String,
    children: Vec<Term>,
}

impl Term {
    fn new(op: &str, children: Vec<Self>) -> Self {
        Self { op: op.to_owned(), children }
    }

    fn leaf(op: &str) -> Self {
        Self::new(op, Vec::new())
    }

    fn size(&self) -> usize {
        1 + self.children.iter().map(Self::size).sum::<usize>()
    }

    fn to_egglog(&self) -> String {
        if self.children.is_empty() {
            if self.op == "Empty" {
                "(Empty)".to_owned()
            } else {
                self.op.clone()
            }
        } else {
            format!(
                "({} {})",
                self.op,
                self.children
                    .iter()
                    .map(Self::to_egglog)
                    .collect::<Vec<_>>()
                    .join(" ")
            )
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Pattern {
    Var(&'static str),
    App(&'static str, Vec<Pattern>),
}

#[derive(Clone, Debug)]
struct Rewrite {
    name: &'static str,
    lhs: Pattern,
    rhs: Pattern,
}

fn rules() -> Vec<Rewrite> {
    use Pattern::{App, Var};

    vec![
        Rewrite {
            name: "ite-then-false",
            lhs: App("Ite", vec![Var("c"), App("False", vec![]), Var("x")]),
            rhs: App("And", vec![App("Not", vec![Var("c")]), Var("x")]),
        },
        Rewrite {
            name: "and-true-right",
            lhs: App("And", vec![Var("x"), App("True", vec![])]),
            rhs: Var("x"),
        },
    ]
}

fn source() -> Term {
    Term::new(
        "Ite",
        vec![Term::leaf("Atom"), Term::leaf("False"), Term::leaf("True")],
    )
}

fn target() -> Term {
    Term::new("Not", vec![Term::leaf("Atom")])
}

fn nested_source() -> Term {
    Term::new("Not", vec![source()])
}

fn nested_target() -> Term {
    Term::new("Not", vec![target()])
}

#[derive(Clone, Debug)]
struct SnapshotNode {
    op: u32,
    child_classes: Vec<u32>,
}

/// Interns e-graph string identifiers (operators and e-class ids) into dense
/// `u32` indices, so the snapshot stores and hashes small integers instead of
/// per-node strings.
#[derive(Clone, Debug, Default)]
struct Interner {
    ids: HashMap<String, u32>,
    names: Vec<String>,
}

impl Interner {
    fn intern(&mut self, name: &str) -> u32 {
        if let Some(&id) = self.ids.get(name) {
            return id;
        }
        let id = self.names.len() as u32;
        self.ids.insert(name.to_owned(), id);
        self.names.push(name.to_owned());
        id
    }
}

/// Provenance-free view of the serialized saturated e-graph.  It deliberately
/// retains only enodes and their canonical e-class/child-class identifiers,
/// interned in a single capture pass.  Enodes are indexed three ways: by
/// e-class, by (e-class, operator) for selective matching, and by signature
/// for constant-time ground-term classification.
#[derive(Clone, Debug, Default)]
struct EGraphSnapshot {
    nodes: Vec<SnapshotNode>,
    class_nodes: Vec<Vec<u32>>,
    class_op_nodes: HashMap<(u32, u32), Vec<u32>>,
    signature_class: HashMap<(u32, Vec<u32>), u32>,
    classes: Interner,
    ops: Interner,
}

impl EGraphSnapshot {
    fn from_raw_nodes(raw: Vec<(String, Vec<String>, String)>) -> Self {
        let mut snapshot = Self::default();
        for (op, child_classes, eclass) in raw {
            let op = snapshot.ops.intern(&op);
            let child_classes = child_classes
                .iter()
                .map(|child| snapshot.classes.intern(child))
                .collect::<Vec<_>>();
            let eclass = snapshot.classes.intern(&eclass);
            let index = snapshot.nodes.len() as u32;
            if snapshot.class_nodes.len() <= eclass as usize {
                snapshot.class_nodes.resize(eclass as usize + 1, Vec::new());
            }
            snapshot.class_nodes[eclass as usize].push(index);
            snapshot
                .class_op_nodes
                .entry((eclass, op))
                .or_default()
                .push(index);
            let previous = snapshot
                .signature_class
                .insert((op, child_classes.clone()), eclass);
            assert!(
                previous.map_or(true, |class| class == eclass),
                "a congruence-closed e-graph cannot assign one signature to two classes"
            );
            snapshot.nodes.push(SnapshotNode { op, child_classes });
        }
        snapshot
    }

    fn capture(egraph: &ProofEGraph) -> Self {
        let serialized = egraph.serialize(ProofSerializeConfig::default());
        assert!(
            serialized.is_complete(),
            "reconstruction requires a complete e-graph snapshot: {}",
            serialized.omitted_description()
        );
        Self::from_raw_nodes(
            serialized
                .egraph
                .nodes
                .values()
                .map(|node| {
                    (
                        node.op.clone(),
                        node.children
                            .iter()
                            .map(|child| serialized.egraph.nodes[child].eclass.to_string())
                            .collect(),
                        node.eclass.to_string(),
                    )
                })
                .collect(),
        )
    }

    fn capture_production(egraph: &ProductionEGraph) -> Self {
        // egglog 0.4 does not return explicit truncation metadata.  Its default
        // configuration has no function/call limits, so this is a complete
        // provenance-free snapshot of Carcara's production e-graph.
        let serialized = egraph.serialize(ProductionSerializeConfig::default());
        Self::from_raw_nodes(
            serialized
                .nodes
                .values()
                .map(|node| {
                    (
                        node.op.clone(),
                        node.children
                            .iter()
                            .map(|child| serialized.nodes[child].eclass.to_string())
                            .collect(),
                        node.eclass.to_string(),
                    )
                })
                .collect(),
        )
    }

    fn class_of(&self, term: &Term, cache: &mut HashMap<Term, u32>) -> Option<u32> {
        if let Some(&eclass) = cache.get(term) {
            return Some(eclass);
        }

        let &op = self.ops.ids.get(&term.op)?;
        let child_classes = term
            .children
            .iter()
            .map(|child| self.class_of(child, cache))
            .collect::<Option<Vec<_>>>()?;
        let eclass = *self.signature_class.get(&(op, child_classes))?;
        cache.insert(term.clone(), eclass);
        Some(eclass)
    }

    fn class_of_term(&self, term: &Term) -> Option<u32> {
        self.class_of(term, &mut HashMap::new())
    }

    fn same_class(&self, lhs: &Term, rhs: &Term) -> bool {
        let mut cache = HashMap::new();
        matches!(
            (self.class_of(lhs, &mut cache), self.class_of(rhs, &mut cache)),
            (Some(lhs), Some(rhs)) if lhs == rhs
        )
    }

    /// E-match a pattern at a particular final e-class, using the
    /// (e-class, operator) index so only relevant rows are scanned.  Pattern
    /// variables map to e-class identifiers, not to freshly generated ground
    /// terms.
    fn ematch_in_class(
        &self,
        pattern: &Pattern,
        eclass: u32,
        initial: &ClassSubstitution,
        stats: &mut ReconstructionStats,
    ) -> Vec<ClassSubstitution> {
        stats.ematch_calls += 1;
        match pattern {
            Pattern::Var(variable) => match initial.get(*variable) {
                Some(&previous) if previous == eclass => vec![initial.clone()],
                Some(_) => Vec::new(),
                None => {
                    let mut substitution = initial.clone();
                    substitution.insert(*variable, eclass);
                    vec![substitution]
                }
            },
            Pattern::App(op, children) => {
                let mut matches = Vec::new();
                let rows = self
                    .ops
                    .ids
                    .get(*op)
                    .and_then(|&op| self.class_op_nodes.get(&(eclass, op)));
                for &index in rows.into_iter().flatten() {
                    stats.relation_rows_examined += 1;
                    let node = &self.nodes[index as usize];
                    if node.child_classes.len() != children.len() {
                        continue;
                    }

                    let mut substitutions = vec![initial.clone()];
                    for (child_pattern, &child_class) in children.iter().zip(&node.child_classes) {
                        substitutions = substitutions
                            .into_iter()
                            .flat_map(|substitution| {
                                self.ematch_in_class(
                                    child_pattern,
                                    child_class,
                                    &substitution,
                                    stats,
                                )
                            })
                            .collect();
                        if substitutions.is_empty() {
                            break;
                        }
                    }
                    matches.extend(substitutions);
                }
                matches.sort();
                matches.dedup();
                matches
            }
        }
    }

    /// E-match an applied pattern against the single e-node carrying
    /// `signature` — a congruence-closed class holds at most one — instead
    /// of scanning every e-node of the class.
    fn ematch_at_signature(
        &self,
        pattern: &Pattern,
        signature: &Signature,
        initial: &ClassSubstitution,
        stats: &mut ReconstructionStats,
    ) -> Vec<ClassSubstitution> {
        stats.ematch_calls += 1;
        let Pattern::App(pattern_op, children) = pattern else {
            return Vec::new();
        };
        let (op, child_classes) = signature;
        if self.ops.ids.get(*pattern_op) != Some(op) || children.len() != child_classes.len() {
            return Vec::new();
        }

        let mut substitutions = vec![initial.clone()];
        for (child_pattern, &child_class) in children.iter().zip(child_classes) {
            substitutions = substitutions
                .into_iter()
                .flat_map(|substitution| {
                    self.ematch_in_class(child_pattern, child_class, &substitution, stats)
                })
                .collect();
            if substitutions.is_empty() {
                break;
            }
        }
        substitutions.sort();
        substitutions.dedup();
        substitutions
    }

    /// Seed representative extraction with source and target subterms. Any
    /// other representative is extracted lazily if an E-match actually binds
    /// a rule variable to that class.
    fn preferred_representatives(&self, preferred: [&Term; 2]) -> HashMap<u32, Term> {
        fn insert_subterms(
            snapshot: &EGraphSnapshot,
            term: &Term,
            classes: &mut HashMap<Term, u32>,
            representatives: &mut HashMap<u32, Term>,
        ) {
            for child in &term.children {
                insert_subterms(snapshot, child, classes, representatives);
            }
            let Some(eclass) = snapshot.class_of(term, classes) else {
                return;
            };
            insert_better(representatives, eclass, term.clone());
        }

        fn insert_better(representatives: &mut HashMap<u32, Term>, eclass: u32, candidate: Term) {
            let replace = representatives.get(&eclass).map_or(true, |current| {
                (candidate.size(), &candidate) < (current.size(), current)
            });
            if replace {
                representatives.insert(eclass, candidate);
            }
        }

        let mut representatives = HashMap::new();
        let mut classes = HashMap::new();
        for term in preferred {
            insert_subterms(self, term, &mut classes, &mut representatives);
        }
        representatives
    }
}

type Substitution = BTreeMap<String, Term>;
type ClassSubstitution = BTreeMap<&'static str, u32>;

#[derive(Clone, Debug, Default)]
struct ReconstructionStats {
    ematch_calls: usize,
    relation_rows_examined: usize,
    lhs_matches: usize,
    rule_instances: usize,
    candidate_vertices: usize,
    congruence_edges: usize,
    computational_edges: usize,
    recursive_obligations: usize,
    rejustifications: usize,
}

fn match_pattern(pattern: &Pattern, term: &Term, substitution: &mut Substitution) -> bool {
    match pattern {
        Pattern::Var(variable) => match substitution.get(*variable) {
            Some(previous) => previous == term,
            None => {
                substitution.insert((*variable).to_owned(), term.clone());
                true
            }
        },
        Pattern::App(op, children) => {
            op == &term.op
                && children.len() == term.children.len()
                && children
                    .iter()
                    .zip(&term.children)
                    .all(|(pattern, term)| match_pattern(pattern, term, substitution))
        }
    }
}

fn has_unbound_variables(pattern: &Pattern, substitution: &ClassSubstitution) -> bool {
    match pattern {
        Pattern::Var(variable) => !substitution.contains_key(variable),
        Pattern::App(_, children) => children
            .iter()
            .any(|child| has_unbound_variables(child, substitution)),
    }
}

fn instantiate(pattern: &Pattern, substitution: &Substitution) -> Option<Term> {
    match pattern {
        Pattern::Var(variable) => substitution.get(*variable).cloned(),
        Pattern::App(op, children) => Some(Term::new(
            op,
            children
                .iter()
                .map(|child| instantiate(child, substitution))
                .collect::<Option<Vec<_>>>()?,
        )),
    }
}

fn encoded_args(elements: Vec<Term>) -> Term {
    elements
        .into_iter()
        .rev()
        .fold(Term::leaf("Empty"), |tail, element| {
            Term::new("Args", vec![element, tail])
        })
}

fn encoded_app(operator: &str, elements: Vec<Term>) -> Term {
    Term::new("Mk", vec![Term::new(operator, vec![encoded_args(elements)])])
}

fn encoded_bool(value: bool) -> Term {
    let literal = if value { "true" } else { "false" };
    Term::new("Mk", vec![Term::new("Bool", vec![Term::leaf(literal)])])
}

/// Elements of an encoded argument list `(Args e1 (Args e2 ... (Empty)))`.
fn list_elements(list: &Term) -> Option<Vec<Term>> {
    let mut elements = Vec::new();
    let mut current = list;
    loop {
        match (current.op.as_str(), current.children.as_slice()) {
            ("Empty", []) => return Some(elements),
            ("Args", [element, tail]) => {
                elements.push(element.clone());
                current = tail;
            }
            _ => return None,
        }
    }
}

/// Decompose an encoded application `Mk(op(list))` into its operator and
/// argument elements.
fn encoded_application(term: &Term) -> Option<(&str, Vec<Term>)> {
    let ("Mk", [application]) = (term.op.as_str(), term.children.as_slice()) else {
        return None;
    };
    let [arguments] = application.children.as_slice() else {
        return None;
    };
    Some((application.op.as_str(), list_elements(arguments)?))
}

fn bool_value(term: &Term) -> Option<bool> {
    let ("Mk", [inner]) = (term.op.as_str(), term.children.as_slice()) else {
        return None;
    };
    let ("Bool", [literal]) = (inner.op.as_str(), inner.children.as_slice()) else {
        return None;
    };
    match literal.op.as_str() {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}

/// The computational egglog solvers whose unions carry no rewrite witness.
/// Each is a deterministic function on terms, so a certificate step is
/// verified by recomputing it — never by consulting the e-graph, whose
/// intermediate solver state (`to_formula` rows, partial lists) is not
/// evidence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Computation {
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
const COMPUTATIONS: [Computation; 3] = [
    Computation::DistinctElim,
    Computation::Evaluation,
    Computation::AciNorm,
];

/// Flatten a term through an ACI operator: nested same-operator
/// applications are inlined and the operator's identity is dropped.
fn flatten_aci(term: &Term, operator: &str, identity: bool, out: &mut Vec<Term>) {
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
fn aci_equal(lhs: &Term, rhs: &Term) -> bool {
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
struct ArithSorts {
    int_functions: HashSet<String>,
    real_functions: HashSet<String>,
}

impl ArithSorts {
    fn from_generated_program(program: &str) -> Self {
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
    fn atom_is_int(&self, atom: &Term) -> Option<bool> {
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

fn sort_name(sort: &Term) -> Option<&str> {
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
type Monomial = BTreeMap<Term, u32>;

/// A polynomial in canonical form: monomial -> nonzero rational
/// coefficient.  The empty monomial is the constant term, and sorts first.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Poly(BTreeMap<Monomial, Rational>);

impl Poly {
    fn constant(value: Rational) -> Self {
        let mut poly = Self::default();
        poly.add_term(Monomial::new(), value);
        poly
    }

    fn atom(term: Term) -> Self {
        let mut poly = Self::default();
        poly.add_term(Monomial::from([(term, 1)]), Rational::from(1));
        poly
    }

    fn add_term(&mut self, monomial: Monomial, coefficient: Rational) {
        let sum = match self.0.remove(&monomial) {
            Some(existing) => existing + coefficient,
            None => coefficient,
        };
        if sum != 0 {
            self.0.insert(monomial, sum);
        }
    }

    fn add(&self, other: &Self) -> Self {
        let mut out = self.clone();
        for (monomial, coefficient) in &other.0 {
            out.add_term(monomial.clone(), coefficient.clone());
        }
        out
    }

    fn scale(&self, factor: &Rational) -> Self {
        let mut out = Self::default();
        for (monomial, coefficient) in &self.0 {
            out.add_term(monomial.clone(), Rational::from(coefficient * factor));
        }
        out
    }

    fn sub(&self, other: &Self) -> Self {
        self.add(&other.scale(&Rational::from(-1)))
    }

    fn mul(&self, other: &Self) -> Self {
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

    fn as_constant(&self) -> Option<Rational> {
        match self.0.len() {
            0 => Some(Rational::new()),
            1 => self.0.get(&Monomial::new()).cloned(),
            _ => None,
        }
    }

    fn constant_term(&self) -> Rational {
        self.0.get(&Monomial::new()).cloned().unwrap_or_default()
    }

    fn without_constant(&self) -> Self {
        let mut out = self.clone();
        out.0.remove(&Monomial::new());
        out
    }

    /// The solver's scaling pivot: the absolute coefficient of the first
    /// non-constant monomial, or of the constant when there is none.
    fn pivot(&self) -> Option<Rational> {
        self.0
            .iter()
            .find(|(monomial, _)| !monomial.is_empty())
            .or_else(|| self.0.iter().next())
            .map(|(_, coefficient)| coefficient.clone().abs())
    }

    fn head_is_nonnegative(&self) -> bool {
        self.0
            .values()
            .next()
            .map_or(true, |coefficient| coefficient.cmp0() != Ordering::Less)
    }

    /// Integer-valued under every integer assignment of its atoms: integer
    /// coefficients over integer atoms.  The constant term only counts when
    /// asked for.
    fn is_int_valued(&self, sorts: &ArithSorts, include_constant: bool) -> bool {
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

    fn atoms_are_numeric(&self, sorts: &ArithSorts) -> bool {
        self.0
            .keys()
            .flat_map(|monomial| monomial.keys())
            .all(|atom| sorts.atom_is_int(atom).is_some())
    }
}

const ARITH_OPS: [&str; 10] = [
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

fn rational_from_leaves(numer: &Term, denom: &Term) -> Option<Rational> {
    let numer: Integer = numer.op.parse().ok()?;
    let denom: Integer = denom.op.parse().ok()?;
    (denom != 0).then(|| Rational::from((numer, denom)))
}

/// A serialized `BigRat` literal, `(bigrat (bigint "n") (bigint "d"))`.
fn bigrat_literal(literal: &str) -> Option<Rational> {
    let parts: Vec<&str> = literal.split('"').collect();
    let numer: Integer = parts.get(1)?.parse().ok()?;
    let denom: Integer = parts.get(3)?.parse().ok()?;
    (denom != 0).then(|| Rational::from((numer, denom)))
}

/// Polynomial normal form of an encoded numeric term, mirroring the
/// solver's `arithCopyOf`/`arithPolyNfOf`: n-ary operators fold left,
/// `to_real` is erased, division scales by a nonzero constant denominator
/// and is otherwise an opaque atom, and any non-arithmetic term is an
/// opaque atom.
fn poly_of(term: &Term) -> Option<Poly> {
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

fn fold_arith(operator: &str, elements: &[Term], polys: &[Poly]) -> Option<Poly> {
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
fn poly_equal(lhs: &Term, rhs: &Term) -> bool {
    matches!((poly_of(lhs), poly_of(rhs)), (Some(l), Some(r)) if l == r)
}

/// Canonical key of an arithmetic relation: `p` in `p = 0`, `p >= 0` or
/// `p > 0`, normalized so equivalent relations share one key.
#[derive(Clone, Debug, PartialEq, Eq)]
enum RelKey {
    Eq(Poly),
    Geq(Poly),
    Gt(Poly),
}

/// Positive scaling by the pivot coefficient.
fn canon_rel(poly: &Poly) -> Poly {
    match poly.pivot() {
        Some(k) if k != 0 => poly.scale(&Rational::from(k.recip_ref())),
        _ => poly.clone(),
    }
}

/// Scaling by any nonzero constant: pivot magnitude, head sign nonnegative.
fn canon_eq(poly: &Poly) -> Poly {
    let scaled = canon_rel(poly);
    if scaled.head_is_nonnegative() {
        scaled
    } else {
        scaled.scale(&Rational::from(-1))
    }
}

/// `p >= 0`: when the non-constant part is integer-valued, the constant
/// tightens to its floor (`q + k >= 0` iff `q + floor(k) >= 0`).
fn canon_geq(poly: &Poly, sorts: &ArithSorts) -> Poly {
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
fn canon_strict(poly: &Poly, sorts: &ArithSorts) -> RelKey {
    if poly.is_int_valued(sorts, true) {
        RelKey::Geq(canon_geq(&poly.sub(&Poly::constant(Rational::from(1))), sorts))
    } else {
        RelKey::Gt(canon_rel(poly))
    }
}

fn rel_key(term: &Term, sorts: &ArithSorts) -> Option<RelKey> {
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
fn rel_equal(lhs: &Term, rhs: &Term, sorts: &ArithSorts) -> bool {
    matches!((rel_key(lhs, sorts), rel_key(rhs, sorts)), (Some(l), Some(r)) if l == r)
}

/// The arithmetic computation, if any, that justifies `lhs = rhs` outright.
fn arith_kind(lhs: &Term, rhs: &Term, sorts: &ArithSorts) -> Option<Computation> {
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
    fn apply(self, term: &Term) -> Option<Term> {
        if term.op == "Mk" {
            return self.apply_wrapped(term);
        }
        let result = self.apply_wrapped(&Term::new("Mk", vec![term.clone()]))?;
        match (result.op.as_str(), result.children.as_slice()) {
            ("Mk", [inner]) => Some(inner.clone()),
            _ => None,
        }
    }

    fn apply_wrapped(self, term: &Term) -> Option<Term> {
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

fn integer_of(term: &Term) -> Option<i64> {
    let ("Mk", [inner]) = (term.op.as_str(), term.children.as_slice()) else {
        return None;
    };
    match (inner.op.as_str(), inner.children.as_slice()) {
        ("Num", [value]) => value.op.parse().ok(),
        _ => None,
    }
}

/// A rational literal in either encoding: the parser's `Real` or the
/// solver's `RatConst`.
fn rational_of(term: &Term) -> Option<Rational> {
    let ("Mk", [inner]) = (term.op.as_str(), term.children.as_slice()) else {
        return None;
    };
    match (inner.op.as_str(), inner.children.as_slice()) {
        ("Real", [numer, denom]) => rational_from_leaves(numer, denom),
        ("RatConst", [literal]) => bigrat_literal(&literal.op),
        _ => None,
    }
}

fn encoded_num(value: i64) -> Term {
    Term::new("Mk", vec![Term::new("Num", vec![Term::leaf(&value.to_string())])])
}

/// The solver's rational constant, with the `BigRat` literal spelled the
/// way egglog serializes it.
fn encoded_rational(value: &Rational) -> Term {
    let literal = format!(
        "(bigrat (from-string \"{}\") (from-string \"{}\"))",
        value.numer(),
        value.denom()
    );
    Term::new("Mk", vec![Term::new("RatConst", vec![Term::leaf(&literal)])])
}

/// SMT-LIB integer division and modulo: the remainder is never negative.
fn euclidean_div_mod(x: i64, y: i64) -> Option<(i64, i64)> {
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
fn evaluate(term: &Term) -> Option<Term> {
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

#[derive(Clone, Debug, PartialEq, Eq)]
enum Certificate {
    Refl {
        term: Term,
    },
    Rule {
        name: String,
        lhs: Term,
        rhs: Term,
        substitution: Substitution,
    },
    Computational {
        kind: Computation,
        lhs: Term,
        rhs: Term,
    },
    Symm {
        lhs: Term,
        rhs: Term,
        proof: Box<Certificate>,
    },
    Congruence {
        lhs: Term,
        rhs: Term,
        child_index: usize,
        child: Box<Certificate>,
    },
    Trans {
        lhs: Term,
        middle: Term,
        rhs: Term,
        first: Box<Certificate>,
        second: Box<Certificate>,
    },
}

impl Certificate {
    fn lhs(&self) -> &Term {
        match self {
            Self::Refl { term } => term,
            Self::Rule { lhs, .. }
            | Self::Computational { lhs, .. }
            | Self::Symm { lhs, .. }
            | Self::Congruence { lhs, .. }
            | Self::Trans { lhs, .. } => lhs,
        }
    }

    fn rhs(&self) -> &Term {
        match self {
            Self::Refl { term } => term,
            Self::Rule { rhs, .. }
            | Self::Computational { rhs, .. }
            | Self::Symm { rhs, .. }
            | Self::Congruence { rhs, .. }
            | Self::Trans { rhs, .. } => rhs,
        }
    }

    fn rule_names(&self, names: &mut Vec<String>) {
        match self {
            Self::Refl { .. } | Self::Computational { .. } => {}
            Self::Rule { name, .. } => names.push(name.clone()),
            Self::Symm { proof, .. } => proof.rule_names(names),
            Self::Congruence { child, .. } => child.rule_names(names),
            Self::Trans { first, second, .. } => {
                first.rule_names(names);
                second.rule_names(names);
            }
        }
    }

    fn contains_congruence(&self) -> bool {
        match self {
            Self::Congruence { .. } => true,
            Self::Symm { proof, .. } => proof.contains_congruence(),
            Self::Trans { first, second, .. } => {
                first.contains_congruence() || second.contains_congruence()
            }
            Self::Refl { .. } | Self::Rule { .. } | Self::Computational { .. } => false,
        }
    }

    fn contains_computation(&self, kind: Computation) -> bool {
        match self {
            Self::Computational { kind: used, .. } => *used == kind,
            Self::Symm { proof, .. } => proof.contains_computation(kind),
            Self::Congruence { child, .. } => child.contains_computation(kind),
            Self::Trans { first, second, .. } => {
                first.contains_computation(kind) || second.contains_computation(kind)
            }
            Self::Refl { .. } | Self::Rule { .. } => false,
        }
    }

    fn verify(&self, rules: &[Rewrite]) -> bool {
        self.verify_in(rules, &ArithSorts::default())
    }

    /// Verification with the arithmetic sort facts the relation checker
    /// needs; `rules` and `sorts` are both trusted problem input.
    fn verify_in(&self, rules: &[Rewrite], sorts: &ArithSorts) -> bool {
        match self {
            Self::Refl { .. } => true,
            Self::Rule { name, lhs, rhs, substitution } => {
                let Some(rule) = rules.iter().find(|rule| rule.name == name) else {
                    return false;
                };
                let mut matched = BTreeMap::new();
                match_pattern(&rule.lhs, lhs, &mut matched)
                    && &matched == substitution
                    && instantiate(&rule.rhs, substitution).as_ref() == Some(rhs)
            }
            // Verified by independent recomputation; the e-graph's own
            // solver state is never consulted.  ACI steps are judged by
            // flatten-and-compare, which subsumes the collapse edges the
            // proposer generates.
            Self::Computational { kind: Computation::AciNorm, lhs, rhs } => aci_equal(lhs, rhs),
            Self::Computational { kind: Computation::ArithPolyNorm, lhs, rhs } => {
                poly_equal(lhs, rhs)
            }
            Self::Computational { kind: Computation::ArithPolyNormRel, lhs, rhs } => {
                rel_equal(lhs, rhs, sorts)
            }
            Self::Computational { kind, lhs, rhs } => kind.apply(lhs).as_ref() == Some(rhs),
            Self::Symm { lhs, rhs, proof } => {
                proof.verify_in(rules, sorts) && proof.lhs() == rhs && proof.rhs() == lhs
            }
            Self::Congruence { lhs, rhs, child_index, child } => {
                child.verify_in(rules, sorts)
                    && lhs.op == rhs.op
                    && lhs.children.len() == rhs.children.len()
                    && lhs.children.get(*child_index) == Some(child.lhs())
                    && rhs.children.get(*child_index) == Some(child.rhs())
                    && lhs
                        .children
                        .iter()
                        .zip(&rhs.children)
                        .enumerate()
                        .all(|(index, (lhs, rhs))| index == *child_index || lhs == rhs)
            }
            Self::Trans { lhs, middle, rhs, first, second } => {
                first.verify_in(rules, sorts)
                    && second.verify_in(rules, sorts)
                    && first.lhs() == lhs
                    && first.rhs() == middle
                    && second.lhs() == middle
                    && second.rhs() == rhs
            }
        }
    }
}

/// Decode an encoded term back to SMT-LIB/Alethe syntax: `Mk`-wrapped
/// constants, booleans, variables, `@`-operator applications over `Args`
/// lists, and curried `App` chains for uninterpreted functions.  Hashed
/// variable identifiers resolve through `names` (built by walking the
/// original conclusion against the encoded goals); solver-internal shapes
/// decode to `None`.
fn decode_term(term: &Term, names: &HashMap<String, String>) -> Option<String> {
    let ("Mk", [inner]) = (term.op.as_str(), term.children.as_slice()) else {
        return None;
    };
    decode_inner(inner, names)
}

fn decode_any(term: &Term, names: &HashMap<String, String>) -> Option<String> {
    if term.op == "Mk" {
        decode_term(term, names)
    } else {
        decode_inner(term, names)
    }
}

fn decode_inner(inner: &Term, names: &HashMap<String, String>) -> Option<String> {
    match (inner.op.as_str(), inner.children.as_slice()) {
        ("Const", [name]) => Some(name.op.trim_matches('"').to_owned()),
        ("Bool", [literal]) => Some(literal.op.clone()),
        ("Op", [name]) => Some(name.op.trim_matches('"').to_owned()),
        // Numerals print the way Carcara prints them, so they parse back.
        ("Num", [value]) => Some(value.op.clone()),
        ("Real", [numer, denom]) => Some(if denom.op == "1" && !numer.op.starts_with('-') {
            format!("{}.0", numer.op)
        } else {
            format!("{}/{}", numer.op, denom.op)
        }),
        ("RatConst", [literal]) => bigrat_literal(&literal.op).map(|value| {
            if value.is_integer() && value.cmp0() != Ordering::Less {
                format!("{}.0", value.numer())
            } else {
                format!("{}/{}", value.numer(), value.denom())
            }
        }),
        ("Var", [id, _sort]) => Some(
            names
                .get(&id.op)
                .cloned()
                .unwrap_or_else(|| format!("v{}", id.op.trim_start_matches('-'))),
        ),
        ("App", [_, _]) => {
            let mut arguments = Vec::new();
            let mut current = inner;
            while let ("App", [next, argument]) = (current.op.as_str(), current.children.as_slice())
            {
                arguments.push(argument);
                current = next;
            }
            arguments.reverse();
            let head = decode_any(current, names)?;
            let arguments = arguments
                .iter()
                .map(|argument| decode_any(argument, names))
                .collect::<Option<Vec<_>>>()?;
            Some(format!("({} {})", head, arguments.join(" ")))
        }
        (operator, [arguments]) if operator.starts_with('@') => {
            let elements = list_elements(arguments)?
                .iter()
                .map(|element| decode_any(element, names))
                .collect::<Option<Vec<_>>>()?;
            Some(format!("({} {})", &operator[1..], elements.join(" ")))
        }
        _ => None,
    }
}

/// Recover original variable names by walking the original conclusion term
/// in parallel with its encoding, recording every hashed `Var` identifier.
fn collect_variable_names(
    encoded: &Term,
    original: &carcara::ast::Rc<carcara::ast::Term>,
    names: &mut HashMap<String, String>,
) {
    use carcara::ast::Term as Original;
    // The Mk wrapper is present on formula positions but absent on the raw
    // arguments of curried App chains; tolerate both.
    let inner = match (encoded.op.as_str(), encoded.children.as_slice()) {
        ("Mk", [inner]) => inner,
        _ => encoded,
    };
    match (inner.op.as_str(), inner.children.as_slice(), original.as_ref()) {
        ("Var", [id, _], _) => {
            names.insert(id.op.clone(), format!("{}", original));
        }
        // Both builtin operators and uninterpreted functions encode as
        // @-prefixed constructors over an Args list; the original term is an
        // Op for the former and an App for the latter.
        (operator, [arguments], Original::Op(_, args) | Original::App(_, args))
            if operator.starts_with('@') =>
        {
            if let Some(elements) = list_elements(arguments) {
                if elements.len() == args.len() {
                    for (element, arg) in elements.iter().zip(args) {
                        collect_variable_names(element, arg, names);
                    }
                }
            }
        }
        ("App", [_, _], Original::App(function, args)) => {
            let mut chain = Vec::new();
            let mut current = inner;
            while let ("App", [next, argument]) = (current.op.as_str(), current.children.as_slice())
            {
                chain.push(argument);
                current = next;
            }
            chain.reverse();
            collect_variable_names(current, function, names);
            if chain.len() == args.len() {
                for (element, arg) in chain.iter().zip(args) {
                    collect_variable_names(element, arg, names);
                }
            }
        }
        _ => {}
    }
}

/// Elaborates a certificate into Alethe proof steps.  Per-kind policy:
/// RARE rules, evaluation, and ACI normalization become cvc5-style
/// `TRUST_THEORY_REWRITE` holes carrying the rewrite's string name;
/// distinct elimination decomposes into Alethe's native, fully checked
/// `distinct_elim` rule; `refl`/`symm`/`trans`/`cong` glue the chain.
/// Congruence steps over the encoding spine (`Mk`, application, `Args`
/// cells) collapse into a single decoded `cong` step.
struct AletheElaborator {
    prefix: String,
    steps: Vec<String>,
    names: HashMap<String, String>,
    /// Generated-rule name -> (RARE rule name, argument order), for emitting
    /// checkable `rare_rewrite` steps instead of trusted holes.
    rare: HashMap<String, (String, Vec<String>)>,
}

impl AletheElaborator {
    fn elaborate(certificate: &Certificate, prefix: &str) -> Option<Vec<String>> {
        Self::elaborate_with_names(certificate, prefix, HashMap::new())
    }

    fn elaborate_with_names(
        certificate: &Certificate,
        prefix: &str,
        names: HashMap<String, String>,
    ) -> Option<Vec<String>> {
        Self::elaborate_full(certificate, prefix, names, HashMap::new())
    }

    fn elaborate_full(
        certificate: &Certificate,
        prefix: &str,
        names: HashMap<String, String>,
        rare: HashMap<String, (String, Vec<String>)>,
    ) -> Option<Vec<String>> {
        let mut elaborator =
            Self { prefix: prefix.to_owned(), steps: Vec::new(), names, rare };
        elaborator.step_for(certificate)?;
        Some(elaborator.steps)
    }

    fn emit(&mut self, lhs: &Term, rhs: &Term, rule: &str, tail: &str) -> Option<String> {
        let id = format!("{}.{}", self.prefix, self.steps.len() + 1);
        self.steps.push(format!(
            "(step {id} (cl (= {} {})) :rule {rule}{tail})",
            decode_any(lhs, &self.names)?,
            decode_any(rhs, &self.names)?,
        ));
        Some(id)
    }

    fn trusted(&mut self, lhs: &Term, rhs: &Term, name: &str) -> Option<String> {
        let tail = format!(" :args (\"TRUST_THEORY_REWRITE\" \"{name}\")");
        self.emit(lhs, rhs, "hole", &tail)
    }

    /// The step id proving `(= lhs rhs)` for this certificate node.
    fn step_for(&mut self, certificate: &Certificate) -> Option<String> {
        match certificate {
            Certificate::Refl { term } => self.emit(term, term, "refl", ""),
            Certificate::Rule { name, lhs, rhs, substitution } => {
                // A rule that maps back to the RARE database becomes a real,
                // checkable rare_rewrite step carrying the rule's name and
                // its argument instantiation; engine-generated rewrites keep
                // the trusted form.
                let mapped = self.rare.get(name).cloned();
                if let Some((rare_name, arguments)) = mapped {
                    let decoded: Option<Vec<String>> = arguments
                        .iter()
                        .map(|parameter| {
                            substitution
                                .get(parameter)
                                .and_then(|term| decode_any(term, &self.names))
                        })
                        .collect();
                    if let Some(decoded) = decoded {
                        let tail = format!(
                            " :args (\"{rare_name}\" {})",
                            decoded.join(" "),
                        );
                        return self.emit(lhs, rhs, "rare_rewrite", &tail);
                    }
                }
                self.trusted(lhs, rhs, name)
            }
            Certificate::Computational { kind, lhs, rhs } => match kind {
                // A literal renormalization (`Real` to `RatConst`) decodes to
                // the same text on both sides: nothing to trust.
                _ if decode_any(lhs, &self.names) == decode_any(rhs, &self.names) => {
                    self.emit(lhs, rhs, "refl", "")
                }
                Computation::DistinctElim => self.emit(lhs, rhs, "distinct_elim", ""),
                Computation::Evaluation => self.trusted(lhs, rhs, "evaluate"),
                Computation::AciNorm => self.trusted(lhs, rhs, "aci_norm"),
                // cvc5's Alethe names for ARITH_POLY_NORM and ARITH_POLY_NORM_REL.
                Computation::ArithPolyNorm => self.trusted(lhs, rhs, "poly_simp"),
                Computation::ArithPolyNormRel => self.trusted(lhs, rhs, "poly_simp_rel"),
            },
            Certificate::Symm { lhs, rhs, proof } => {
                let premise = self.step_for(proof)?;
                let tail = format!(" :premises ({premise})");
                self.emit(lhs, rhs, "symm", &tail)
            }
            Certificate::Trans { lhs, rhs, first, second, .. } => {
                // The solver's two-element seam (`distinct` to singleton
                // `and` to the negation) is exactly Alethe's two-element
                // `distinct_elim` shape, so the pair collapses into the
                // native rule.
                if let (
                    Certificate::Computational { kind: Computation::DistinctElim, lhs: d, .. },
                    Certificate::Computational { kind: Computation::AciNorm, .. },
                ) = (first.as_ref(), second.as_ref())
                {
                    if matches!(encoded_application(d), Some(("@distinct", elements)) if elements.len() == 2)
                    {
                        return self.emit(lhs, rhs, "distinct_elim", "");
                    }
                }
                // A leg whose sides decode identically (a literal
                // renormalization) adds nothing: the other leg already
                // states the whole equality.
                let identity = |certificate: &Certificate, names: &HashMap<String, String>| {
                    decode_any(certificate.lhs(), names) == decode_any(certificate.rhs(), names)
                };
                if identity(first, &self.names) {
                    return self.step_for(second);
                }
                if identity(second, &self.names) {
                    return self.step_for(first);
                }
                let first = self.step_for(first)?;
                let second = self.step_for(second)?;
                let tail = format!(" :premises ({first} {second})");
                self.emit(lhs, rhs, "trans", &tail)
            }
            Certificate::Congruence { lhs, rhs, child, .. } => {
                // The `Mk` wrapper is invisible in Alethe: a congruence
                // through it alone states exactly the child's equality.
                if lhs.op == "Mk" && !matches!(child.as_ref(), Certificate::Congruence { .. }) {
                    return self.step_for(child);
                }
                let mut arguments = Vec::new();
                spine_arguments(certificate, &mut arguments)?;
                let premises = arguments
                    .iter()
                    .map(|argument| self.step_for(argument))
                    .collect::<Option<Vec<_>>>()?;
                let tail = format!(" :premises ({})", premises.join(" "));
                self.emit(lhs, rhs, "cong", &tail)
            }
        }
    }
}

/// Descend an encoded congruence spine (`Mk` wrapper, application node,
/// `Args` cells, and the transitivity chains congruence builds when several
/// arguments differ), collecting the certificates of the differing
/// arguments in argument order — one `cong` premise each.
fn spine_arguments<'c>(certificate: &'c Certificate, out: &mut Vec<&'c Certificate>) -> Option<()> {
    match certificate {
        Certificate::Refl { .. } => Some(()),
        Certificate::Congruence { lhs, child_index, child, .. } => {
            match (lhs.op.as_str(), child_index) {
                // Wrapper and application layers pass straight through.
                ("Mk", 0) => spine_arguments(child, out),
                (operator, 0) if operator.starts_with('@') => spine_arguments(child, out),
                // An Args cell: index 0 is a differing element itself, index 1
                // continues along the list spine.
                ("Args", 0) => {
                    out.push(child);
                    Some(())
                }
                ("Args", 1) => spine_arguments(child, out),
                _ => None,
            }
        }
        Certificate::Trans { first, second, .. } => {
            spine_arguments(first, out)?;
            spine_arguments(second, out)
        }
        _ => None,
    }
}

/// Operators belonging to the egglog solvers' internal machinery
/// (computation tables, demand relations, ACI set forms) rather than to the
/// proof term language.  They appear in the serialized snapshot co-classed
/// with real terms and must be ignored by term extraction.
const INTERNAL_OPS: [&str; 12] = [
    "to_formula",
    "to_formula_rel",
    "Avaliable",
    "Assoc",
    "set-of",
    "set-insert",
    "set-empty",
    // Arithmetic solver keys and the functions producing them.
    "ArithEqKey",
    "GeqKey",
    "GtKey",
    "arithRelBoolKeyOf",
    "strictOrderBoolKeyN",
];

/// Enodes the cross-class arithmetic strategy grounds as candidates.
const ARITH_CANDIDATE_OPS: [&str; 12] = [
    "@+", "@-", "@*", "@/", "@/_total", "@to_real", "@=", "@<", "@<=", "@>", "@>=", "@not",
];

#[derive(Clone, Copy, Debug)]
struct SearchStrategy {
    max_depth: usize,
    max_states: usize,
}

impl Default for SearchStrategy {
    fn default() -> Self {
        Self { max_depth: 8, max_states: 256 }
    }
}

fn chain(source: Term, steps: Vec<Certificate>) -> Certificate {
    if steps.is_empty() {
        return Certificate::Refl { term: source };
    }

    let mut steps = steps.into_iter();
    let mut certificate = steps.next().unwrap();
    for next in steps {
        certificate = Certificate::Trans {
            lhs: certificate.lhs().clone(),
            middle: certificate.rhs().clone(),
            rhs: next.rhs().clone(),
            first: Box::new(certificate),
            second: Box::new(next),
        };
    }
    certificate
}

fn reverse(certificate: Certificate) -> Certificate {
    Certificate::Symm {
        lhs: certificate.rhs().clone(),
        rhs: certificate.lhs().clone(),
        proof: Box::new(certificate),
    }
}

/// Follow parent pointers from `vertex` up to a search root, collecting
/// `(parent, child, edge)` triples in root-ward order.
fn walk_edges(
    parents: &HashMap<Term, (Term, CandidateEdge)>,
    mut vertex: Term,
) -> Vec<(Term, Term, CandidateEdge)> {
    let mut edges = Vec::new();
    while let Some((parent, edge)) = parents.get(&vertex) {
        edges.push((parent.clone(), vertex.clone(), edge.clone()));
        vertex = parent.clone();
    }
    edges
}

/// Root signature of an enode: interned operator plus child e-classes.  Two
/// terms of one e-class are congruence-compatible exactly when their root
/// signatures agree, so signatures determine which rule matches can touch a
/// vertex — before any match is grounded into terms.
type Signature = (u32, Vec<u32>);

#[derive(Clone, Copy, Debug)]
enum InstanceSide {
    Lhs,
    Rhs,
}

/// One relational match of a rule, discovered from a visited signature:
/// variable-to-class bindings plus which side carried the signature.  No
/// representative has been extracted and no term built.
struct SignatureMatch {
    rule_index: usize,
    substitution: ClassSubstitution,
    anchored: InstanceSide,
}

/// One grounded rule instance: `lhs = rhs` under `substitution`, with both
/// sides in the same e-class.  Kept as plain data; a `Certificate` is only
/// built once a search actually traverses the corresponding edge.
#[derive(Clone, Debug)]
struct RuleInstance {
    rule: &'static str,
    lhs: Term,
    rhs: Term,
    substitution: Substitution,
}

impl RuleInstance {
    fn certificate(&self) -> Certificate {
        Certificate::Rule {
            name: self.rule.to_owned(),
            lhs: self.lhs.clone(),
            rhs: self.rhs.clone(),
            substitution: self.substitution.clone(),
        }
    }
}

/// An unjustified equality candidate between two terms of the class,
/// trusted from the e-graph during the search.  Justification into a
/// `Certificate` happens only for edges on the chosen path.
#[derive(Clone, Debug)]
enum CandidateEdge {
    /// A grounded rule instance; `reversed` when traversed rhs-to-lhs.
    Rule {
        instance: Rc<RuleInstance>,
        reversed: bool,
    },
    /// Endpoints share a root signature, so the e-graph holds their children
    /// pairwise equal; the child equalities still need rule-level proofs.
    Congruence,
    /// The neighbour is derived from the vertex by checker-side
    /// recomputation of a computational solver; justification is by replay.
    Computational { kind: Computation },
}

/// Per-obligation search state over the candidate c-graph.  Vertices and
/// edges are discovered lazily: expanding a vertex looks up, by root
/// signature, the class-level matches that can touch it, and only those are
/// grounded into terms.
struct CandidateGraph {
    eclass: u32,
    source: Term,
    target: Term,
    /// Ground terms discovered so far, counted against `max_states`.
    discovered: HashSet<Term>,
    over_budget: bool,
    /// Expanded vertex -> its out-edges `(neighbour, candidate)`.
    adjacency: HashMap<Term, Vec<(Term, CandidateEdge)>>,
    /// Candidate edges (both orientations) that failed to justify on an
    /// earlier met path of this obligation.
    banned: HashSet<(Term, Term)>,
}

/// One half of the bidirectional search: a tree of visited terms rooted at
/// the proof's source or at its target.
struct SearchTree {
    frontier: Vec<Term>,
    depths: HashMap<Term, usize>,
    parents: HashMap<Term, (Term, CandidateEdge)>,
}

impl SearchTree {
    fn rooted_at(root: &Term) -> Self {
        Self {
            frontier: vec![root.clone()],
            depths: HashMap::from([(root.clone(), 0)]),
            parents: HashMap::new(),
        }
    }
}

#[derive(Clone, Debug)]
struct ReconstructionResult {
    certificate: Option<Certificate>,
    stats: ReconstructionStats,
}

struct Reconstructor<'a> {
    snapshot: &'a EGraphSnapshot,
    rules: &'a [Rewrite],
    strategy: SearchStrategy,
    /// Sort facts for the arithmetic strategy and checkers.
    sorts: &'a ArithSorts,
    representatives: HashMap<u32, Term>,
    terms_by_class: HashMap<u32, Vec<Term>>,
    term_classes: HashMap<Term, u32>,
    /// Signature-anchored match discovery, memoized per (class, signature).
    matches_by_signature: HashMap<(u32, Signature), Rc<Vec<SignatureMatch>>>,
    /// Grounded matches, memoized by their class-level bindings; `None`
    /// records a match that failed to ground.
    grounded_matches: HashMap<(u32, usize, ClassSubstitution), Option<Rc<RuleInstance>>>,
    memo: HashMap<(Term, Term), Option<Certificate>>,
    in_progress: HashSet<(Term, Term)>,
    prune_events: usize,
    stats: ReconstructionStats,
}

impl Reconstructor<'_> {
    fn class_of(&mut self, term: &Term) -> Option<u32> {
        if let Some(&eclass) = self.term_classes.get(term) {
            return Some(eclass);
        }
        let eclass = self.snapshot.class_of(term, &mut self.term_classes)?;
        // Goal-directed representatives: every classified term becomes a
        // candidate representative of its class, so lazy extraction prefers
        // goal and instance subterms over unrelated enode expansions.
        self.terms_by_class
            .entry(eclass)
            .or_default()
            .push(term.clone());
        Some(eclass)
    }

    /// Classify every goal subterm up front so lazy representative extraction
    /// can prefer goal-shaped terms.
    fn seed_goal_terms(&mut self, term: &Term) {
        if let Some(eclass) = self.class_of(term) {
            let terms = self.terms_by_class.entry(eclass).or_default();
            if !terms.contains(term) {
                terms.push(term.clone());
            }
        }
        for child in &term.children {
            self.seed_goal_terms(child);
        }
    }

    fn representative(&mut self, eclass: u32) -> Option<Term> {
        if let Some(term) = self.representatives.get(&eclass) {
            return Some(term.clone());
        }
        if let Some(terms) = self.terms_by_class.get(&eclass) {
            if let Some(best) = terms.iter().min_by_key(|term| (term.size(), *term)) {
                let best = best.clone();
                self.representatives.insert(eclass, best.clone());
                return Some(best);
            }
        }
        self.extract_representative(eclass, &mut HashSet::new())
    }

    fn extract_representative(&mut self, eclass: u32, visiting: &mut HashSet<u32>) -> Option<Term> {
        if let Some(term) = self.representatives.get(&eclass) {
            return Some(term.clone());
        }
        if !visiting.insert(eclass) {
            return None;
        }

        let indices = self.snapshot.class_nodes.get(eclass as usize)?.clone();
        let mut best: Option<Term> = None;
        for index in indices {
            let node = &self.snapshot.nodes[index as usize];
            let op = self.snapshot.ops.names[node.op as usize].clone();
            // Solver-internal rows share classes with real terms — a
            // `to_formula` row is serialized into the class of its output
            // list — and are often the smallest enode there.  They are not
            // part of the proof term language, so they must never become a
            // representative.
            if INTERNAL_OPS.contains(&op.as_str()) {
                continue;
            }
            let child_classes = node.child_classes.clone();
            let Some(children) = child_classes
                .iter()
                .map(|&class| self.extract_representative(class, visiting))
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            let candidate = Term::new(&op, children);
            if best.as_ref().map_or(true, |current| {
                (candidate.size(), &candidate) < (current.size(), current)
            }) {
                best = Some(candidate);
            }
        }
        visiting.remove(&eclass);
        if let Some(term) = &best {
            self.representatives.insert(eclass, term.clone());
        }
        best
    }

    /// Recover the rule matches able to touch a vertex carrying `signature`,
    /// by anchoring the E-match at that signature instead of scanning the
    /// class.  The anchored side is matched against the signature's child
    /// classes; the other side is then matched in the class under the shared
    /// bindings, completing the relational query:
    ///
    ///   Q_rule(sig, subst) :- match_at(side, sig, subst),
    ///                          match(other, root, subst).
    ///
    /// Memoized per (class, signature), so discovery cost follows the
    /// vertices the search visits — not the number of rules times the number
    /// of e-nodes in the class.
    fn matches_at_signature(
        &mut self,
        eclass: u32,
        signature: &Signature,
    ) -> Rc<Vec<SignatureMatch>> {
        let key = (eclass, signature.clone());
        if let Some(matches) = self.matches_by_signature.get(&key) {
            return matches.clone();
        }

        let mut matches = Vec::new();
        for (rule_index, rule) in self.rules.iter().enumerate() {
            let sides = [
                (InstanceSide::Lhs, &rule.lhs, &rule.rhs),
                (InstanceSide::Rhs, &rule.rhs, &rule.lhs),
            ];
            for (anchored, side, other) in sides {
                let side_matches = self.side_matches_at_signature(side, signature, eclass);
                self.stats.lhs_matches += side_matches.len();
                for side_substitution in side_matches {
                    // The other side must be represented in the same class
                    // under the shared bindings for the match to be an
                    // equality usable inside it.  With every variable bound
                    // by the anchor — the common case — that is a pure
                    // membership check through the signature relation: no
                    // row scan, no enumeration.
                    let substitution = if has_unbound_variables(other, &side_substitution) {
                        // Rare: enumerate, keeping only the first witness —
                        // the goal is a certificate fast, not every
                        // reconstructable path.
                        self.snapshot
                            .ematch_in_class(other, eclass, &side_substitution, &mut self.stats)
                            .into_iter()
                            .next()
                    } else {
                        (self.pattern_class(other, &side_substitution) == Some(eclass))
                            .then_some(side_substitution)
                    };
                    if let Some(substitution) = substitution {
                        matches.push(SignatureMatch { rule_index, substitution, anchored });
                    }
                }
            }
        }
        let matches = Rc::new(matches);
        self.matches_by_signature.insert(key, matches.clone());
        matches
    }

    /// Matches of one side pattern whose grounded root will carry
    /// `signature`.  An applied pattern anchors on the signature's child
    /// classes directly; a bare-variable side grounds to the class
    /// representative, so it anchors exactly when the representative carries
    /// the signature — one extraction for the class being searched.
    fn side_matches_at_signature(
        &mut self,
        pattern: &Pattern,
        signature: &Signature,
        eclass: u32,
    ) -> Vec<ClassSubstitution> {
        match pattern {
            Pattern::Var(variable) => {
                if self.representative_signature(eclass).as_ref() == Some(signature) {
                    vec![ClassSubstitution::from([(*variable, eclass)])]
                } else {
                    Vec::new()
                }
            }
            Pattern::App(..) => self.snapshot.ematch_at_signature(
                pattern,
                signature,
                &ClassSubstitution::new(),
                &mut self.stats,
            ),
        }
    }

    fn representative_signature(&mut self, eclass: u32) -> Option<Signature> {
        let representative = self.representative(eclass)?;
        self.term_signature(&representative)
    }

    /// E-class a fully substituted pattern grounds into, resolved bottom-up
    /// through the signature relation without building any term.
    fn pattern_class(&self, pattern: &Pattern, substitution: &ClassSubstitution) -> Option<u32> {
        match pattern {
            Pattern::Var(variable) => substitution.get(variable).copied(),
            Pattern::App(op, children) => {
                let &op = self.snapshot.ops.ids.get(*op)?;
                let child_classes = children
                    .iter()
                    .map(|child| self.pattern_class(child, substitution))
                    .collect::<Option<Vec<_>>>()?;
                self.snapshot.signature_class.get(&(op, child_classes)).copied()
            }
        }
    }

    fn term_signature(&mut self, term: &Term) -> Option<Signature> {
        let &op = self.snapshot.ops.ids.get(term.op.as_str())?;
        let child_classes = term
            .children
            .iter()
            .map(|child| self.class_of(child))
            .collect::<Option<Vec<_>>>()?;
        Some((op, child_classes))
    }

    /// Ground one discovered match into terms, extracting a representative
    /// for every bound class — paid once per match, and only for matches
    /// discovered at a visited signature.
    fn grounded_match(
        &mut self,
        eclass: u32,
        class_match: &SignatureMatch,
    ) -> Option<Rc<RuleInstance>> {
        let key = (eclass, class_match.rule_index, class_match.substitution.clone());
        if let Some(instance) = self.grounded_matches.get(&key) {
            return instance.clone();
        }
        let rule = &self.rules[class_match.rule_index];
        let instance = self.ground(rule, &class_match.substitution, eclass).map(Rc::new);
        if instance.is_some() {
            self.stats.rule_instances += 1;
        }
        self.grounded_matches.insert(key, instance.clone());
        instance
    }

    fn ground(
        &mut self,
        rule: &Rewrite,
        class_substitution: &ClassSubstitution,
        eclass: u32,
    ) -> Option<RuleInstance> {
        let mut substitution = Substitution::new();
        for (variable, &class) in class_substitution {
            substitution.insert((*variable).to_owned(), self.representative(class)?);
        }
        let lhs = instantiate(&rule.lhs, &substitution)?;
        let rhs = instantiate(&rule.rhs, &substitution)?;
        (lhs != rhs
            && self.snapshot.class_of_term(&lhs) == Some(eclass)
            && self.snapshot.class_of_term(&rhs) == Some(eclass))
        .then(|| RuleInstance { rule: rule.name, lhs, rhs, substitution })
    }

    fn congruence_compatible(&mut self, lhs: &Term, rhs: &Term) -> bool {
        lhs.op == rhs.op
            && lhs.children.len() == rhs.children.len()
            && lhs.children.iter().zip(&rhs.children).all(|(lhs, rhs)| {
                matches!((self.class_of(lhs), self.class_of(rhs)), (Some(lhs), Some(rhs)) if lhs == rhs)
            })
    }

    fn congruence_certificate(&mut self, lhs: &Term, rhs: &Term) -> Option<Certificate> {
        if !self.congruence_compatible(lhs, rhs) || lhs == rhs {
            return None;
        }

        let mut current = lhs.clone();
        let mut steps = Vec::new();
        for child_index in 0..current.children.len() {
            if current.children[child_index] == rhs.children[child_index] {
                continue;
            }
            let child = self.prove(&current.children[child_index], &rhs.children[child_index])?;
            let mut children = current.children.clone();
            children[child_index] = rhs.children[child_index].clone();
            let next = Term::new(&current.op, children);
            steps.push(Certificate::Congruence {
                lhs: current.clone(),
                rhs: next.clone(),
                child_index,
                child: Box::new(child),
            });
            current = next;
        }
        self.stats.congruence_edges += 1;
        Some(chain(lhs.clone(), steps))
    }

    fn prove(&mut self, source: &Term, target: &Term) -> Option<Certificate> {
        self.stats.recursive_obligations += 1;
        if source == target {
            return Some(Certificate::Refl { term: source.clone() });
        }
        if let Some(entry) = self.memo.get(&(source.clone(), target.clone())) {
            return entry.clone();
        }
        if let Some(entry) = self.memo.get(&(target.clone(), source.clone())) {
            return entry.clone().map(reverse);
        }
        let source_class = self.class_of(source)?;
        if self.class_of(target).as_ref() != Some(&source_class) {
            return None;
        }

        let key = (source.clone(), target.clone());
        let reverse_key = (target.clone(), source.clone());
        if self.in_progress.contains(&key) || self.in_progress.contains(&reverse_key) {
            self.prune_events += 1;
            return None;
        }
        // A failure is only sound to cache if the in-progress guard never fired
        // while evaluating it: a prune makes the result depend on the current
        // proof stack, and the obligation may become provable once the stack
        // unwinds. Successes are always cacheable, since a found certificate is
        // independently checkable no matter how it was discovered.
        let prune_mark = self.prune_events;
        self.in_progress.insert(key.clone());
        let certificate = self.prove_in_class(source, target, source_class);
        self.in_progress.remove(&key);
        if certificate.is_some() || self.prune_events == prune_mark {
            self.memo.insert(key, certificate.clone());
        }
        certificate
    }

    /// Candidate terms of a goal's class for the cross-class arithmetic
    /// strategy: the goal itself plus every arithmetic or relational enode
    /// of the class, grounded through representative arguments — so a RARE
    /// rewrite the e-graph applied first (a stripped double negation, say)
    /// is bridged by an in-class proof to the term the solver normalized.
    fn arith_candidates(&mut self, goal: &Term, eclass: u32) -> Vec<Term> {
        const LIMIT: usize = 64;
        let snapshot = self.snapshot;
        let mut candidates = vec![goal.clone()];
        let wrapper = snapshot.ops.ids.get("Mk").copied();
        for &index in snapshot.class_nodes.get(eclass as usize).into_iter().flatten() {
            let node = &snapshot.nodes[index as usize];
            let ([inner_class], true) = (node.child_classes.as_slice(), Some(node.op) == wrapper)
            else {
                continue;
            };
            for &inner in snapshot.class_nodes.get(*inner_class as usize).into_iter().flatten() {
                let inner = &snapshot.nodes[inner as usize];
                let operator = snapshot.ops.names[inner.op as usize].as_str();
                let ([arguments_class], true) =
                    (inner.child_classes.as_slice(), ARITH_CANDIDATE_OPS.contains(&operator))
                else {
                    continue;
                };
                let Some(arguments) =
                    self.extract_representative(*arguments_class, &mut HashSet::new())
                else {
                    continue;
                };
                let candidate = Term::new("Mk", vec![Term::new(operator, vec![arguments])]);
                if !candidates.contains(&candidate) {
                    candidates.push(candidate);
                }
                if candidates.len() >= LIMIT {
                    return candidates;
                }
            }
        }
        candidates
    }

    /// Arithmetic strategy for goals whose sides the e-graph never merged:
    /// the solver proved them by equal polynomial normal forms or relation
    /// keys.  Find a candidate pair the checker-side recomputation agrees
    /// on, and bridge each side to its candidate with an in-class proof.
    fn prove_across_classes(&mut self, source: &Term, target: &Term) -> Option<Certificate> {
        let (Some(source_class), Some(target_class)) =
            (self.class_of(source), self.class_of(target))
        else {
            return None;
        };
        let left = self.arith_candidates(source, source_class);
        let right = self.arith_candidates(target, target_class);
        for lhs in &left {
            for rhs in &right {
                let Some(kind) = arith_kind(lhs, rhs, self.sorts) else {
                    continue;
                };
                let (Some(before), Some(after)) = (self.prove(source, lhs), self.prove(rhs, target))
                else {
                    continue;
                };
                self.stats.computational_edges += 1;
                let step = Certificate::Computational {
                    kind,
                    lhs: lhs.clone(),
                    rhs: rhs.clone(),
                };
                let steps = [before, step, after]
                    .into_iter()
                    .filter(|certificate| !matches!(certificate, Certificate::Refl { .. }))
                    .collect();
                return Some(chain(source.clone(), steps));
            }
        }
        None
    }

    fn prove_in_class(&mut self, source: &Term, target: &Term, eclass: u32) -> Option<Certificate> {
        self.prove_by_congruence(source, target)
            .or_else(|| self.prove_by_transitivity(source, target, eclass))
            .or_else(|| self.prove_by_aci(source, target))
    }

    /// ACI strategy: `and`/`or` obligations whose sides flatten to the same
    /// literal set are one computational step — the oracle derives these
    /// through its native set machinery, which leaves no rewrite trace the
    /// declarative search could follow.
    fn prove_by_aci(&mut self, source: &Term, target: &Term) -> Option<Certificate> {
        aci_equal(source, target).then(|| {
            self.stats.computational_edges += 1;
            Certificate::Computational {
                kind: Computation::AciNorm,
                lhs: source.clone(),
                rhs: target.clone(),
            }
        })
    }

    /// Congruence strategy: identical head symbols whose children sit
    /// pairwise in the same e-classes decompose directly into per-child
    /// proofs, without consulting the rule index.
    fn prove_by_congruence(&mut self, source: &Term, target: &Term) -> Option<Certificate> {
        if source.op != target.op || source.children.len() != target.children.len() {
            return None;
        }
        self.congruence_certificate(source, target)
    }

    /// Transitivity strategy, in two phases.  First a bidirectional
    /// breadth-first search over *candidate* edges — rule instances and
    /// signature-level congruence links taken on the e-graph's word, with no
    /// proof effort spent.  Then only the edges on the met path are justified
    /// into certificates and chained.  A path edge that fails to justify
    /// fails the whole obligation: the oracle is trusted to guide the search,
    /// never the final certificate.
    fn prove_by_transitivity(
        &mut self,
        source: &Term,
        target: &Term,
        eclass: u32,
    ) -> Option<Certificate> {
        // A congruence candidate on the met path may still fail to justify:
        // its child obligation is beyond the rules.  Such an edge is banned
        // and the search rerun, a bounded number of times, so one
        // unjustifiable shortcut does not hide a path that replays.
        const MAX_REJUSTIFICATIONS: usize = 4;
        let mut banned = HashSet::new();
        for attempt in 0..=MAX_REJUSTIFICATIONS {
            let discovered = HashSet::from([source.clone(), target.clone()]);
            self.stats.candidate_vertices += discovered.len();
            let mut graph = CandidateGraph {
                eclass,
                source: source.clone(),
                target: target.clone(),
                discovered,
                over_budget: false,
                adjacency: HashMap::new(),
                banned: banned.clone(),
            };
            let mut forward = SearchTree::rooted_at(source);
            let mut backward = SearchTree::rooted_at(target);

            // Expand the smaller non-empty frontier one level at a time until
            // the two trees meet on a shared vertex within the depth budget.
            // A tree whose frontier has died out (its last vertices were dead
            // ends) can still be met by the other tree's expansion.
            let mut meet = None;
            while !forward.frontier.is_empty() || !backward.frontier.is_empty() {
                let expand_forward = !forward.frontier.is_empty()
                    && (backward.frontier.is_empty()
                        || forward.frontier.len() <= backward.frontier.len());
                meet = if expand_forward {
                    self.expand_level(&mut graph, &mut forward, &backward)
                } else {
                    self.expand_level(&mut graph, &mut backward, &forward)
                };
                if meet.is_some() || graph.over_budget {
                    break;
                }
            }
            let meet = meet?;
            match self.justify_path(source, &forward, &backward, meet) {
                Ok(certificate) => return Some(certificate),
                Err((parent, child)) => {
                    if attempt == MAX_REJUSTIFICATIONS {
                        return None;
                    }
                    self.stats.rejustifications += 1;
                    banned.insert((parent.clone(), child.clone()));
                    banned.insert((child, parent));
                }
            }
        }
        None
    }

    /// Justify every candidate edge on the met path and chain the results.
    /// Tree edges prove parent = child; the forward half is emitted in that
    /// direction, the backward half flipped, so the chain runs source to
    /// target.  The first edge that fails to justify is returned instead.
    fn justify_path(
        &mut self,
        source: &Term,
        forward: &SearchTree,
        backward: &SearchTree,
        meet: Term,
    ) -> Result<Certificate, (Term, Term)> {
        let mut steps = Vec::new();
        let mut forward_edges = walk_edges(&forward.parents, meet.clone());
        forward_edges.reverse();
        for (parent, child, edge) in &forward_edges {
            let step = self.justify(parent, child, edge, false);
            steps.push(step.ok_or_else(|| (parent.clone(), child.clone()))?);
        }
        for (parent, child, edge) in &walk_edges(&backward.parents, meet) {
            let step = self.justify(parent, child, edge, true);
            steps.push(step.ok_or_else(|| (parent.clone(), child.clone()))?);
        }
        Ok(chain(source.clone(), steps))
    }

    /// Turn one candidate edge into a certificate for parent = child, or
    /// child = parent when `flip` is set.  Rule candidates always succeed;
    /// congruence candidates recursively prove the differing children and
    /// may fail — the e-graph knew an equality the rules cannot replay, or a
    /// child search ran out of budget.
    fn justify(
        &mut self,
        parent: &Term,
        child: &Term,
        edge: &CandidateEdge,
        flip: bool,
    ) -> Option<Certificate> {
        match edge {
            CandidateEdge::Rule { instance, reversed } => {
                let certificate = instance.certificate();
                Some(if *reversed != flip {
                    reverse(certificate)
                } else {
                    certificate
                })
            }
            CandidateEdge::Congruence => {
                if flip {
                    self.congruence_certificate(child, parent)
                } else {
                    self.congruence_certificate(parent, child)
                }
            }
            CandidateEdge::Computational { kind } => {
                let certificate = Certificate::Computational {
                    kind: *kind,
                    lhs: parent.clone(),
                    rhs: child.clone(),
                };
                Some(if flip { reverse(certificate) } else { certificate })
            }
        }
    }

    /// Expand one breadth-first level of `near`, recording parent edges, and
    /// return the first vertex that `far` has also reached within the
    /// combined depth budget.
    fn expand_level(
        &mut self,
        graph: &mut CandidateGraph,
        near: &mut SearchTree,
        far: &SearchTree,
    ) -> Option<Term> {
        let frontier = std::mem::take(&mut near.frontier);
        for vertex in frontier {
            let depth = near.depths[&vertex];
            if depth >= self.strategy.max_depth {
                continue;
            }
            for (neighbour, edge) in self.neighbors(graph, &vertex) {
                if near.depths.contains_key(neighbour) {
                    continue;
                }
                near.parents
                    .insert(neighbour.clone(), (vertex.clone(), edge.clone()));
                near.depths.insert(neighbour.clone(), depth + 1);
                if let Some(&far_depth) = far.depths.get(neighbour) {
                    if depth + 1 + far_depth <= self.strategy.max_depth {
                        return Some(neighbour.clone());
                    }
                }
                near.frontier.push(neighbour.clone());
            }
            if graph.over_budget {
                return None;
            }
        }
        None
    }

    /// The out-edges of a vertex, generated on its first expansion and
    /// memoized in the graph.  Terms discovered by grounding count against
    /// the `max_states` budget; crossing it marks the graph over budget.
    fn neighbors<'g>(
        &mut self,
        graph: &'g mut CandidateGraph,
        vertex: &Term,
    ) -> &'g [(Term, CandidateEdge)] {
        if !graph.adjacency.contains_key(vertex) {
            let edges = self.expand_vertex(graph, vertex);
            if graph.discovered.len() > self.strategy.max_states {
                graph.over_budget = true;
            }
            graph.adjacency.insert(vertex.clone(), edges);
        }
        &graph.adjacency[vertex]
    }

    /// Discover the candidate edges out of `vertex`: ground exactly the
    /// class-level matches with a side whose signature equals the vertex's —
    /// a rule edge when the grounded side is the vertex itself, a congruence
    /// candidate towards it otherwise — plus congruence candidates to the
    /// goal terms.  No proof work happens here: candidates are taken on the
    /// e-graph's word and only justified if they land on the chosen path.
    fn expand_vertex(
        &mut self,
        graph: &mut CandidateGraph,
        vertex: &Term,
    ) -> Vec<(Term, CandidateEdge)> {
        let mut edges = Vec::new();
        if let Some(signature) = self.term_signature(vertex) {
            let matches = self.matches_at_signature(graph.eclass, &signature);
            for class_match in matches.iter() {
                let Some(instance) = self.grounded_match(graph.eclass, class_match) else {
                    continue;
                };
                for term in [&instance.lhs, &instance.rhs] {
                    if graph.discovered.insert((*term).clone()) {
                        self.stats.candidate_vertices += 1;
                    }
                }
                let (matched, other, reversed) = match class_match.anchored {
                    InstanceSide::Lhs => (&instance.lhs, &instance.rhs, false),
                    InstanceSide::Rhs => (&instance.rhs, &instance.lhs, true),
                };
                if matched == vertex {
                    let rule = CandidateEdge::Rule { instance: instance.clone(), reversed };
                    edges.push((other.clone(), rule));
                } else {
                    // Same signature as the vertex, so the e-graph holds
                    // them congruent.
                    edges.push((matched.clone(), CandidateEdge::Congruence));
                }
            }
        }
        // Computational edges: any vertex a solver's function applies to
        // sprouts an edge to the recomputed result — vertex-local, so the
        // step is found even in the interior of a chain of rewrites.  The
        // e-graph acts only as a filter: the edge exists when the oracle
        // agrees the result is in the class.
        for kind in COMPUTATIONS {
            let Some(result) = kind.apply(vertex) else {
                continue;
            };
            if self.class_of(&result) != Some(graph.eclass) {
                continue;
            }
            if graph.discovered.insert(result.clone()) {
                self.stats.candidate_vertices += 1;
            }
            self.stats.computational_edges += 1;
            edges.push((result, CandidateEdge::Computational { kind }));
        }
        for goal in [&graph.source, &graph.target] {
            if *goal == *vertex {
                continue;
            }
            if self.congruence_compatible(vertex, goal) {
                edges.push((goal.clone(), CandidateEdge::Congruence));
            } else if aci_equal(vertex, goal) {
                self.stats.computational_edges += 1;
                edges.push((
                    goal.clone(),
                    CandidateEdge::Computational { kind: Computation::AciNorm },
                ));
            }
        }
        edges.retain(|(neighbour, _)| !graph.banned.contains(&(vertex.clone(), neighbour.clone())));
        edges
    }
}

fn reconstruct_detailed(
    snapshot: &EGraphSnapshot,
    source: &Term,
    target: &Term,
    rules: &[Rewrite],
    strategy: SearchStrategy,
) -> ReconstructionResult {
    reconstruct_with_sorts(snapshot, source, target, rules, &ArithSorts::default(), strategy)
}

/// Full entry point.  Sides the e-graph merged are proved by the in-class
/// search; otherwise the goal can only have been proved arithmetically, by
/// normal forms the solver compared without ever unioning the sides.
fn reconstruct_with_sorts(
    snapshot: &EGraphSnapshot,
    source: &Term,
    target: &Term,
    rules: &[Rewrite],
    sorts: &ArithSorts,
    strategy: SearchStrategy,
) -> ReconstructionResult {
    let mut reconstructor = Reconstructor {
        snapshot,
        rules,
        strategy,
        sorts,
        representatives: snapshot.preferred_representatives([source, target]),
        terms_by_class: HashMap::new(),
        term_classes: HashMap::new(),
        matches_by_signature: HashMap::new(),
        grounded_matches: HashMap::new(),
        memo: HashMap::new(),
        in_progress: HashSet::new(),
        prune_events: 0,
        stats: ReconstructionStats::default(),
    };
    reconstructor.seed_goal_terms(source);
    reconstructor.seed_goal_terms(target);
    let certificate = if snapshot.same_class(source, target) {
        reconstructor.prove(source, target)
    } else {
        reconstructor.prove_across_classes(source, target)
    };
    // Certificates are built lazily during the search, so soundness is
    // enforced once here, on the assembled proof.
    if let Some(certificate) = &certificate {
        assert!(
            certificate.verify_in(rules, sorts),
            "a reconstructed certificate must pass the independent rule checker"
        );
    }
    ReconstructionResult {
        certificate,
        stats: reconstructor.stats,
    }
}

fn reconstruct(
    snapshot: &EGraphSnapshot,
    source: &Term,
    target: &Term,
    rules: &[Rewrite],
    strategy: SearchStrategy,
) -> Option<Certificate> {
    reconstruct_detailed(snapshot, source, target, rules, strategy).certificate
}

fn run_normal() -> (ProofEGraph, Duration) {
    let mut egraph = ProofEGraph::new(1);
    let start = Instant::now();
    egraph
        .parse_and_run_program(None, PROGRAM)
        .expect("raw RARE saturation should run");
    (egraph, start.elapsed())
}

#[test]
fn reconstructs_from_provenance_free_saturated_egraph() {
    let (egraph, _) = run_normal();
    let snapshot = EGraphSnapshot::capture(&egraph);
    let rules = rules();
    let reconstruction = reconstruct_detailed(
        &snapshot,
        &source(),
        &target(),
        &rules,
        SearchStrategy::default(),
    );
    let certificate = reconstruction
        .certificate
        .expect("known RARE rules should connect the two terms in the saturated class");

    assert!(certificate.verify(&rules));
    assert_eq!(certificate.lhs(), &source());
    assert_eq!(certificate.rhs(), &target());
    let mut names = Vec::new();
    certificate.rule_names(&mut names);
    assert_eq!(names, ["ite-then-false", "and-true-right"]);
    assert!(reconstruction.stats.lhs_matches >= 2);
    assert!(reconstruction.stats.rule_instances >= 2);
    assert!(reconstruction.stats.relation_rows_examined > 0);

    let nested = reconstruct(
        &snapshot,
        &nested_source(),
        &nested_target(),
        &rules,
        SearchStrategy::default(),
    )
    .expect("the structural traversal should reconstruct rewriting under Not");
    assert!(nested.verify(&rules));
    assert!(nested.contains_congruence());

    // The e-graph still says source and target are equal, but without the
    // second declarative rule there is no independently checkable replay.
    assert!(snapshot.same_class(&source(), &target()));
    assert!(
        reconstruct(
            &snapshot,
            &source(),
            &target(),
            &rules[..1],
            SearchStrategy::default(),
        )
        .is_none()
    );

    eprintln!(
        "post-hoc certificate reconstructed from e-graph: stats={:?}\n{certificate:#?}",
        reconstruction.stats
    );
}

#[test]
#[ignore = "diagnostic microbenchmark; run explicitly with --ignored --nocapture"]
fn compare_posthoc_reconstruction_with_egglog_proofs() {
    const SAMPLES: usize = 100;

    fn median(mut samples: Vec<Duration>) -> Duration {
        samples.sort_unstable();
        samples[samples.len() / 2]
    }

    fn run_reconstruction(egraph: &ProofEGraph, rules: &[Rewrite]) -> Duration {
        let start = Instant::now();
        let snapshot = EGraphSnapshot::capture(egraph);
        let certificate = reconstruct(
            &snapshot,
            &source(),
            &target(),
            rules,
            SearchStrategy::default(),
        )
        .expect("post-hoc reconstruction should succeed");
        assert!(certificate.verify(rules));
        start.elapsed()
    }

    fn run_egglog_proofs() -> Duration {
        let mut egraph = ProofEGraph::new_with_proofs();
        let program = format!("{PROGRAM}\n(prove (= $lhs (Not (Atom))))");
        let start = Instant::now();
        let outputs = egraph
            .parse_and_run_program(None, &program)
            .expect("egglog proof production should succeed");
        assert!(
            outputs
                .iter()
                .any(|output| matches!(output, CommandOutput::ProveExists { .. }))
        );
        start.elapsed()
    }

    let rules = rules();
    let (saturated, _) = run_normal();
    run_normal();
    run_reconstruction(&saturated, &rules);
    run_egglog_proofs();

    let normal = median((0..SAMPLES).map(|_| run_normal().1).collect());
    let reconstruction = median(
        (0..SAMPLES)
            .map(|_| run_reconstruction(&saturated, &rules))
            .collect(),
    );
    let posthoc = normal + reconstruction;
    let egglog_proofs = median((0..SAMPLES).map(|_| run_egglog_proofs()).collect());

    eprintln!(
        "raw RARE reconstruction ({SAMPLES} samples): normal={normal:?}, reconstruction={reconstruction:?}, estimated-posthoc-total={posthoc:?} ({:.2}x), egglog-proofs={egglog_proofs:?} ({:.2}x)",
        posthoc.as_secs_f64() / normal.as_secs_f64(),
        egglog_proofs.as_secs_f64() / normal.as_secs_f64(),
    );
}

fn repository_path(relative: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join(relative)
}

fn term_from_egglog_expr(expression: &EgglogExpr) -> Term {
    match expression {
        GenericExpr::Lit(_, literal) => Term::leaf(&literal.to_string()),
        GenericExpr::Var(_, variable) => Term::leaf(&variable.to_string()),
        GenericExpr::Call(_, operator, children) => Term::new(
            &operator.to_string(),
            children.iter().map(term_from_egglog_expr).collect(),
        ),
    }
}

fn generated_goals(program: &str) -> (Term, Term) {
    let commands = egglog::ast::Parser::default()
        .get_program_from_string(None, program)
        .expect("Carcara's generated egglog program should parse");
    let mut lhs = None;
    let mut rhs = None;

    for command in commands {
        let EgglogCommand::Action(EgglogAction::Let(_, name, expression)) = command else {
            continue;
        };
        match name.to_string().as_str() {
            "goal_lhs" => lhs = Some(term_from_egglog_expr(&expression)),
            "goal_rhs" => rhs = Some(term_from_egglog_expr(&expression)),
            _ => {}
        }
    }

    (
        lhs.expect("generated program should bind goal_lhs"),
        rhs.expect("generated program should bind goal_rhs"),
    )
}

fn encoded_mk(term: Pattern) -> Pattern {
    Pattern::App("Mk", vec![term])
}

fn encoded_call(operator: &'static str, arguments: Vec<Pattern>) -> Pattern {
    let arguments = arguments
        .into_iter()
        .rev()
        .fold(Pattern::App("Empty", vec![]), |tail, argument| {
            Pattern::App("Args", vec![encoded_mk(argument), tail])
        });
    Pattern::App(operator, vec![arguments])
}

fn encoded_formula(operator: &'static str, arguments: Vec<Pattern>) -> Pattern {
    encoded_mk(encoded_call(operator, arguments))
}

fn encoded_eq_symm_rule() -> Rewrite {
    use Pattern::Var;

    Rewrite {
        name: "eq-symm",
        lhs: encoded_formula("@=", vec![Var("t1"), Var("s1")]),
        rhs: encoded_formula("@=", vec![Var("s1"), Var("t1")]),
    }
}

fn encoded_bool_double_not_elim_rule() -> Rewrite {
    use Pattern::Var;

    Rewrite {
        name: "bool-double-not-elim",
        lhs: encoded_formula("@not", vec![encoded_call("@not", vec![Var("t1")])]),
        rhs: encoded_mk(Var("t1")),
    }
}

fn encoded_bool_or_false_rule() -> Rewrite {
    use Pattern::{App, Var};

    Rewrite {
        name: "bool-or-false",
        lhs: encoded_formula("@or", vec![Var("x"), App("Bool", vec![App("false", vec![])])]),
        rhs: encoded_mk(Var("x")),
    }
}

struct QfUfRun {
    egraph: ProductionEGraph,
    generated_program: String,
    lhs: Term,
    rhs: Term,
    saturation: Duration,
    conclusion: carcara::ast::Rc<carcara::ast::Term>,
    rare_rules: indexmap::IndexMap<String, carcara::ast::rare_rules::RuleDefinition>,
}

fn run_qf_uf_case(
    problem_relative: &str,
    proof_relative: &str,
    rare_relative: &str,
    root_id: &str,
    required_rule: Option<&str>,
) -> QfUfRun {
    let problem_path = repository_path(problem_relative);
    let proof_path = repository_path(proof_relative);
    let rare_path = repository_path(rare_relative);
    let parser_config = parser::Config {
        expand_lets: true,
        allow_int_real_subtyping: true,
        parse_hole_args: true,
        ..parser::Config::default()
    };
    let (_, proof, database, mut pool) = parser::parse_instance(
        BufReader::new(File::open(problem_path).expect("QF_UF problem should exist")),
        BufReader::new(File::open(proof_path).expect("QF_UF proof should exist")),
        Some(BufReader::new(
            File::open(rare_path).expect("RARE database should exist"),
        )),
        parser_config,
    )
    .expect("QF_UF instance should parse");
    if let Some(required_rule) = required_rule {
        assert!(
            database.rules.contains_key(required_rule),
            "the real RARE database should contain the rule being reconstructed"
        );
    }
    let node = ProofNode::from_commands_with_root_id(proof.commands, root_id)
        .expect("sliced proof should contain the requested root");
    let conclusion = node.clause()[0].clone();

    let start = Instant::now();
    let (result, generated_program) = run_egglog(
        &mut pool,
        (conclusion.clone(), &node),
        &database,
        RunEgglogOptions::default(),
    );
    let saturation = start.elapsed();
    let egraph = result.expect("production egglog should prove the QF_UF equality");
    let (lhs, rhs) = generated_goals(&generated_program);

    QfUfRun {
        egraph,
        generated_program,
        lhs,
        rhs,
        saturation,
        conclusion,
        rare_rules: database.rules.clone(),
    }
}

fn run_qf_uf_t37() -> QfUfRun {
    run_qf_uf_case(
        "tests/rare/sliced_proofs/Examples/QF_UF/2018-Goel-hwbench/\
         QF_UF_brp.5.prop1_ab_reg_max/QF_UF_brp.5.prop1_ab_reg_max.smt2",
        "tests/rare/sliced_proofs/Examples/QF_UF/2018-Goel-hwbench/\
         QF_UF_brp.5.prop1_ab_reg_max/\
         QF_UF_brp.5.prop1_ab_reg_max__from-t37.smt2.alethe",
        "tests/rare/big.rare",
        "t37",
        Some("eq-symm"),
    )
}

fn run_qf_uf_double_not_t3() -> QfUfRun {
    run_qf_uf_case(
        "tests/rare/sliced_proofs/Examples/QF_UF/20170829-Rodin/\
         smt249825283571301584/smt249825283571301584.smt2",
        "tests/rare/sliced_proofs/Examples/QF_UF/20170829-Rodin/\
         smt249825283571301584/smt249825283571301584__from-t3.smt2.alethe",
        "tests/rare/big.rare",
        "t3",
        Some("bool-double-not-elim"),
    )
}

/// The distinct-elimination solver from `rare::computational::distinct_elim`,
/// translated to a standalone egglog program over a three-element distinct.
const RAW_DISTINCT_PROGRAM: &str = r#"
(datatype Term
  (Const String)
  (Empty)
  (Args Term Term)
  (Mk Term))
(constructor @distinct (Term) Term)
(constructor @and (Term) Term)
(constructor @not (Term) Term)
(constructor @= (Term) Term)
(relation Avaliable (Term))
(function to_formula (Term Term Term) Term :no-merge)
(relation to_formula_rel (Term Term Term))
(ruleset list-ruleset)

; Header axioms from create_headers: Args associativity (both directions)
; and Mk injectivity.
(rewrite (Args (Args t1 t2) t3) (Args t1 (Args t2 t3)))
(rewrite (Args t1 (Args t2 t3)) (Args (Args t1 t2) t3))
(rule ((= (Mk x) (Mk y))) ((union x y)))

(rule ((to_formula_rel (Empty) k (Empty)))
      ((set (to_formula (Empty) k (Empty)) (Empty)))
      :ruleset list-ruleset)
(rule ((= res (Args r rs))
       (to_formula_rel res y (Empty)))
      ((to_formula_rel rs r rs))
      :ruleset list-ruleset)
(rule ((= xs (Args x rxs))
       (to_formula_rel res y xs))
      ((to_formula_rel res y rxs))
      :ruleset list-ruleset)
(rule ((to_formula_rel res y (Args x rxs))
       (= (to_formula res y rxs) f))
      ((set (to_formula res y (Args x rxs))
            (Args (Mk (@not (Args (Mk (@= (Args y (Args x (Empty))))) (Empty)))) f)))
      :ruleset list-ruleset)
(rule ((to_formula_rel (Args r res) y (Empty))
       (= (to_formula res r res) f))
      ((set (to_formula (Args r res) y (Empty)) f))
      :ruleset list-ruleset)
(rule ((Avaliable (Mk (@distinct (Args x xs))))
       (= (to_formula xs x xs) f))
      ((union (Mk (@and f)) (Mk (@distinct (Args x xs)))))
      :ruleset list-ruleset)
(rule ((Avaliable (Mk (@distinct (Args x xs)))))
      ((to_formula_rel xs x xs))
      :ruleset list-ruleset)

(let a (Mk (Const "a")))
(let b (Mk (Const "b")))
(let c (Mk (Const "c")))
(let goal_lhs (Mk (@distinct (Args a (Args b (Args c (Empty)))))))
(Avaliable goal_lhs)
; Complete the fold before the default ruleset (Args associativity) runs:
; interleaving them makes rule 4 match reassociated list splits and fail
; to_formula's assert-eq merge.
(run-schedule (repeat 30 (run list-ruleset)))
(run-schedule (repeat 10 (run)))
"#;

/// Extract the smallest term of `eclass` whose enodes avoid `banned_ops`,
/// for diagnostic rendering of class members.  Memoized per class: large
/// snapshots hold classes with many equivalent enodes, and unmemoized
/// extraction revisits them combinatorially.
fn extract_avoiding(
    snapshot: &EGraphSnapshot,
    eclass: u32,
    banned_ops: &[&str],
    visiting: &mut HashSet<u32>,
    memo: &mut HashMap<u32, Option<Term>>,
) -> Option<Term> {
    if let Some(cached) = memo.get(&eclass) {
        return cached.clone();
    }
    if !visiting.insert(eclass) {
        return None;
    }
    let mut best: Option<Term> = None;
    for &index in snapshot.class_nodes.get(eclass as usize)? {
        let node = &snapshot.nodes[index as usize];
        let op = &snapshot.ops.names[node.op as usize];
        if banned_ops.contains(&op.as_str()) {
            continue;
        }
        let Some(children) = node
            .child_classes
            .clone()
            .iter()
            .map(|&class| extract_avoiding(snapshot, class, banned_ops, visiting, memo))
            .collect::<Option<Vec<_>>>()
        else {
            continue;
        };
        let candidate = Term::new(op, children);
        if best
            .as_ref()
            .map_or(true, |current| candidate.size() < current.size())
        {
            best = Some(candidate);
        }
    }
    visiting.remove(&eclass);
    // Cache successes only: a found term is a genuine class member either
    // way, while a failure may be an artifact of the cycle guard and the
    // path taken to reach the class.
    if best.is_some() {
        memo.insert(eclass, best.clone());
    }
    best
}

#[test]
#[ignore = "diagnostic dump of the e-graph produced by the raw distinct-elimination solver"]
fn inspect_distinct_solver_egraph_minimal() {
    let mut egraph = ProductionEGraph::default();
    egraph
        .parse_and_run_program(None, RAW_DISTINCT_PROGRAM)
        .expect("raw distinct solver program should run");
    let snapshot = EGraphSnapshot::capture_production(&egraph);

    eprintln!(
        "egraph: {} enodes, {} classes",
        snapshot.nodes.len(),
        snapshot.class_nodes.len(),
    );
    let mut op_counts: BTreeMap<&str, usize> = BTreeMap::new();
    for node in &snapshot.nodes {
        *op_counts
            .entry(snapshot.ops.names[node.op as usize].as_str())
            .or_default() += 1;
    }
    eprintln!("operators in the serialized e-graph: {op_counts:#?}");

    let lhs = Term::new(
        "Mk",
        vec![Term::new(
            "@distinct",
            vec![["a", "b", "c"].iter().rev().fold(
                Term::leaf("Empty"),
                |tail, name| {
                    Term::new(
                        "Args",
                        vec![
                            Term::new("Mk", vec![Term::new("Const", vec![Term::leaf(&format!("\"{name}\""))])]),
                            tail,
                        ],
                    )
                },
            )],
        )],
    );
    let mut cache = HashMap::new();
    let Some(eclass) = snapshot.class_of(&lhs, &mut cache) else {
        panic!("the distinct goal term should be represented in the snapshot");
    };
    eprintln!("goal class {eclass} holds:");
    for &index in &snapshot.class_nodes[eclass as usize] {
        let node = &snapshot.nodes[index as usize];
        eprintln!(
            "  {}({})",
            snapshot.ops.names[node.op as usize],
            node.child_classes
                .iter()
                .map(|class| class.to_string())
                .collect::<Vec<_>>()
                .join(", "),
        );
    }

    let rhs = extract_avoiding(
        &snapshot,
        eclass,
        &["@distinct", "to_formula"],
        &mut HashSet::new(),
        &mut HashMap::new(),
    )
    .expect("the goal class should hold a term besides the distinct application");
    eprintln!("distinct term  = {}", lhs.to_egglog());
    eprintln!("expanded term  = {}", rhs.to_egglog());
    eprintln!("same_class     = {}", snapshot.same_class(&lhs, &rhs));

    let reconstruction = reconstruct_detailed(
        &snapshot,
        &lhs,
        &rhs,
        &[],
        SearchStrategy::default(),
    );
    eprintln!(
        "declarative reconstruction: found={}, stats={:?}",
        reconstruction.certificate.is_some(),
        reconstruction.stats,
    );

    // The and-term the goal encoding would produce: conjuncts directly as
    // the operator's argument list, not wrapped in an extra Args cell.
    let constant = |name: &str| Term::new("Mk", vec![Term::new("Const", vec![Term::leaf(&format!("\"{name}\""))])]);
    let not_equal = |x: &str, y: &str| {
        let equality = Term::new(
            "Mk",
            vec![Term::new(
                "@=",
                vec![Term::new(
                    "Args",
                    vec![constant(x), Term::new("Args", vec![constant(y), Term::leaf("Empty")])],
                )],
            )],
        );
        Term::new(
            "Mk",
            vec![Term::new(
                "@not",
                vec![Term::new("Args", vec![equality, Term::leaf("Empty")])],
            )],
        )
    };
    let conjuncts = [("a", "b"), ("a", "c"), ("b", "c")]
        .iter()
        .rev()
        .fold(Term::leaf("Empty"), |tail, (x, y)| {
            Term::new("Args", vec![not_equal(x, y), tail])
        });
    let wrapped_list = Term::new("Args", vec![conjuncts.clone(), Term::leaf("Empty")]);
    eprintln!(
        "same_class(f, (Args f (Empty))) = {:?}",
        snapshot.same_class(&conjuncts, &wrapped_list),
    );
    let goal_encoded_and = Term::new("Mk", vec![Term::new("@and", vec![conjuncts])]);
    eprintln!("goal-encoded and = {}", goal_encoded_and.to_egglog());
    eprintln!(
        "same_class(distinct, goal-encoded and) = {:?}",
        snapshot.same_class(&lhs, &goal_encoded_and),
    );
    eprintln!(
        "goal-encoded and represented in snapshot = {}",
        snapshot.class_of_term(&goal_encoded_and).is_some(),
    );
}

/// Certificates elaborate into Alethe steps: trusted `TRUST_THEORY_REWRITE`
/// holes named after the RARE rule or computational rewrite, the native
/// `distinct_elim` rule for distinct expansion (with the two-element seam
/// collapsed onto it), and `trans`/`cong` glue over decoded terms.
#[test]
fn elaborates_certificates_to_alethe_steps() {
    // distinct(a, b) = (not (= b a)): distinct_elim + aci collapse + eq-symm
    // under a negation.
    let snapshot = raw_solver_snapshot(
        r#"
(rewrite (Mk (@and (Args (Mk x) (Empty)))) (Mk x))
(rewrite (Mk (@= (Args (Mk t1) (Args (Mk s1) (Empty)))))
         (Mk (@= (Args (Mk s1) (Args (Mk t1) (Empty))))))
(let a (Mk (Const "a")))
(let b (Mk (Const "b")))
(let d2 (Mk (@distinct (Args a (Args b (Empty))))))
(Avaliable d2)
(run-schedule (repeat 20 (run list-ruleset) (run)))
"#,
    );
    let [a, b] = ["a", "b"].map(encoded_const);
    let source = encoded_app("@distinct", vec![a.clone(), b.clone()]);
    let target = encoded_not_equal(&b, &a);
    let rules = [encoded_eq_symm_rule()];
    let certificate =
        reconstruct(&snapshot, &source, &target, &rules, SearchStrategy::default())
            .expect("the mixed chain should reconstruct");
    let steps = AletheElaborator::elaborate(&certificate, "t1")
        .expect("the mixed certificate should elaborate to Alethe");
    eprintln!("distinct_symm elaboration:\n{}", steps.join("\n"));
    assert!(steps
        .iter()
        .any(|step| step.contains("(= (distinct a b) (not (= a b))") && step.contains(":rule distinct_elim")));
    assert!(steps
        .iter()
        .any(|step| step.contains(":rule hole") && step.contains("\"eq-symm\"")));
    assert!(steps.iter().any(|step| step.contains(":rule cong")));
    assert!(steps
        .last()
        .is_some_and(|step| step.contains("(= (distinct a b) (not (= b a))")
            && step.contains(":rule trans")));

    // not(not(distinct(a,b,c))) = pairwise and: a trusted RARE step chained
    // with the native three-element distinct_elim.
    let snapshot = raw_solver_snapshot(
        r#"
(rewrite (Mk (@not (Args (Mk (@not (Args (Mk t1) (Empty)))) (Empty)))) (Mk t1))
(let a (Mk (Const "a")))
(let b (Mk (Const "b")))
(let c (Mk (Const "c")))
(let d3 (Mk (@distinct (Args a (Args b (Args c (Empty)))))))
(let source (Mk (@not (Args (Mk (@not (Args d3 (Empty)))) (Empty)))))
(Avaliable source)
(Avaliable d3)
(run-schedule (repeat 40 (run list-ruleset) (run)))
"#,
    );
    let [a, b, c] = ["a", "b", "c"].map(encoded_const);
    let distinct = encoded_app("@distinct", vec![a.clone(), b.clone(), c.clone()]);
    let source = encoded_app("@not", vec![encoded_app("@not", vec![distinct])]);
    let target = encoded_app(
        "@and",
        vec![
            encoded_not_equal(&a, &b),
            encoded_not_equal(&a, &c),
            encoded_not_equal(&b, &c),
        ],
    );
    let rules = [encoded_bool_double_not_elim_rule()];
    let certificate =
        reconstruct(&snapshot, &source, &target, &rules, SearchStrategy::default())
            .expect("the interior chain should reconstruct");
    let steps = AletheElaborator::elaborate(&certificate, "t2")
        .expect("the interior certificate should elaborate to Alethe");
    eprintln!("interior distinct elaboration:\n{}", steps.join("\n"));
    assert!(steps
        .iter()
        .any(|step| step.contains(":rule hole") && step.contains("\"bool-double-not-elim\"")));
    assert!(steps.iter().any(|step| {
        step.contains(":rule distinct_elim")
            && step.contains("(= (distinct a b c) (and (not (= a b)) (not (= a c)) (not (= b c))")
    }));
    assert!(steps
        .last()
        .is_some_and(|step| step.contains(":rule trans")));
}

/// The `distinct_symm` fixture through the full production pipeline: the
/// Alethe step claims `(= (distinct a b) (not (= b a)))`, so the certificate
/// must chain distinct elimination, the ACI singleton collapse, and the
/// `eq-symm` rule from the RARE file applied under the negation.
#[test]
fn reconstructs_distinct_symm_mix_from_production_egraph() {
    let run = run_qf_uf_case(
        "tests/rare/computational_mix/distinct_symm.smt2",
        "tests/rare/computational_mix/distinct_symm.alethe",
        "tests/rare/computational_mix/mix.rare",
        "t1",
        Some("eq-symm"),
    );
    let snapshot = EGraphSnapshot::capture_production(&run.egraph);
    let rules = [encoded_eq_symm_rule()];
    let reconstruction = reconstruct_detailed(
        &snapshot,
        &run.lhs,
        &run.rhs,
        &rules,
        SearchStrategy::default(),
    );
    let certificate = reconstruction
        .certificate
        .expect("distinct elimination, ACI collapse, and eq-symm should chain");

    assert!(certificate.verify(&rules));
    assert_eq!(certificate.lhs(), &run.lhs);
    assert_eq!(certificate.rhs(), &run.rhs);
    let mut names = Vec::new();
    certificate.rule_names(&mut names);
    assert_eq!(names, ["eq-symm"]);
    assert!(certificate.contains_computation(Computation::DistinctElim));
    assert!(certificate.contains_computation(Computation::AciNorm));
    assert!(certificate.contains_congruence());
    eprintln!(
        "distinct_symm mix: saturation={:?}, stats={:?}",
        run.saturation, reconstruction.stats,
    );
}

/// The `or_eval` fixture through the full production pipeline: the step
/// claims `(= (or p (and true false)) p)`, so evaluation must fold the
/// conjunction inside a congruence obligation before the RARE rule
/// `bool-or-false` strips the identity.
#[test]
fn reconstructs_or_evaluation_mix_from_production_egraph() {
    let run = run_qf_uf_case(
        "tests/rare/computational_mix/or_eval.smt2",
        "tests/rare/computational_mix/or_eval.alethe",
        "tests/rare/computational_mix/mix.rare",
        "t1",
        Some("bool-or-false"),
    );
    let snapshot = EGraphSnapshot::capture_production(&run.egraph);
    let rules = [encoded_bool_or_false_rule()];
    let reconstruction = reconstruct_detailed(
        &snapshot,
        &run.lhs,
        &run.rhs,
        &rules,
        SearchStrategy::default(),
    );
    let certificate = reconstruction
        .certificate
        .expect("evaluation under congruence should chain with bool-or-false");

    assert!(certificate.verify(&rules));
    assert_eq!(certificate.lhs(), &run.lhs);
    assert_eq!(certificate.rhs(), &run.rhs);
    let mut names = Vec::new();
    certificate.rule_names(&mut names);
    assert_eq!(names, ["bool-or-false"]);
    assert!(certificate.contains_computation(Computation::Evaluation));
    eprintln!(
        "or_eval mix: saturation={:?}, stats={:?}",
        run.saturation, reconstruction.stats,
    );
}

/// Variable names of the goal's sides, recovered from the original
/// conclusion `(= lhs rhs)`.
fn goal_variable_names(
    lhs: &Term,
    rhs: &Term,
    conclusion: &carcara::ast::Rc<carcara::ast::Term>,
) -> HashMap<String, String> {
    let mut names = HashMap::new();
    if let carcara::ast::Term::Op(carcara::ast::Operator::Equals, sides) = conclusion.as_ref() {
        if sides.len() == 2 {
            collect_variable_names(lhs, &sides[0], &mut names);
            collect_variable_names(rhs, &sides[1], &mut names);
        }
    }
    names
}

/// Round-trip emitted steps through the real Carcara checker against the
/// original problem and RARE database.
fn check_with_carcara(problem: &Path, steps: &[String], rare: &Path) -> Result<(), String> {
    let proof_text = format!("{}\n", steps.join("\n"));
    let problem_text = std::fs::read_to_string(problem).map_err(|error| error.to_string())?;
    let rare_text = std::fs::read_to_string(rare).map_err(|error| error.to_string())?;
    carcara::check(
        std::io::Cursor::new(problem_text.into_bytes()),
        std::io::Cursor::new(proof_text.into_bytes()),
        Some(std::io::Cursor::new(rare_text.into_bytes())),
        parser::Config {
            expand_lets: true,
            allow_int_real_subtyping: true,
            parse_hole_args: true,
            ..parser::Config::default()
        },
        carcara::checker::Config::default(),
        false,
    )
    .map(|_| ())
    .map_err(|error| error.to_string())
}

/// Elaborate a production-run certificate to Alethe and round-trip it
/// through Carcara; returns the emitted steps.
fn elaborate_and_check(
    run: &QfUfRun,
    certificate: &Certificate,
    hole: &str,
    problem_relative: &str,
    rare_relative: &str,
) -> Vec<String> {
    let rules = rules_from_generated_program(&run.generated_program);
    let names = goal_variable_names(&run.lhs, &run.rhs, &run.conclusion);
    let rare_index = rare_rule_index(&run.rare_rules, &rules);
    let steps = AletheElaborator::elaborate_full(certificate, hole, names, rare_index)
        .expect("certificate should elaborate to Alethe");
    if let Err(error) = check_with_carcara(
        &repository_path(problem_relative),
        &steps,
        &repository_path(rare_relative),
    ) {
        panic!(
            "emitted proof failed the Carcara check: {error}\n{}",
            steps.join("\n")
        );
    }
    steps
}

fn encoded_real(numer: i64, denom: i64) -> Term {
    Term::new(
        "Mk",
        vec![Term::new(
            "Real",
            vec![Term::leaf(&numer.to_string()), Term::leaf(&denom.to_string())],
        )],
    )
}

fn encoded_var(id: i64, sort: &str) -> Term {
    let sort = Term::new("Sort", vec![Term::new("Const", vec![Term::leaf(&format!("\"{sort}\""))])]);
    Term::new("Mk", vec![Term::new("Var", vec![Term::leaf(&id.to_string()), sort])])
}

/// The checker-side normal form is a ring normal form: distribution,
/// commutativity, cancellation, `to_real` erasure, constant division.
#[test]
fn arith_polynomials_normalize_modulo_ring_axioms() {
    let (x, y) = (encoded_var(1, "Int"), encoded_var(2, "Int"));
    let app = |op: &str, elements: Vec<Term>| encoded_app(op, elements);

    // (x + 1)(x - 1) = x*x - 1
    let product = app("@*", vec![app("@+", vec![x.clone(), encoded_num(1)]), app("@-", vec![x.clone(), encoded_num(1)])]);
    let expanded = app("@-", vec![app("@*", vec![x.clone(), x.clone()]), encoded_num(1)]);
    assert!(poly_equal(&product, &expanded));
    // 4x + 1 = 1 + 4x, n-ary and binarized alike
    let left = app("@+", vec![app("@*", vec![encoded_num(4), x.clone()]), encoded_num(1)]);
    let right = app("@+", vec![encoded_num(1), app("@*", vec![encoded_num(4), x.clone()])]);
    assert!(poly_equal(&left, &right));
    // to_real(x) / 2 = 1/2 * x
    let halved = app("@/", vec![app("@to_real", vec![x.clone()]), encoded_num(2)]);
    assert!(poly_equal(&halved, &app("@*", vec![encoded_real(1, 2), x.clone()])));
    // x - x + y = y; x + y != x - y
    assert!(poly_equal(&app("@+", vec![app("@-", vec![x.clone(), x.clone()]), y.clone()]), &y));
    assert!(!poly_equal(&app("@+", vec![x.clone(), y.clone()]), &app("@-", vec![x.clone(), y.clone()])));
    // division by a non-constant is opaque, but still a value
    let quotient = app("@/", vec![x.clone(), y.clone()]);
    assert!(poly_equal(&app("@*", vec![encoded_num(2), quotient.clone()]), &app("@+", vec![quotient.clone(), quotient])));
}

/// Relation keys identify equivalent relations across scaling, flipping,
/// negation, and integer tightening — and, unlike the solver's own key,
/// never tighten a strict bound with a fractional constant.
#[test]
fn arith_relation_keys_are_sound_on_fractional_strict_bounds() {
    let sorts = ArithSorts::default();
    let (x, y) = (encoded_var(1, "Int"), encoded_var(2, "Int"));
    let app = |op: &str, elements: Vec<Term>| encoded_app(op, elements);
    let twice = |term: &Term| app("@*", vec![encoded_num(2), term.clone()]);

    // 2x <= 2y  is  y >= x
    assert!(rel_equal(&app("@<=", vec![twice(&x), twice(&y)]), &app("@>=", vec![y.clone(), x.clone()]), &sorts));
    // x < y  is  not (x >= y)
    assert!(rel_equal(&app("@<", vec![x.clone(), y.clone()]), &app("@not", vec![app("@>=", vec![x.clone(), y.clone()])]), &sorts));
    // over the integers, x > 1  is  x >= 2
    assert!(rel_equal(&app("@>", vec![x.clone(), encoded_num(1)]), &app("@>=", vec![x.clone(), encoded_num(2)]), &sorts));
    // ... but to_real(x) > 1/2 is x >= 1, never x >= 2
    let fractional = app("@>", vec![app("@to_real", vec![x.clone()]), encoded_real(1, 2)]);
    assert!(!rel_equal(&fractional, &app("@>=", vec![x.clone(), encoded_num(2)]), &sorts));
    // equalities are keyed up to any nonzero scaling
    assert!(rel_equal(
        &app("@=", vec![app("@+", vec![x.clone(), y.clone()]), encoded_num(0)]),
        &app("@=", vec![app("@-", vec![encoded_num(0), y.clone()]), x.clone()]),
        &sorts
    ));
    // a boolean equality is not an arithmetic one
    let (p, q) = (encoded_var(3, "Bool"), encoded_var(4, "Bool"));
    assert!(!rel_equal(&app("@=", vec![p.clone(), q.clone()]), &app("@=", vec![q, p]), &sorts));
}

/// The `poly_norm` fixture through the full production pipeline: the step
/// claims `(= (+ (* 4 f3) 1) (+ 1 (* 4 f3)))`, which no RARE rule derives.
/// The solver proves it by polynomial normal forms without merging the two
/// sides, so the certificate is one arithmetic step, elaborated as cvc5's
/// `poly_simp`.
#[test]
fn reconstructs_arith_poly_norm_from_production_egraph() {
    let run = run_qf_uf_case(
        "tests/rare/computational_mix/poly_norm.smt2",
        "tests/rare/computational_mix/poly_norm.alethe",
        "tests/rare/computational_mix/mix.rare",
        "t1",
        None,
    );
    let snapshot = EGraphSnapshot::capture_production(&run.egraph);
    assert!(
        !snapshot.same_class(&run.lhs, &run.rhs),
        "polynomial goals are proved by normal forms, not by union"
    );
    let rules = rules_from_generated_program(&run.generated_program);
    let sorts = ArithSorts::from_generated_program(&run.generated_program);
    let reconstruction = reconstruct_with_sorts(
        &snapshot,
        &run.lhs,
        &run.rhs,
        &rules,
        &sorts,
        SearchStrategy::default(),
    );
    let certificate = reconstruction
        .certificate
        .expect("polynomial normalization should reconstruct across classes");
    assert_eq!(
        certificate,
        Certificate::Computational {
            kind: Computation::ArithPolyNorm,
            lhs: run.lhs.clone(),
            rhs: run.rhs.clone(),
        }
    );
    let steps = elaborate_and_check(
        &run,
        &certificate,
        "t1",
        "tests/rare/computational_mix/poly_norm.smt2",
        "tests/rare/computational_mix/mix.rare",
    );
    assert_eq!(steps.len(), 1);
    assert!(steps[0].contains("\"poly_simp\""), "{}", steps[0]);
    eprintln!("poly_norm: saturation={:?}, steps={steps:#?}", run.saturation);
}

/// The `poly_norm_rel` fixture: `(= (not (not (<= (* 2 x) (* 2 y)))) (>= y x))`
/// mixes a RARE rewrite with relation normalization.  The e-graph strips
/// the double negation first, so the solver keys the class holding the
/// `<=`; reconstruction bridges to that enode with the RARE rule and then
/// takes one `poly_simp_rel` step.
#[test]
fn reconstructs_arith_poly_norm_rel_mixed_with_double_not_from_production_egraph() {
    let run = run_qf_uf_case(
        "tests/rare/computational_mix/poly_norm_rel.smt2",
        "tests/rare/computational_mix/poly_norm_rel.alethe",
        "tests/rare/computational_mix/mix.rare",
        "t1",
        Some("bool-double-not-elim"),
    );
    let snapshot = EGraphSnapshot::capture_production(&run.egraph);
    assert!(!snapshot.same_class(&run.lhs, &run.rhs));
    let rules = rules_from_generated_program(&run.generated_program);
    let sorts = ArithSorts::from_generated_program(&run.generated_program);
    let reconstruction = reconstruct_with_sorts(
        &snapshot,
        &run.lhs,
        &run.rhs,
        &rules,
        &sorts,
        SearchStrategy::default(),
    );
    let certificate = reconstruction
        .certificate
        .expect("double negation then relation normalization should chain");
    assert_eq!(certificate.lhs(), &run.lhs);
    assert_eq!(certificate.rhs(), &run.rhs);
    assert!(certificate.contains_computation(Computation::ArithPolyNormRel));
    let mut names = Vec::new();
    certificate.rule_names(&mut names);
    assert_eq!(names.len(), 1, "one RARE step bridges the negations: {names:?}");
    let steps = elaborate_and_check(
        &run,
        &certificate,
        "t1",
        "tests/rare/computational_mix/poly_norm_rel.smt2",
        "tests/rare/computational_mix/mix.rare",
    );
    assert!(steps.iter().any(|step| step.contains("rare_rewrite") && step.contains("\"bool-double-not-elim\"")), "{steps:#?}");
    assert!(steps.iter().any(|step| step.contains("\"poly_simp_rel\"")), "{steps:#?}");
    eprintln!("poly_norm_rel mix: saturation={:?}, steps={steps:#?}", run.saturation);
}

/// The `real_eval` fixture: `(= (+ 1/2 1/2) 1.0)`.  The solver rewrites
/// every `Real` literal to its `BigRat` form and folds the sum there, so
/// the recomputed rational must be spelled exactly as egglog serializes
/// it for the step to land in the goal's class; the literal renormalization
/// on the right elaborates to `refl`.
#[test]
fn reconstructs_rational_evaluation_from_production_egraph() {
    let run = run_qf_uf_case(
        "tests/rare/computational_mix/real_eval.smt2",
        "tests/rare/computational_mix/real_eval.alethe",
        "tests/rare/computational_mix/mix.rare",
        "t1",
        None,
    );
    let snapshot = EGraphSnapshot::capture_production(&run.egraph);
    let rules = rules_from_generated_program(&run.generated_program);
    let reconstruction = reconstruct_detailed(
        &snapshot,
        &run.lhs,
        &run.rhs,
        &rules,
        SearchStrategy::default(),
    );
    let certificate = reconstruction
        .certificate
        .expect("rational constant folding should reconstruct");
    assert!(certificate.contains_computation(Computation::Evaluation));
    let steps = elaborate_and_check(
        &run,
        &certificate,
        "t1",
        "tests/rare/computational_mix/real_eval.smt2",
        "tests/rare/computational_mix/mix.rare",
    );
    assert!(steps.iter().any(|step| step.contains("\"evaluate\"")), "{steps:#?}");
    eprintln!("real_eval: saturation={:?}, steps={steps:#?}", run.saturation);
}

fn leak(string: String) -> &'static str {
    Box::leak(string.into_boxed_str())
}

fn pattern_from_egglog_expr(expression: &EgglogExpr) -> Pattern {
    match expression {
        GenericExpr::Lit(_, literal) => Pattern::App(leak(literal.to_string()), Vec::new()),
        GenericExpr::Var(_, variable) => Pattern::Var(leak(variable.to_string())),
        GenericExpr::Call(_, operator, children) => Pattern::App(
            leak(operator.to_string()),
            children.iter().map(pattern_from_egglog_expr).collect(),
        ),
    }
}

/// The full effective declarative rule set of a generated egglog program:
/// every unconditional rewrite, converted to reconstruction patterns.
/// Rules with conditions, native computations on their right-hand sides, or
/// global references simply never e-match in the snapshot and are covered by
/// the computational certificate kinds instead.
fn rules_from_generated_program(program: &str) -> Vec<Rewrite> {
    let commands = egglog::ast::Parser::default()
        .get_program_from_string(None, program)
        .expect("Carcara's generated egglog program should parse");
    let mut rules = Vec::new();
    let mut add = |lhs: &EgglogExpr, rhs: &EgglogExpr, rules: &mut Vec<Rewrite>| {
        rules.push(Rewrite {
            name: leak(format!("gen-{}", rules.len())),
            lhs: pattern_from_egglog_expr(lhs),
            rhs: pattern_from_egglog_expr(rhs),
        });
    };
    for command in commands {
        match &command {
            EgglogCommand::Rewrite(_, rewrite, _) if rewrite.conditions.is_empty() => {
                add(&rewrite.lhs, &rewrite.rhs, &mut rules);
            }
            EgglogCommand::BiRewrite(_, rewrite) if rewrite.conditions.is_empty() => {
                add(&rewrite.lhs, &rewrite.rhs, &mut rules);
                add(&rewrite.rhs, &rewrite.lhs, &mut rules);
            }
            _ => {}
        }
    }
    rules
}

/// Compile a RARE rule term into the encoded pattern shape the engine
/// generates: rule parameters become pattern variables (their names are
/// preserved verbatim by the compilation), operators and uninterpreted
/// functions become `@`-prefixed constructors over `Args` lists.
fn encode_rare_pattern(
    term: &carcara::ast::Rc<carcara::ast::Term>,
    parameters: &indexmap::IndexMap<String, carcara::ast::rare_rules::TypeParameter>,
) -> Option<Pattern> {
    use carcara::ast::Term as Original;
    let mk = |inner: Pattern| Pattern::App("Mk", vec![inner]);
    let encode_call = |operator: String,
                       args: &[carcara::ast::Rc<carcara::ast::Term>]|
     -> Option<Pattern> {
        let list = args.iter().rev().try_fold(
            Pattern::App("Empty", Vec::new()),
            |tail, argument| {
                Some(Pattern::App(
                    "Args",
                    vec![encode_rare_pattern(argument, parameters)?, tail],
                ))
            },
        )?;
        Some(mk(Pattern::App(leak(operator), vec![list])))
    };
    match term.as_ref() {
        Original::Var(name, _) if parameters.contains_key(name) => {
            Some(mk(Pattern::Var(leak(name.clone()))))
        }
        Original::Op(operator, args) => encode_call(format!("@{operator}"), args),
        Original::App(function, args) => {
            let Original::Var(name, _) = function.as_ref() else {
                return None;
            };
            encode_call(format!("@{name}"), args)
        }
        Original::Const(carcara::ast::Constant::Integer(value)) => Some(mk(Pattern::App(
            "Num",
            vec![Pattern::App(leak(value.to_string()), Vec::new())],
        ))),
        Original::Const(carcara::ast::Constant::Real(value)) => {
            let (numer, denom) = value.clone().into_numer_denom();
            Some(mk(Pattern::App(
                "Real",
                vec![
                    Pattern::App(leak(numer.to_string()), Vec::new()),
                    Pattern::App(leak(denom.to_string()), Vec::new()),
                ],
            )))
        }
        _ => match format!("{term}").as_str() {
            "true" => Some(mk(Pattern::App("Bool", vec![Pattern::App("true", Vec::new())]))),
            "false" => Some(mk(Pattern::App("Bool", vec![Pattern::App("false", Vec::new())]))),
            _ => None,
        },
    }
}

/// Associate generated egglog rewrites back to the RARE rules they were
/// compiled from, by structural pattern equality of both sides.  Returns
/// generated-name -> (RARE name, argument order).
fn rare_rule_index(
    database: &indexmap::IndexMap<String, carcara::ast::rare_rules::RuleDefinition>,
    generated: &[Rewrite],
) -> HashMap<String, (String, Vec<String>)> {
    use carcara::ast::Term as Original;
    let mut compiled = Vec::new();
    for (name, rule) in database {
        if !rule.premises.is_empty() {
            continue;
        }
        let Original::Op(carcara::ast::Operator::Equals, sides) = rule.conclusion.as_ref() else {
            continue;
        };
        if sides.len() != 2 {
            continue;
        }
        let (Some(lhs), Some(rhs)) = (
            encode_rare_pattern(&sides[0], &rule.parameters),
            encode_rare_pattern(&sides[1], &rule.parameters),
        ) else {
            continue;
        };
        compiled.push((name.clone(), rule.arguments.clone(), lhs, rhs));
    }

    let mut index = HashMap::new();
    for rewrite in generated {
        for (name, arguments, lhs, rhs) in &compiled {
            if &rewrite.lhs == lhs && &rewrite.rhs == rhs {
                index.insert(rewrite.name.to_owned(), (name.clone(), arguments.clone()));
                break;
            }
        }
    }
    index
}

/// Corpus sweep for OUR algorithm: for every hole slice where the egglog
/// oracle succeeds, reconstruct a certificate from the provenance-free
/// snapshot, verify it, and elaborate it to Alethe — stopping at the first
/// case where reconstruction or elaboration fails.  Oracle failures are
/// skipped: they are engine territory, not reconstruction territory.
///
/// Driven by env vars: BENCH_LIST (tsv: alethe, smt2, hole id), BENCH_RARE,
/// optional BENCH_SKIP / BENCH_LIMIT.
#[test]
#[ignore = "corpus reconstruction sweep; set BENCH_LIST and BENCH_RARE"]
fn reconstructs_benchmark_corpus() {
    let list = std::fs::read_to_string(std::env::var("BENCH_LIST").expect("set BENCH_LIST"))
        .expect("BENCH_LIST should be readable");
    let rare_path = std::env::var("BENCH_RARE").expect("set BENCH_RARE");
    let skip: usize = std::env::var("BENCH_SKIP").ok().and_then(|s| s.parse().ok()).unwrap_or(0);
    let limit: usize = std::env::var("BENCH_LIMIT")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(usize::MAX);

    let (mut oracle_failed, mut reconstructed) = (0usize, 0usize);
    let started = Instant::now();
    for (index, line) in list.lines().enumerate().skip(skip).take(limit) {
        let mut fields = line.split('\t');
        let (Some(alethe), Some(smt2), Some(hole)) =
            (fields.next(), fields.next(), fields.next())
        else {
            continue;
        };
        // One line per case before any work, so an abort (e.g. an oracle
        // saturation exceeding the memory cap) identifies its case for the
        // restart-and-skip driver.
        eprintln!("case {index}: {alethe}");

        let parser_config = parser::Config {
            expand_lets: true,
            allow_int_real_subtyping: true,
            parse_hole_args: true,
            ..parser::Config::default()
        };
        let (_, proof, database, mut pool) = parser::parse_instance(
            BufReader::new(File::open(smt2).expect("problem should exist")),
            BufReader::new(File::open(alethe).expect("slice should exist")),
            Some(BufReader::new(
                File::open(&rare_path).expect("RARE database should exist"),
            )),
            parser_config,
        )
        .expect("slice should parse");
        let node = ProofNode::from_commands_with_root_id(proof.commands, hole)
            .expect("slice should contain its hole");
        let conclusion = node.clause()[0].clone();

        let (result, program) = run_egglog(
            &mut pool,
            (conclusion.clone(), &node),
            &database,
            RunEgglogOptions::default(),
        );
        if result.is_err() {
            oracle_failed += 1;
            continue;
        }
        let snapshot = EGraphSnapshot::capture_production(&result.unwrap());
        let (lhs, rhs) = generated_goals(&program);
        let rules = rules_from_generated_program(&program);
        let sorts = ArithSorts::from_generated_program(&program);

        let reconstruction = reconstruct_with_sorts(
            &snapshot,
            &lhs,
            &rhs,
            &rules,
            &sorts,
            SearchStrategy::default(),
        );
        let Some(certificate) = reconstruction.certificate else {
            panic!(
                "\nSTOPPED at case {index}: RECONSTRUCTION FAILED (oracle succeeded)\n\
                 slice: {alethe}\nhole: {hole}\nrules: {}\nstats: {:?}\n\
                 lhs: {}\nrhs: {}",
                rules.len(),
                reconstruction.stats,
                lhs.to_egglog(),
                rhs.to_egglog(),
            );
        };
        let names = goal_variable_names(&lhs, &rhs, &conclusion);
        let rare_index = rare_rule_index(&database.rules, &rules);
        let Some(steps) =
            AletheElaborator::elaborate_full(&certificate, hole, names.clone(), rare_index)
        else {
            panic!(
                "\nSTOPPED at case {index}: ALETHE ELABORATION FAILED\n\
                 slice: {alethe}\nhole: {hole}\ncertificate: {certificate:#?}",
            );
        };

        // Round-trip: the emitted steps must pass the real Carcara checker
        // against the original problem.
        if std::env::var("BENCH_PRINT").is_ok() {
            eprintln!(
                "--- elaborated proof (case {index}, hole {hole}) ---\n{}\n",
                steps.join("\n")
            );
        }
        if let Err(error) = check_with_carcara(Path::new(smt2), &steps, Path::new(&rare_path)) {
            panic!(
                "\nSTOPPED at case {index}: CARCARA CHECK FAILED: {error}\n\
                 slice: {alethe}\nhole: {hole}\n--- emitted proof ---\n{}\n\
                 names: {names:?}\nencoded lhs: {}\nconclusion: {conclusion}",
                steps.join("\n"),
                lhs.to_egglog(),
            );
        }
        reconstructed += 1;
        if index % 25 == 0 {
            eprintln!(
                "[{index}] reconstructed={reconstructed} oracle_failed={oracle_failed} \
                 ({:.0}s elapsed)",
                started.elapsed().as_secs_f64(),
            );
        }
    }
    eprintln!(
        "corpus sweep done: reconstructed={reconstructed} oracle_failed={oracle_failed} \
         in {:.0}s",
        started.elapsed().as_secs_f64(),
    );
}

/// Shared prelude for raw computational-solver programs: the term datatype
/// and the (fixed) distinct-elimination solver, without the header axioms.
const RAW_SOLVER_PRELUDE: &str = r#"
(datatype Term
  (Const String)
  (Bool bool)
  (Empty)
  (Args Term Term)
  (Mk Term))
(constructor @distinct (Term) Term)
(constructor @and (Term) Term)
(constructor @or (Term) Term)
(constructor @not (Term) Term)
(constructor @= (Term) Term)
(relation Avaliable (Term))
(function to_formula (Term Term Term) Term :no-merge)
(relation to_formula_rel (Term Term Term))
(ruleset list-ruleset)

(rule ((to_formula_rel (Empty) k (Empty)))
      ((set (to_formula (Empty) k (Empty)) (Empty)))
      :ruleset list-ruleset)
(rule ((= res (Args r rs))
       (to_formula_rel res y (Empty)))
      ((to_formula_rel rs r rs))
      :ruleset list-ruleset)
(rule ((= xs (Args x rxs))
       (to_formula_rel res y xs))
      ((to_formula_rel res y rxs))
      :ruleset list-ruleset)
(rule ((to_formula_rel res y (Args x rxs))
       (= (to_formula res y rxs) f))
      ((set (to_formula res y (Args x rxs))
            (Args (Mk (@not (Args (Mk (@= (Args y (Args x (Empty))))) (Empty)))) f)))
      :ruleset list-ruleset)
(rule ((to_formula_rel (Args r res) y (Empty))
       (= (to_formula res r res) f))
      ((set (to_formula (Args r res) y (Empty)) f))
      :ruleset list-ruleset)
(rule ((Avaliable (Mk (@distinct (Args x xs))))
       (= (to_formula xs x xs) f))
      ((union (Mk (@and f)) (Mk (@distinct (Args x xs)))))
      :ruleset list-ruleset)
(rule ((Avaliable (Mk (@distinct (Args x xs)))))
      ((to_formula_rel xs x xs))
      :ruleset list-ruleset)
"#;

fn raw_solver_snapshot(tail: &str) -> EGraphSnapshot {
    let program = format!("{RAW_SOLVER_PRELUDE}\n{tail}");
    let mut egraph = ProductionEGraph::default();
    egraph
        .parse_and_run_program(None, &program)
        .expect("raw computational solver program should run");
    EGraphSnapshot::capture_production(&egraph)
}

fn encoded_const(name: &str) -> Term {
    Term::new(
        "Mk",
        vec![Term::new("Const", vec![Term::leaf(&format!("\"{name}\""))])],
    )
}

fn encoded_not_equal(x: &Term, y: &Term) -> Term {
    encoded_app(
        "@not",
        vec![encoded_app("@=", vec![x.clone(), y.clone()])],
    )
}

/// The distinct-elimination union sits in the interior of the chain: the
/// obligation's endpoints are a double negation and the expanded
/// conjunction, so neither is distinct-shaped and only a vertex-local
/// computational edge can cross the gap.
#[test]
fn reconstructs_interior_distinct_elimination_between_rewrites() {
    let snapshot = raw_solver_snapshot(
        r#"
(rewrite (Mk (@not (Args (Mk (@not (Args (Mk t1) (Empty)))) (Empty)))) (Mk t1))
(let a (Mk (Const "a")))
(let b (Mk (Const "b")))
(let c (Mk (Const "c")))
(let d3 (Mk (@distinct (Args a (Args b (Args c (Empty)))))))
(let source (Mk (@not (Args (Mk (@not (Args d3 (Empty)))) (Empty)))))
(Avaliable source)
(Avaliable d3)
(run-schedule (repeat 40 (run list-ruleset) (run)))
"#,
    );

    let [a, b, c] = ["a", "b", "c"].map(encoded_const);
    let distinct = encoded_app("@distinct", vec![a.clone(), b.clone(), c.clone()]);
    let source = encoded_app("@not", vec![encoded_app("@not", vec![distinct])]);
    let target = encoded_app(
        "@and",
        vec![
            encoded_not_equal(&a, &b),
            encoded_not_equal(&a, &c),
            encoded_not_equal(&b, &c),
        ],
    );

    let rules = [encoded_bool_double_not_elim_rule()];
    let reconstruction = reconstruct_detailed(
        &snapshot,
        &source,
        &target,
        &rules,
        SearchStrategy::default(),
    );
    let certificate = reconstruction
        .certificate
        .expect("the rewrite and the computational step should chain");
    assert!(certificate.verify(&rules));
    assert_eq!(certificate.lhs(), &source);
    assert_eq!(certificate.rhs(), &target);
    let mut names = Vec::new();
    certificate.rule_names(&mut names);
    assert_eq!(names, ["bool-double-not-elim"]);
    assert!(certificate.contains_computation(Computation::DistinctElim));
    assert!(reconstruction.stats.computational_edges >= 1);
}

/// The two-element seam: the solver unions `distinct(a, b)` with the
/// singleton `and`, and ACI singleton elimination carries it the rest of the
/// way to the Alethe shape `(not (= a b))` — two computational edges, no
/// declarative rule at all.
#[test]
fn reconstructs_two_element_distinct_via_aci_singleton() {
    let snapshot = raw_solver_snapshot(
        r#"
(rewrite (Mk (@and (Args (Mk x) (Empty)))) (Mk x))
(let a (Mk (Const "a")))
(let b (Mk (Const "b")))
(let d2 (Mk (@distinct (Args a (Args b (Empty))))))
(Avaliable d2)
(run-schedule (repeat 20 (run list-ruleset) (run)))
"#,
    );

    let [a, b] = ["a", "b"].map(encoded_const);
    let source = encoded_app("@distinct", vec![a.clone(), b.clone()]);
    let target = encoded_not_equal(&a, &b);

    let reconstruction =
        reconstruct_detailed(&snapshot, &source, &target, &[], SearchStrategy::default());
    let certificate = reconstruction
        .certificate
        .expect("distinct elimination and ACI singleton collapse should chain");
    assert!(certificate.verify(&[]));
    assert_eq!(certificate.lhs(), &source);
    assert_eq!(certificate.rhs(), &target);
    assert!(certificate.contains_computation(Computation::DistinctElim));
    assert!(certificate.contains_computation(Computation::AciNorm));
}

/// Boolean constant folding, mirroring evaluation.egglog: a single
/// computational edge certifies `(and true false) = false`.
#[test]
fn reconstructs_boolean_evaluation() {
    let snapshot = raw_solver_snapshot(
        r#"
(rewrite (Mk (@and (Args (Mk (Bool x)) (Args (Mk (Bool y)) (Empty)))))
         (Mk (Bool (and x y))))
(let e (Mk (@and (Args (Mk (Bool true)) (Args (Mk (Bool false)) (Empty))))))
(Avaliable e)
(run-schedule (repeat 5 (run)))
"#,
    );

    let source = encoded_app("@and", vec![encoded_bool(true), encoded_bool(false)]);
    let target = encoded_bool(false);

    let reconstruction =
        reconstruct_detailed(&snapshot, &source, &target, &[], SearchStrategy::default());
    let certificate = reconstruction
        .certificate
        .expect("boolean evaluation should certify the folding");
    assert!(certificate.verify(&[]));
    assert!(certificate.contains_computation(Computation::Evaluation));
}

/// Full mix on the two-element seam: distinct elimination and the ACI
/// singleton collapse cross to `(not (= a b))`, and the RARE rule `eq-symm`
/// — applied under a `not` through congruence — carries the chain to the
/// flipped `(not (= b a))`.  One certificate, all edge kinds.
#[test]
fn reconstructs_distinct_elimination_mixed_with_eq_symm() {
    let snapshot = raw_solver_snapshot(
        r#"
(rewrite (Mk (@and (Args (Mk x) (Empty)))) (Mk x))
(rewrite (Mk (@= (Args (Mk t1) (Args (Mk s1) (Empty)))))
         (Mk (@= (Args (Mk s1) (Args (Mk t1) (Empty))))))
(let a (Mk (Const "a")))
(let b (Mk (Const "b")))
(let d2 (Mk (@distinct (Args a (Args b (Empty))))))
(Avaliable d2)
(run-schedule (repeat 20 (run list-ruleset) (run)))
"#,
    );

    let [a, b] = ["a", "b"].map(encoded_const);
    let source = encoded_app("@distinct", vec![a.clone(), b.clone()]);
    let target = encoded_not_equal(&b, &a);

    let rules = [encoded_eq_symm_rule()];
    let reconstruction = reconstruct_detailed(
        &snapshot,
        &source,
        &target,
        &rules,
        SearchStrategy::default(),
    );
    let certificate = reconstruction
        .certificate
        .expect("computational steps and eq-symm should chain");
    assert!(certificate.verify(&rules));
    assert_eq!(certificate.lhs(), &source);
    assert_eq!(certificate.rhs(), &target);
    let mut names = Vec::new();
    certificate.rule_names(&mut names);
    assert_eq!(names, ["eq-symm"]);
    assert!(certificate.contains_computation(Computation::DistinctElim));
    assert!(certificate.contains_computation(Computation::AciNorm));
    assert!(certificate.contains_congruence());
}

/// Evaluation buried inside a congruence child obligation, chained with a
/// RARE rule: `(or p (and true false))` needs the inner conjunction folded
/// to `false` before `bool-or-false` can strip it.
#[test]
fn reconstructs_evaluation_inside_congruence_with_rare_rule() {
    let snapshot = raw_solver_snapshot(
        r#"
(rewrite (Mk (@and (Args (Mk (Bool x)) (Args (Mk (Bool y)) (Empty)))))
         (Mk (Bool (and x y))))
(rewrite (Mk (@or (Args (Mk x) (Args (Mk (Bool false)) (Empty))))) (Mk x))
(let p (Mk (Const "p")))
(let tf (Mk (@and (Args (Mk (Bool true)) (Args (Mk (Bool false)) (Empty))))))
(let source (Mk (@or (Args p (Args tf (Empty))))))
(Avaliable source)
(run-schedule (repeat 10 (run)))
"#,
    );

    let p = encoded_const("p");
    let inner = encoded_app("@and", vec![encoded_bool(true), encoded_bool(false)]);
    let source = encoded_app("@or", vec![p.clone(), inner]);
    let target = p;

    let rules = [encoded_bool_or_false_rule()];
    let reconstruction = reconstruct_detailed(
        &snapshot,
        &source,
        &target,
        &rules,
        SearchStrategy::default(),
    );
    let certificate = reconstruction
        .certificate
        .expect("evaluation under congruence should chain with bool-or-false");
    assert!(certificate.verify(&rules));
    assert_eq!(certificate.lhs(), &source);
    assert_eq!(certificate.rhs(), &target);
    let mut names = Vec::new();
    certificate.rule_names(&mut names);
    assert_eq!(names, ["bool-or-false"]);
    assert!(certificate.contains_computation(Computation::Evaluation));
    assert!(certificate.contains_congruence());
}

#[test]
#[ignore = "diagnostic dump of the e-graph contents for a distinct_elim obligation"]
fn inspect_distinct_elim_egraph() {
    let run = run_qf_uf_case(
        "tests/rare/distinct_elim/QF_UF_resistance.1.prop2_ab_cti_max.smt2",
        "tests/rare/distinct_elim/QF_UF_resistance.1.prop2_ab_cti_max__from-t600.smt2.alethe",
        "tests/rare/big.rare",
        "t600",
        None,
    );
    let snapshot = EGraphSnapshot::capture_production(&run.egraph);
    eprintln!("goal lhs = {}", run.lhs.to_egglog());
    eprintln!("goal rhs = {}", run.rhs.to_egglog());
    eprintln!(
        "egraph: {} enodes, {} classes, saturation={:?}",
        snapshot.nodes.len(),
        snapshot.class_nodes.len(),
        run.saturation,
    );
    eprintln!("same_class(lhs, rhs) = {}", snapshot.same_class(&run.lhs, &run.rhs));

    let mut op_counts: BTreeMap<&str, usize> = BTreeMap::new();
    for node in &snapshot.nodes {
        *op_counts
            .entry(snapshot.ops.names[node.op as usize].as_str())
            .or_default() += 1;
    }
    eprintln!("operators in the serialized e-graph: {op_counts:#?}");

    let mut cache = HashMap::new();
    for (label, goal) in [("lhs", &run.lhs), ("rhs", &run.rhs)] {
        let Some(eclass) = snapshot.class_of(goal, &mut cache) else {
            eprintln!("goal {label} is not represented in the snapshot");
            continue;
        };
        eprintln!("goal {label} class {eclass} holds:");
        for &index in &snapshot.class_nodes[eclass as usize] {
            let node = &snapshot.nodes[index as usize];
            eprintln!(
                "  {}({})",
                snapshot.ops.names[node.op as usize],
                node.child_classes
                    .iter()
                    .map(|class| class.to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
            );
        }
    }

    let reconstruction = reconstruct_detailed(
        &snapshot,
        &run.lhs,
        &run.rhs,
        &[],
        SearchStrategy::default(),
    );
    eprintln!(
        "declarative reconstruction without rules: found={}, stats={:?}",
        reconstruction.certificate.is_some(),
        reconstruction.stats,
    );

    // Intermediate-state contamination check: a `to_formula` row is
    // serialized into the class of its output list, and being small it wins
    // naive minimal-size extraction; the internal-op guard must pick the
    // real term instead.
    let mut contaminated = 0;
    let mut example = None;
    let mut naive_memo = HashMap::new();
    let mut guarded_memo = HashMap::new();
    for (eclass, nodes) in snapshot.class_nodes.iter().enumerate() {
        let holds_row = nodes.iter().any(|&index| {
            snapshot.ops.names[snapshot.nodes[index as usize].op as usize] == "to_formula"
        });
        if !holds_row {
            continue;
        }
        let eclass = eclass as u32;
        let naive = extract_avoiding(&snapshot, eclass, &[], &mut HashSet::new(), &mut naive_memo);
        let guarded = extract_avoiding(
            &snapshot,
            eclass,
            &INTERNAL_OPS,
            &mut HashSet::new(),
            &mut guarded_memo,
        );
        if naive != guarded {
            contaminated += 1;
            example.get_or_insert((eclass, naive, guarded));
        }
    }
    eprintln!("classes where a to_formula row wins naive minimal-size extraction: {contaminated}");
    if let Some((eclass, naive, guarded)) = example {
        eprintln!(
            "example class {eclass}:\n  naive extraction   = {}\n  guarded extraction = {}",
            naive.map_or("<none>".to_owned(), |term| term.to_egglog()),
            guarded.map_or("<none>".to_owned(), |term| {
                let rendered = term.to_egglog();
                if rendered.len() > 200 {
                    format!("{}… ({} chars)", &rendered[..200], rendered.len())
                } else {
                    rendered
                }
            }),
        );
    }
}

#[test]
fn reconstructs_real_qf_uf_t37_from_production_egraph() {
    let run = run_qf_uf_t37();
    let snapshot = EGraphSnapshot::capture_production(&run.egraph);
    let rules = [encoded_eq_symm_rule()];
    let reconstruction = reconstruct_detailed(
        &snapshot,
        &run.lhs,
        &run.rhs,
        &rules,
        SearchStrategy::default(),
    );
    let certificate = reconstruction
        .certificate
        .expect("eq-symm should reconstruct the real QF_UF t37 equality");

    assert!(certificate.verify(&rules));
    assert_eq!(certificate.lhs(), &run.lhs);
    assert_eq!(certificate.rhs(), &run.rhs);
    let mut names = Vec::new();
    certificate.rule_names(&mut names);
    assert_eq!(names, ["eq-symm"]);
    assert!(reconstruction.stats.lhs_matches >= 1);
    assert!(reconstruction.stats.rule_instances >= 1);
    assert!(snapshot.same_class(&run.lhs, &run.rhs));
    assert!(
        reconstruct(
            &snapshot,
            &run.lhs,
            &run.rhs,
            &[],
            SearchStrategy::default(),
        )
        .is_none()
    );

    eprintln!(
        "QF_UF t37: generated={} bytes, egraph={} enodes, saturation={:?}, stats={:?}, certificate={certificate:#?}",
        run.generated_program.len(),
        snapshot.nodes.len(),
        run.saturation,
        reconstruction.stats,
    );
}

#[test]
fn reconstructs_real_qf_uf_double_not_from_production_egraph() {
    let run = run_qf_uf_double_not_t3();
    let snapshot = EGraphSnapshot::capture_production(&run.egraph);
    let rules = [encoded_bool_double_not_elim_rule()];
    let reconstruction = reconstruct_detailed(
        &snapshot,
        &run.lhs,
        &run.rhs,
        &rules,
        SearchStrategy::default(),
    );
    let certificate = reconstruction
        .certificate
        .expect("the final e-graph should yield the bool-double-not-elim instance");

    assert!(certificate.verify(&rules));
    assert_eq!(certificate.lhs(), &run.lhs);
    assert_eq!(certificate.rhs(), &run.rhs);
    let mut names = Vec::new();
    certificate.rule_names(&mut names);
    assert_eq!(names, ["bool-double-not-elim"]);
    assert!(reconstruction.stats.lhs_matches >= 1);
    assert!(reconstruction.stats.rule_instances >= 1);
    assert!(snapshot.same_class(&run.lhs, &run.rhs));
    assert!(
        reconstruct(
            &snapshot,
            &run.lhs,
            &run.rhs,
            &[],
            SearchStrategy::default(),
        )
        .is_none()
    );

    eprintln!(
        "QF_UF t3 double-not: generated={} bytes, egraph={} enodes, saturation={:?}, stats={:?}, certificate={certificate:#?}",
        run.generated_program.len(),
        snapshot.nodes.len(),
        run.saturation,
        reconstruction.stats,
    );
}

#[test]
#[ignore = "diagnostic benchmark over the full QF_UF rule database"]
fn benchmark_real_qf_uf_raw_rules_posthoc_reconstruction() {
    const CHECK_SAMPLES: usize = 11;
    const SAMPLES: usize = 100;

    fn median(mut samples: Vec<Duration>) -> Duration {
        samples.sort_unstable();
        samples[samples.len() / 2]
    }

    fn benchmark_case(
        label: &str,
        run_case: fn() -> QfUfRun,
        rule: Rewrite,
    ) -> (Duration, Duration) {
        // Warm the code and allocator paths, then keep one real saturated
        // e-graph for all post-check reconstruction samples.
        run_case();
        let run = run_case();
        let mut saturation_samples = vec![run.saturation];
        saturation_samples.extend((1..CHECK_SAMPLES).map(|_| run_case().saturation));
        let saturation = median(saturation_samples);
        let rules = [rule];
        let snapshot = EGraphSnapshot::capture_production(&run.egraph);
        let serialization = median(
            (0..SAMPLES)
                .map(|_| {
                    let start = Instant::now();
                    let snapshot = EGraphSnapshot::capture_production(&run.egraph);
                    assert!(!snapshot.nodes.is_empty());
                    start.elapsed()
                })
                .collect(),
        );
        let diagnostic = reconstruct_detailed(
            &snapshot,
            &run.lhs,
            &run.rhs,
            &rules,
            SearchStrategy::default(),
        );
        assert!(diagnostic.certificate.unwrap().verify(&rules));
        let search_and_verification = median(
            (0..SAMPLES)
                .map(|_| {
                    let start = Instant::now();
                    let reconstruction = reconstruct_detailed(
                        &snapshot,
                        &run.lhs,
                        &run.rhs,
                        &rules,
                        SearchStrategy::default(),
                    );
                    assert!(reconstruction.certificate.unwrap().verify(&rules));
                    start.elapsed()
                })
                .collect(),
        );
        let reconstruction = serialization + search_and_verification;
        let total = saturation + reconstruction;

        eprintln!(
            "{label} ({CHECK_SAMPLES} check samples, {SAMPLES} reconstruction samples): generated={} bytes, egraph={} enodes, normal-check={saturation:?}, serialization+indexing={serialization:?}, egraph-matching+proof-search+verification={search_and_verification:?}, posthoc={reconstruction:?}, estimated-total={total:?} ({:.4}x normal), stats={:?}",
            run.generated_program.len(),
            snapshot.nodes.len(),
            total.as_secs_f64() / saturation.as_secs_f64(),
            diagnostic.stats,
        );
        (saturation, reconstruction)
    }

    benchmark_case("QF_UF t37 eq-symm", run_qf_uf_t37, encoded_eq_symm_rule());
    benchmark_case(
        "QF_UF t3 bool-double-not-elim",
        run_qf_uf_double_not_t3,
        encoded_bool_double_not_elim_rule(),
    );
}

fn raw_qf_uf_program(lhs: &Term, rhs: &Term) -> String {
    format!(
        r#"
(datatype Term
  (Const String)
  (Var i64 Term)
  (Sort Term)
  (Empty)
  (Args Term Term)
  (Mk Term))
(constructor @= (Term) Term)
(rewrite
  (Mk (@= (Args (Mk t1) (Args (Mk s1) (Empty)))))
  (Mk (@= (Args (Mk s1) (Args (Mk t1) (Empty)))))
  :name "eq-symm")
(let $lhs {})
(let $rhs {})
(run 1)
"#,
        lhs.to_egglog(),
        rhs.to_egglog(),
    )
}

fn raw_qf_uf_double_not_program(lhs: &Term, rhs: &Term) -> String {
    format!(
        r#"
(datatype Term
  (Const String)
  (Var i64 Term)
  (Sort Term)
  (Empty)
  (Args Term Term)
  (Mk Term))
(constructor @not (Term) Term)
(rewrite
  (Mk (@not (Args (Mk (@not (Args (Mk t1) (Empty)))) (Empty))))
  (Mk t1)
  :name "bool-double-not-elim")
(let $lhs {})
(let $rhs {})
(run 1)
"#,
        lhs.to_egglog(),
        rhs.to_egglog(),
    )
}

#[test]
#[ignore = "diagnostic comparison using only raw QF_UF rewrite rules"]
fn compare_real_qf_uf_raw_rules_posthoc_with_egglog_proofs() {
    const SAMPLES: usize = 100;

    fn median(mut samples: Vec<Duration>) -> Duration {
        samples.sort_unstable();
        samples[samples.len() / 2]
    }

    fn run_normal(program: &str) -> (ProofEGraph, Duration) {
        let mut egraph = ProofEGraph::new(1);
        let start = Instant::now();
        egraph
            .parse_and_run_program(None, program)
            .expect("raw QF_UF program should saturate");
        (egraph, start.elapsed())
    }

    fn run_proofs(program: &str) -> Duration {
        let mut egraph = ProofEGraph::new_with_proofs();
        let program = format!("{program}\n(prove (= $lhs $rhs))");
        let start = Instant::now();
        let outputs = egraph
            .parse_and_run_program(None, &program)
            .expect("raw QF_UF program should produce an egglog proof");
        assert!(
            outputs
                .iter()
                .any(|output| matches!(output, CommandOutput::ProveExists { .. }))
        );
        start.elapsed()
    }

    fn benchmark_case(label: &str, program: &str, lhs: &Term, rhs: &Term, rules: &[Rewrite]) {
        let (saturated, _) = run_normal(program);
        run_normal(program);
        run_proofs(program);
        let snapshot = EGraphSnapshot::capture(&saturated);
        let diagnostic =
            reconstruct_detailed(&snapshot, lhs, rhs, rules, SearchStrategy::default());
        assert!(diagnostic.certificate.unwrap().verify(rules));

        let normal = median((0..SAMPLES).map(|_| run_normal(program).1).collect());
        let reconstruction = median(
            (0..SAMPLES)
                .map(|_| {
                    let start = Instant::now();
                    let snapshot = EGraphSnapshot::capture(&saturated);
                    let reconstruction =
                        reconstruct_detailed(&snapshot, lhs, rhs, rules, SearchStrategy::default());
                    assert!(reconstruction.certificate.unwrap().verify(rules));
                    start.elapsed()
                })
                .collect(),
        );
        let posthoc = normal + reconstruction;
        let proofs = median((0..SAMPLES).map(|_| run_proofs(program)).collect());

        eprintln!(
            "{label} ({SAMPLES} samples): normal={normal:?}, reconstruction={reconstruction:?}, posthoc={posthoc:?} ({:.2}x normal), egglog-proofs={proofs:?} ({:.2}x normal, {:.2}x posthoc), stats={:?}",
            posthoc.as_secs_f64() / normal.as_secs_f64(),
            proofs.as_secs_f64() / normal.as_secs_f64(),
            proofs.as_secs_f64() / posthoc.as_secs_f64(),
            diagnostic.stats,
        );
    }

    let eq_symm = run_qf_uf_t37();
    let eq_symm_program = raw_qf_uf_program(&eq_symm.lhs, &eq_symm.rhs);
    benchmark_case(
        "raw QF_UF eq-symm",
        &eq_symm_program,
        &eq_symm.lhs,
        &eq_symm.rhs,
        &[encoded_eq_symm_rule()],
    );

    let double_not = run_qf_uf_double_not_t3();
    let double_not_program = raw_qf_uf_double_not_program(&double_not.lhs, &double_not.rhs);
    benchmark_case(
        "raw QF_UF bool-double-not-elim",
        &double_not_program,
        &double_not.lhs,
        &double_not.rhs,
        &[encoded_bool_double_not_elim_rule()],
    );
}
