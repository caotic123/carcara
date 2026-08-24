use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fs::File,
    io::BufReader,
    path::{Path, PathBuf},
    time::{Duration, Instant},
};

use carcara::{
    ast::ProofNode,
    parser,
    rare::engine::{run_egglog, RunEgglogOptions},
};
use egglog::{
    ast::{Action as EgglogAction, Command as EgglogCommand, Expr as EgglogExpr, GenericExpr},
    EGraph as ProductionEGraph, SerializeConfig as ProductionSerializeConfig,
};
use egglog_proofs::{
    CommandOutput, EGraph as ProofEGraph, SerializeConfig as ProofSerializeConfig,
};

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

#[derive(Clone, Debug)]
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
    recursive_obligations: usize,
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
            | Self::Symm { lhs, .. }
            | Self::Congruence { lhs, .. }
            | Self::Trans { lhs, .. } => lhs,
        }
    }

    fn rhs(&self) -> &Term {
        match self {
            Self::Refl { term } => term,
            Self::Rule { rhs, .. }
            | Self::Symm { rhs, .. }
            | Self::Congruence { rhs, .. }
            | Self::Trans { rhs, .. } => rhs,
        }
    }

    fn rule_names(&self, names: &mut Vec<String>) {
        match self {
            Self::Refl { .. } => {}
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
            Self::Refl { .. } | Self::Rule { .. } => false,
        }
    }

    fn verify(&self, rules: &[Rewrite]) -> bool {
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
            Self::Symm { lhs, rhs, proof } => {
                proof.verify(rules) && proof.lhs() == rhs && proof.rhs() == lhs
            }
            Self::Congruence { lhs, rhs, child_index, child } => {
                child.verify(rules)
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
                first.verify(rules)
                    && second.verify(rules)
                    && first.lhs() == lhs
                    && first.rhs() == middle
                    && second.lhs() == middle
                    && second.rhs() == rhs
            }
        }
    }
}

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

/// Follow parent pointers from `vertex` up to a search root, collecting the
/// edges in root-ward order.
fn walk_back(parents: &HashMap<Term, (Term, Certificate)>, mut vertex: Term) -> Vec<Certificate> {
    let mut edges = Vec::new();
    while let Some((parent, edge)) = parents.get(&vertex) {
        edges.push(edge.clone());
        vertex = parent.clone();
    }
    edges
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
    representatives: HashMap<u32, Term>,
    terms_by_class: HashMap<u32, Vec<Term>>,
    term_classes: HashMap<Term, u32>,
    rule_edges_by_class: HashMap<u32, Vec<Certificate>>,
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

    /// Recover all instances of all supplied rules whose two sides are
    /// represented in `eclass` under one shared e-class substitution. This is
    /// the post-hoc analogue of a relational multi-pattern E-match:
    ///
    ///   Q_rule(root, subst) :- match(lhs, root, subst),
    ///                           match(rhs, root, subst).
    fn rule_edges(&mut self, eclass: u32) -> Vec<Certificate> {
        if let Some(edges) = self.rule_edges_by_class.get(&eclass) {
            return edges.clone();
        }

        let mut edges = Vec::new();
        let mut seen = HashSet::new();
        let rules = self.rules.to_vec();
        for rule in &rules {
            let lhs_matches = self.snapshot.ematch_in_class(
                &rule.lhs,
                eclass,
                &ClassSubstitution::new(),
                &mut self.stats,
            );
            self.stats.lhs_matches += lhs_matches.len();

            for lhs_substitution in lhs_matches {
                // Matching the RHS with the LHS substitution and the same
                // root class is what makes this use the saturated e-graph as
                // the source of candidate rule instances.
                let rhs_matches = self.snapshot.ematch_in_class(
                    &rule.rhs,
                    eclass,
                    &lhs_substitution,
                    &mut self.stats,
                );
                for class_substitution in rhs_matches {
                    let mut substitution = Substitution::new();
                    let mut complete = true;
                    for (variable, class) in class_substitution {
                        let Some(term) = self.representative(class) else {
                            complete = false;
                            break;
                        };
                        substitution.insert(variable.to_owned(), term);
                    }
                    if !complete {
                        continue;
                    }
                    let Some(lhs) = instantiate(&rule.lhs, &substitution) else {
                        continue;
                    };
                    let Some(rhs) = instantiate(&rule.rhs, &substitution) else {
                        continue;
                    };
                    if lhs == rhs
                        || self.snapshot.class_of_term(&lhs) != Some(eclass)
                        || self.snapshot.class_of_term(&rhs) != Some(eclass)
                        || !seen.insert((rule.name, lhs.clone(), rhs.clone()))
                    {
                        continue;
                    }

                    let certificate = Certificate::Rule {
                        name: rule.name.to_owned(),
                        lhs,
                        rhs,
                        substitution,
                    };
                    assert!(
                        certificate.verify(self.rules),
                        "an E-matched candidate must still pass the independent rule checker"
                    );
                    edges.push(certificate);
                }
            }
        }
        self.stats.rule_instances += edges.len();
        self.rule_edges_by_class.insert(eclass, edges.clone());
        edges
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

    fn prove_in_class(&mut self, source: &Term, target: &Term, eclass: u32) -> Option<Certificate> {
        // Congruence-first fast path: equal head symbols with children in
        // pairwise-equal classes are decomposed directly, without touching
        // the rule index.
        if source.op == target.op
            && source.children.len() == target.children.len()
            && self.congruence_compatible(source, target)
        {
            if let Some(certificate) = self.congruence_certificate(source, target) {
                return Some(certificate);
            }
        }

        let rule_edges = self.rule_edges(eclass);
        let mut vertices = vec![source.clone(), target.clone()];
        for edge in &rule_edges {
            vertices.push(edge.lhs().clone());
            vertices.push(edge.rhs().clone());
        }
        let mut seen_vertices = HashSet::new();
        vertices.retain(|vertex| seen_vertices.insert(vertex.clone()));
        self.stats.candidate_vertices += vertices.len();
        if vertices.len() > self.strategy.max_states {
            return None;
        }

        let mut adjacency: HashMap<Term, Vec<(Term, Certificate)>> = HashMap::new();
        for edge in rule_edges {
            adjacency
                .entry(edge.lhs().clone())
                .or_default()
                .push((edge.rhs().clone(), edge.clone()));
            let reversed = reverse(edge);
            adjacency
                .entry(reversed.lhs().clone())
                .or_default()
                .push((reversed.rhs().clone(), reversed));
        }

        // Congruence partners grouped by head symbol, so expansion only
        // compares vertices that can actually be congruent.
        let mut vertices_by_op: HashMap<&str, Vec<usize>> = HashMap::new();
        for (index, vertex) in vertices.iter().enumerate() {
            vertices_by_op
                .entry(vertex.op.as_str())
                .or_default()
                .push(index);
        }

        // Bidirectional breadth-first search over the candidate c-graph.
        // Side 0 grows from source, side 1 from target; the smaller frontier
        // is expanded one level at a time until the two meet.
        let mut congruence_expanded = HashSet::new();
        let mut parents: [HashMap<Term, (Term, Certificate)>; 2] = [HashMap::new(), HashMap::new()];
        let mut depths: [HashMap<Term, usize>; 2] = [HashMap::new(), HashMap::new()];
        depths[0].insert(source.clone(), 0);
        depths[1].insert(target.clone(), 0);
        let mut frontiers = [vec![source.clone()], vec![target.clone()]];

        while !frontiers[0].is_empty() && !frontiers[1].is_empty() {
            let side = usize::from(frontiers[0].len() > frontiers[1].len());
            let frontier = std::mem::take(&mut frontiers[side]);
            let mut next = Vec::new();
            for vertex in frontier {
                let depth = depths[side][&vertex];
                if depth >= self.strategy.max_depth {
                    continue;
                }
                self.ensure_neighbors(
                    &vertex,
                    &mut adjacency,
                    &mut congruence_expanded,
                    &vertices_by_op,
                    &vertices,
                );
                for (neighbour, edge) in adjacency.get(&vertex).into_iter().flatten() {
                    if depths[side].contains_key(neighbour) {
                        continue;
                    }
                    // Backward-side edges point towards the target: store the
                    // reversed certificate so parent walks always follow the
                    // certificate direction.
                    let edge = if side == 0 {
                        edge.clone()
                    } else {
                        reverse(edge.clone())
                    };
                    parents[side].insert(neighbour.clone(), (vertex.clone(), edge));
                    depths[side].insert(neighbour.clone(), depth + 1);
                    if let Some(&other_depth) = depths[1 - side].get(neighbour) {
                        if depth + 1 + other_depth <= self.strategy.max_depth {
                            let mut first = walk_back(&parents[0], neighbour.clone());
                            first.reverse();
                            let second = walk_back(&parents[1], neighbour.clone());
                            let steps = first.into_iter().chain(second).collect();
                            return Some(chain(source.clone(), steps));
                        }
                    }
                    next.push(neighbour.clone());
                }
            }
            frontiers[side] = next;
        }
        None
    }

    /// Ensure the adjacency map holds every out-neighbour of a vertex: the
    /// rule edges, plus congruence edges to same-head vertices.  Congruence
    /// edges are generated on a vertex's first expansion — so child proof
    /// obligations are only incurred for vertices the search actually
    /// reaches — and are cached in both directions, so each pair is attempted
    /// at most once.
    fn ensure_neighbors(
        &mut self,
        vertex: &Term,
        adjacency: &mut HashMap<Term, Vec<(Term, Certificate)>>,
        congruence_expanded: &mut HashSet<Term>,
        vertices_by_op: &HashMap<&str, Vec<usize>>,
        vertices: &[Term],
    ) {
        if !congruence_expanded.insert(vertex.clone()) {
            return;
        }
        let mut edges = Vec::new();
        if let Some(partners) = vertices_by_op.get(vertex.op.as_str()) {
            for &index in partners {
                let other = &vertices[index];
                if other == vertex {
                    continue;
                }
                if let Some(edge) = self.congruence_certificate(vertex, other) {
                    edges.push((other.clone(), edge));
                }
            }
        }
        for (other, edge) in edges {
            let reversed = reverse(edge.clone());
            adjacency
                .entry(other.clone())
                .or_default()
                .push((vertex.clone(), reversed));
            adjacency
                .entry(vertex.clone())
                .or_default()
                .push((other, edge));
        }
    }
}

fn reconstruct_detailed(
    snapshot: &EGraphSnapshot,
    source: &Term,
    target: &Term,
    rules: &[Rewrite],
    strategy: SearchStrategy,
) -> ReconstructionResult {
    if !snapshot.same_class(source, target) {
        return ReconstructionResult {
            certificate: None,
            stats: ReconstructionStats::default(),
        };
    }

    let mut reconstructor = Reconstructor {
        snapshot,
        rules,
        strategy,
        representatives: snapshot.preferred_representatives([source, target]),
        terms_by_class: HashMap::new(),
        term_classes: HashMap::new(),
        rule_edges_by_class: HashMap::new(),
        memo: HashMap::new(),
        in_progress: HashSet::new(),
        prune_events: 0,
        stats: ReconstructionStats::default(),
    };
    reconstructor.seed_goal_terms(source);
    reconstructor.seed_goal_terms(target);
    let certificate = reconstructor.prove(source, target);
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
    assert!(reconstruct(
        &snapshot,
        &source(),
        &target(),
        &rules[..1],
        SearchStrategy::default(),
    )
    .is_none());

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
        assert!(outputs
            .iter()
            .any(|output| matches!(output, CommandOutput::ProveExists { .. })));
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

struct QfUfRun {
    egraph: ProductionEGraph,
    generated_program: String,
    lhs: Term,
    rhs: Term,
    saturation: Duration,
}

fn run_qf_uf_case(
    problem_relative: &str,
    proof_relative: &str,
    root_id: &str,
    required_rule: &str,
) -> QfUfRun {
    let problem_path = repository_path(problem_relative);
    let proof_path = repository_path(proof_relative);
    let rare_path = repository_path("tests/rare/big.rare");
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
    assert!(
        database.rules.contains_key(required_rule),
        "the real RARE database should contain the rule being reconstructed"
    );
    let node = ProofNode::from_commands_with_root_id(proof.commands, root_id)
        .expect("sliced proof should contain the requested root");
    let conclusion = node.clause()[0].clone();

    let start = Instant::now();
    let (result, generated_program) = run_egglog(
        &mut pool,
        (conclusion, &node),
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
    }
}

fn run_qf_uf_t37() -> QfUfRun {
    run_qf_uf_case(
        "tests/rare/sliced_proofs/Examples/QF_UF/2018-Goel-hwbench/\
         QF_UF_brp.5.prop1_ab_reg_max/QF_UF_brp.5.prop1_ab_reg_max.smt2",
        "tests/rare/sliced_proofs/Examples/QF_UF/2018-Goel-hwbench/\
         QF_UF_brp.5.prop1_ab_reg_max/\
         QF_UF_brp.5.prop1_ab_reg_max__from-t37.smt2.alethe",
        "t37",
        "eq-symm",
    )
}

fn run_qf_uf_double_not_t3() -> QfUfRun {
    run_qf_uf_case(
        "tests/rare/sliced_proofs/Examples/QF_UF/20170829-Rodin/\
         smt249825283571301584/smt249825283571301584.smt2",
        "tests/rare/sliced_proofs/Examples/QF_UF/20170829-Rodin/\
         smt249825283571301584/smt249825283571301584__from-t3.smt2.alethe",
        "t3",
        "bool-double-not-elim",
    )
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
    assert!(reconstruct(
        &snapshot,
        &run.lhs,
        &run.rhs,
        &[],
        SearchStrategy::default(),
    )
    .is_none());

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
    assert!(reconstruct(
        &snapshot,
        &run.lhs,
        &run.rhs,
        &[],
        SearchStrategy::default(),
    )
    .is_none());

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
        assert!(outputs
            .iter()
            .any(|output| matches!(output, CommandOutput::ProveExists { .. })));
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
