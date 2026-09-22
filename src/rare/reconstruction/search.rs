//! Candidate-graph search reconstructing a certificate from a snapshot.
use super::*;
use std::{
    collections::{BTreeSet, HashMap, HashSet},
    rc::Rc,
    time::Instant,
};

/// Operators belonging to the egglog solvers' internal machinery
/// (computation tables, demand relations, ACI set forms) rather than to the
/// proof term language.  They appear in the serialized snapshot co-classed
/// with real terms and must be ignored by term extraction.
/// How deep a class constant may be: `Mk`, the constructor, the literal.
pub const CONSTANT_DEPTH: usize = 3;

pub const INTERNAL_OPS: [&str; 12] = [
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
pub const ARITH_CANDIDATE_OPS: [&str; 12] = [
    "@+", "@-", "@*", "@/", "@/_total", "@to_real", "@=", "@<", "@<=", "@>", "@>=", "@not",
];

#[derive(Clone, Copy, Debug)]
pub struct SearchStrategy {
    pub max_depth: usize,
    pub max_states: usize,
    /// Wall-clock instant past which the search abandons the goal, reusing
    /// the same over-budget path as `max_states`.  The egglog check and this
    /// search are separate phases of one per-hole budget, so a bound on the
    /// former alone leaves the latter free to run away.
    pub deadline: Option<Instant>,
}

impl Default for SearchStrategy {
    fn default() -> Self {
        Self {
            max_depth: 8,
            max_states: 256,
            deadline: None,
        }
    }
}

impl SearchStrategy {
    pub fn with_deadline(self, deadline: Option<Instant>) -> Self {
        Self { deadline, ..self }
    }

    fn out_of_time(&self) -> bool {
        self.deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
    }
}

/// Follow parent pointers from `vertex` up to a search root, collecting
/// `(parent, child, edge)` triples in root-ward order.
pub fn walk_edges(
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum InstanceSide {
    Lhs,
    Rhs,
}

/// One relational match of a rule, discovered from a visited signature:
/// variable-to-class bindings plus which side carried the signature.  No
/// representative has been extracted and no term built.
pub struct SignatureMatch {
    pub rule_index: usize,
    pub substitution: ClassSubstitution,
    pub anchored: InstanceSide,
}

/// One grounded rule instance: `lhs = rhs` under `substitution`, with both
/// sides in the same e-class.  Kept as plain data; a `Certificate` is only
/// built once a search actually traverses the corresponding edge.
#[derive(Clone, Debug)]
pub struct RuleInstance {
    pub rule: &'static str,
    pub lhs: Term,
    pub rhs: Term,
    pub substitution: Substitution,
}

impl RuleInstance {
    pub fn certificate(&self) -> Certificate {
        Certificate::Rule {
            name: self.rule.to_owned(),
            lhs: self.lhs.clone(),
            rhs: self.rhs.clone(),
            substitution: self.substitution.clone(),
        }
    }
}

/// One symbol of a p-string: an operator interned by the snapshot, with the
/// arity it is applied at, or the `*` every variable collapses to.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PSymbol {
    Op(u32, usize),
    Star,
}

/// The p-string of a pattern: its preorder symbol string with variables
/// collapsed to `*`.  `None` when the pattern uses an operator the snapshot
/// never interned — such a side occurs nowhere in the e-graph and can match
/// no e-node.
pub fn p_string(pattern: &Pattern, ops: &Interner, out: &mut Vec<PSymbol>) -> Option<()> {
    match pattern {
        Pattern::Var(_) => out.push(PSymbol::Star),
        Pattern::App(op, children) => {
            out.push(PSymbol::Op(*ops.ids.get(*op)?, children.len()));
            for child in children {
                p_string(child, ops, out)?;
            }
        }
    }
    Some(())
}

/// Standard discrimination tree over the rule pattern sides, built once per
/// reconstruction (Sekar, Ramakrishnan and Voronkov, "Term Indexing",
/// Handbook of Automated Reasoning, vol. 2, ch. 26): p-strings are encoded
/// in a trie, and the node ending a side's p-string stores that side.
/// Filtering is imperfect, as in the chapter's standard tree — variable
/// identities are dropped, so retrieval yields a candidate superset that
/// the exact e-matcher must confirm.
#[derive(Debug)]
pub struct DiscriminationTree {
    pub nodes: Vec<DtNode>,
}

#[derive(Debug, Default)]
pub struct DtNode {
    pub children: HashMap<PSymbol, u32>,
    /// Rule sides whose p-string ends at this node.
    pub entries: Vec<(usize, InstanceSide)>,
}

impl DiscriminationTree {
    pub fn build(rules: &[Rewrite], ops: &Interner) -> Self {
        let mut tree = Self { nodes: vec![DtNode::default()] };
        for (rule_index, rule) in rules.iter().enumerate() {
            for (side, pattern) in [
                (InstanceSide::Lhs, &rule.lhs),
                (InstanceSide::Rhs, &rule.rhs),
            ] {
                let mut string = Vec::new();
                if p_string(pattern, ops, &mut string).is_some() {
                    tree.insert(&string, (rule_index, side));
                }
            }
        }
        tree
    }

    /// Insertion: walk the p-string from the root, adding a node for every
    /// missing edge; the entry is stored where its string ends.
    pub fn insert(&mut self, string: &[PSymbol], entry: (usize, InstanceSide)) {
        let mut node = 0;
        for &symbol in string {
            node = match self.nodes[node].children.get(&symbol) {
                Some(&next) => next as usize,
                None => {
                    let next = self.nodes.len();
                    self.nodes.push(DtNode::default());
                    self.nodes[node].children.insert(symbol, next as u32);
                    next
                }
            };
        }
        self.nodes[node].entries.push(entry);
    }

    /// Retrieval of generalizations, anchored at an e-node: the signature
    /// is the query's first symbol and its child classes the rest of the
    /// preorder.  The root `*` edge skips the whole query term, reaching
    /// the bare-variable sides directly.
    pub fn candidates_at_signature(
        &self,
        snapshot: &EGraphSnapshot,
        signature: &Signature,
        stats: &mut ReconstructionStats,
    ) -> BTreeSet<(usize, InstanceSide)> {
        let mut candidates = BTreeSet::new();
        let root = &self.nodes[0];
        if let Some(&node) = root.children.get(&PSymbol::Star) {
            candidates.extend(self.nodes[node as usize].entries.iter().copied());
        }
        let (op, child_classes) = signature;
        if let Some(&node) = root.children.get(&PSymbol::Op(*op, child_classes.len())) {
            let mut pending: Vec<u32> = child_classes.iter().rev().copied().collect();
            self.retrieve(
                snapshot,
                node as usize,
                &mut pending,
                &mut candidates,
                stats,
            );
        }
        stats.index_candidates += candidates.len();
        candidates
    }

    /// The chapter's backtracking traversal, with the query read off the
    /// e-graph instead of a flatterm: `pending` is the preorder stack of
    /// e-classes still to be matched, front on top.  A symbol edge consumes
    /// one e-node of the front class and exposes its children — the
    /// flatterm's `next` — while a `*` edge pops the front class whole —
    /// its `after`, constant-time here because a class is exactly one query
    /// subterm.  A node reached with the stack empty ends the query, and
    /// its entries are candidates.
    pub fn retrieve(
        &self,
        snapshot: &EGraphSnapshot,
        node: usize,
        pending: &mut Vec<u32>,
        candidates: &mut BTreeSet<(usize, InstanceSide)>,
        stats: &mut ReconstructionStats,
    ) {
        let Some(&eclass) = pending.last() else {
            candidates.extend(self.nodes[node].entries.iter().copied());
            return;
        };
        for (&symbol, &child) in &self.nodes[node].children {
            match symbol {
                PSymbol::Star => {
                    pending.pop();
                    self.retrieve(snapshot, child as usize, pending, candidates, stats);
                    pending.push(eclass);
                }
                PSymbol::Op(op, arity) => {
                    let Some(rows) = snapshot.class_op_nodes.get(&(eclass, op)) else {
                        continue;
                    };
                    for &index in rows {
                        stats.relation_rows_examined += 1;
                        let enode = &snapshot.nodes[index as usize];
                        if enode.child_classes.len() != arity {
                            continue;
                        }
                        pending.pop();
                        pending.extend(enode.child_classes.iter().rev());
                        self.retrieve(snapshot, child as usize, pending, candidates, stats);
                        pending.truncate(pending.len() - arity);
                        pending.push(eclass);
                    }
                }
            }
        }
    }
}

/// An unjustified equality candidate between two terms of the class,
/// trusted from the e-graph during the search.  Justification into a
/// `Certificate` happens only for edges on the chosen path.
#[derive(Clone, Debug)]
pub enum CandidateEdge {
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
    /// `and`/`or` endpoints whose literal sets differ only in literals the
    /// e-graph unioned; justified by `aci_simp` on the matching literals and
    /// in-class proofs of the unioned ones.
    AciModulo,
}

/// Per-obligation search state over the candidate c-graph.  Vertices and
/// edges are discovered lazily: expanding a vertex looks up, by root
/// signature, the class-level matches that can touch it, and only those are
/// grounded into terms.
pub struct CandidateGraph {
    pub eclass: u32,
    pub source: Term,
    pub target: Term,
    /// Ground terms discovered so far, counted against `max_states`.
    pub discovered: HashSet<Term>,
    pub over_budget: bool,
    /// Expanded vertex -> its out-edges `(neighbour, candidate)`.
    pub adjacency: HashMap<Term, Vec<(Term, CandidateEdge)>>,
    /// Candidate edges (both orientations) that failed to justify on an
    /// earlier met path of this obligation.
    pub banned: HashSet<(Term, Term)>,
}

/// One half of the bidirectional search: a tree of visited terms rooted at
/// the proof's source or at its target.
pub struct SearchTree {
    pub frontier: Vec<Term>,
    pub depths: HashMap<Term, usize>,
    pub parents: HashMap<Term, (Term, CandidateEdge)>,
}

impl SearchTree {
    pub fn rooted_at(root: &Term) -> Self {
        Self {
            frontier: vec![root.clone()],
            depths: HashMap::from([(root.clone(), 0)]),
            parents: HashMap::new(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct ReconstructionResult {
    pub certificate: Option<Certificate>,
    pub stats: ReconstructionStats,
}

pub struct Reconstructor<'a> {
    pub snapshot: &'a EGraphSnapshot,
    pub rules: &'a [Rewrite],
    /// Discrimination tree over the rule pattern sides, built once; match
    /// discovery retrieves candidate sides from it instead of scanning the
    /// rule list.
    pub pattern_index: DiscriminationTree,
    pub strategy: SearchStrategy,
    /// Sort facts for the arithmetic strategy and checkers.
    pub sorts: &'a ArithSorts,
    pub representatives: HashMap<u32, Term>,
    pub terms_by_class: HashMap<u32, Vec<Term>>,
    pub term_classes: HashMap<Term, u32>,
    /// Signature-anchored match discovery, memoized per (class, signature).
    pub matches_by_signature: HashMap<(u32, Signature), Rc<Vec<SignatureMatch>>>,
    /// Grounded matches, memoized by their class-level bindings; `None`
    /// records a match that failed to ground.
    pub grounded_matches:
        HashMap<(u32, usize, ClassSubstitution, Option<Term>), Option<Rc<RuleInstance>>>,
    pub memo: HashMap<(Term, Term), Option<Certificate>>,
    pub in_progress: HashSet<(Term, Term)>,
    pub prune_events: usize,
    pub stats: ReconstructionStats,
}

impl Reconstructor<'_> {
    pub fn class_of(&mut self, term: &Term) -> Option<u32> {
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
    pub fn seed_goal_terms(&mut self, term: &Term) {
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

    pub fn representative(&mut self, eclass: u32) -> Option<Term> {
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

    /// A constant of a class, built only from the constant constructors, or
    /// `None` when the class holds no constant.  Deliberately not
    /// `extract_representative`: that one answers with the goal's own
    /// subterm whenever the class has one, which is exactly the term the
    /// caller already has.
    pub fn class_constant(&self, eclass: u32, depth: usize) -> Option<Term> {
        if depth == 0 {
            return None;
        }
        for &index in self.snapshot.class_nodes.get(eclass as usize)?.iter() {
            let node = &self.snapshot.nodes[index as usize];
            let op = self.snapshot.ops.names[node.op as usize].as_str();
            if node.child_classes.is_empty() {
                return Some(Term::leaf(op));
            }
            if !matches!(op, "Mk" | "Bool" | "Num" | "Real" | "RatConst") {
                continue;
            }
            let children: Option<Vec<Term>> = node
                .child_classes
                .iter()
                .map(|&child| self.class_constant(child, depth - 1))
                .collect();
            if let Some(children) = children {
                return Some(Term::new(op, children));
            }
        }
        None
    }

    pub fn extract_representative(
        &mut self,
        eclass: u32,
        visiting: &mut HashSet<u32>,
    ) -> Option<Term> {
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
    /// Candidate sides are retrieved from the discrimination tree rather
    /// than by scanning the rule list, and the whole query is memoized per
    /// (class, signature) — so discovery cost follows the vertices the
    /// search visits, not the number of rules times the number of e-nodes
    /// in the class.
    pub fn matches_at_signature(
        &mut self,
        eclass: u32,
        signature: &Signature,
    ) -> Rc<Vec<SignatureMatch>> {
        let key = (eclass, signature.clone());
        if let Some(matches) = self.matches_by_signature.get(&key) {
            return matches.clone();
        }

        let mut matches = Vec::new();
        // Candidate sides come from the discrimination tree — an imperfect
        // filter, so each retrieved side still goes through the exact
        // anchored e-match below.  Sides the tree does not return match no
        // e-node of the signature and are exactly the ones the old rule
        // scan rejected one by one.
        let candidates =
            self.pattern_index
                .candidates_at_signature(self.snapshot, signature, &mut self.stats);
        for (rule_index, anchored) in candidates {
            let rule = &self.rules[rule_index];
            let (side, other) = match anchored {
                InstanceSide::Lhs => (&rule.lhs, &rule.rhs),
                InstanceSide::Rhs => (&rule.rhs, &rule.lhs),
            };
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
        let matches = Rc::new(matches);
        self.matches_by_signature.insert(key, matches.clone());
        matches
    }

    /// Matches of one side pattern whose grounded root will carry
    /// `signature`.  An applied pattern anchors on the signature's child
    /// classes directly; a bare-variable side grounds to the class
    /// representative, so it anchors exactly when the representative carries
    /// the signature — one extraction for the class being searched.
    pub fn side_matches_at_signature(
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

    pub fn representative_signature(&mut self, eclass: u32) -> Option<Signature> {
        let representative = self.representative(eclass)?;
        self.term_signature(&representative)
    }

    /// E-class a fully substituted pattern grounds into, resolved bottom-up
    /// through the signature relation without building any term.
    pub fn pattern_class(
        &self,
        pattern: &Pattern,
        substitution: &ClassSubstitution,
    ) -> Option<u32> {
        match pattern {
            Pattern::Var(variable) => substitution.get(variable).copied(),
            Pattern::App(op, children) => {
                let &op = self.snapshot.ops.ids.get(*op)?;
                let child_classes = children
                    .iter()
                    .map(|child| self.pattern_class(child, substitution))
                    .collect::<Option<Vec<_>>>()?;
                self.snapshot
                    .signature_class
                    .get(&(op, child_classes))
                    .copied()
            }
        }
    }

    pub fn term_signature(&mut self, term: &Term) -> Option<Signature> {
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
    pub fn grounded_match(
        &mut self,
        eclass: u32,
        class_match: &SignatureMatch,
        vertex: &Term,
    ) -> Option<Rc<RuleInstance>> {
        // A side that is a bare variable matches the class as a whole; it
        // is grounded to the vertex the search stands on, so the instance
        // is a rule edge out of that vertex.  Grounded to the class
        // representative instead, it read as a "congruence" between the
        // vertex and the representative, an edge no child proof justifies
        // when the two have different heads: `(= (= false x) (not x))` was
        // lost that way, though `eq-symm` and `bool-eq-false` prove it.
        let rule = &self.rules[class_match.rule_index];
        let anchored_side = match class_match.anchored {
            InstanceSide::Lhs => &rule.lhs,
            InstanceSide::Rhs => &rule.rhs,
        };
        let pinned = match anchored_side {
            Pattern::Var(variable) => Some((*variable, vertex.clone())),
            Pattern::App(..) => None,
        };
        let key = (
            eclass,
            class_match.rule_index,
            class_match.substitution.clone(),
            pinned.as_ref().map(|(_, term)| term.clone()),
        );
        if let Some(instance) = self.grounded_matches.get(&key) {
            return instance.clone();
        }
        let instance = self
            .ground(rule, &class_match.substitution, eclass, pinned)
            .map(Rc::new);
        if instance.is_some() {
            self.stats.rule_instances += 1;
        }
        self.grounded_matches.insert(key, instance.clone());
        instance
    }

    pub fn ground(
        &mut self,
        rule: &Rewrite,
        class_substitution: &ClassSubstitution,
        eclass: u32,
        pinned: Option<(&str, Term)>,
    ) -> Option<RuleInstance> {
        let mut substitution = Substitution::new();
        for (variable, &class) in class_substitution {
            substitution.insert((*variable).to_owned(), self.representative(class)?);
        }
        if let Some((variable, term)) = pinned {
            substitution.insert(variable.to_owned(), term);
        }
        // A guarded variable bound to a term of another known sort is not an
        // instance: `arith-eq-elim-real` does not apply to integers.
        for (variable, sort) in &rule.guards {
            let Some(bound) = substitution.get(variable) else {
                continue;
            };
            // the pattern variable stands for the term under the `Mk` wrapper
            let wrapped = if bound.op == "Mk" {
                bound.clone()
            } else {
                Term::new("Mk", vec![bound.clone()])
            };
            if let Some(actual) = encoded_sort(&wrapped, self.sorts) {
                if actual != *sort {
                    log::debug!(
                        "guard: {} rejected, {variable} is {actual} not {sort}",
                        rule.name
                    );
                    return None;
                }
            }
        }
        let lhs = instantiate(&rule.lhs, &substitution)?;
        let rhs = instantiate(&rule.rhs, &substitution)?;
        (lhs != rhs
            && self.snapshot.class_of_term(&lhs) == Some(eclass)
            && self.snapshot.class_of_term(&rhs) == Some(eclass))
        .then(|| RuleInstance {
            rule: rule.name,
            lhs,
            rhs,
            substitution,
        })
    }

    pub fn congruence_compatible(&mut self, lhs: &Term, rhs: &Term) -> bool {
        if lhs.op != rhs.op || lhs.children.len() != rhs.children.len() {
            return false;
        }
        lhs.children.iter().zip(&rhs.children).all(|(lhs, rhs)| {
            matches!((self.class_of(lhs), self.class_of(rhs)), (Some(lhs), Some(rhs)) if lhs == rhs)
        })
    }

    /// Congruence compatibility one level below the wrapper: for two wrapped
    /// applications, the applications themselves must have one head and
    /// their argument lists one class.  The wrapper level alone is not
    /// enough for a term met through the class signature: the engine keeps
    /// the unwrapped terms of a class together, so every two wrapped members
    /// pass the wrapper's test, whatever their heads.
    pub fn inner_congruence_compatible(&mut self, lhs: &Term, rhs: &Term) -> bool {
        if lhs.op == "Mk" && rhs.op == "Mk" {
            if let ([inner_lhs], [inner_rhs]) = (lhs.children.as_slice(), rhs.children.as_slice())
            {
                return self.congruence_compatible(inner_lhs, inner_rhs);
            }
        }
        self.congruence_compatible(lhs, rhs)
    }

    pub fn congruence_certificate(&mut self, lhs: &Term, rhs: &Term) -> Option<Certificate> {
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

    pub fn prove(&mut self, source: &Term, target: &Term) -> Option<Certificate> {
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
    pub fn arith_candidates(&mut self, goal: &Term, eclass: u32) -> Vec<Term> {
        const LIMIT: usize = 64;
        let snapshot = self.snapshot;
        let mut candidates = vec![goal.clone()];
        let wrapper = snapshot.ops.ids.get("Mk").copied();
        for &index in snapshot
            .class_nodes
            .get(eclass as usize)
            .into_iter()
            .flatten()
        {
            let node = &snapshot.nodes[index as usize];
            let ([inner_class], true) = (node.child_classes.as_slice(), Some(node.op) == wrapper)
            else {
                continue;
            };
            for &inner in snapshot
                .class_nodes
                .get(*inner_class as usize)
                .into_iter()
                .flatten()
            {
                let inner = &snapshot.nodes[inner as usize];
                let operator = snapshot.ops.names[inner.op as usize].as_str();
                let ([arguments_class], true) = (
                    inner.child_classes.as_slice(),
                    ARITH_CANDIDATE_OPS.contains(&operator),
                ) else {
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
    pub fn prove_across_classes(&mut self, source: &Term, target: &Term) -> Option<Certificate> {
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
                let (Some(before), Some(after)) =
                    (self.prove(source, lhs), self.prove(rhs, target))
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

    pub fn prove_in_class(
        &mut self,
        source: &Term,
        target: &Term,
        eclass: u32,
    ) -> Option<Certificate> {
        // The computational strategies come after the rule search: a rule
        // path is a checkable certificate, while an arithmetic computation
        // still has to be routed into `poly_simp_rel` steps and may end up
        // trusted.
        self.prove_by_list_rule(source, target)
            .or_else(|| self.prove_by_congruence(source, target))
            .or_else(|| self.prove_by_transitivity(source, target, eclass))
            .or_else(|| self.prove_by_aci(source, target))
            .or_else(|| self.prove_by_arith(source, target))
            .or_else(|| self.prove_by_aci_modulo(source, target))
    }

    /// A rule whose `:list` parameters stand for segments of an n-ary
    /// operator's arguments.  The engine proves such a rule on the set form,
    /// where the segments have no positions to fill, and that leaves no
    /// rewrite for the search to follow; the instantiation is recovered here
    /// instead, by matching the rule's argument pattern against the term's
    /// arguments as a sequence.  Each list parameter binds the segment it
    /// covers, as an argument chain, which is what a `rare-list` argument of
    /// the emitted step spells out.
    pub fn prove_by_list_rule(&mut self, source: &Term, target: &Term) -> Option<Certificate> {
        let (operator, elements) = encoded_application(source)?;
        if !matches!(operator, "@and" | "@or") {
            return None;
        }
        for index in 0..self.rules.len() {
            let rule = &self.rules[index];
            if rule.lists.is_empty() {
                continue;
            }
            let Some(patterns) = argument_patterns(&rule.lhs, operator) else {
                continue;
            };
            let mut substitution = Substitution::new();
            if !match_sequence(&patterns, &elements, &rule.lists, &mut substitution) {
                continue;
            }
            let Some(instance) = instantiate(&rule.rhs, &substitution) else {
                continue;
            };
            if flat_form(&instance) != flat_form(target) {
                continue;
            }
            let rule = &self.rules[index];
            self.stats.rule_instances += 1;
            return Some(Certificate::Rule {
                name: rule.name.to_owned(),
                lhs: source.clone(),
                rhs: target.clone(),
                substitution,
            });
        }
        None
    }

    /// Arithmetic strategy inside a class: two relation (or polynomial)
    /// terms the e-graph unioned because their canonical keys agree -- the
    /// all-relations fallback merges a relation with its mirror image
    /// anywhere in a formula -- are one computational step, which the
    /// checker recomputes.
    pub fn prove_by_arith(&mut self, source: &Term, target: &Term) -> Option<Certificate> {
        let kind = arith_kind(source, target, self.sorts)?;
        self.stats.computational_edges += 1;
        Some(Certificate::Computational {
            kind,
            lhs: source.clone(),
            rhs: target.clone(),
        })
    }

    /// ACI strategy modulo the class: `and`/`or` sides whose literal sets
    /// differ only in literals the e-graph unioned (a bound and its mirror
    /// image, say).  The target is rewritten, at those literals, into the
    /// source's literals, which makes the sides ACI-equal; that intermediate
    /// is then proved congruent to the target literal by literal, without
    /// looking the intermediate up in the e-graph, where it need not exist.
    pub fn prove_by_aci_modulo(&mut self, source: &Term, target: &Term) -> Option<Certificate> {
        let (operator, replacement) = self.aci_modulo_pairs(source, target)?;
        for (literal, partner) in &replacement {
            if self.prove(partner, literal).is_none() {
                log::debug!("aci modulo: no in-class proof of {partner:?} = {literal:?}");
                return None;
            }
        }
        let rewritten = replace_literals(target, operator, &replacement);
        if !aci_equal(source, &rewritten) {
            log::debug!("aci modulo: rewritten target is not ACI-equal to the source");
            return None;
        }
        let first = Certificate::Computational {
            kind: Computation::AciNorm,
            lhs: source.clone(),
            rhs: rewritten.clone(),
        };
        let second = self.congruence_by_structure(&rewritten, target, &replacement);
        if second.is_none() {
            log::debug!("aci modulo: no congruence from the rewritten target to the target");
        }
        let second = second?;
        self.stats.computational_edges += 1;
        Some(chain(source.clone(), vec![first, second]))
    }

    /// For `and`/`or` sides whose literal sets differ, the pairing of each
    /// target-only literal with a source-only literal of its e-class (one
    /// each, every source-only literal used), without proving the pairs;
    /// with the operator.  `None` when the sides are not such a pair.
    fn aci_modulo_pairs(
        &mut self,
        source: &Term,
        target: &Term,
    ) -> Option<(&'static str, HashMap<Term, Term>)> {
        let (operator, identity) = match encoded_application(source) {
            Some(("@and", _)) => ("@and", true),
            Some(("@or", _)) => ("@or", false),
            _ => return None,
        };
        if !matches!(encoded_application(target), Some((op, _)) if op == operator) {
            return None;
        }
        let (mut left, mut right) = (Vec::new(), Vec::new());
        flatten_aci(source, operator, identity, &mut left);
        flatten_aci(target, operator, identity, &mut right);
        let left_set: HashSet<Term> = left.into_iter().collect();
        let right_set: HashSet<Term> = right.into_iter().collect();
        let unmatched_source: Vec<Term> = left_set.difference(&right_set).cloned().collect();
        let unmatched_target: Vec<Term> = right_set.difference(&left_set).cloned().collect();
        if unmatched_source.is_empty() || unmatched_target.is_empty() {
            return None;
        }
        let mut replacement: HashMap<Term, Term> = HashMap::new();
        let mut used: HashSet<Term> = HashSet::new();
        for literal in &unmatched_target {
            let class = self.class_of(literal)?;
            let partner = unmatched_source
                .iter()
                .find(|candidate| {
                    !used.contains(*candidate) && self.class_of(candidate) == Some(class)
                })
                .cloned();
            let Some(partner) = partner else {
                log::debug!(
                    "aci modulo: no source literal in the class of a target literal ({} source-only, {} target-only)",
                    unmatched_source.len(),
                    unmatched_target.len()
                );
                return None;
            };
            used.insert(partner.clone());
            replacement.insert(literal.clone(), partner);
        }
        if used.len() != unmatched_source.len() {
            log::debug!(
                "aci modulo: {} source-only literals left unpaired",
                unmatched_source.len() - used.len()
            );
            return None;
        }
        Some((operator, replacement))
    }

    /// The congruence proof of `from = to` for two terms that differ only at
    /// literals `replacement` maps (`to`'s literal to `from`'s), built along
    /// the structure without e-graph lookups; the literal pairs themselves
    /// are proved in their class.
    fn congruence_by_structure(
        &mut self,
        from: &Term,
        to: &Term,
        replacement: &HashMap<Term, Term>,
    ) -> Option<Certificate> {
        if from == to {
            return Some(Certificate::Refl { term: from.clone() });
        }
        if replacement.get(to) == Some(from) {
            return self.prove(from, to);
        }
        if from.op != to.op || from.children.len() != to.children.len() {
            return None;
        }
        let mut current = from.clone();
        let mut steps = Vec::new();
        for child_index in 0..current.children.len() {
            if current.children[child_index] == to.children[child_index] {
                continue;
            }
            let child = self.congruence_by_structure(
                &current.children[child_index],
                &to.children[child_index],
                replacement,
            )?;
            let mut children = current.children.clone();
            children[child_index] = to.children[child_index].clone();
            let next = Term::new(&current.op, children);
            steps.push(Certificate::Congruence {
                lhs: current.clone(),
                rhs: next.clone(),
                child_index,
                child: Box::new(child),
            });
            current = next;
        }
        Some(chain(from.clone(), steps))
    }

    /// ACI strategy: `and`/`or` obligations whose sides flatten to the same
    /// literal set are one computational step — the oracle derives these
    /// through its native set machinery, which leaves no rewrite trace the
    /// declarative search could follow.
    pub fn prove_by_aci(&mut self, source: &Term, target: &Term) -> Option<Certificate> {
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
    pub fn prove_by_congruence(&mut self, source: &Term, target: &Term) -> Option<Certificate> {
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
    pub fn prove_by_transitivity(
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
                if meet.is_some() || graph.over_budget || self.strategy.out_of_time() {
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
    pub fn justify_path(
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
            steps.push(step.ok_or_else(|| {
                log::debug!("path: {} edge {} = {} failed to justify", edge_kind(edge), parent.to_egglog(), child.to_egglog());
                (parent.clone(), child.clone())
            })?);
        }
        for (parent, child, edge) in &walk_edges(&backward.parents, meet) {
            let step = self.justify(parent, child, edge, true);
            steps.push(step.ok_or_else(|| {
                log::debug!("path: {} edge {} = {} failed to justify", edge_kind(edge), child.to_egglog(), parent.to_egglog());
                (parent.clone(), child.clone())
            })?);
        }
        Ok(chain(source.clone(), steps))
    }

    /// Turn one candidate edge into a certificate for parent = child, or
    /// child = parent when `flip` is set.  Rule candidates always succeed;
    /// congruence candidates recursively prove the differing children and
    /// may fail — the e-graph knew an equality the rules cannot replay, or a
    /// child search ran out of budget.
    pub fn justify(
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
                Some(if flip {
                    reverse(certificate)
                } else {
                    certificate
                })
            }
            CandidateEdge::AciModulo => {
                if flip {
                    self.prove_by_aci_modulo(child, parent)
                } else {
                    self.prove_by_aci_modulo(parent, child)
                }
            }
        }
    }

    /// Expand one breadth-first level of `near`, recording parent edges, and
    /// return the first vertex that `far` has also reached within the
    /// combined depth budget.
    pub fn expand_level(
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
            if graph.over_budget || self.strategy.out_of_time() {
                graph.over_budget = true;
                return None;
            }
        }
        None
    }

    /// The out-edges of a vertex, generated on its first expansion and
    /// memoized in the graph.  Terms discovered by grounding count against
    /// the `max_states` budget; crossing it marks the graph over budget.
    pub fn neighbors<'g>(
        &mut self,
        graph: &'g mut CandidateGraph,
        vertex: &Term,
    ) -> &'g [(Term, CandidateEdge)] {
        if !graph.adjacency.contains_key(vertex) {
            let edges = self.expand_vertex(graph, vertex);
            if graph.discovered.len() > self.strategy.max_states || self.strategy.out_of_time() {
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
    pub fn expand_vertex(
        &mut self,
        graph: &mut CandidateGraph,
        vertex: &Term,
    ) -> Vec<(Term, CandidateEdge)> {
        let mut edges = Vec::new();
        if let Some(signature) = self.term_signature(vertex) {
            let matches = self.matches_at_signature(graph.eclass, &signature);
            for class_match in matches.iter() {
                let Some(instance) = self.grounded_match(graph.eclass, class_match, vertex) else {
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
                    let rule = CandidateEdge::Rule {
                        instance: instance.clone(),
                        reversed,
                    };
                    edges.push((other.clone(), rule));
                } else if self.inner_congruence_compatible(matched, vertex) {
                    // Same head as the vertex with the children pairwise in
                    // one class: a congruence the child proofs replay.  The
                    // signature the match was found at is the wrapper's,
                    // and the engine keeps the unwrapped terms of a class
                    // together, so a match there can also ground to another
                    // member of the class that is no congruence of the
                    // vertex at all (`(= x false)` at `(= false x)`); such a
                    // member is reached by the rule that relates them, not
                    // by a congruence edge that cannot be justified and
                    // costs one of the bounded rejustifications.  That is
                    // how `(= (= false x) (not x))` went unreconstructed
                    // though `eq-symm` and `bool-eq-false` prove it.
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
        // Congruence candidates towards the vertex with one subterm
        // replaced by a constant of its class.  After the computational
        // edges: when both reach the same neighbour, the computation is the
        // single replayable step and the congruence only a decomposition.  The e-graph holds
        // `(not X) = false` because a rule made `X` true and the evaluator
        // then folded the negation, but it never holds the *term*
        // `(not true)` that both steps go through, and the goal's own
        // subterms are this class's preferred representatives, so nothing
        // else produces it.  Substituting the constant builds the
        // intermediate the evaluation and the constant-folding rules state.
        // Only for a wrapped vertex: the rules are stated on `Mk`-wrapped
        // terms, so a path through the unwrapped applications can cite none
        // of them, and handing that level more reach only makes the search
        // prefer a generic computation where a named rule was available.
        let positions = if vertex.op == "Mk" {
            subterm_positions(vertex)
        } else {
            Vec::new()
        };
        for position in positions {
            let subterm = at_position(vertex, &position);
            let Some(class) = self.class_of(subterm) else {
                continue;
            };
            let Some(constant) = self.class_constant(class, CONSTANT_DEPTH) else {
                continue;
            };
            if constant == *subterm {
                continue;
            }
            let candidate = replace_at_position(vertex, &position, &constant);
            // Never shadow an edge the vertex already has: a rule or a
            // computation towards the same neighbour is a single replayable
            // step, and the breadth-first search keeps only the first edge
            // it sees to a vertex.
            if edges.iter().any(|(neighbour, _)| *neighbour == candidate) {
                continue;
            }
            if graph.discovered.insert(candidate.clone()) {
                self.stats.candidate_vertices += 1;
            }
            edges.push((candidate, CandidateEdge::Congruence));
        }
        for goal in [&graph.source, &graph.target] {
            if *goal == *vertex {
                continue;
            }
            // The ACI and relation edges come before the congruence one.
            // Two `and`/`or` applications whose arguments are a permutation
            // of each other are congruence-compatible as soon as the e-graph
            // holds the arguments equal position by position -- which the
            // set form makes it do -- but that edge only pushes the
            // obligation one level down, onto the unwrapped applications,
            // where neither the ACI strategies nor the relation
            // recomputation apply.  Each of these edges is instead one step
            // the checker replays.
            if aci_equal(vertex, goal) {
                self.stats.computational_edges += 1;
                edges.push((
                    goal.clone(),
                    CandidateEdge::Computational { kind: Computation::AciNorm },
                ));
            } else if self.aci_modulo_pairs(vertex, goal).is_some() {
                edges.push((goal.clone(), CandidateEdge::AciModulo));
            } else if let Some(kind) = arith_kind(vertex, goal, self.sorts) {
                self.stats.computational_edges += 1;
                edges.push((goal.clone(), CandidateEdge::Computational { kind }));
            } else if self.congruence_compatible(vertex, goal) {
                edges.push((goal.clone(), CandidateEdge::Congruence));
            }
        }
        edges.retain(|(neighbour, _)| !graph.banned.contains(&(vertex.clone(), neighbour.clone())));
        edges
    }
}

/// The kind of a candidate edge, for the search's debug log.
fn edge_kind(edge: &CandidateEdge) -> &'static str {
    match edge {
        CandidateEdge::Rule { .. } => "rule",
        CandidateEdge::Congruence => "congruence",
        CandidateEdge::Computational { .. } => "computational",
        CandidateEdge::AciModulo => "aci-modulo",
    }
}

pub fn reconstruct_detailed(
    snapshot: &EGraphSnapshot,
    source: &Term,
    target: &Term,
    rules: &[Rewrite],
    strategy: SearchStrategy,
) -> ReconstructionResult {
    reconstruct_with_sorts(
        snapshot,
        source,
        target,
        rules,
        &ArithSorts::default(),
        strategy,
    )
}

/// Full entry point.  Sides the e-graph merged are proved by the in-class
/// search; otherwise the goal can only have been proved arithmetically, by
/// normal forms the solver compared without ever unioning the sides.
pub fn reconstruct_with_sorts(
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
        pattern_index: DiscriminationTree::build(rules, &snapshot.ops),
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
    let same_class = snapshot.same_class(source, target);
    log::debug!(
        "reconstructing {} = {} ({})",
        source.to_egglog(),
        target.to_egglog(),
        if same_class {
            "one class"
        } else {
            "across classes"
        }
    );
    let mut certificate = if same_class {
        reconstructor.prove(source, target)
    } else {
        reconstructor.prove_across_classes(source, target)
    };
    // Certificates are built lazily during the search, so soundness is
    // enforced once here, on the assembled proof.  One that fails the
    // independent rule checker is a search bug; it is reported and dropped
    // rather than trusted, and the hole is kept.
    if certificate
        .as_ref()
        .is_some_and(|certificate| !certificate.verify_in(rules, sorts))
    {
        log::warn!(
            "a reconstructed certificate failed the independent rule checker; the hole is kept"
        );
        certificate = None;
    }
    ReconstructionResult {
        certificate,
        stats: reconstructor.stats,
    }
}

pub fn reconstruct(
    snapshot: &EGraphSnapshot,
    source: &Term,
    target: &Term,
    rules: &[Rewrite],
    strategy: SearchStrategy,
) -> Option<Certificate> {
    reconstruct_detailed(snapshot, source, target, rules, strategy).certificate
}

/// `term` with every literal of an `operator` list that `replacement` maps
/// replaced, through nested lists of the same operator.
fn replace_literals(term: &Term, operator: &str, replacement: &HashMap<Term, Term>) -> Term {
    if let Some(mapped) = replacement.get(term) {
        return mapped.clone();
    }
    match encoded_application(term) {
        Some((op, elements)) if op == operator => encoded_app(
            operator,
            elements
                .iter()
                .map(|element| replace_literals(element, operator, replacement))
                .collect(),
        ),
        _ => term.clone(),
    }
}

/// The element patterns of an n-ary application pattern
/// `Mk(op(Args p1 (Args p2 ... Empty)))`, when its operator is `operator`.
fn argument_patterns(pattern: &Pattern, operator: &str) -> Option<Vec<Pattern>> {
    let Pattern::App("Mk", application) = pattern else {
        return None;
    };
    let [Pattern::App(op, arguments)] = application.as_slice() else {
        return None;
    };
    if *op != operator {
        return None;
    }
    let [chain] = arguments.as_slice() else {
        return None;
    };
    let mut elements = Vec::new();
    let mut current = chain;
    loop {
        match current {
            Pattern::App("Empty", _) => return Some(elements),
            Pattern::App("Args", cells) => {
                let [head, tail] = cells.as_slice() else {
                    return None;
                };
                elements.push(head.clone());
                current = tail;
            }
            _ => return None,
        }
    }
}

/// Matches element patterns against a term's arguments, where a pattern that
/// is one of the rule's `:list` parameters consumes a segment of any length,
/// the empty one included.  The segment is bound as an argument chain.
fn match_sequence(
    patterns: &[Pattern],
    elements: &[Term],
    lists: &[String],
    substitution: &mut Substitution,
) -> bool {
    let is_list = |pattern: &Pattern| {
        matches!(pattern, Pattern::Var(name) if lists.iter().any(|list| list == name))
    };
    let Some((first, rest)) = patterns.split_first() else {
        return elements.is_empty();
    };
    if is_list(first) {
        let Pattern::Var(name) = first else {
            return false;
        };
        // The shortest segment first, so that a list takes no more than it
        // must; the fixed patterns after it decide how much it may take.
        for taken in 0..=elements.len() {
            let mut attempt = substitution.clone();
            let segment = encoded_args(elements[..taken].to_vec());
            let consistent = match attempt.get(*name) {
                Some(previous) => *previous == segment,
                None => {
                    attempt.insert((*name).to_owned(), segment);
                    true
                }
            };
            if consistent && match_sequence(rest, &elements[taken..], lists, &mut attempt) {
                *substitution = attempt;
                return true;
            }
        }
        return false;
    }
    let Some((element, elements)) = elements.split_first() else {
        return false;
    };
    let mut attempt = substitution.clone();
    if !match_pattern(first, element, &mut attempt) {
        return false;
    }
    if match_sequence(rest, elements, lists, &mut attempt) {
        *substitution = attempt;
        return true;
    }
    false
}

/// The positions of a term's proper subterms, outermost first, bounded so a
/// large term does not flood the candidate search.
fn subterm_positions(term: &Term) -> Vec<Vec<usize>> {
    const MAX_POSITIONS: usize = 32;
    fn walk(term: &Term, prefix: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
        for (index, child) in term.children.iter().enumerate() {
            if out.len() >= MAX_POSITIONS {
                return;
            }
            prefix.push(index);
            out.push(prefix.clone());
            walk(child, prefix, out);
            prefix.pop();
        }
    }
    let mut out = Vec::new();
    walk(term, &mut Vec::new(), &mut out);
    out
}

fn at_position<'t>(term: &'t Term, position: &[usize]) -> &'t Term {
    position
        .iter()
        .fold(term, |current, &index| &current.children[index])
}

fn replace_at_position(term: &Term, position: &[usize], replacement: &Term) -> Term {
    let Some((&index, rest)) = position.split_first() else {
        return replacement.clone();
    };
    let mut children = term.children.clone();
    children[index] = replace_at_position(&children[index], rest, replacement);
    Term::new(&term.op, children)
}
