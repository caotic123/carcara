//! Provenance-free snapshot of a saturated e-graph, with e-matching.
use std::collections::HashMap;
use egglog::{EGraph as ProductionEGraph, SerializeConfig as ProductionSerializeConfig};
use super::*;

#[derive(Clone, Debug)]
pub struct SnapshotNode {
    pub op: u32,
    pub child_classes: Vec<u32>,
}

/// Interns e-graph string identifiers (operators and e-class ids) into dense
/// `u32` indices, so the snapshot stores and hashes small integers instead of
/// per-node strings.
#[derive(Clone, Debug, Default)]
pub struct Interner {
    pub ids: HashMap<String, u32>,
    pub names: Vec<String>,
}

impl Interner {
    pub fn intern(&mut self, name: &str) -> u32 {
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
pub struct EGraphSnapshot {
    pub nodes: Vec<SnapshotNode>,
    pub class_nodes: Vec<Vec<u32>>,
    pub class_op_nodes: HashMap<(u32, u32), Vec<u32>>,
    pub signature_class: HashMap<(u32, Vec<u32>), u32>,
    pub classes: Interner,
    pub ops: Interner,
}

impl EGraphSnapshot {
    pub fn from_raw_nodes(raw: Vec<(String, Vec<String>, String)>) -> Self {
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


    pub fn capture_production(egraph: &ProductionEGraph) -> Self {
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

    pub fn class_of(&self, term: &Term, cache: &mut HashMap<Term, u32>) -> Option<u32> {
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

    pub fn class_of_term(&self, term: &Term) -> Option<u32> {
        self.class_of(term, &mut HashMap::new())
    }

    pub fn same_class(&self, lhs: &Term, rhs: &Term) -> bool {
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
    pub fn ematch_in_class(
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
    pub fn ematch_at_signature(
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
    pub fn preferred_representatives(&self, preferred: [&Term; 2]) -> HashMap<u32, Term> {
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

#[derive(Clone, Debug, Default)]
pub struct ReconstructionStats {
    pub ematch_calls: usize,
    pub relation_rows_examined: usize,
    pub index_candidates: usize,
    pub lhs_matches: usize,
    pub rule_instances: usize,
    pub candidate_vertices: usize,
    pub congruence_edges: usize,
    pub computational_edges: usize,
    pub recursive_obligations: usize,
    pub rejustifications: usize,
}

/// Root signature of an enode: interned operator plus child e-classes.  Two
/// terms of one e-class are congruence-compatible exactly when their root
/// signatures agree, so signatures determine which rule matches can touch a
/// vertex — before any match is grounded into terms.
pub type Signature = (u32, Vec<u32>);
