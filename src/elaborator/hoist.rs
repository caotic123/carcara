//! Hoisting of repeated closed derivations to the top level.
//!
//! Solvers emit the same premise-free reasoning over and over: over cvc5's `QF_LIA`, `QF_LRA` and
//! `QF_UFLIA` proofs, half of all premise-free steps are exact duplicates of an earlier one — 2.3
//! million steps with 1.15 million distinct conclusions — and the duplication is almost entirely
//! *across* subproofs, so nothing that stays inside one scope can remove it.
//!
//! This pass derives each distinct closed conclusion once, at depth 0, and re-points every other use
//! at it. Since premises are pointers in a [`ProofNodeForest`], replacing a node makes every step
//! that referred to it refer to the shared derivation instead, and a use from inside a subproof
//! becomes an ordinary outbound premise. It runs first in the elaboration pipelines, so every later
//! pass sees the smaller proof.
//!
//! Lifting a derivation out of its subproof is only sound if the derivation does not depend on
//! anything that subproof provides, so a step is a candidate only if it is
//!
//! - *closed*: every node reachable from it is a step whose depth is either the candidate's own
//!   depth (a step that the hoist would copy) or 0 (a step that is already visible from everywhere),
//!   with no `:discharge` and no implicit premise. In one predicate this excludes assumptions, steps
//!   of an enclosing scope, and subproofs, and forces the leaves to be premise-free steps;
//! - *context-free*: no clause or argument term of the steps that would move has a free variable
//!   bound by an anchor in scope, so checking them outside those anchors is the same problem as
//!   checking them inside;
//! - *hole-free*: no step of the derivation uses a rule that the checker treats as a hole.
//!
//! A closed derivation proves its conclusion on its own, which is what makes the conclusion a
//! complete key: two closed derivations of the same clause are interchangeable, whatever the steps
//! they were built from.
//!
//! The hole-freeness guard is what keeps the pass from laundering a hole. A proof may contain both a
//! real derivation of a clause and a `hole`-like step concluding it; replacing the former by the
//! latter would silently turn a valid proof into a holey one.  With `share_holes`, a derivation
//! that contains holes is shared too, but only with other holey derivations of the same clause: the
//! memo keys the two kinds apart, so a real derivation is never replaced by a holey one nor the
//! other way round, and the set of rules the checker sees as holes is the same before and after
//! the pass.  What changes is their number: cvc5 prints the same `TRUST_THEORY_REWRITE` equality
//! once per subproof that uses it, and sharing leaves one hole per distinct equality.

use super::Mutate;
use crate::ast::pool::{PrimitivePool, TermPool};
use crate::ast::*;
use std::collections::{HashMap, HashSet};

/// A hasher for keys whose hash is already a well-spread pointer. `Rc<ProofNode>` hashes as the
/// address of its allocation, which the default hasher then runs through `SipHash`; this pass keys
/// two whole-forest maps by node, so that mixing is a measurable part of its cost.
#[derive(Default)]
pub(super) struct PtrHasher(u64);

impl std::hash::Hasher for PtrHasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        for b in bytes {
            self.write_usize(*b as usize);
        }
    }

    fn write_usize(&mut self, i: usize) {
        // Fibonacci hashing: multiplying by 2^64 / phi spreads an address over the whole word
        self.0 ^= (i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    }
}

pub(super) type PtrBuildHasher = std::hash::BuildHasherDefault<PtrHasher>;
pub(super) type NodeMap<V> = HashMap<Rc<ProofNode>, V, PtrBuildHasher>;
pub(super) type NodeSet<'a> = HashSet<&'a Rc<ProofNode>, PtrBuildHasher>;

/// What the memo holds for a clause that some closed derivation already proves.
enum Entry {
    /// A derivation that is available for reuse, because it is at depth 0.
    Shared(Rc<ProofNode>),

    /// A derivation that is still inside a subproof, and that hoisting would have to copy more than
    /// one step of the proof out of: it is kept aside, and only lifted if a second step needs it.
    Pending(Vec<Rc<ProofNode>>),
}

impl Entry {
    /// The clause the derivation proves, which is the key it is filed under.
    fn clause(&self) -> &[Rc<Term>] {
        match self {
            Entry::Shared(node) => node.clause(),
            Entry::Pending(derivation) => derivation.last().unwrap().clause(),
        }
    }
}

/// What looking a candidate's conclusion up in the memo found, without borrowing the memo.
enum Hit {
    Shared(Rc<ProofNode>),
    Pending,
    Miss,
}

/// A digest of a clause, used to file derivations by their conclusion.
///
/// The memo cannot be keyed by the clause itself: clauses can have tens of thousands of literals,
/// and a hash map over them re-reads every key each time it grows. Hashing each clause once, into
/// a bucket of the derivations whose conclusions collide, keeps the memo's cost proportional to the
/// proof and leaves the literal-by-literal comparison for the one entry that is really a candidate's
/// conclusion.
fn digest(clause: &[Rc<Term>]) -> u64 {
    use std::hash::{Hash, Hasher};

    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    clause.hash(&mut hasher);
    hasher.finish()
}

/// Lifts every repeated closed derivation of `proof` to depth 0, and returns the resulting proof.
///
/// With `share_holes`, derivations that contain hole steps are shared as well, among themselves
/// only (see the module documentation).
pub fn hoist(
    pool: &mut PrimitivePool,
    proof: ProofNodeForest,
    allowed_rules: &HashSet<String>,
    share_holes: bool,
) -> ProofNodeForest {
    let mut hoisting = Hoisting::new(&proof, allowed_rules, share_holes);
    // With no conclusion proved twice there is nothing to share: skip the whole rebuild
    if hoisting.duplicated.is_empty() && std::env::var_os("CARCARA_HOIST_NO_PREFILTER").is_none() {
        return proof;
    }
    let result = proof
        .mutate(|context, node, _| {
            Ok::<_, std::convert::Infallible>(hoisting.rewrite(pool, context, node))
        })
        .unwrap();
    log::info!(
        "hoisting: lifted {} steps to depth 0, dropped {} repeated derivations ({} of them holey)",
        hoisting.lifted,
        hoisting.reused,
        hoisting.reused_holey,
    );
    result
}

/// A memo of the closed derivations seen so far, keyed by their conclusion.
struct Hoisting<'a> {
    /// The closed derivations seen so far, bucketed by the digest of the clause they prove and by
    /// whether they contain a hole: the two kinds never replace each other.
    cache: HashMap<(u64, bool), Vec<Entry>>,

    /// Whether a node's derivation is closed, relative to that node's own depth. Every node the
    /// pass produces or is asked about is in here, which is what lets the answer for a step be
    /// read off the answers for its premises.
    is_closed: NodeMap<bool>,

    /// Whether a node's derivation contains a hole step.
    is_holey: NodeMap<bool>,

    /// The prefix of the ids given to lifted steps. It is chosen so that it is not a prefix of any
    /// id already in the proof, which makes the lifted ids unique, and also keeps the ids that later
    /// passes derive from them (by appending to them) unique.
    prefix: String,

    /// The number of lifted steps emitted so far, which is also the next id to use.
    emitted: usize,

    /// The ids of the steps that a subproof refers to by their position: its last step, and that
    /// step's implicit premise. Neither can leave its subproof.
    pinned: HashSet<String>,

    /// The digests of the conclusions that more than one step of the input proves. Only those can
    /// ever produce a reuse, so every other candidate skips the memo — and with it the derivation
    /// walk, the context check, and the memo insertion, which on proofs with little duplication
    /// (veriT's) were nearly all of the pass's cost.
    duplicated: HashSet<u64>,

    /// The rules that the checker was told to accept as holes.
    allowed_rules: &'a HashSet<String>,

    /// Whether derivations containing holes are shared among themselves.
    share_holes: bool,

    /// The number of steps copied to depth 0, for logging.
    lifted: usize,

    /// The number of derivations that were replaced by an earlier one, for logging, and how many
    /// of those contained a hole.
    reused: usize,
    reused_holey: usize,
}

impl<'a> Hoisting<'a> {
    /// Prepares to hoist derivations in the given proof: picks an id namespace that is free in it,
    /// and collects the steps that cannot be moved out of their subproof.
    fn new(
        proof: &ProofNodeForest,
        allowed_rules: &'a HashSet<String>,
        share_holes: bool,
    ) -> Self {
        let mut pinned = HashSet::new();
        let mut seen_digests = HashSet::new();
        let mut duplicated = HashSet::new();
        // Only an id that starts with the base can be a prefix conflict, so the id scan that
        // picks the pass's namespace rides along with this walk instead of taking a second one
        let base = "ho";
        let mut conflicting = Vec::new();
        visit_all_with(proof, |node| {
            if node.id().starts_with(base) {
                conflicting.push(node.id().to_owned());
            }
            match node.as_ref() {
                ProofNode::Step(s) => {
                    if let Some(previous) = &s.previous_step {
                        pinned.insert(previous.id().to_owned());
                    }
                    if s.discharge.is_empty() && s.previous_step.is_none() {
                        let d = digest(&s.clause);
                        if !seen_digests.insert(d) {
                            duplicated.insert(d);
                        }
                    }
                }
                ProofNode::Subproof(s) => {
                    pinned.insert(s.last_step.id().to_owned());
                }
                ProofNode::Assume { .. } => (),
            }
        });
        let mut prefix = base.to_owned();
        while conflicting.iter().any(|id| id.starts_with(&prefix)) {
            prefix.push('_');
        }

        Self {
            cache: HashMap::new(),
            is_closed: NodeMap::default(),
            is_holey: NodeMap::default(),
            prefix,
            emitted: 0,
            pinned,
            duplicated,
            allowed_rules,
            share_holes,
            lifted: 0,
            reused: 0,
            reused_holey: 0,
        }
    }

    /// Returns the node to use in place of `node`: the derivation already recorded for an earlier
    /// step with the same conclusion, or `node` itself, recorded for later steps.
    ///
    /// If `node` is not a candidate, it is returned unchanged and the proof is left as it was.
    fn rewrite(
        &mut self,
        pool: &mut PrimitivePool,
        context: &ContextStack,
        node: &Rc<ProofNode>,
    ) -> Rc<ProofNode> {
        // Subproofs are never candidates: what they prove depends on what they discharge
        if matches!(node.as_ref(), ProofNode::Subproof(_)) {
            return node.clone();
        }

        // Every node the pass visits is recorded, candidate or not, so that the steps that use it
        // as a premise can decide whether they are closed by looking it up
        let closed = self.record_closed(node);

        let Some(s) = node.as_step() else {
            return node.clone();
        };
        if !closed {
            return node.clone();
        }
        // A step that a subproof refers to by its position inside it cannot leave that subproof.
        // The steps with a `:discharge` or an implicit premise, which close a subproof, are not
        // closed derivations to begin with, so they never get this far
        if self.pinned.contains(&s.id) {
            return node.clone();
        }
        // A conclusion no other step of the proof proves can never be reused, so nothing needs to
        // be recorded or checked for it
        let digest = digest(&s.clause);
        if !self.duplicated.contains(&digest)
            && std::env::var_os("CARCARA_HOIST_NO_PREFILTER").is_none()
        {
            return node.clone();
        }
        // A candidate whose conclusion mentions a variable that an anchor in scope binds cannot be
        // replaced by a derivation from outside that anchor, even if the two clauses are equal: an
        // anchor may shadow a symbol of the problem, and then the same term means different things
        // on either side of it
        if mentions_bound(pool, context, &s.clause) {
            return node.clone();
        }

        let holey = self.is_holey.get(node).copied().unwrap_or(false);
        let key = (digest, holey);
        let bucket = self.cache.entry(key).or_default();
        let found = bucket.iter().position(|e| e.clause() == s.clause);
        let hit = match found.map(|i| &bucket[i]) {
            Some(Entry::Shared(shared)) => Hit::Shared(shared.clone()),
            Some(Entry::Pending(_)) => Hit::Pending,
            None => Hit::Miss,
        };
        match hit {
            Hit::Shared(shared) => {
                if shared != *node {
                    self.reused += 1;
                    self.reused_holey += holey as usize;
                }
                return shared;
            }
            Hit::Pending => {
                // The second step to need this derivation makes lifting it worthwhile: from here on
                // there is one copy at depth 0 instead of one copy per subproof
                let index = found.unwrap();
                let Entry::Pending(pending) = self.cache.get_mut(&key).unwrap().remove(index)
                else {
                    unreachable!()
                };
                let shared = self.lift(&pending);
                self.cache
                    .get_mut(&key)
                    .unwrap()
                    .push(Entry::Shared(shared.clone()));
                self.reused += 1;
                self.reused_holey += holey as usize;
                return shared;
            }
            Hit::Miss => (),
        }

        // A derivation already at depth 0 is recorded as it is: it is visible from everywhere, so
        // there is nothing to copy and nothing to renumber
        if s.depth == 0 {
            self.cache
                .get_mut(&key)
                .unwrap()
                .push(Entry::Shared(node.clone()));
            return node.clone();
        }
        let derivation = local_nodes(node);
        if !context_free(pool, context, &derivation) {
            return node.clone();
        }

        // Copying the derivation out of its subproof replaces its steps one for one only if there is
        // a single one to copy: then every reference to it is re-pointed at the copy and the
        // original is left with none, so the proof keeps exactly the size it had. This is the
        // common case, because the pass runs bottom-up and lifts the premises first. When several
        // steps would have to be copied, some of them may still be used where they are, so the
        // derivation is only lifted once a second step needs it, and lifting always pays for itself
        let entry = if derivation.len() == 1 {
            Entry::Shared(self.lift(&derivation))
        } else {
            Entry::Pending(derivation)
        };
        let result = match &entry {
            Entry::Shared(shared) => shared.clone(),
            Entry::Pending(_) => node.clone(),
        };
        self.cache.get_mut(&key).unwrap().push(entry);
        result
    }

    /// Records whether every node reachable from `node` is a hole-free step, with no `:discharge`
    /// and no implicit premise, whose depth is either `node`'s depth or 0, and returns the answer.
    ///
    /// The whole subgraph is never walked: the pass visits a step only after its premises, so the
    /// answer for each of them is already recorded and the property is decided in one look at the
    /// step itself. Every node the pass sees is recorded, whether or not it is a candidate, so that
    /// its users find it here.
    fn record_closed(&mut self, node: &Rc<ProofNode>) -> bool {
        if let Some(&answer) = self.is_closed.get(node) {
            return answer;
        }
        let holey = node.as_step().is_some_and(|s| {
            self.is_hole(&s.rule)
                || s.premises
                    .iter()
                    .any(|p| self.is_holey.get(p).copied().unwrap_or(false))
        });
        let answer = node.as_step().is_some_and(|s| {
            s.discharge.is_empty()
                && s.previous_step.is_none()
                && (self.share_holes || !self.is_hole(&s.rule))
                && s.premises.iter().all(|p| {
                    // A premise of the step's own depth is copied along with it; one at depth 0 is
                    // already visible from everywhere and is used where it is. A premise at any
                    // other depth belongs to an enclosing subproof, and would be out of scope
                    (p.depth() == s.depth || p.depth() == 0)
                        && self.is_closed.get(p).copied().unwrap_or(false)
                })
        });
        self.is_closed.insert(node.clone(), answer);
        self.is_holey.insert(node.clone(), holey);
        answer
    }

    /// Returns `true` if the checker would treat a step with this rule as a hole.
    ///
    /// A rule the checker does not know is one too, since `--ignore-unknown-rules` accepts it as a
    /// hole and, without that option, the step is an error and the proof is rejected either way.
    fn is_hole(&self, rule: &str) -> bool {
        rule == "hole"
            || rule == "lia_generic"
            || self.allowed_rules.contains(rule)
            || crate::checker::shared::get_rule(rule, false, false).is_none()
    }

    fn next_id(&mut self) -> String {
        self.emitted += 1;
        format!("{}{}", self.prefix, self.emitted)
    }

    /// Rebuilds a derivation at depth 0, with fresh ids. The derivation is given in postorder, so
    /// every premise of a step that moves has already been rebuilt when the step is reached; the
    /// premises that were already at depth 0 are kept as they are.
    fn lift(&mut self, derivation: &[Rc<ProofNode>]) -> Rc<ProofNode> {
        let mut lifted: HashMap<&Rc<ProofNode>, Rc<ProofNode>> = HashMap::new();
        for node in derivation {
            let s = node.as_step().expect("derivation node must be a step");
            let premises = s
                .premises
                .iter()
                .map(|p| lifted.get(p).unwrap_or(p).clone())
                .collect();
            let id = self.next_id();
            let new_node = Rc::new(ProofNode::Step(StepNode {
                id,
                depth: 0,
                clause: s.clause.clone(),
                rule: s.rule.clone(),
                premises,
                args: s.args.clone(),
                discharge: Vec::new(),
                previous_step: None,
            }));
            // The copies are closed by construction, and the root of the derivation becomes a
            // premise of the steps that used the original
            self.is_closed.insert(new_node.clone(), true);
            let holey = self.is_holey.get(node).copied().unwrap_or(false);
            self.is_holey.insert(new_node.clone(), holey);
            lifted.insert(node, new_node);
        }
        self.lifted += derivation.len();
        lifted[derivation.last().unwrap()].clone()
    }
}

/// Returns the nodes of `root`'s derivation that are at `root`'s depth, in postorder: the ones that
/// hoisting the derivation would have to copy.
fn local_nodes(root: &Rc<ProofNode>) -> Vec<Rc<ProofNode>> {
    let depth = root.depth();
    let mut order = Vec::new();
    let mut done: HashSet<Rc<ProofNode>> = HashSet::new();
    let mut todo = vec![(root.clone(), false)];
    while let Some((node, is_done)) = todo.pop() {
        if is_done {
            order.push(node);
            continue;
        }
        if node.depth() != depth || done.contains(&node) {
            continue;
        }
        done.insert(node.clone());
        let s = node.as_step().expect("derivation node must be a step");
        let premises: Vec<_> = s.premises.iter().map(|p| (p.clone(), false)).collect();
        todo.push((node, true));
        todo.extend(premises);
    }
    order
}

/// Returns `true` if any of the given terms has a free variable that an anchor in scope binds.
///
/// The comparison is by name, so a term is rejected even when the anchor declares its variable with
/// another sort: a name an anchor binds means something else outside it either way.
pub(super) fn mentions_bound(
    pool: &mut PrimitivePool,
    context: &ContextStack,
    terms: &[Rc<Term>],
) -> bool {
    if context.binds_nothing() {
        return false;
    }
    terms.iter().any(|t| {
        pool.free_vars(t)
            .iter()
            .any(|v: &Rc<Term>| v.as_var().is_some_and(|name| context.binds(name)))
    })
}

/// Returns `true` if no term in the derivation has a free variable that an anchor in scope binds.
///
/// When that holds, the anchors' substitution is the identity on every term of the derivation, and
/// the variables they declare are not among the derivation's, so checking the derivation outside
/// the anchors is the same problem as checking it inside them.
pub(super) fn context_free(
    pool: &mut PrimitivePool,
    context: &ContextStack,
    derivation: &[Rc<ProofNode>],
) -> bool {
    if context.binds_nothing() {
        return true;
    }
    !derivation.iter().any(|node| {
        let s = node.as_step().unwrap();
        mentions_bound(pool, context, &s.clause) || mentions_bound(pool, context, &s.args)
    })
}

/// Picks an id prefix that is not a prefix of any id in the proof.
///
/// Ids built by appending to it are then unique, and so are the ids that later passes derive from
/// those by appending further.
pub(super) fn fresh_prefix(proof: &ProofNodeForest, base: &str) -> String {
    // Only an id that starts with the base can conflict, and those are rare, so the walk keeps
    // just those rather than every id in the proof
    let mut conflicting = Vec::new();
    visit_all_with(proof, |node| {
        if node.id().starts_with(base) {
            conflicting.push(node.id());
        }
    });
    let mut prefix = base.to_owned();
    while conflicting.iter().any(|id| id.starts_with(&prefix)) {
        prefix.push('_');
    }
    prefix
}

/// Visits every node of a proof forest, including the ones that [`Rc<ProofNode>::traverse`] skips
/// because nothing depends on them.
pub(super) fn visit_all(proof: &ProofNodeForest) -> Vec<&Rc<ProofNode>> {
    let mut result = Vec::new();
    visit_all_with(proof, |node| result.push(node));
    result
}

/// Visits every node of a proof forest, without collecting them.
pub(super) fn visit_all_with<'a>(proof: &'a ProofNodeForest, mut f: impl FnMut(&'a Rc<ProofNode>)) {
    let mut seen: NodeSet = NodeSet::default();
    let mut todo: Vec<&Rc<ProofNode>> = proof.0.iter().collect();
    while let Some(node) = todo.pop() {
        if !seen.insert(node) {
            continue;
        }
        f(node);
        match node.as_ref() {
            ProofNode::Assume { .. } => (),
            ProofNode::Step(s) => {
                todo.extend(
                    s.premises
                        .iter()
                        .chain(&s.discharge)
                        .chain(&s.previous_step),
                );
            }
            ProofNode::Subproof(s) => {
                todo.push(&s.last_step);
                todo.extend(s.extra_steps.iter().chain(&s.outbound_premises));
            }
        }
    }
}
