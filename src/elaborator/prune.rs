//! Removal of steps that nothing on the path to the empty clause uses.
//!
//! A [`ProofNodeForest`] is not pruned by construction: every top-level command becomes a root, and
//! every non-last command of a subproof is kept in its [`SubproofNode::extra_steps`] "even if not
//! used", so dead steps in the input survive parsing, every elaboration pass, and printing. Solvers
//! do emit them — scaffolding for lemmas that CDCL(T) ended up not needing — and elaboration can
//! strand more: a pass that re-points a step's premises leaves the old premises in place, where
//! only their membership in a root list or an `extra_steps` keeps them in the output.
//!
//! This pass keeps exactly the derivation of the proof's conclusion: the forest is restricted to
//! the roots concluding the empty clause, and every subproof reachable from them drops the extra
//! steps that its own last step does not (transitively) use. Soundness is immediate — checking is
//! per-step, so a valid proof stays valid under deleting steps nothing depends on — and the
//! conclusion is untouched, so the verdict is preserved. Unused `assume` commands are dropped
//! along with everything else: what checking requires of the assumes is that each is among the
//! problem's premises — a subset, not the full list — so a proof that assumes less proves the
//! same refutation from less.
//!
//! A proof with no empty-clause root — a partial proof, or one truncated by the solver — is
//! returned unchanged: there is no conclusion to prune towards.

use super::hoist::{NodeMap, NodeSet};
use crate::ast::*;

/// Restricts the proof to the derivation of its empty-clause conclusion(s), and returns it along
/// with how many steps were dropped.
pub fn prune(proof: ProofNodeForest) -> ProofNodeForest {
    let goals: Vec<Rc<ProofNode>> = proof
        .0
        .iter()
        .filter(|node| node.clause().is_empty())
        .cloned()
        .collect();
    if goals.is_empty() {
        log::info!("prune: no empty-clause conclusion, proof left unchanged");
        return proof;
    }

    let counting = log::log_enabled!(log::Level::Info);
    let before = if counting { count_commands(&proof) } else { 0 };

    // Everything must be reachable from a goal — including the assumes: an `assume` is checked
    // against the problem's premises individually, so the used subset stands on its own. The ones
    // the goals reach are kept as *leading* roots all the same, because Alethe wants the `assume`
    // commands before the steps and the printer emits roots in order
    let reached = {
        let mut reached: NodeMap<()> = NodeMap::default();
        let mut todo: Vec<Rc<ProofNode>> = goals.clone();
        while let Some(node) = todo.pop() {
            if reached.insert(node.clone(), ()).is_some() {
                continue;
            }
            match node.as_ref() {
                ProofNode::Assume { .. } => (),
                ProofNode::Step(s) => todo.extend(
                    s.premises
                        .iter()
                        .chain(&s.discharge)
                        .chain(&s.previous_step)
                        .cloned(),
                ),
                ProofNode::Subproof(s) => {
                    todo.push(s.last_step.clone());
                    todo.extend(s.outbound_premises.iter().cloned());
                    todo.extend(live_extra_steps(s));
                }
            }
        }
        reached
    };
    let mut roots: Vec<Rc<ProofNode>> = proof
        .0
        .iter()
        .filter(|n| matches!(n.as_ref(), ProofNode::Assume { .. }) && reached.contains_key(*n))
        .cloned()
        .collect();
    roots.extend(goals);

    // Rebuild bottom-up, dropping each subproof's dead extra steps. Only subproofs (and the nodes
    // above one) change, so unaffected subgraphs are passed through as they are
    let mut cache: NodeMap<Rc<ProofNode>> = NodeMap::default();
    let mut todo: Vec<(Rc<ProofNode>, bool)> =
        roots.iter().rev().map(|r| (r.clone(), false)).collect();
    while let Some((node, is_done)) = todo.pop() {
        if cache.contains_key(&node) {
            continue;
        }
        if !is_done {
            todo.push((node.clone(), true));
            match node.as_ref() {
                ProofNode::Assume { .. } => (),
                ProofNode::Step(s) => {
                    todo.extend(
                        s.premises
                            .iter()
                            .chain(&s.discharge)
                            .chain(&s.previous_step)
                            .map(|p| (p.clone(), false)),
                    );
                }
                ProofNode::Subproof(s) => {
                    // Dead extra steps are decided here, so they are simply not visited
                    todo.push((s.last_step.clone(), false));
                    todo.extend(s.outbound_premises.iter().map(|p| (p.clone(), false)));
                    for extra in live_extra_steps(s) {
                        todo.push((extra, false));
                    }
                }
            }
            continue;
        }
        let rebuilt = match node.as_ref() {
            ProofNode::Assume { .. } => node.clone(),
            ProofNode::Step(s) => {
                let changed = s
                    .premises
                    .iter()
                    .chain(&s.discharge)
                    .chain(&s.previous_step)
                    .any(|p| cache[p] != *p);
                if changed {
                    Rc::new(ProofNode::Step(StepNode {
                        premises: s.premises.iter().map(|p| cache[p].clone()).collect(),
                        discharge: s.discharge.iter().map(|p| cache[p].clone()).collect(),
                        previous_step: s.previous_step.as_ref().map(|p| cache[p].clone()),
                        ..s.clone()
                    }))
                } else {
                    node.clone()
                }
            }
            ProofNode::Subproof(s) => {
                let extra_steps: Vec<_> = live_extra_steps(s)
                    .into_iter()
                    .map(|e| cache[&e].clone())
                    .collect();
                Rc::new(ProofNode::Subproof(SubproofNode {
                    last_step: cache[&s.last_step].clone(),
                    args: s.args.clone(),
                    outbound_premises: s
                        .outbound_premises
                        .iter()
                        .map(|p| cache[p].clone())
                        .collect(),
                    extra_steps,
                }))
            }
        };
        cache.insert(node, rebuilt);
    }

    let result = ProofNodeForest(roots.iter().map(|r| cache[r].clone()).collect());
    if counting {
        let after = count_commands(&result);
        log::info!(
            "prune: dropped {} of {} commands unreachable from the conclusion",
            before.saturating_sub(after),
            before,
        );
    }
    result
}

/// The extra steps of a subproof that its own last step transitively uses, plus the ones a pass
/// moved out of the subproof (depth at most the subproof's own), which the printer needs listed to
/// emit them before the anchor.
///
/// Everything else is dead: a step inside a subproof can only be referenced from inside it, so an
/// extra step the last step does not reach is referenced by nothing in the whole proof.
fn live_extra_steps(s: &SubproofNode) -> Vec<Rc<ProofNode>> {
    let subproof_depth = s.last_step.depth() - 1;
    let mut used: NodeSet = NodeSet::default();
    let mut todo: Vec<&Rc<ProofNode>> = vec![&s.last_step];
    while let Some(node) = todo.pop() {
        if !used.insert(node) {
            continue;
        }
        match node.as_ref() {
            ProofNode::Assume { .. } => (),
            ProofNode::Step(step) => {
                todo.extend(
                    step.premises
                        .iter()
                        .chain(&step.discharge)
                        .chain(&step.previous_step),
                );
            }
            ProofNode::Subproof(inner) => {
                todo.push(&inner.last_step);
                todo.extend(&inner.outbound_premises);
            }
        }
    }
    s.extra_steps
        .iter()
        .filter(|e| used.contains(e) || e.depth() <= subproof_depth)
        .cloned()
        .collect()
}

fn count_commands(proof: &ProofNodeForest) -> usize {
    let mut n = 0;
    super::hoist::visit_all_with(proof, |_| n += 1);
    n
}
