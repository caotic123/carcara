//! Folding of rewrite derivations into `TRUST_THEORY_REWRITE` holes.
//!
//! cvc5 justifies a rewrite `t = t'` with one `hole` step tagged `TRUST_THEORY_REWRITE` — the
//! whole rewrite at once — and the RARE/egglog machinery behind the `hole` pass re-derives it.
//! veriT justifies the same rewrite with a derivation: `*_simplify`, `ac_simp`, `la_rw_eq`, ...
//! steps rewrite subterms, and `cong`, `trans`, `refl` and `symm` steps assemble the subterm
//! rewrites into the rewrite of the whole term.
//!
//! This pass finds those derivations and replaces each by a single hole concluding the same
//! equality, so that a proof from any Alethe producer can be put through the same hole checking
//! and elaboration as a cvc5 proof.  A *rewrite derivation* is a closed sub-DAG of steps whose
//! rules are rewrite rules ([`REWRITE_RULES`]) or glue rules ([`GLUE_RULES`]), each concluding a
//! unit clause `(= l r)` with no arguments, no discharge and premises only within the derivation.
//! Its roots — the members that some step outside the derivation uses — become holes, tagged
//! with the rewrite rules folded into them; its other members are dropped when nothing else uses
//! them.  A derivation of glue rules alone (`refl`s and `cong`s over them) is left as it is:
//! there is nothing in it for egglog to prove.
//!
//! veriT rewrites an assertion in one derivation, however large: one `cong` at the top over the
//! rewrites of the conjuncts, so folding without limit makes one hole of the whole assertion.
//! The `limit` bounds the steps a folded derivation may have (as a tree, a shared step counting
//! once per use): a step whose derivation would be larger is not a member, so it stays and the
//! derivations of its premises are folded instead, which cuts the hole at that granularity.
//!
//! The closedness condition is what keeps the pass from turning theory reasoning into holes:
//! `cong` and `trans` premises may come from anywhere, and a `cong` over an assumed equality has
//! a premise outside any rewrite derivation, so it stays, as does everything above it.
//!
//! The holes keep the id, depth and clause of the step they replace, so the rest of the proof is
//! untouched.  A hole inside a subproof whose anchor assigns variables (`:=`) is still only
//! provable under that assignment; the hole checker does not apply anchor assignments, so such
//! proofs are best folded after their `let`s are expanded away.

use super::Mutate;
use super::hoist::NodeMap;
use crate::ast::pool::{PrimitivePool, TermPool};
use crate::ast::*;
use std::collections::{BTreeMap, HashMap, HashSet};

/// The Alethe rules that rewrite a term into an equal one on their own: the seeds of a rewrite
/// derivation.  Quantifier rules are left out (the hole checker has no rules for binders), and so
/// are `ite_intro` and `bfun_elim`, whose conclusions are not rewrites of a term.
pub const REWRITE_RULES: &[&str] = &[
    "ac_simp",
    "all_simplify",
    "and_simplify",
    "or_simplify",
    "not_simplify",
    "implies_simplify",
    "equiv_simplify",
    "bool_simplify",
    "ite_simplify",
    "eq_simplify",
    "div_simplify",
    "prod_simplify",
    "unary_minus_simplify",
    "minus_simplify",
    "sum_simplify",
    "comp_simplify",
    "la_rw_eq",
    "distinct_elim",
    "nary_elim",
    "connective_def",
];

/// The rules that assemble subterm rewrites into the rewrite of a term.
pub const GLUE_RULES: &[&str] = &["cong", "trans", "refl", "symm"];

/// The tag the hole checker recognizes, as cvc5 prints it.
const TAG: &str = "TRUST_THEORY_REWRITE";

pub fn is_rewrite_rule(rule: &str) -> bool {
    REWRITE_RULES.contains(&rule)
}

fn is_glue_rule(rule: &str) -> bool {
    GLUE_RULES.contains(&rule)
}

/// Whether `step`, by its own shape, may be a member of a rewrite derivation.
fn has_rewrite_shape(step: &StepNode) -> bool {
    (is_rewrite_rule(&step.rule) || is_glue_rule(&step.rule))
        && step.args.is_empty()
        && step.discharge.is_empty()
        && step.previous_step.is_none()
        && matches!(
            step.clause.as_slice(),
            [literal] if matches!(literal.as_ref(), Term::Op(Operator::Equals, args) if args.len() == 2)
        )
}

/// What the classification found about the proof's rewrite derivations.
#[derive(Default)]
struct Members {
    /// Every step that is a member of a rewrite derivation: of rewrite shape, with member
    /// premises, and within the size limit.
    member: NodeMap<bool>,
    /// The steps of the derivation rooted at each member, counted as a tree.
    size: NodeMap<usize>,
    /// The members whose derivation contains a rewrite rule (not only glue).
    seeded: NodeMap<bool>,
    /// The members that a step outside their derivation uses.
    consumed_outside: NodeMap<bool>,
}

/// Classifies every step of `proof`, in postorder so that a step's premises are classified first.
fn classify(proof: &ProofNodeForest, limit: usize) -> Members {
    let mut members = Members::default();
    let mut todo: Vec<(Rc<ProofNode>, bool)> =
        proof.0.iter().rev().map(|n| (n.clone(), false)).collect();
    while let Some((node, done)) = todo.pop() {
        if members.member.contains_key(&node) {
            continue;
        }
        if !done {
            todo.push((node.clone(), true));
            match node.as_ref() {
                ProofNode::Assume { .. } => (),
                ProofNode::Step(s) => todo.extend(
                    s.premises
                        .iter()
                        .chain(&s.discharge)
                        .chain(&s.previous_step)
                        .map(|p| (p.clone(), false)),
                ),
                ProofNode::Subproof(s) => {
                    todo.push((s.last_step.clone(), false));
                    todo.extend(s.extra_steps.iter().map(|e| (e.clone(), false)));
                    todo.extend(s.outbound_premises.iter().map(|p| (p.clone(), false)));
                }
            }
            continue;
        }
        let (member, seeded) = match node.as_ref() {
            ProofNode::Step(s) => {
                let mut member =
                    has_rewrite_shape(s) && s.premises.iter().all(|p| members.member[p]);
                if member {
                    let size = 1 + s.premises.iter().map(|p| members.size[p]).sum::<usize>();
                    member = limit == 0 || size <= limit;
                    members.size.insert(node.clone(), size);
                }
                let seeded = member
                    && (is_rewrite_rule(&s.rule) || s.premises.iter().any(|p| members.seeded[p]));
                if !member {
                    for p in s
                        .premises
                        .iter()
                        .chain(&s.discharge)
                        .chain(&s.previous_step)
                    {
                        members.consumed_outside.insert(p.clone(), true);
                    }
                }
                (member, seeded)
            }
            _ => (false, false),
        };
        members.member.insert(node.clone(), member);
        members.seeded.insert(node.clone(), seeded);
    }
    members
}

/// The rewrite rules of the derivation rooted at `root`, with how many steps use each, and the
/// derivation's size in steps.
fn derivation_summary(root: &Rc<ProofNode>) -> (BTreeMap<String, usize>, usize) {
    let mut rules: BTreeMap<String, usize> = BTreeMap::new();
    let mut seen: NodeMap<()> = NodeMap::default();
    let mut todo = vec![root.clone()];
    while let Some(node) = todo.pop() {
        if seen.insert(node.clone(), ()).is_some() {
            continue;
        }
        let Some(s) = node.as_step() else { continue };
        if is_rewrite_rule(&s.rule) {
            *rules.entry(s.rule.clone()).or_default() += 1;
        }
        todo.extend(s.premises.iter().cloned());
    }
    (rules, seen.len())
}

/// Replaces every rewrite derivation of `proof` by a `TRUST_THEORY_REWRITE` hole concluding the
/// same equality, drops the derivation steps nothing else uses, and returns the resulting proof.
pub fn fold(pool: &mut PrimitivePool, proof: ProofNodeForest, limit: usize) -> ProofNodeForest {
    let members = classify(&proof, limit);

    // The roots, keyed by id: `mutate` hands the closure rebuilt nodes, whose ids are the only
    // thing they share with the classified ones
    let mut holes: HashMap<String, Rc<Term>> = HashMap::new();
    let mut member_ids: HashSet<String> = HashSet::new();
    let mut folded_rules: BTreeMap<String, usize> = BTreeMap::new();
    let (mut member_steps, mut folded_steps) = (0usize, 0usize);
    for (node, &member) in &members.member {
        if !member {
            continue;
        }
        member_steps += 1;
        member_ids.insert(node.id().to_owned());
        if members.seeded[node] && members.consumed_outside.get(node).copied().unwrap_or(false) {
            let (rules, size) = derivation_summary(node);
            folded_steps += size;
            let names = rules
                .iter()
                .map(|(rule, count)| format!("{rule}:{count}"))
                .collect::<Vec<_>>()
                .join(",");
            for (rule, count) in rules {
                *folded_rules.entry(rule).or_default() += count;
            }
            holes.insert(
                node.id().to_owned(),
                pool.add(Term::Const(Constant::String(names))),
            );
        }
    }
    if holes.is_empty() {
        log::info!("fold: no rewrite derivation to fold ({member_steps} candidate steps)");
        return proof;
    }
    let tag = pool.add(Term::Const(Constant::String(TAG.to_owned())));

    let folded = proof
        .mutate(|_, node, _| -> Result<Rc<ProofNode>, ()> {
            let ProofNode::Step(s) = node.as_ref() else {
                return Ok(node.clone());
            };
            let Some(names) = holes.get(&s.id) else {
                return Ok(node.clone());
            };
            Ok(Rc::new(ProofNode::Step(StepNode {
                id: s.id.clone(),
                depth: s.depth,
                clause: s.clause.clone(),
                rule: "hole".to_owned(),
                premises: Vec::new(),
                args: vec![tag.clone(), names.clone()],
                discharge: Vec::new(),
                previous_step: None,
            })))
        })
        .unwrap_or_else(|()| unreachable!());

    // A member that no kept step reaches any more is dead: the members of a folded derivation,
    // unless a derivation that was left alone (glue only) or a hole's other user still needs them
    let live = live_nodes(&folded, |node| {
        node.as_step()
            .is_some_and(|s| s.rule != "hole" && member_ids.contains(&s.id))
    });
    let dead = |node: &Rc<ProofNode>| {
        node.as_step()
            .is_some_and(|s| s.rule != "hole" && member_ids.contains(&s.id))
            && !live.contains_key(node)
    };
    let (result, dropped) = drop_dead(folded, dead);

    log::info!(
        "fold: {} rewrite derivations folded into holes, {} steps in them, {} dropped; rewrite rules folded: {}",
        holes.len(),
        folded_steps,
        dropped,
        folded_rules
            .iter()
            .map(|(rule, count)| format!("{rule} {count}"))
            .collect::<Vec<_>>()
            .join(", ")
    );
    result
}

/// The nodes reachable, along premises, from any node that is not a `candidate`: what the proof
/// still uses once the candidates are only kept when reached.
fn live_nodes(proof: &ProofNodeForest, candidate: impl Fn(&Rc<ProofNode>) -> bool) -> NodeMap<()> {
    let mut sources: Vec<Rc<ProofNode>> = Vec::new();
    let mut seen: NodeMap<()> = NodeMap::default();
    let mut todo: Vec<Rc<ProofNode>> = proof.0.iter().cloned().collect();
    while let Some(node) = todo.pop() {
        if seen.insert(node.clone(), ()).is_some() {
            continue;
        }
        if !candidate(&node) {
            sources.push(node.clone());
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
                todo.extend(s.extra_steps.iter().cloned());
                todo.extend(s.outbound_premises.iter().cloned());
            }
        }
    }
    let mut live: NodeMap<()> = NodeMap::default();
    let mut todo = sources;
    while let Some(node) = todo.pop() {
        if live.insert(node.clone(), ()).is_some() {
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
            }
        }
    }
    live
}

/// Removes the `dead` nodes from the forest's roots and from every subproof's extra steps and
/// outbound premises, and returns the result with the number of nodes removed.  Dead nodes are
/// never premises of kept steps, so steps only change when a subproof below them does.
fn drop_dead(
    proof: ProofNodeForest,
    dead: impl Fn(&Rc<ProofNode>) -> bool,
) -> (ProofNodeForest, usize) {
    let mut dropped = 0usize;
    let mut cache: NodeMap<Rc<ProofNode>> = NodeMap::default();
    let mut todo: Vec<(Rc<ProofNode>, bool)> = proof
        .0
        .iter()
        .rev()
        .filter(|n| !dead(n))
        .map(|n| (n.clone(), false))
        .collect();
    dropped += proof.0.len() - todo.len();
    while let Some((node, done)) = todo.pop() {
        if cache.contains_key(&node) {
            continue;
        }
        if !done {
            todo.push((node.clone(), true));
            match node.as_ref() {
                ProofNode::Assume { .. } => (),
                ProofNode::Step(s) => todo.extend(
                    s.premises
                        .iter()
                        .chain(&s.discharge)
                        .chain(&s.previous_step)
                        .map(|p| (p.clone(), false)),
                ),
                ProofNode::Subproof(s) => {
                    todo.push((s.last_step.clone(), false));
                    todo.extend(
                        s.extra_steps
                            .iter()
                            .chain(&s.outbound_premises)
                            .filter(|n| !dead(n))
                            .map(|n| (n.clone(), false)),
                    );
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
                let extra_steps: Vec<_> = s
                    .extra_steps
                    .iter()
                    .filter(|e| !dead(e))
                    .map(|e| cache[e].clone())
                    .collect();
                let outbound_premises: Vec<_> = s
                    .outbound_premises
                    .iter()
                    .filter(|p| !dead(p))
                    .map(|p| cache[p].clone())
                    .collect();
                dropped += s.extra_steps.len() - extra_steps.len();
                let last_step = cache[&s.last_step].clone();
                if last_step == s.last_step
                    && extra_steps == s.extra_steps
                    && outbound_premises == s.outbound_premises
                {
                    node.clone()
                } else {
                    Rc::new(ProofNode::Subproof(SubproofNode {
                        last_step,
                        args: s.args.clone(),
                        outbound_premises,
                        extra_steps,
                    }))
                }
            }
        };
        cache.insert(node, rebuilt);
    }
    let roots = proof
        .0
        .iter()
        .filter(|n| !dead(n))
        .map(|n| cache[n].clone())
        .collect();
    (ProofNodeForest(roots), dropped)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser;

    const PROBLEM: &str =
        "(declare-const p Bool) (declare-const q Bool) (declare-const a Int) (declare-const b Int)
        (assert (=> (and p (and q true)) (= a b)))
        (assert (not (=> (and p q true) (= a b))))";

    fn fold_text(proof: &str) -> String {
        fold_text_limited(proof, 0)
    }

    fn fold_text_limited(proof: &str, limit: usize) -> String {
        let (problem, proof, _, mut pool) = parser::parse_instance(
            parser::Source::new(std::path::Path::new("<p>"), PROBLEM),
            parser::Source::new(std::path::Path::new("<a>"), proof),
            None,
            parser::Config::new(),
        )
        .expect("parses");
        let folded = fold(
            &mut pool,
            ProofNodeForest::from_commands(proof.commands),
            limit,
        );
        let printed = Proof {
            filename: std::path::PathBuf::new(),
            constant_definitions: Vec::new(),
            commands: folded.into_commands(),
        };
        let mut out = Vec::new();
        crate::ast::printer::write_proof_to_dest(
            &mut pool,
            &problem.prelude,
            &printed,
            &mut out,
            false,
        )
        .expect("prints");
        String::from_utf8(out).unwrap()
    }

    #[test]
    fn a_rewrite_derivation_becomes_one_hole() {
        let out = fold_text(
            "(assume h1 (=> (and p (and q true)) (= a b)))
             (assume h2 (not (=> (and p q true) (= a b))))
             (step t1 (cl (= (and p (and q true)) (and p q true))) :rule ac_simp)
             (step t2 (cl (= (= a b) (= a b))) :rule refl)
             (step t3 (cl (= (=> (and p (and q true)) (= a b)) (=> (and p q true) (= a b)))) :rule cong :premises (t1 t2))
             (step t4 (cl (not (= (=> (and p (and q true)) (= a b)) (=> (and p q true) (= a b)))) (not (=> (and p (and q true)) (= a b))) (=> (and p q true) (= a b))) :rule equiv_pos2)
             (step t5 (cl) :rule resolution :premises (t4 t3 h1 h2))",
        );
        assert!(
            out.contains(":rule hole :args (\"TRUST_THEORY_REWRITE\" \"ac_simp:1\")"),
            "{out}"
        );
        assert!(out.contains("(step t3 (cl (= (=> (and p (and q true)) (= a b)) (=> (and p q true) (= a b)))) :rule hole"), "{out}");
        assert!(!out.contains("(step t1 "), "{out}");
        assert!(!out.contains("(step t2 "), "{out}");
        assert!(
            out.contains(":rule resolution :premises (t4 t3 h1 h2)"),
            "{out}"
        );
    }

    #[test]
    fn a_cong_over_an_assumption_is_not_a_rewrite() {
        let out = fold_text(
            "(assume h1 (= a b))
             (step t1 (cl (= (= a a) (= a b))) :rule cong :premises (h1))
             (step t2 (cl (= (and p (and q true)) (and p q true))) :rule ac_simp)
             (step t3 (cl (= (and (= a a) (and p (and q true))) (and (= a b) (and p q true)))) :rule cong :premises (t1 t2))",
        );
        assert!(
            out.contains("(step t1 (cl (= (= a a) (= a b))) :rule cong :premises (h1))"),
            "{out}"
        );
        assert!(out.contains("(step t3 (cl (= (and (= a a) (and p (and q true))) (and (= a b) (and p q true)))) :rule cong :premises (t1 t2))"), "{out}");
        assert!(out.contains("(step t2 (cl (= (and p (and q true)) (and p q true))) :rule hole :args (\"TRUST_THEORY_REWRITE\" \"ac_simp:1\"))"), "{out}");
    }

    #[test]
    fn glue_only_derivations_are_left_alone() {
        let out = fold_text(
            "(step t1 (cl (= p p)) :rule refl)
             (step t2 (cl (= (and p q) (and p q))) :rule cong :premises (t1))
             (step t3 (cl (= (and p q) (and p q)) (not (and p q)) (and p q)) :rule equiv_pos2)",
        );
        assert!(out.contains(":rule refl"), "{out}");
        assert!(out.contains(":rule cong :premises (t1)"), "{out}");
        assert!(!out.contains("hole"), "{out}");
    }

    #[test]
    fn the_limit_cuts_a_derivation_below_its_top() {
        let out = fold_text_limited(
            "(assume h1 (=> (and p (and q true)) (= a b)))
             (assume h2 (not (=> (and p q true) (= a b))))
             (step t1 (cl (= (and p (and q true)) (and p q true))) :rule ac_simp)
             (step t2 (cl (= (= a b) (= a b))) :rule refl)
             (step t3 (cl (= (=> (and p (and q true)) (= a b)) (=> (and p q true) (= a b)))) :rule cong :premises (t1 t2))
             (step t4 (cl (not (= (=> (and p (and q true)) (= a b)) (=> (and p q true) (= a b)))) (not (=> (and p (and q true)) (= a b))) (=> (and p q true) (= a b))) :rule equiv_pos2)
             (step t5 (cl) :rule resolution :premises (t4 t3 h1 h2))",
            2,
        );
        assert!(out.contains("(step t1 (cl (= (and p (and q true)) (and p q true))) :rule hole :args (\"TRUST_THEORY_REWRITE\" \"ac_simp:1\"))"), "{out}");
        assert!(
            out.contains("(step t2 (cl (= (= a b) (= a b))) :rule refl)"),
            "{out}"
        );
        assert!(out.contains(":rule cong :premises (t1 t2)"), "{out}");
    }

    #[test]
    fn a_member_used_outside_becomes_its_own_hole() {
        let out = fold_text(
            "(step t1 (cl (= (and p (and q true)) (and p q true))) :rule ac_simp)
             (step t2 (cl (= (not (and p (and q true))) (not (and p q true)))) :rule cong :premises (t1))
             (step t3 (cl (= (not (and p (and q true))) (not (and p q true))) (not (not (and p (and q true)))) (not (and p q true))) :rule equiv_pos2)
             (step t4 (cl (= (and p (and q true)) (and p q true)) (not (and p (and q true))) (and p q true)) :rule equiv_pos2)
             (step t5 (cl (not (= (not (and p (and q true))) (not (and p q true))))) :rule resolution :premises (t2 t3))
             (step t6 (cl (not (= (and p (and q true)) (and p q true)))) :rule resolution :premises (t1 t4))",
        );
        assert!(
            out.contains("(step t1 (cl (= (and p (and q true)) (and p q true))) :rule hole"),
            "{out}"
        );
        assert!(
            out.contains(
                "(step t2 (cl (= (not (and p (and q true))) (not (and p q true)))) :rule hole"
            ),
            "{out}"
        );
    }
}
