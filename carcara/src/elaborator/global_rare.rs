use super::Elaborator;
use crate::{ast::*, rare::engine::reconstruct_global_rules};
use std::collections::HashMap;

pub fn global_rare_elaboration(elaborator: &mut Elaborator, root: &Rc<ProofNode>) -> Rc<ProofNode> {
    let goals = collect_reachable_goals(root);
    if goals.is_empty() {
        return root.clone();
    }

    let goal_refs: Vec<_> = goals
        .iter()
        .map(|(conclusion, node)| (conclusion.clone(), node))
        .collect();
    let print_generated_egglog = elaborator
        .config
        .hole_options
        .as_ref()
        .is_some_and(|options| options.print_generated_egglog);
    reconstruct_global_rules(
        elaborator.pool,
        &goal_refs,
        elaborator.rules,
        print_generated_egglog,
    );

    root.clone()
}

fn collect_reachable_goals(root: &Rc<ProofNode>) -> Vec<(Rc<Term>, Rc<ProofNode>)> {
    let mut nodes_by_id = HashMap::new();
    root.traverse(|node| {
        if matches!(node.as_ref(), ProofNode::Step(_)) {
            nodes_by_id.insert(node.id().to_owned(), node.clone());
        }
    });

    let mut goals = Vec::new();
    let commands = root.into_commands();
    collect_goals_from_commands(&commands, &nodes_by_id, &mut goals);
    goals
}

fn collect_goals_from_commands(
    commands: &[ProofCommand],
    nodes_by_id: &HashMap<String, Rc<ProofNode>>,
    out: &mut Vec<(Rc<Term>, Rc<ProofNode>)>,
) {
    for command in commands {
        match command {
            ProofCommand::Step(step) if is_global_rare_target(step) => {
                if step.clause.len() != 1 {
                    log::warn!(
                        "skipping global rare elaboration for step `{}`: expected unit clause, found {} literals",
                        step.id,
                        step.clause.len()
                    );
                    continue;
                }

                if let Some(node) = nodes_by_id.get(&step.id) {
                    out.push((step.clause[0].clone(), node.clone()));
                }
            }
            ProofCommand::Subproof(subproof) => {
                collect_goals_from_commands(&subproof.commands, nodes_by_id, out);
            }
            _ => (),
        }
    }
}

fn is_global_rare_target(step: &ProofStep) -> bool {
    step.rule == "hole"
        && step
            .args
            .first()
            .is_some_and(|arg| **arg == Term::new_string("TRUST_THEORY_REWRITE"))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mk_step(
        pool: &mut PrimitivePool,
        id: &str,
        conclusion: Rc<Term>,
        is_target: bool,
        premises: Vec<Rc<ProofNode>>,
    ) -> Rc<ProofNode> {
        let args = if is_target {
            vec![pool.add(Term::new_string("TRUST_THEORY_REWRITE"))]
        } else {
            vec![pool.add(Term::new_string("OTHER"))]
        };

        Rc::new(ProofNode::Step(StepNode {
            id: id.to_owned(),
            depth: 0,
            clause: vec![conclusion],
            rule: "hole".to_owned(),
            premises,
            args,
            discharge: Vec::new(),
            previous_step: None,
        }))
    }

    #[test]
    fn collects_only_reachable_global_rare_targets_in_proof_order() {
        let mut pool = PrimitivePool::new();
        let true_term = pool.bool_true();
        let false_term = pool.bool_false();
        let done_term = pool.add(Term::new_string("done"));
        let step_1 = mk_step(&mut pool, "t1", true_term, true, Vec::new());
        let step_2 = mk_step(&mut pool, "t2", false_term, false, Vec::new());
        let root = mk_step(
            &mut pool,
            "t3",
            done_term,
            true,
            vec![step_1.clone(), step_2],
        );

        let goals = collect_reachable_goals(&root);
        let collected: Vec<_> = goals.iter().map(|(_, node)| node.id().to_owned()).collect();

        assert_eq!(collected, vec!["t1".to_string(), "t3".to_string()]);
    }
}
