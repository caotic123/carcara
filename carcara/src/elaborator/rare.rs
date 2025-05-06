use crate::{ast::*, checker::error::CheckerError, rare::engine::reconstruct_rule};

use super::{Elaborator, IdHelper};

pub fn elaborate_rule(
    elaborator: &mut Elaborator,
    root: &Rc<ProofNode>,
    step: &StepNode,
) -> Option<Rc<ProofNode>> {
    let mut ids = IdHelper::new(&step.id);
    let rules_reconstruction = reconstruct_rule(
        elaborator.pool,
        step.clause[0].clone(),
        root,
        elaborator.rules,
    );

    return Some(Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth: step.depth,
        ..step.clone()
    })));
}
