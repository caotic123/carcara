use crate::{ast::*, checker::error::CheckerError};

use super::IdHelper;

pub fn elaborate_rule(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, CheckerError> {
    let mut ids = IdHelper::new(&step.id);

    return Ok(Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth: step.depth,
        ..step.clone()
    })))
}