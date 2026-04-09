use crate::{ast::*, rare::engine::reconstruct_rule};

use super::{ElaborationStep, Elaborator, IdHelper};

pub fn elaborate_rule(
    elaborator: &mut Elaborator,
    root: &Rc<ProofNode>,
    step: &StepNode,
    pipeline: &[ElaborationStep],
) -> Option<Rc<ProofNode>> {
    if pipeline
        .iter()
        .any(|step| matches!(step, ElaborationStep::GlobalRareElaboration))
    {
        return Some(Rc::new(ProofNode::Step(step.clone())));
    }

    let mut ids = IdHelper::new(&step.id);
    reconstruct_rule(
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
