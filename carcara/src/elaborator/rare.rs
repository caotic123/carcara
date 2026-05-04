use crate::{ast::*, rare::engine::reconstruct_rule};

use super::{Elaborator, IdHelper};

pub fn elaborate_rule(elaborator: &mut Elaborator, node: &Rc<ProofNode>) -> Option<Rc<ProofNode>> {
    let step = node.as_step()?;
    let mut ids = IdHelper::new(&step.id);
    let print_generated_egglog = elaborator
        .config
        .hole_options
        .as_ref()
        .is_some_and(|options| options.print_generated_egglog);
    reconstruct_rule(
        elaborator.pool,
        step.clause[0].clone(),
        node,
        elaborator.rules,
        elaborator.config.rare_egglog_options,
        print_generated_egglog,
    );

    return Some(Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth: step.depth,
        ..step.clone()
    })));
}
