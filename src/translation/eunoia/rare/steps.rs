//! The `rare_rewrite` steps of a proof: their references to the supplied
//! definitions, and the sorts of their empty list arguments.

use super::RareTranslationError;
use crate::ast::{
    Constant, Operator, Proof, ProofCommand, Rc, Sort, Term,
    rare_rules::{AttributeParameters, RuleDefinition, Rules},
};

fn validate_steps(commands: &[ProofCommand], rules: &Rules) -> Result<(), RareTranslationError> {
    for command in commands {
        match command {
            ProofCommand::Subproof(subproof) => validate_steps(&subproof.commands, rules)?,
            ProofCommand::Step(step) if step.rule == "rare_rewrite" => {
                let Some(Term::Const(Constant::String(name))) =
                    step.args.first().map(|x| x.as_ref())
                else {
                    return Err(RareTranslationError {
                        rule: step.id.clone(),
                        reason: "expected a rule name as the first argument".into(),
                    });
                };
                let rule = rules.rules.get(name).ok_or_else(|| RareTranslationError {
                    rule: name.clone(),
                    reason: "definition missing; supply --rare-file".into(),
                })?;
                if step.args.len() != rule.arguments.len() + 1 {
                    return Err(RareTranslationError {
                        rule: name.clone(),
                        reason: format!("wrong argument count in step '{}'", step.id),
                    });
                }
                for (parameter, value) in rule.arguments.iter().zip(&step.args[1..]) {
                    let parameter =
                        rule.parameters
                            .get(parameter)
                            .ok_or_else(|| RareTranslationError {
                                rule: name.clone(),
                                reason: format!("undeclared argument '{parameter}'"),
                            })?;
                    let is_list = matches!(value.as_ref(), Term::Op(Operator::RareList, _));
                    if is_list != (parameter.attribute == AttributeParameters::List) {
                        return Err(RareTranslationError {
                            rule: name.clone(),
                            reason: format!("list/scalar argument mismatch in step '{}'", step.id),
                        });
                    }
                }
            }
            _ => {}
        }
    }
    Ok(())
}

pub fn validate_proof(rules: &Rules, proof: &Proof) -> Result<(), RareTranslationError> {
    validate_steps(&proof.commands, rules)
}

/// The element sort of an empty sequence passed as the `index`-th argument of
/// a step using `rule`. The rare-list encoding states it in the nil.
pub fn empty_list_sort(rule: &RuleDefinition, index: usize, args: &[Rc<Term>]) -> Option<Sort> {
    let sort = rule
        .parameters
        .get(rule.arguments.get(index)?)?
        .sort
        .as_ref();
    if !rule
        .parameters
        .get(&sort.to_string())
        .is_some_and(|p| p.sort.as_ref() == &Sort::Type)
    {
        return Some(sort.clone());
    }
    // A type parameter is instantiated by the sort of its scalar anchor, as
    // in `RuleCompiler::sort_term`.
    rule.arguments.iter().zip(args).find_map(|(arg, value)| {
        rule.parameters
            .get(arg)
            .is_some_and(|p| p.attribute != AttributeParameters::List && p.sort.as_ref() == sort)
            .then(|| value.raw_sort())
    })
}
