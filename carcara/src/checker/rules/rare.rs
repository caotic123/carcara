use indexmap::IndexMap;

use crate::{
    ast::{rules::AttributeParameters, Constant, Polyeq, Rc, Term},
    checker::{error::CheckerError, rules::get_premise_term},
    // rare::{apply_arg, convert_rare_term_to_term},
};

use super::{RuleArgs, RuleResult};

pub fn check_rare(
    RuleArgs {
        premises,
        conclusion,
        pool,
        args,
        rare_rules,
        ..
    }: RuleArgs,
) -> RuleResult {
    let rule_literal = args.get(0);
    if rule_literal == None {
        return Err(CheckerError::RareNotSpecifiedRule);
    }

    Ok(())

    // if let Term::Const(Constant::String(v)) = &**rule_literal.unwrap() {
    //     let rule = rare_rules.get(v);
    //     if rule.is_none() {
    //         return Err(CheckerError::RareRuleNotFound(v.clone()));
    //     }

    //     let mut rare_term = rule.unwrap().clone();
    //     rare_term.arguments.reverse();
    //     let mut type_equations: IndexMap<String, Rc<Term>> = IndexMap::new();

    //     for term in args[1..].iter() {
    //         let argument = rare_term.arguments.pop();
    //         if argument == None {
    //             return Err(CheckerError::RareNumberOfPremisesWrong(args.len()));
    //         }

    //         let argument = argument.unwrap();
    //         let parameter = rare_term.parameters.0.get(&argument);
    //         if parameter.is_none() {
    //             return Err(CheckerError::RareArgumentNotFound(argument.clone()));
    //         }

    //         let parameter = parameter.unwrap();
    //         let mut sort = None;
    //         if let Some(list) = match_term!((rarelist ...) = term) {
    //             if parameter.attribute != AttributeParameters::List {
    //                 return Err(CheckerError::RareArgumentIsNotRareList(argument));
    //             }

    //             for variable in list {
    //                 if sort != None && sort != Some(pool.sort(variable)) {
    //                     return Err(CheckerError::RareListNotSortUniform(
    //                         term.clone(),
    //                         sort.unwrap(),
    //                         pool.sort(variable),
    //                     ));
    //                 }
    //                 sort = Some(pool.sort(variable))
    //             }
    //         } else {
    //             sort = Some(pool.sort(term));
    //         }

    //         match sort {
    //             Some(sort) => {
    //                 apply_arg(
    //                     argument.clone(),
    //                     parameter.clone(),
    //                     &mut rare_term,
    //                     term.clone(),
    //                     sort.clone(),
    //                 )?;

    //                 type_equations.insert(argument, sort);
    //             }
    //             None => {
    //                 return Err(CheckerError::RareNotFoundSort(term.clone()));
    //             }
    //         }
    //     }

    //     rare_term.premises.reverse();
    //     let mut premises = premises.iter();
    //     for rare_premise in rare_term.premises {
    //         let premise = premises.next();
    //         if premise == None {
    //             return Err(CheckerError::RareNumberOfPremisesWrong(premises.len()));
    //         }

    //         let premise = premise.unwrap();
    //         let term = get_premise_term(premise)?;
    //         let rare_premise = convert_rare_term_to_term(rare_premise, &type_equations, pool);
    //         let polyeq = Polyeq::new().alpha_equiv(true).eq(term, &rare_premise);
    //         if !polyeq {
    //             return Err(CheckerError::RarePremiseAreNotEqual(
    //                 term.clone(),
    //                 rare_premise,
    //             ));
    //         }
    //     }

    //     if conclusion.is_empty() || conclusion.len() > 1 {
    //         return Err(CheckerError::RareConclusionNumberInvalid());
    //     }

    //     let rare_conclusion =
    //         convert_rare_term_to_term(rare_term.conclusion.clone(), &type_equations, pool);
    //     let polyeq = Polyeq::new()
    //         .alpha_equiv(true)
    //         .eq(&conclusion[0], &rare_conclusion);

    //     if !polyeq {
    //         return Err(CheckerError::RareConclusionAreNotEqual(
    //             conclusion[0].clone(),
    //             rare_conclusion,
    //         ));
    //     }

    //     return Ok(());
    // }

    // return Err(CheckerError::RareRuleExpectedLiteral(
    //     rule_literal.unwrap().clone(),
    // ));
}
