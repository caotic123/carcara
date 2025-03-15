use indexmap::IndexMap;

use crate::{
    ast::{
        alpha_equiv, polyeq, rules::{AttributeParameters, RuleDefinition}, Polyeq, Rc, Term
    },
    checker::{error::CheckerError, rules::{get_premise_term, rare}},
    rare::{apply_arg, convert_rare_term_to_term},
};

use super::{Premise, RuleArgs, RuleResult};

pub fn check_rare(
    rule: &RuleDefinition,
    RuleArgs {
        premises,
        conclusion,
        pool,
        args,
        ..
    }: RuleArgs,
) -> RuleResult {
    let mut rare_term = rule.clone();
    rare_term.arguments.0.reverse();
    let mut type_equations: IndexMap<String, Rc<Term>> = IndexMap::new();

    for term in args.iter() {
        let argument = rare_term.arguments.0.pop();
        if argument == None {
            return Err(CheckerError::RareNumberOfPremisesWrong(args.len()));
        }

        let argument = argument.unwrap();
        let parameter = rare_term.parameters.0.get(&argument);
        if parameter.is_none() {
            return Err(CheckerError::RareArgumentNotFound(argument.clone()));
        }

        let parameter = parameter.unwrap();
        let mut sort = None;
        if let Some(list) = match_term!((rarelist ...) = term) {
            if parameter.attribute != AttributeParameters::List {
                return Err(CheckerError::RareArgumentIsNotRareList(argument));
            }

            for variable in list {
                if sort != None && sort != Some(pool.sort(variable)) {
                    return Err(CheckerError::RareListNotSortUniform(
                        term.clone(),
                        sort.unwrap(),
                        pool.sort(variable),
                    ));
                }
                sort = Some(pool.sort(variable))
            }
        } else {
            sort = Some(pool.sort(term));
        }

        match sort {
            Some(sort) => {
                apply_arg(
                    argument.clone(),
                    parameter.clone(),
                    &mut rare_term,
                    term.clone(),
                    sort.clone(),
                )?;

                type_equations.insert(argument, sort);
            }
            None => {
                return Err(CheckerError::RareNotFoundSort(term.clone()));
            }
        }
    }

    rare_term.premises.reverse();
    let mut premises = premises.iter();
    for rare_premise in rare_term.premises {
        let premise = premises.next();
        if premise == None {
            return Err(CheckerError::RareNumberOfPremisesWrong(premises.len()));
        }

        let premise = premise.unwrap();
        let term = get_premise_term(premise)?;
        let rare_premise = convert_rare_term_to_term(rare_premise, &type_equations, pool);
        let polyeq = Polyeq::new().alpha_equiv(true).eq(term, &rare_premise);
        if !polyeq {
            return Err(CheckerError::RarePremiseAreNotEqual(term.clone(), rare_premise));
        }        
    }  

    if conclusion.is_empty() || conclusion.len() > 1{
        return Err(CheckerError::RareConclusionNumberInvalid()) ;
    }

    let rare_conclusion = convert_rare_term_to_term(rule.conclusion.clone(), &type_equations, pool);
    let polyeq = Polyeq::new().alpha_equiv(true).eq(&conclusion[0], &rare_conclusion);

    if !polyeq {
        return Err(CheckerError::RareConclusionAreNotEqual(conclusion[0].clone(), rare_conclusion));
    }     

    return Ok(())
}
