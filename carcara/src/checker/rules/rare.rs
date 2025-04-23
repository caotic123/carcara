use indexmap::IndexMap;

use crate::{
    ast::{Constant, Substitution, Term},
    checker::{error::CheckerError, rules::get_premise_term},
    rare::{get_rules, rewrite_meta_terms},
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

    if let Term::Const(Constant::String(v)) = &**rule_literal.unwrap() {
        let rule = rare_rules.get(v);
        if rule.is_none() {
            return Err(CheckerError::RareRuleNotFound(v.clone()));
        }

        let rare_term = rule.unwrap();
        if rare_term.arguments.len() + 1 != args.len() {
            return Err(CheckerError::RareNumberOfPremisesWrong(
                rare_term.arguments.len(),
            ));
        }

        if conclusion.is_empty() || conclusion.len() > 1 {
            return Err(CheckerError::RareConclusionNumberInvalid());
        }

        let mut arguments = args.iter().rev();
        let mut map = IndexMap::new();

        for arg in rare_term.arguments.iter().rev() {
            let arg_sort = rare_term.parameters.get(arg).unwrap();
            map.insert(
                pool.add(Term::Var(arg.clone(), arg_sort.term.clone())),
                arguments.next().unwrap().clone(),
            );
        }

        if rare_term.premises.len() != premises.len() {
            return Err(CheckerError::RareNumberOfPremisesWrong(
                rare_term.premises.len(),
            ));
        }

        let mut rare_premises = rare_term.premises.iter();

        for premise in premises {
            let premise = get_premise_term(premise)?;
            let rare_premise = rare_premises.next().unwrap();
            let rare_premise = Substitution::new(pool, map.clone())
                .unwrap()
                .apply(pool, rare_premise);
            let rare_premise =
                rewrite_meta_terms(pool, rare_premise, &mut IndexMap::new(), &get_rules());

            if *premise != rare_premise {
                return Err(CheckerError::RarePremiseAreNotEqual(
                    premise.clone(),
                    rare_premise.clone(),
                ));
            }
        }

        let got = Substitution::new(pool, map)
            .unwrap()
            .apply(pool, &rare_term.conclusion);

        for premise in premises {
            let premise = get_premise_term(premise)?;
            let premise_rare =
                rewrite_meta_terms(pool, premise.clone(), &mut IndexMap::new(), &get_rules());
            if *premise != premise_rare {
                return Err(CheckerError::RarePremiseAreNotEqual(
                    premise.clone(),
                    premise_rare,
                ));
            }
        }

        let rule_conclusion = rewrite_meta_terms(pool, got, &mut IndexMap::new(), &get_rules());
        if rule_conclusion != conclusion[0] {
            return Err(CheckerError::RareConclusionAreNotEqual(
                rule_conclusion,
                conclusion[0].clone(),
            ));
        }

        return Ok(());
    }

    return Err(CheckerError::RareRuleExpectedLiteral(
        rule_literal.unwrap().clone(),
    ));
}
