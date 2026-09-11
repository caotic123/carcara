//! Bridge from the engine's generated egglog program: goals, rules, RARE names.
use std::collections::HashMap;
use egglog::ast::{
    Action as EgglogAction, Command as EgglogCommand, Expr as EgglogExpr, GenericAction,
    GenericExpr, GenericFact,
};
use super::*;

/// Recover original variable names by walking the original conclusion term
/// in parallel with its encoding, recording every hashed `Var` identifier.
pub fn collect_variable_names(
    encoded: &Term,
    original: &crate::ast::Rc<crate::ast::Term>,
    names: &mut HashMap<String, String>,
) {
    use crate::ast::Term as Original;
    // The Mk wrapper is present on formula positions but absent on the raw
    // arguments of curried App chains; tolerate both.
    let inner = match (encoded.op.as_str(), encoded.children.as_slice()) {
        ("Mk", [inner]) => inner,
        _ => encoded,
    };
    match (inner.op.as_str(), inner.children.as_slice(), original.as_ref()) {
        ("Var", [id, _], _) => {
            names.insert(id.op.clone(), format!("{}", original));
        }
        // Both builtin operators and uninterpreted functions encode as
        // @-prefixed constructors over an Args list; the original term is an
        // Op for the former and an App for the latter.
        (operator, [arguments], Original::Op(_, args) | Original::App(_, args))
            if operator.starts_with('@') =>
        {
            if let Some(elements) = list_elements(arguments) {
                if elements.len() == args.len() {
                    for (element, arg) in elements.iter().zip(args) {
                        collect_variable_names(element, arg, names);
                    }
                }
            }
        }
        ("App", [_, _], Original::App(function, args)) => {
            let mut chain = Vec::new();
            let mut current = inner;
            while let ("App", [next, argument]) = (current.op.as_str(), current.children.as_slice())
            {
                chain.push(argument);
                current = next;
            }
            chain.reverse();
            collect_variable_names(current, function, names);
            if chain.len() == args.len() {
                for (element, arg) in chain.iter().zip(args) {
                    collect_variable_names(element, arg, names);
                }
            }
        }
        _ => {}
    }
}

pub fn term_from_egglog_expr(expression: &EgglogExpr) -> Term {
    match expression {
        GenericExpr::Lit(_, literal) => Term::leaf(&literal.to_string()),
        GenericExpr::Var(_, variable) => Term::leaf(&variable.to_string()),
        GenericExpr::Call(_, operator, children) => Term::new(
            &operator.to_string(),
            children.iter().map(term_from_egglog_expr).collect(),
        ),
    }
}

pub fn generated_goals(program: &str) -> (Term, Term) {
    let commands = egglog::ast::Parser::default()
        .get_program_from_string(None, program)
        .expect("Carcara's generated egglog program should parse");
    let mut lhs = None;
    let mut rhs = None;

    for command in commands {
        let EgglogCommand::Action(EgglogAction::Let(_, name, expression)) = command else {
            continue;
        };
        match name.to_string().as_str() {
            "goal_lhs" => lhs = Some(term_from_egglog_expr(&expression)),
            "goal_rhs" => rhs = Some(term_from_egglog_expr(&expression)),
            _ => {}
        }
    }

    (
        lhs.expect("generated program should bind goal_lhs"),
        rhs.expect("generated program should bind goal_rhs"),
    )
}

/// Variable names of the goal's sides, recovered from the original
/// conclusion `(= lhs rhs)`.
pub fn goal_variable_names(
    lhs: &Term,
    rhs: &Term,
    conclusion: &crate::ast::Rc<crate::ast::Term>,
) -> HashMap<String, String> {
    let mut names = HashMap::new();
    if let crate::ast::Term::Op(crate::ast::Operator::Equals, sides) = conclusion.as_ref() {
        if sides.len() == 2 {
            collect_variable_names(lhs, &sides[0], &mut names);
            collect_variable_names(rhs, &sides[1], &mut names);
        }
    }
    names
}

pub fn pattern_from_egglog_expr(expression: &EgglogExpr) -> Pattern {
    match expression {
        GenericExpr::Lit(_, literal) => Pattern::App(leak(literal.to_string()), Vec::new()),
        GenericExpr::Var(_, variable) => Pattern::Var(leak(variable.to_string())),
        GenericExpr::Call(_, operator, children) => Pattern::App(
            leak(operator.to_string()),
            children.iter().map(pattern_from_egglog_expr).collect(),
        ),
    }
}

/// The full effective declarative rule set of a generated egglog program:
/// every unconditional rewrite, converted to reconstruction patterns.
/// Rules with conditions, native computations on their right-hand sides, or
/// global references simply never e-match in the snapshot and are covered by
/// the computational certificate kinds instead.
pub fn rules_from_generated_program(program: &str) -> Vec<Rewrite> {
    let commands = egglog::ast::Parser::default()
        .get_program_from_string(None, program)
        .expect("Carcara's generated egglog program should parse");
    let mut rules = Vec::new();
    let add = |lhs: &EgglogExpr, rhs: &EgglogExpr, rules: &mut Vec<Rewrite>| {
        rules.push(Rewrite {
            name: leak(format!("gen-{}", rules.len())),
            lhs: pattern_from_egglog_expr(lhs),
            rhs: pattern_from_egglog_expr(rhs),
        });
    };
    for command in commands {
        match &command {
            EgglogCommand::Rewrite(_, rewrite, _) if rewrite.conditions.is_empty() => {
                add(&rewrite.lhs, &rewrite.rhs, &mut rules);
            }
            EgglogCommand::BiRewrite(_, rewrite) if rewrite.conditions.is_empty() => {
                add(&rewrite.lhs, &rewrite.rhs, &mut rules);
                add(&rewrite.rhs, &rewrite.lhs, &mut rules);
            }
            // A named RARE rewrite lowers to the rule it is sugar for,
            // `((= pivot lhs)) ((union pivot rhs))`; only that unconditional
            // shape is a declarative rule, and it keeps the RARE name.
            EgglogCommand::Rule { name, rule, .. } => {
                let egglog_name = name.to_string();
                let Some(rare_name) = rare_name_of(&egglog_name) else {
                    continue;
                };
                let (
                    [GenericFact::Eq(_, GenericExpr::Var(_, pivot), lhs)],
                    [GenericAction::Union(_, GenericExpr::Var(_, target), rhs)],
                ) = (rule.body.as_slice(), rule.head.0.as_slice())
                else {
                    continue;
                };
                if pivot != target {
                    continue;
                }
                rules.push(Rewrite {
                    name: leak(rare_name.to_owned()),
                    lhs: pattern_from_egglog_expr(lhs),
                    rhs: pattern_from_egglog_expr(rhs),
                });
            }
            _ => {}
        }
    }
    rules
}

/// The RARE rule name a generated egglog rule carries, if the engine
/// compiled it from one: `rare:<name>#<k>`, the suffix keeping several
/// instantiations of one rule apart.
fn rare_name_of(egglog_name: &str) -> Option<&str> {
    let name = egglog_name.strip_prefix("rare:")?;
    Some(name.rsplit_once('#').map_or(name, |(name, _)| name))
}

/// Argument order of every RARE rule, by name: the instantiation a
/// `rare_rewrite` step spells out.
pub fn rare_arguments(
    database: &indexmap::IndexMap<String, crate::ast::rare_rules::RuleDefinition>,
) -> HashMap<String, Vec<String>> {
    database
        .iter()
        .map(|(name, rule)| (name.clone(), rule.arguments.clone()))
        .collect()
}
