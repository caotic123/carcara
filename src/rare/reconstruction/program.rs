//! Bridge from the engine's generated egglog program: goals, rules, RARE names.
use std::collections::HashMap;
use egglog::ast::{Action as EgglogAction, Command as EgglogCommand, Expr as EgglogExpr, GenericExpr};
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
    let mut add = |lhs: &EgglogExpr, rhs: &EgglogExpr, rules: &mut Vec<Rewrite>| {
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
            _ => {}
        }
    }
    rules
}

/// Compile a RARE rule term into the encoded pattern shape the engine
/// generates: rule parameters become pattern variables (their names are
/// preserved verbatim by the compilation), operators and uninterpreted
/// functions become `@`-prefixed constructors over `Args` lists.
pub fn encode_rare_pattern(
    term: &crate::ast::Rc<crate::ast::Term>,
    parameters: &indexmap::IndexMap<String, crate::ast::rare_rules::TypeParameter>,
) -> Option<Pattern> {
    use crate::ast::Term as Original;
    let mk = |inner: Pattern| Pattern::App("Mk", vec![inner]);
    let encode_call = |operator: String,
                       args: &[crate::ast::Rc<crate::ast::Term>]|
     -> Option<Pattern> {
        let list = args.iter().rev().try_fold(
            Pattern::App("Empty", Vec::new()),
            |tail, argument| {
                Some(Pattern::App(
                    "Args",
                    vec![encode_rare_pattern(argument, parameters)?, tail],
                ))
            },
        )?;
        Some(mk(Pattern::App(leak(operator), vec![list])))
    };
    match term.as_ref() {
        Original::Var(name, _) if parameters.contains_key(name) => {
            Some(mk(Pattern::Var(leak(name.clone()))))
        }
        // Boolean constants are operators in Carcara's AST but literals in
        // the encoding; without this arm the generic operator case would
        // encode them as `@true`/`@false` applications and no `-> true`
        // rule would ever map back to its RARE name.
        Original::Op(crate::ast::Operator::True, args) if args.is_empty() => {
            Some(mk(Pattern::App("Bool", vec![Pattern::App("true", Vec::new())])))
        }
        Original::Op(crate::ast::Operator::False, args) if args.is_empty() => {
            Some(mk(Pattern::App("Bool", vec![Pattern::App("false", Vec::new())])))
        }
        Original::Op(operator, args) => encode_call(format!("@{operator}"), args),
        Original::App(function, args) => {
            let Original::Var(name, _) = function.as_ref() else {
                return None;
            };
            encode_call(format!("@{name}"), args)
        }
        Original::Const(crate::ast::Constant::Integer(value)) => Some(mk(Pattern::App(
            "Num",
            vec![Pattern::App(leak(value.to_string()), Vec::new())],
        ))),
        Original::Const(crate::ast::Constant::Real(value)) => {
            let (numer, denom) = value.clone().into_numer_denom();
            Some(mk(Pattern::App(
                "Real",
                vec![
                    Pattern::App(leak(numer.to_string()), Vec::new()),
                    Pattern::App(leak(denom.to_string()), Vec::new()),
                ],
            )))
        }
        _ => match format!("{term}").as_str() {
            "true" => Some(mk(Pattern::App("Bool", vec![Pattern::App("true", Vec::new())]))),
            "false" => Some(mk(Pattern::App("Bool", vec![Pattern::App("false", Vec::new())]))),
            _ => None,
        },
    }
}

/// Associate generated egglog rewrites back to the RARE rules they were
/// compiled from, by structural pattern equality of both sides.  Returns
/// generated-name -> (RARE name, argument order).
pub fn rare_rule_index(
    database: &indexmap::IndexMap<String, crate::ast::rare_rules::RuleDefinition>,
    generated: &[Rewrite],
) -> HashMap<String, (String, Vec<String>)> {
    use crate::ast::Term as Original;
    let mut compiled = Vec::new();
    for (name, rule) in database {
        if !rule.premises.is_empty() {
            continue;
        }
        let Original::Op(crate::ast::Operator::Equals, sides) = rule.conclusion.as_ref() else {
            continue;
        };
        if sides.len() != 2 {
            continue;
        }
        let (Some(lhs), Some(rhs)) = (
            encode_rare_pattern(&sides[0], &rule.parameters),
            encode_rare_pattern(&sides[1], &rule.parameters),
        ) else {
            continue;
        };
        compiled.push((name.clone(), rule.arguments.clone(), lhs, rhs));
    }

    let mut index = HashMap::new();
    for rewrite in generated {
        for (name, arguments, lhs, rhs) in &compiled {
            if &rewrite.lhs == lhs && &rewrite.rhs == rhs {
                index.insert(rewrite.name.to_owned(), (name.clone(), arguments.clone()));
                break;
            }
        }
    }
    index
}
