//! Compile supplied RARE definitions, preserving sequence parameters until
//! each operator occurrence interprets them. Every rule in the supplied database
//! is compiled; proof references are validated separately.

use super::ast::*;
use crate::ast::{
    Constant, Operator, Proof, ProofCommand, Rc, Sort, Term,
    rare_rules::{AttributeParameters, RuleDefinition, Rules},
};
use indexmap::IndexMap;

#[derive(Debug, thiserror::Error)]
#[error("cannot translate RARE rule '{rule}': {reason}")]
pub struct RareTranslationError {
    pub rule: String,
    pub reason: String,
}

pub struct CompiledRules {
    pub declarations: EunoiaProof,
    pub names: IndexMap<String, String>,
}

fn id(name: impl Into<String>) -> EunoiaTerm {
    EunoiaTerm::Id(name.into())
}

fn app(name: impl Into<String>, args: Vec<EunoiaTerm>) -> EunoiaTerm {
    EunoiaTerm::App(name.into(), args)
}

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

/// Compile the complete rule database in its declaration order.
pub fn compile(rules: &Rules) -> Result<CompiledRules, RareTranslationError> {
    let mut names = IndexMap::new();
    let mut declarations = Vec::new();
    for (i, (name, rule)) in rules.rules.iter().enumerate() {
        // Keep supplied rule names in their own namespace, even if a RARE
        // definition has the same name as an Alethe rule such as `refl`.
        let generated = format!("@rare.rule.{i}");
        declarations.push(RuleCompiler { rule }.compile(&generated)?);
        names.insert(name.clone(), generated);
    }
    Ok(CompiledRules { declarations, names })
}

struct RuleCompiler<'a> {
    rule: &'a RuleDefinition,
}

impl RuleCompiler<'_> {
    fn error(&self, reason: impl Into<String>) -> RareTranslationError {
        RareTranslationError {
            rule: self.rule.name.clone(),
            reason: reason.into(),
        }
    }

    fn sort(&self, sort: &Sort) -> Result<EunoiaType, RareTranslationError> {
        Ok(match sort {
            Sort::Bool => EunoiaType::Bool,
            Sort::Int => EunoiaType::Name("Int".into()),
            Sort::Real => EunoiaType::Real,
            Sort::Type => EunoiaType::Type,
            Sort::Var(name) => EunoiaType::Name(name.clone()),
            Sort::Atom(name, args) if args.is_empty() => EunoiaType::Name(name.to_string()),
            Sort::Function(sorts) if sorts.len() >= 2 => EunoiaType::Fun(
                vec![],
                sorts[..sorts.len() - 1]
                    .iter()
                    .map(|s| self.sort(s))
                    .collect::<Result<_, _>>()?,
                Box::new(self.sort(sorts.last().unwrap())?),
            ),
            _ => return Err(self.error(format!("unsupported sort '{sort}'"))),
        })
    }

    fn is_list(&self, name: &str) -> bool {
        self.rule
            .parameters
            .get(name)
            .is_some_and(|p| p.attribute == AttributeParameters::List)
    }

    fn sort_term(&self, sort: &Sort) -> Result<EunoiaTerm, RareTranslationError> {
        // Ethos binds argument terms, not the type parameters appearing only
        // in their declarations. Recover such a type from its scalar anchor.
        let name = sort.to_string();
        if self
            .rule
            .parameters
            .get(&name)
            .is_some_and(|p| p.sort.as_ref() == &Sort::Type)
            && !self.rule.arguments.contains(&name)
        {
            if let Some(anchor) = self.rule.arguments.iter().find(|arg| {
                self.rule.parameters.get(*arg).is_some_and(|p| {
                    p.attribute != AttributeParameters::List && p.sort.as_ref() == sort
                })
            }) {
                return Ok(app("eo::typeof", vec![id(anchor.clone())]));
            }
            return Err(self.error(format!(
                "no scalar argument determines element sort '{sort}'"
            )));
        }
        Ok(EunoiaTerm::Type(self.sort(sort)?))
    }

    fn sequence(&self, operands: &[Rc<Term>]) -> Result<EunoiaTerm, RareTranslationError> {
        if operands.is_empty() {
            return Ok(id("eo::List::nil"));
        }
        Ok(app(
            "eo::List::cons",
            operands
                .iter()
                .map(|x| self.term(x, true))
                .collect::<Result<_, _>>()?,
        ))
    }

    fn term(&self, term: &Term, allow_list: bool) -> Result<EunoiaTerm, RareTranslationError> {
        Ok(match term {
            Term::Var(name, _) => {
                if self.is_list(name) && !allow_list {
                    return Err(self.error(format!(
                        "list parameter '{name}' used outside a supported variadic application"
                    )));
                }
                id(name.clone())
            }
            Term::Const(Constant::Integer(n)) => EunoiaTerm::Numeral(n.clone()),
            Term::Const(Constant::Real(r)) => EunoiaTerm::Decimal(r.clone()),
            Term::Op(Operator::True, _) => EunoiaTerm::True,
            Term::Op(Operator::False, _) => EunoiaTerm::False,
            Term::Op(
                op @ (Operator::And | Operator::Or | Operator::Add | Operator::Mult),
                operands,
            ) => {
                let sort = match op {
                    Operator::And | Operator::Or => Sort::Bool,
                    _ => operands.first().map(|x| x.raw_sort()).unwrap_or(Sort::Int),
                };
                if operands.iter().any(|x| x.raw_sort() != sort) {
                    return Err(
                        self.error(format!("mixed operand sorts in '{op}' are not supported"))
                    );
                }
                // Normalize once after all ordinary operands and list fragments
                // have been assembled; never flatten ordinary nested formulas.
                app(
                    "eo::list_singleton_elim",
                    vec![
                        id(op.to_string()),
                        app(
                            "$normalize_eo_list",
                            vec![
                                self.sort_term(&sort)?,
                                self.sort_term(&sort)?,
                                id(op.to_string()),
                                self.sequence(operands)?,
                            ],
                        ),
                    ],
                )
            }
            Term::Op(Operator::Distinct, operands) => {
                let sort = operands
                    .first()
                    .ok_or_else(|| self.error("cannot infer the element sort of empty distinct"))?
                    .raw_sort();
                if operands.iter().any(|x| x.raw_sort() != sort) {
                    return Err(self.error("mixed operand sorts in distinct"));
                }
                app(
                    "eo::list_singleton_elim",
                    vec![
                        id("and"),
                        app(
                            "$normalize_eo_pairwise",
                            vec![
                                self.sort_term(&sort)?,
                                id("distinct"),
                                self.sequence(operands)?,
                                id("eo::List::nil"),
                            ],
                        ),
                    ],
                )
            }
            Term::Op(
                op @ (Operator::Not
                | Operator::Implies
                | Operator::Xor
                | Operator::Ite
                | Operator::Equals
                | Operator::GreaterThan
                | Operator::GreaterEq
                | Operator::LessThan
                | Operator::LessEq
                | Operator::Sub
                | Operator::IntDiv
                | Operator::RealDiv
                | Operator::Mod
                | Operator::Abs
                | Operator::ToInt
                | Operator::ToReal
                | Operator::IsInt),
                operands,
            ) => app(
                op.to_string(),
                operands
                    .iter()
                    .map(|x| self.term(x, false))
                    .collect::<Result<_, _>>()?,
            ),
            Term::App(f, operands) => {
                // RARE list splicing into arbitrary functions needs arity-aware
                // application construction and is deliberately rejected here.
                EunoiaTerm::HOApp(
                    Box::new(self.term(f, false)?),
                    operands
                        .iter()
                        .map(|x| self.term(x, false))
                        .collect::<Result<_, _>>()?,
                )
            }
            _ => return Err(self.error(format!("unsupported term in rule: {term}"))),
        })
    }

    fn compile(&self, generated_name: &str) -> Result<EunoiaCommand, RareTranslationError> {
        let mut params = Vec::new();
        let mut requirements = Vec::new();
        for (name, parameter) in &self.rule.parameters {
            if parameter.sort.as_ref() != &Sort::Type && !self.rule.arguments.contains(name) {
                return Err(self.error(format!("parameter '{name}' is not supplied in :args; inference from computed premises is not supported")));
            }
            if parameter.sort.as_ref() == &Sort::Type && !self.rule.arguments.contains(name) {
                let anchored = self.rule.arguments.iter().any(|arg| {
                    self.rule.parameters.get(arg).is_some_and(|p| {
                        p.attribute != AttributeParameters::List && p.sort.to_string() == *name
                    })
                });
                if !anchored {
                    return Err(self.error(format!(
                        "type parameter '{name}' cannot be inferred from an ordinary argument"
                    )));
                }
            }
            let list = parameter.attribute == AttributeParameters::List;
            let element_sort = self.sort(&parameter.sort)?;
            params.push(EunoiaTypedParam {
                name: name.clone(),
                eunoia_type: if list {
                    EunoiaType::Name("eo::List".into())
                } else {
                    element_sort.clone()
                },
                attrs: if list {
                    vec![EunoiaConsAttr::List]
                } else {
                    vec![]
                },
            });
            if list {
                requirements.push((
                    app(
                        "$normalize_eo_list",
                        vec![
                            self.sort_term(&parameter.sort)?,
                            EunoiaTerm::Type(EunoiaType::Name("eo::List".into())),
                            id("eo::List::cons"),
                            id(name.clone()),
                        ],
                    ),
                    id(name.clone()),
                ));
            }
        }

        // Computed applications cannot occur in premise patterns. Bind each
        // premise formula first and compare it with its instantiated template.
        let mut premises = Vec::new();
        for (i, premise) in self.rule.premises.iter().enumerate() {
            let mut name = format!("@rare.premise.{i}");
            while self.rule.parameters.contains_key(&name) {
                name.push('_');
            }
            params.push(EunoiaTypedParam {
                name: name.clone(),
                eunoia_type: EunoiaType::Bool,
                attrs: vec![],
            });
            premises.push(app("@cl", vec![id(name.clone())]));
            requirements.push((id(name), self.term(premise, false)?));
        }
        Ok(EunoiaCommand::DeclareRule {
            name: generated_name.into(),
            typed_params: EunoiaList { list: params },
            arguments: self
                .rule
                .arguments
                .iter()
                .map(|name| id(name.clone()))
                .collect(),
            premises,
            requirements,
            conclusion: app("@cl", vec![self.term(&self.rule.conclusion, false)?]),
        })
    }
}
