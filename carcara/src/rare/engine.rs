use crate::{
    ast::{rules::Rules, Constant, Operator, PrimitivePool, ProofNode, Rc, Term},
    rare::{
        language::*,
        meta::lower_egg_language,
        util::{clauses_to_or, get_equational_terms},
    },
};
use egglog::{self, EGraph};
use indexmap::{IndexMap, IndexSet};
use rug::Integer;

type EggFunctions = IndexSet<String>;

pub fn create_headers() -> EggLanguage {
    vec![
        EggStatement::DataType(
            "Term".to_string(),
            vec![
                Constructor {
                    constr: (
                        "App".to_string(),
                        vec![
                            ConstType::ConstrType("Term".to_string()),
                            ConstType::ConstrType("Term".to_string()),
                        ],
                    ),
                },
                Constructor {
                    constr: ("Var".to_string(), vec![ConstType::Var]),
                },
                Constructor {
                    constr: ("Bool".to_string(), vec![ConstType::Bool]),
                },
                Constructor {
                    constr: ("Num".to_string(), vec![ConstType::Integer]),
                },
                Constructor {
                    constr: ("Op".to_string(), vec![ConstType::Operator]),
                },
                Constructor {
                    constr: ("Empty".to_string(), vec![]),
                },
                Constructor {
                    constr: (
                        "Args".to_string(),
                        vec![
                            ConstType::ConstrType("Term".to_string()),
                            ConstType::ConstrType("Term".to_string()),
                        ],
                    ),
                },
                Constructor {
                    constr: (
                        "Mk".to_string(),
                        vec![ConstType::ConstrType("Term".to_string())],
                    ),
                },
            ],
        ),
        EggStatement::Rule(
            vec![EggExpr::Equal(
                Box::new(EggExpr::Mk(Box::new(EggExpr::Literal("x".to_string())))),
                Box::new(EggExpr::Mk(Box::new(EggExpr::Literal("y".to_string())))),
            )],
            vec![EggExpr::Union(
                Box::new(EggExpr::Literal("x".to_string())),
                Box::new(EggExpr::Literal("y".to_string())),
            )],
        ),
        // EggStatement::Rule(
        //     vec![EggExpr::Equal(
        //         Box::new(EggExpr::Literal("x".to_string())),
        //         Box::new(EggExpr::Literal("y".to_string())),
        //     )],
        //     vec![EggExpr::Union(
        //         Box::new(EggExpr::Mk(Box::new(EggExpr::Literal("x".to_string())))),
        //         Box::new(EggExpr::Mk(Box::new(EggExpr::Literal("y".to_string())))),
        //     )],
        // ),
    ]
}

pub fn to_egg_expr(
    term_rc: &Rc<Term>,
    subs: &IndexMap<&String, EggExpr>,
    func_cache: &mut EggFunctions,
    encapsule: bool,
) -> Option<EggExpr> {
    pub fn to_raw_egg(
        term_rc: &Rc<Term>,
        subs: &IndexMap<&String, EggExpr>,
        func_cache: &mut EggFunctions,
    ) -> Option<EggExpr> {
        match &**term_rc {
            Term::Const(c) => match c {
                Constant::Integer(i) => Some(EggExpr::Num(i.clone())),
                Constant::String(s) => Some(EggExpr::String(s.clone())),
                Constant::BitVec(i, j) => Some(EggExpr::BitVec(i.clone(), j.clone())),
                Constant::Real(d) => Some(EggExpr::Real(Integer::from_f64(d.to_f64()).unwrap())),
            },
            Term::Var(name, _) => {
                if let Some(literal) = subs.get(name) {
                    Some(literal.clone())
                } else {
                    Some(EggExpr::Var(name.clone()))
                }
            }
            Term::App(head, args) => {
                if let Some(func_name) = head.as_var() {
                    func_cache.insert(func_name.to_string());
                }

                if args.len() == 0 {
                    return to_raw_egg(head, subs, func_cache);
                }
                let mut args: Vec<EggExpr> = args
                    .clone()
                    .iter()
                    .flat_map(|x| to_raw_egg(x, subs, func_cache))
                    .collect();
                args.reverse();
                args.push(EggExpr::Op(head.to_string()));
                let mut stream = args.iter();
                let (first, second) = (
                    Box::new(stream.next().cloned()?),
                    Box::new(stream.next().cloned()?),
                );
                let mut func = EggExpr::App(second, first);
                for a in stream {
                    func = EggExpr::App(Box::new(a.clone()), Box::new(func));
                }
                Some(func)
            }
            Term::Op(head, args) => {
                if args.len() == 0 {
                    if head == &Operator::True || head == &Operator::False {
                        return Some(EggExpr::Bool(if head == &Operator::True {
                            true
                        } else {
                            false
                        }));
                    }
                    return None;
                }

                func_cache.insert(format!("{}!", head));

                let args: Vec<EggExpr> = args
                    .clone()
                    .iter()
                    .flat_map(|x| to_raw_egg(x, subs, func_cache))
                    .collect();
                //     args.reverse();
                //   args.push(EggExpr::Op(head.to_string()));
                let mut stream = args.iter();
                let mut args = EggExpr::Args(
                    Box::new(stream.next().cloned()?),
                    Box::new(EggExpr::Empty()),
                );
                for a in stream {
                    args = EggExpr::Args(Box::new(a.clone()), Box::new(args));
                }

                Some(EggExpr::App(
                    Box::new(EggExpr::Op(head.to_string())),
                    Box::new(args),
                ))
            }
            _ => None,
        }
    }

    return to_raw_egg(term_rc, subs, func_cache).map(|x| {
        if encapsule {
            EggExpr::Mk(Box::new(x))
        } else {
            x
        }
    });
}

fn construct_premises(
    pool: &mut PrimitivePool,
    premises: &Rc<ProofNode>,
    func_cache: &mut EggFunctions,
) -> EggLanguage {
    let mut grounds_terms = vec![];
    for premise in premises.get_assumptions() {
        let clause = clauses_to_or(pool, premise.clause());
        if let Some(clause) = clause {
            let expr = get_equational_terms(&clause);
            if let Some((lhs, rhs)) = expr {
                grounds_terms.push(EggStatement::Union(
                    Box::new(to_egg_expr(lhs, &IndexMap::new(), func_cache, false).unwrap()),
                    Box::new(to_egg_expr(rhs, &IndexMap::new(), func_cache, false).unwrap()),
                ));
            }
        }
    }

    grounds_terms
}

fn construct_rules(database: &Rules, func_cache: &mut EggFunctions) -> EggLanguage {
    let mut rules = vec![];
    for (_name, definition) in database {
        let mut premises = vec![];

        let subs = definition
            .arguments
            .iter()
            .map(|arg| (arg, EggExpr::Literal(arg.clone())))
            .collect::<IndexMap<_, _>>();
        // for arg in definition.arguments.iter() {
        //     premises.push(EggExpr::Ground(Box::new(EggExpr::Literal(arg.clone()))));
        // }

        for premise in definition.premises.iter() {
            let (lhs, rhs) = get_equational_terms(&premise).unwrap();
            premises.push(EggExpr::Equal(
                Box::new(to_egg_expr(lhs, &subs, func_cache, false).unwrap()),
                Box::new(to_egg_expr(rhs, &subs, func_cache, false).unwrap()),
            ));
        }
        let (lhs, rhs) = get_equational_terms(&definition.conclusion).unwrap();
        let egg_equations = (
            Box::new(to_egg_expr(lhs, &subs, func_cache, true).unwrap()),
            Box::new(to_egg_expr(rhs, &subs, func_cache, true).unwrap()),
        );

        rules.push(EggStatement::Rewrite(
            egg_equations.0.clone(),
            egg_equations.1.clone(),
            premises.clone(),
        ));
    }
    rules
}

fn set_goal(term: &Rc<Term>, func_cache: &mut EggFunctions) -> Option<Vec<EggStatement>> {
    let mut goal = vec![];
    let expr = get_equational_terms(term);
    if let Some((lhs, rhs)) = expr {
        goal.push(EggStatement::Let(
            "goal_lhs".to_string(),
            Box::new(to_egg_expr(lhs, &IndexMap::new(), func_cache, true).unwrap()),
        ));

        goal.push(EggStatement::Let(
            "goal_rhs".to_string(),
            Box::new(to_egg_expr(rhs, &IndexMap::new(), func_cache, true).unwrap()),
        ));

        goal.push(EggStatement::Run(3));

        goal.push(EggStatement::Check(Box::new(EggExpr::Equal(
            Box::new(EggExpr::Literal("goal_lhs".to_string())),
            Box::new(EggExpr::Literal("goal_rhs".to_string())),
        ))));

        return Some(goal);
    }
    None
}

fn declare_functions(functions: EggFunctions) -> Vec<EggStatement> {
    let mut declarations = vec![];
    for name in functions {
        declarations.push(EggStatement::Function(
            name,
            vec![ConstType::ConstrType("Term".to_string())],
            ConstType::ConstrType("Term".to_string()),
        ));
    }

    declarations
}

pub fn reconstruct_rule(
    pool: &mut PrimitivePool,
    conclusion: Rc<Term>,
    root: &Rc<ProofNode>,
    database: &Rules,
) {
    let mut egg_functions = EggFunctions::new();

    let rules = construct_rules(database, &mut egg_functions);
    let premises = construct_premises(pool, root, &mut egg_functions);
    let goal = set_goal(&conclusion, &mut egg_functions);
    let declarations = declare_functions(egg_functions);
    let mut ast = create_headers();

    ast.extend(declarations);
    ast.extend(rules);
    ast.extend(premises);

    if goal.is_none() {
        println!("Elaboration failed");
        return;
    }

    ast.append(&mut goal.unwrap());
    let mut egraph = EGraph::default();
    let egglog = lower_egg_language(ast);
    for rule in egglog.iter() {
        println!("{}", rule);
    }

    let result = egraph.run_program(egglog);
    match result {
        Ok(r) => {
            println!("Elaboration successed");
        }
        Err(error) => println!("{0}", error),
    }
}
