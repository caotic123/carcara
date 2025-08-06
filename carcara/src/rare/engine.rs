use crate::{
    ast::{
        rare_rules::{AttributeParameters, RuleDefinition, Rules},
        Constant, Operator, PrimitivePool, ProofNode, Rc, Term,
    },
    rare::{
        computational::compile_program,
        language::*,
        meta::lower_egg_language,
        util::{clauses_to_or, collect_vars, get_equational_terms},
    },
};
use egglog::{self, EGraph};
use indexmap::{IndexMap, IndexSet};
use rug::Integer;

#[derive(Debug, Default)]
pub struct EggFunctions {
    names: IndexMap<String, (bool, usize)>,
    shapes: IndexMap<String, IndexSet<Rc<Term>>>,
}

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
        EggStatement::Relation(
            "Avaliable".to_string(),
            ConstType::ConstrType("Term".to_string()),
        ),
        EggStatement::Rewrite(
            Box::new(EggExpr::Args(
                Box::new(EggExpr::Args(
                    Box::new(EggExpr::Literal("t1".to_string())),
                    Box::new(EggExpr::Literal("t2".to_string())),
                )),
                Box::new(EggExpr::Literal("t3".to_string())),
            )),
            Box::new(EggExpr::Args(
                Box::new(EggExpr::Literal("t1".to_string())),
                Box::new(EggExpr::Args(
                    Box::new(EggExpr::Literal("t2".to_string())),
                    Box::new(EggExpr::Literal("t3".to_string())),
                )),
            )),
            vec![],
        ),
        EggStatement::Rewrite(
            Box::new(EggExpr::Args(
                Box::new(EggExpr::Literal("t1".to_string())),
                Box::new(EggExpr::Args(
                    Box::new(EggExpr::Literal("t2".to_string())),
                    Box::new(EggExpr::Literal("t3".to_string())),
                )),
            )),
            Box::new(EggExpr::Args(
                Box::new(EggExpr::Args(
                    Box::new(EggExpr::Literal("t1".to_string())),
                    Box::new(EggExpr::Literal("t2".to_string())),
                )),
                Box::new(EggExpr::Literal("t3".to_string())),
            )),
            vec![],
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
        EggStatement::Rewrite(
            Box::new(EggExpr::Args(
                Box::new(EggExpr::Literal("t1".to_string())),
                Box::new(EggExpr::Literal("t2".to_string())),
            )),
            Box::new(EggExpr::Args(
                Box::new(EggExpr::Args(
                    Box::new(EggExpr::Literal("t1".to_string())),
                    Box::new(EggExpr::Empty()),
                )),
                Box::new(EggExpr::Literal("t2".to_string())),
            )),
            vec![],
        ),
        EggStatement::Rewrite(
            Box::new(EggExpr::Args(
                Box::new(EggExpr::Args(
                    Box::new(EggExpr::Literal("t1".to_string())),
                    Box::new(EggExpr::Empty()),
                )),
                Box::new(EggExpr::Literal("t2".to_string())),
            )),
            Box::new(EggExpr::Args(
                Box::new(EggExpr::Literal("t1".to_string())),
                Box::new(EggExpr::Literal("t2".to_string())),
            )),
            vec![],
        ),
    ]
}

pub fn to_egg_expr(
    term_rc: &Rc<Term>,
    subs: &IndexMap<&String, (EggExpr, AttributeParameters)>,
    func_cache: &mut EggFunctions,
    collect_functions_shape: bool,
) -> Option<EggExpr> {
    pub fn encapluse(egg_term: EggExpr) -> EggExpr {
        return EggExpr::Mk(Box::new(egg_term));
    }

    pub fn to_raw_egg(
        term_rc: &Rc<Term>,
        subs: &IndexMap<&String, (EggExpr, AttributeParameters)>,
        func_cache: &mut EggFunctions,
        collect_functions_shape: bool,
    ) -> Option<EggExpr> {
        match &**term_rc {
            Term::Const(c) => match c {
                Constant::Integer(i) => Some(EggExpr::Num(i.clone())),
                Constant::String(s) => Some(EggExpr::String(s.clone())),
                Constant::BitVec(i, j) => Some(EggExpr::BitVec(i.clone(), j.clone())),
                Constant::Real(d) => Some(EggExpr::Real(Integer::from_f64(d.to_f64()).unwrap())),
            },
            Term::Var(name, _) => {
                if let Some(argument) = subs.get(name) {
                    Some(argument.0.clone())
                } else {
                    Some(EggExpr::Var(name.clone()))
                }
            }
            Term::App(head, args) => {
                if let Some(func_name) = head.as_var() {
                    func_cache
                        .names
                        .insert(func_name.to_string(), (false, args.len()));
                    if collect_functions_shape {
                        func_cache
                            .shapes
                            .entry(func_name.to_string())
                            .and_modify(|v| {v.insert(term_rc.clone());})
                            .or_insert({
                                let mut v = IndexSet::new();
                                v.insert(term_rc.clone());
                                v
                            });
                    }
                }

                if args.len() == 0 {
                    return to_egg_expr(head, subs, func_cache, collect_functions_shape);
                }
                let args: Vec<EggExpr> = args
                    .clone()
                    .iter()
                    .flat_map(|x| to_egg_expr(x, subs, func_cache, collect_functions_shape))
                    .rev()
                    .collect();
                let mut stream = args.iter();
                let mut args = EggExpr::Args(
                    Box::new(stream.next().cloned()?),
                    Box::new(EggExpr::Empty()),
                );
                for a in stream {
                    args = EggExpr::Args(Box::new(a.clone()), Box::new(args));
                }

                Some(EggExpr::Call(format!("@{}", head.to_string()), vec![args]))
            }
            Term::Op(Operator::RareList, args) => {
                let args: Vec<EggExpr> = args
                    .clone()
                    .iter()
                    .flat_map(|x| to_egg_expr(x, subs, func_cache, collect_functions_shape))
                    .rev()
                    .collect();
                let mut stream = args.iter();
                let mut args = EggExpr::Args(
                    Box::new(stream.next().cloned()?),
                    Box::new(EggExpr::Empty()),
                );
                for a in stream {
                    args = EggExpr::Args(Box::new(a.clone()), Box::new(args));
                }

                Some(args)
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

                func_cache
                    .names
                    .insert(head.to_string(), (true, args.len()));
                let args: Vec<EggExpr> = args
                    .clone()
                    .iter()
                    .flat_map(|x| to_egg_expr(x, subs, func_cache, collect_functions_shape))
                    .rev()
                    .collect();
                let mut stream = args.iter();
                let mut args = EggExpr::Args(
                    Box::new(stream.next().cloned()?),
                    Box::new(EggExpr::Empty()),
                );
                for a in stream {
                    args = EggExpr::Args(Box::new(a.clone()), Box::new(args));
                }

                Some(EggExpr::Call(format!("@{0}", head.to_string()), vec![args]))
            }
            _ => None,
        }
    }

    return to_raw_egg(term_rc, subs, func_cache, collect_functions_shape).map(|x| {
        match &x {
            EggExpr::Literal(name) => {
                if let Some(argument) = subs.get(&name) {
                    if argument.1 != AttributeParameters::List {
                        return encapluse(x);
                    } else {
                        return x;
                    }
                }
            }
            _ => (),
        };

        encapluse(x)
    });
}

fn construct_premises(
    pool: &mut PrimitivePool,
    premises: &Rc<ProofNode>,
    func_cache: &mut EggFunctions,
) -> EggLanguage {
    let mut grounds_terms = vec![];

    for premise in premises.get_assumptions() {
        let clause: Option<Rc<Term>> = clauses_to_or(pool, premise.clause());
        if let Some(clause) = clause {
            let expr = get_equational_terms(&clause);
            if let Some((Operator::Equals, lhs, rhs)) = expr {
                grounds_terms.push(EggStatement::Union(
                    Box::new(to_egg_expr(lhs, &IndexMap::new(), func_cache, false).unwrap()),
                    Box::new(to_egg_expr(rhs, &IndexMap::new(), func_cache, false).unwrap()),
                ));
            }
            grounds_terms.push(EggStatement::Premise(
                "Avaliable".to_string(),
                Box::new(to_egg_expr(&clause, &IndexMap::new(), func_cache, false).unwrap()),
            ));
        }
    }

    grounds_terms
}

fn construct_rules(database: &[RuleDefinition], func_cache: &mut EggFunctions) -> EggLanguage {
    let mut rules = vec![];
    for definition in database {
        let mut premises = vec![];

        let subs = definition
            .arguments
            .iter()
            .map(|arg| {
                (
                    arg,
                    (
                        EggExpr::Literal(arg.clone()),
                        definition
                            .parameters
                            .get(arg)
                            .map(|x| x.attribute)
                            .unwrap_or(AttributeParameters::None),
                    ),
                )
            })
            .collect::<IndexMap<_, _>>();

        for premise in definition.premises.iter() {
            let (op, lhs, rhs) = get_equational_terms(&premise).unwrap();
            match op {
                Operator::Equals => premises.push(EggExpr::Equal(
                    Box::new(to_egg_expr(lhs, &subs, func_cache, definition.is_elaborated).unwrap()),
                    Box::new(to_egg_expr(rhs, &subs, func_cache, definition.is_elaborated).unwrap()),
                )),
                Operator::Distinct => premises.push(EggExpr::Distinct(
                    Box::new(to_egg_expr(lhs, &subs, func_cache, definition.is_elaborated).unwrap()),
                    Box::new(to_egg_expr(rhs, &subs, func_cache, definition.is_elaborated).unwrap()),
                )),
                _ => unreachable!(),
            }
        }
        let (_, lhs, rhs) = get_equational_terms(&definition.conclusion).unwrap();
        let egg_equations = (
            Box::new(to_egg_expr(lhs, &subs, func_cache, definition.is_elaborated).unwrap()),
            Box::new(to_egg_expr(rhs, &subs, func_cache, definition.is_elaborated).unwrap()),
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
    if let Some((_, lhs, rhs)) = expr {
        goal.push(EggStatement::Let(
            "goal_lhs".to_string(),
            Box::new(to_egg_expr(lhs, &IndexMap::new(), func_cache, false).unwrap()),
        ));

        goal.push(EggStatement::Let(
            "goal_rhs".to_string(),
            Box::new(to_egg_expr(rhs, &IndexMap::new(), func_cache, false).unwrap()),
        ));

        goal.push(EggStatement::Premise("Avaliable".to_string(),
            Box::new(EggExpr::Literal("goal_lhs".to_string())),
        ));

        goal.push(EggStatement::Premise("Avaliable".to_string(),
            Box::new(EggExpr::Literal("goal_rhs".to_string())),
        ));

        goal.push(EggStatement::Run(5));

        goal.push(EggStatement::Check(Box::new(EggExpr::Equal(
            Box::new(EggExpr::Literal("goal_lhs".to_string())),
            Box::new(EggExpr::Literal("goal_rhs".to_string())),
        ))));

        return Some(goal);
    }
    None
}

fn declare_functions(functions: EggFunctions) -> Vec<EggStatement> {
    // ───────────────────────────────────────────────────────────
    // base‐case defaults: when an operator sees no args → this
    // ───────────────────────────────────────────────────────────
    let default_empty: &[(&str, bool)] = &[
        ("or", false),
        ("and", false),
        // ← add new operator defaults here
    ];

    let mut decls = Vec::new();

    for (func, (is_op, _arity)) in functions.names.iter() {
        // 1) always declare the function symbol
        decls.push(EggStatement::Constructor(
            format!("@{}", func),
            vec![ConstType::ConstrType("Term".to_string())],
            ConstType::ConstrType("Term".to_string()),
        ));

        if !*is_op {
            // ───────────────────────────────────────────────────────────
            // A) merged‐arity rule for non-operators
            //    (rule ((= (Mk __var1) (Mk k1))
            //            …
            //            (= (Mk __varN) (Mk kN)))
            //          ((Mk (@func (Args k1 (Args … Empty))))))
            // ───────────────────────────────────────────────────────────
            for shape in functions.shapes.get(func).unwrap_or(&IndexSet::default()) {
                let mut premises = Vec::new();
                let mut sorted_vars = IndexMap::new();
                let mut vars = collect_vars(shape);
                vars.swap_remove(func);

                for (name, _sort) in vars.iter() {
                    let egg_expr = EggExpr::Literal(name.clone());
                    sorted_vars.insert(name, (egg_expr.clone(), AttributeParameters::List));
                    premises.push(EggExpr::Call("Avaliable".to_string(), vec![egg_expr]));
                }

                decls.push(EggStatement::Rule(
                    premises,
                    vec![
                        to_egg_expr(shape, &sorted_vars, &mut EggFunctions::default(), false)
                            .unwrap(),
                    ],
                ));
            }
        } else {
            if let Some((_, default_val)) = default_empty.iter().find(|&&(op, _)| op == func) {
                decls.push(EggStatement::Rewrite(
                    Box::new(EggExpr::Call(format!("@{}", func), vec![EggExpr::Empty()])),
                    Box::new(EggExpr::Bool(*default_val)),
                    vec![],
                ));
            }
        }
    }

    if functions.names.get("@+").is_some() {
        decls.push(EggStatement::Rewrite(
            Box::new(EggExpr::Call(
                "@+".to_string(),
                vec![EggExpr::Args(
                    Box::new(EggExpr::Call(
                        "Num".to_string(),
                        vec![EggExpr::Literal("t1".to_string())],
                    )),
                    Box::new(EggExpr::Args(
                        Box::new(EggExpr::Call(
                            "Num".to_string(),
                            vec![EggExpr::Literal("t2".to_string())],
                        )),
                        Box::new(EggExpr::Empty()),
                    )),
                )],
            )),
            Box::new(EggExpr::Call(
                "@+".to_string(),
                vec![EggExpr::Args(
                    Box::new(EggExpr::Call(
                        "Num".to_string(),
                        vec![EggExpr::Call(
                            "+".to_string(),
                            vec![
                                EggExpr::Literal("t1".to_string()),
                                EggExpr::Literal("t2".to_string()),
                            ],
                        )],
                    )),
                    Box::new(EggExpr::Empty()),
                )],
            )),
            vec![],
        ));
    }

    decls
}

pub fn reconstruct_rule(
    pool: &mut PrimitivePool,
    conclusion: Rc<Term>,
    root: &Rc<ProofNode>,
    database: &Rules,
) {
    let mut egg_functions = EggFunctions::default();
    let mut rules: Vec<Vec<RuleDefinition>> = database
        .programs
        .iter()
        .map(|db| compile_program(pool, db.1))
        .collect();
    let db: Vec<RuleDefinition> = database.rules.values().cloned().collect();
    rules.push(db);
    let rules = &rules.concat();

    for rule in rules.iter() {
        println!("{}", rule);
    }

    let rules = construct_rules(&rules, &mut egg_functions);

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
