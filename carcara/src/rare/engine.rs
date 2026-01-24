use std::{collections::HashMap, iter::once, sync::Arc};

use crate::{
    ast::{
        Binder, Constant, Operator, PrimitivePool, ProofNode, Rc, Sort, Term, rare_rules::{AttributeParameters, DeclAttr, DeclConst, RuleDefinition, Rules}
    },
    rare::{
        computational::{aci_norm::singleton_operators, core::declare_special_eunoia_eliminations, defunctionalization::elaborate_rule, distinct_elim::declare_logic_operators},
        language::*,
        meta::lower_egg_language,
        util::{clauses_to_or, collect_vars, get_equational_terms, hash_var_name},
    },
};
use egg::Symbol;
use egglog::{
    self,
    ast::Span,
    constraint::{SimpleTypeConstraint, TypeConstraint},
    sort::{BoolSort, EqSort},
    ArcSort, EGraph, PrimitiveLike, Value,
};
use indexmap::{IndexMap, IndexSet};
use rug::Integer;

#[derive(Debug, Default)]
pub struct EggFunctions {
    pub names: IndexMap<String, (bool, usize)>,
    pub shapes: IndexMap<String, IndexSet<Rc<Term>>>,
    pub assoc_calls: IndexMap<String, IndexSet<EggExpr>>,
}

struct CustomPrimitive {
    name: Symbol,
    input: Vec<ArcSort>,
    output: ArcSort,
    f: fn(&[Value]) -> Option<Value>,
}

impl PrimitiveLike for CustomPrimitive {
    fn name(&self) -> Symbol {
        self.name
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        let sorts: Vec<_> = self
            .input
            .iter()
            .chain(once(&self.output as &ArcSort))
            .cloned()
            .collect();
        SimpleTypeConstraint::new(self.name(), sorts, span.clone()).into_box()
    }
    fn apply(
        &self,
        values: &[Value],
        _sorts: (&[ArcSort], &ArcSort),
        _egraph: Option<&mut EGraph>,
    ) -> Option<Value> {
        (self.f)(values)
    }
}

pub fn create_headers() -> EggLanguage {
    let stmts = vec![
        EggStatement::Ruleset("list-ruleset".to_string()),
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
                    constr: ("Real".to_string(), vec![ConstType::Integer, ConstType::Integer]),
                },
                Constructor {
                    constr: ("Op".to_string(), vec![ConstType::Operator]),
                },
                Constructor {
                    constr: ("@String".to_string(), vec![ConstType::Operator]),
                },
                Constructor {
                    constr: (
                        "Forall".to_string(),
                        vec![ConstType::ConstrType("Term".to_string())],
                    ),
                },
                Constructor {
                    constr: (
                        "Exists".to_string(),
                        vec![ConstType::ConstrType("Term".to_string())],
                    ),
                },
                Constructor {
                    constr: (
                        "Lambda".to_string(),
                        vec![ConstType::ConstrType("Term".to_string())],
                    ),
                },
                Constructor {
                    constr: (
                        "Choice".to_string(),
                        vec![ConstType::ConstrType("Term".to_string())],
                    ),
                },
                Constructor {
                    constr: (
                        "Sort".to_string(),
                        vec![ConstType::ConstrType("Term".to_string())],
                    ),
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
        EggStatement::Sort(
            "AssocArgs".to_owned(),
            "Set".to_owned(),
            Box::new(EggExpr::Literal("Term".to_string())),
        ),
        EggStatement::Constructor(
            "Assoc".to_string(),
            vec![ConstType::ConstrType("AssocArgs".to_string())],
            ConstType::ConstrType("Term".to_string()),
        ),
        EggStatement::Relation(
            "Avaliable".to_string(),
            vec![ConstType::ConstrType("Term".to_string())],
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
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Equal(
                Box::new(EggExpr::Mk(Box::new(EggExpr::Literal("x".to_string())))),
                Box::new(EggExpr::Mk(Box::new(EggExpr::Literal("y".to_string())))),
            )],
            head: vec![EggExpr::Union(
                Box::new(EggExpr::Literal("x".to_string())),
                Box::new(EggExpr::Literal("y".to_string())),
            )],
        },
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
    ];

    stmts
}

// This function is primarily used to insert premises to egraph
// But we use the relation Avaliable so we can know each one we added by using our translation
fn create_avaliable_premise(
    term: &Rc<Term>,
    func_cache: &mut EggFunctions,
    var_map: &mut HashMap<String, u64>,
    recognize_vars: bool,
) -> Option<EggStatement> {
    if term.is_var() {
        return None;
    }

    let mut premises = Vec::new();
    let mut sorted_vars = IndexMap::new();
    let vars = if recognize_vars {
        collect_vars(term, false)
    } else {
        IndexMap::default()
    };

    for (name, _sort) in vars.iter() {
        let egg_expr = EggExpr::Literal(name.clone());
        sorted_vars.insert(name, (egg_expr.clone(), AttributeParameters::List));
        premises.push(EggExpr::Call("Avaliable".to_string(), vec![egg_expr]));
    }

    Some(EggStatement::Rule {
        ruleset: None,
        body: premises,
        head: vec![to_egg_expr(term, &sorted_vars, func_cache, var_map, false).unwrap()],
    })
}

pub fn to_egg_expr(
    term_rc: &Rc<Term>,
    subs: &IndexMap<&String, (EggExpr, AttributeParameters)>,
    func_cache: &mut EggFunctions,
    var_map: &mut HashMap<String, u64>,
    collect_functions_shape: bool,
) -> Option<EggExpr> {
    fn build_args_list<I: IntoIterator<Item = EggExpr>>(it: I) -> EggExpr {
        let v: Vec<EggExpr> = it.into_iter().collect();
        if v.is_empty() {
            return EggExpr::Empty();
        }
        let mut it = v.into_iter().rev();
        let first = it.next().unwrap();
        let mut acc = EggExpr::Args(Box::new(first), Box::new(EggExpr::Empty()));
        for e in it {
            acc = EggExpr::Args(Box::new(e), Box::new(acc));
        }
        acc
    }

    pub fn encapluse(egg_term: EggExpr) -> EggExpr {
        return EggExpr::Mk(Box::new(egg_term));
    }

    pub fn to_raw_egg(
        term_rc: &Rc<Term>,
        subs: &IndexMap<&String, (EggExpr, AttributeParameters)>,
        func_cache: &mut EggFunctions,
        var_map: &mut HashMap<String, u64>,
        collect_functions_shape: bool,
    ) -> Option<EggExpr> {
        match &**term_rc {
            Term::Const(c) => match c {
                Constant::Integer(i) => Some(EggExpr::Num(i.clone())),
                Constant::String(s) => Some(EggExpr::String(s.clone())),
                Constant::BitVec(i, j) => Some(EggExpr::BitVec(i.clone(), j.clone())),
                Constant::Real(d) => Some(EggExpr::Real((d.clone().into_numer_denom()))),
            },
            Term::Var(name, _) => {
                if let Some(argument) = subs.get(name) {
                    Some(argument.0.clone())
                } else {
                    Some(EggExpr::Var(hash_var_name(var_map, name)))
                }
            }
            Term::App(head, args) => {
                let func_name = head.to_string();
                func_cache
                    .names
                    .insert(func_name.to_string(), (false, args.len()));
                if collect_functions_shape {
                    func_cache
                        .shapes
                        .entry(func_name.to_string())
                        .and_modify(|v| {
                            v.insert(term_rc.clone());
                        })
                        .or_insert({
                            let mut v = IndexSet::new();
                            v.insert(term_rc.clone());
                            v
                        });
                }

                if args.len() == 0 {
                    return to_egg_expr(head, subs, func_cache, var_map, collect_functions_shape);
                }
                let args = build_args_list(
                    args.clone()
                        .iter()
                        .flat_map(|x| to_egg_expr(x, subs, func_cache, var_map, collect_functions_shape)),
                );

                Some(EggExpr::Call(format!("@{}", func_name), vec![args]))
            }
            Term::Op(Operator::RareList, args) => {
                let args = build_args_list(
                    args.clone()
                        .iter()
                        .flat_map(|x| to_egg_expr(x, subs, func_cache, var_map, collect_functions_shape)),
                );

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
                    return Some(EggExpr::Op(head.to_string()));
                }

                func_cache
                    .names
                    .insert(head.to_string(), (true, args.len()));
                let args_list = build_args_list(
                    args.clone()
                        .iter()
                        .flat_map(|x| to_egg_expr(x, subs, func_cache, var_map, collect_functions_shape)),
                );

                if singleton_operators(*head).is_some() {
                    let op_with_at = format!("@{}", head.to_string());
                    func_cache
                        .assoc_calls
                        .entry(op_with_at.clone())
                        .or_default()
                        .insert(args_list.clone());
                    Some(EggExpr::Call(op_with_at, vec![args_list]))
                } else {
                    Some(EggExpr::Call(
                        format!("@{0}", head.to_string()),
                        vec![args_list],
                    ))
                }
            }
            Term::Binder(binder, bindings, body) => {
                // map binder enum -> ctor name (now arity = 1)
                let ctor = match binder {
                    Binder::Forall => "Forall",
                    Binder::Exists => "Exists",
                    Binder::Lambda => "Lambda",
                    Binder::Choice => "Choice",
                }
                .to_string();

                // encode the bound variable list
                let vars_list = build_args_list(
                    bindings
                        .0
                        .iter()
                        .map(|(name, _sort)| EggExpr::Var(hash_var_name(var_map, name))),
                );

                // encode the body
                let body_e = to_egg_expr(body, subs, func_cache, var_map, collect_functions_shape)?;

                // single Term parameter: Args(vars_list, body_e)
                let packed = EggExpr::Args(Box::new(vars_list), Box::new(body_e));

                Some(EggExpr::Call(ctor, vec![packed]))
            }
            Term::Sort(sort) => {
                // Encode a Sort as a Term value (to be wrapped by the "Sort" ctor).
                fn sort_to_egg(
                    s: &Sort,
                    subs: &IndexMap<&String, (EggExpr, AttributeParameters)>,
                    func_cache: &mut EggFunctions,
                    var_map: &mut HashMap<String, u64>,
                    collect_shapes: bool,
                ) -> Option<EggExpr> {
                    match s {
                        Sort::Var(name) => Some(EggExpr::Var(hash_var_name(var_map, name))),
                        Sort::Bool => Some(EggExpr::Const("Bool".to_string())),
                        Sort::Int => Some(EggExpr::Const("Int".to_string())),
                        Sort::Real => Some(EggExpr::Const("Real".to_string())),
                        Sort::String => Some(EggExpr::Const("String".to_string())),
                        Sort::RegLan => Some(EggExpr::Const("RegLan".to_string())),
                        Sort::RareList => Some(EggExpr::Const("RareList".to_string())),
                        Sort::Type => Some(EggExpr::Const("Type".to_string())),

                        Sort::BitVec(w) => {
                            let tag = EggExpr::Const("BitVec".to_string());
                            let width = EggExpr::Num(w.clone());
                            Some(build_args_list(vec![tag, width]))
                        }

                        Sort::Array(x, y) => {
                            let tag = EggExpr::Const("Array".to_string());
                            let xs = to_egg_expr(x, subs, func_cache, var_map, collect_shapes)?;
                            let ys = to_egg_expr(y, subs, func_cache, var_map, collect_shapes)?;
                            Some(build_args_list(vec![tag, xs, ys]))
                        }

                        Sort::Function(parts) => {
                            let mut v = Vec::with_capacity(1 + parts.len());
                            v.push(EggExpr::Const("Function".to_string()));
                            for p in parts {
                                v.push(to_egg_expr(p, subs, func_cache, var_map, collect_shapes)?);
                            }
                            Some(build_args_list(v))
                        }

                        Sort::Atom(name, args) => {
                            let mut v = Vec::with_capacity(1 + args.len());
                            v.push(EggExpr::Const(name.clone()));
                            for a in args {
                                v.push(to_egg_expr(a, subs, func_cache, var_map, collect_shapes)?);
                            }
                            Some(build_args_list(v))
                        }

                        Sort::ParamSort(vars, inner) => {
                            // list of vars
                            let mut vs = Vec::with_capacity(vars.len());
                            for v in vars {
                                vs.push(to_egg_expr(v, subs, func_cache, var_map, collect_shapes)?);
                            }
                            let vars_list = build_args_list(vs);

                            // body sort
                            let body = to_egg_expr(inner, subs, func_cache, var_map, collect_shapes)?;

                            let tag = EggExpr::Const("ParamSort".to_string());
                            Some(build_args_list(vec![tag, vars_list, body]))
                        }
                    }
                }

                let encoded = sort_to_egg(sort,  subs, func_cache, var_map, collect_functions_shape)?;
                // Wrap the encoded sort with the "Sort" constructor (as declared in create_headers)
                Some(EggExpr::Call("Sort".to_string(), vec![encoded]))
            }
            Term::Let(bindings, body) => {
                // Build list of variable *names* (ignore bound values here)
                let vars_list = build_args_list(
                    bindings
                        .0
                        .iter()
                        .map(|(name, _val)| EggExpr::Var(hash_var_name(var_map, name))),
                );

                // Translate the let-body
                let body_e = to_egg_expr(body, subs, func_cache, var_map, collect_functions_shape)?;

                // Make a single-argument constructor call for the Lambda binder:
                //   Lambda( Args(vars_list, body_e) )
                let lambda_e = EggExpr::Call(
                    "Lambda".to_string(),
                    vec![EggExpr::Args(Box::new(vars_list), Box::new(body_e))],
                );

                // Now apply the lambda to each bound value using nested `App`:
                //   App(App(... App(lambda_e, v1), v2), ... vn)
                let mut applied = lambda_e;
                for (_name, val_term) in bindings.0.iter() {
                    let val_e = to_egg_expr(val_term, subs, func_cache, var_map, collect_functions_shape)?;
                    applied = EggExpr::Call("App".to_string(), vec![applied, val_e]);
                }

                Some(applied)
            }

            Term::ParamOp { op, op_args, args } => {
                // Register the symbol; we treat param-ops as operators.
                // Arity here is "parameters + arguments" because we flatten them below.
                func_cache
                    .names
                    .insert(op.to_string(), (true, op_args.len() + args.len()));

                // Encode parameters (indexed or qualified) *first*,
                // then the regular arguments, all in a single Args list.
                let mut flat: Vec<EggExpr> = Vec::with_capacity(op_args.len() + args.len());

                for p in op_args {
                    flat.push(to_egg_expr(p, subs, func_cache, var_map, collect_functions_shape)?);
                }
                for a in args {
                    flat.push(to_egg_expr(a, subs, func_cache, var_map, collect_functions_shape)?);
                }

                let packed = build_args_list(flat);

                // Call as @<param-op> with the single packed argument,
                // consistent with how Op/App are encoded elsewhere.
                Some(EggExpr::Call(format!("@{}", op.to_string()), vec![packed]))
            }
        }
    }

    return to_raw_egg(term_rc, subs, func_cache, var_map, collect_functions_shape).map(|x| {
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
    var_map: &mut HashMap<String, u64>,
    func_cache: &mut EggFunctions,
) -> EggLanguage {
    let mut grounds_terms = vec![];

    for premise in premises.get_assumptions() {
        let clause: Option<Rc<Term>> = clauses_to_or(pool, premise.clause());
        if let Some(clause) = clause {
            let expr = get_equational_terms(&clause);
            if let Some((Operator::Equals, lhs, rhs)) = expr {
                grounds_terms.push(EggStatement::Union(
                    Box::new(to_egg_expr(lhs, &IndexMap::new(), func_cache, var_map, false).unwrap()),
                    Box::new(to_egg_expr(rhs, &IndexMap::new(), func_cache, var_map, false).unwrap()),
                ));
            }

            if let Some(ground) = create_avaliable_premise(&clause, func_cache, var_map, false) {
                grounds_terms.push(ground)
            }
        }
    }

    grounds_terms
}

fn construct_rules(
    database: &[RuleDefinition],
    func_cache: &mut EggFunctions,
    var_map: &mut HashMap<String, u64>,
) -> IndexSet<EggStatement> {
    let mut rules = IndexSet::new();
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
                Operator::Equals => {
                    if let Some(lhs) =
                        create_avaliable_premise(lhs, func_cache, var_map, true)
                    {
                        rules.insert(lhs);
                    }

                    let lhs = Box::new(
                        to_egg_expr(lhs, &subs, func_cache, var_map, definition.is_elaborated)
                            .unwrap(),
                    );

                    if let Some(rhs) =
                        create_avaliable_premise(rhs, func_cache, var_map, true)
                    {
                        rules.insert(rhs);
                    }
                    let rhs = Box::new(
                        to_egg_expr(rhs, &subs, func_cache, var_map, definition.is_elaborated)
                            .unwrap(),
                    );

                    premises.push(EggExpr::Equal(lhs, rhs))
                }

                Operator::Distinct => {
                    if let Some(lhs) =
                        create_avaliable_premise(lhs, func_cache, var_map, true)
                    {
                        rules.insert(lhs);
                    }

                    let lhs = Box::new(
                        to_egg_expr(lhs, &subs, func_cache, var_map, definition.is_elaborated)
                            .unwrap(),
                    );

                    if let Some(rhs) =
                        create_avaliable_premise(rhs, func_cache, var_map, true)
                    {
                        rules.insert(rhs);
                    }

                    let rhs = Box::new(
                        to_egg_expr(rhs, &subs, func_cache, var_map, definition.is_elaborated)
                            .unwrap(),
                    );

                    premises.push(EggExpr::Distinct(lhs, rhs));
                }
                _ => unreachable!(),
            }
        }

        let (_, lhs, rhs) = get_equational_terms(&definition.conclusion).unwrap();
        let egg_equations: (Box<EggExpr>, Box<EggExpr>) = (
            Box::new(
                to_egg_expr(lhs, &subs, func_cache, var_map, definition.is_elaborated).unwrap(),
            ),
            Box::new(
                to_egg_expr(rhs, &subs, func_cache, var_map, definition.is_elaborated).unwrap(),
            ),
        );

        rules.insert(EggStatement::Rewrite(
            egg_equations.0.clone(),
            egg_equations.1.clone(),
            premises.clone(),
        ));
    }
    rules
}

fn set_goal(term: &Rc<Term>, var_map: &mut HashMap<String, u64>, func_cache: &mut EggFunctions) -> Option<Vec<EggStatement>> {
    let mut goal = vec![];
    let expr = get_equational_terms(term);
    if let Some((_, lhs, rhs)) = expr {
        goal.push(EggStatement::Let(
            "goal_lhs".to_string(),
            Box::new(to_egg_expr(lhs, &IndexMap::new(), func_cache, var_map, false).unwrap()),
        ));

        goal.push(EggStatement::Let(
            "goal_rhs".to_string(),
            Box::new(to_egg_expr(rhs, &IndexMap::new(), func_cache, var_map, false).unwrap()),
        ));

        goal.push(EggStatement::Premise(
            "Avaliable".to_string(),
            Box::new(EggExpr::Literal("goal_lhs".to_string())),
        ));

        goal.push(EggStatement::Premise(
            "Avaliable".to_string(),
            Box::new(EggExpr::Literal("goal_rhs".to_string())),
        ));

        goal.push(EggStatement::Saturate {
            ruleset: Some("list-ruleset".to_string()),
        });

        goal.push(EggStatement::Run { ruleset: None, iterations: 5 });

        goal.push(EggStatement::Check(Box::new(EggExpr::Equal(
            Box::new(EggExpr::Literal("goal_lhs".to_string())),
            Box::new(EggExpr::Literal("goal_rhs".to_string())),
        ))));

        return Some(goal);
    }
    None
}

fn declare_functions(
    functions: &mut EggFunctions,
    constant: &IndexMap<String, DeclConst>,
    var_map: &mut HashMap<String, u64>
) -> Vec<EggStatement> {
    use super::computational::arith_poly_norm;

    let mut decls = Vec::new();
    declare_logic_operators(functions);

    // Collect arith operator names to skip (they're declared in arith_poly_norm.egglog)
    let arith_ops: std::collections::HashSet<&str> = if arith_poly_norm::has_arith_operator(functions) {
        arith_poly_norm::arith_operators().map(|(name, _)| name).collect()
    } else {
        std::collections::HashSet::new()
    };

    for (func, (is_op, _arity)) in functions.names.iter() {
        // Skip arith operators - they're declared in arith_poly_norm.egglog
        if arith_ops.contains(func.as_str()) {
            continue;
        }

        // 1) always declare the function symbol
        decls.push(EggStatement::Constructor(
            format!("@{}", func),
            vec![ConstType::ConstrType("Term".to_string())],
            ConstType::ConstrType("Term".to_string()),
        ));

        if !*is_op {
            // For now let's remove this part if we feel that we need more power/expression
            // in the graph we add again
            // ───────────────────────────────────────────────────────────
            // A) merged‐arity rule for non-operators
            //    (rule ((= (Mk __var1) (Mk k1))
            //            …
            //            (= (Mk __varN) (Mk kN)))
            //          ((Mk (@func (Args k1 (Args … Empty))))))
            // ───────────────────────────────────────────────────────────
            // for shape in functions.shapes.get(func).unwrap_or(&IndexSet::default()) {
            //     let mut premises = Vec::new();
            //     let mut sorted_vars = IndexMap::new();
            //     let mut vars = collect_vars(shape, false);
            //     vars.swap_remove(func);

            //     for (name, _sort) in vars.iter() {
            //         let egg_expr = EggExpr::Literal(name.clone());
            //         sorted_vars.insert(name, (egg_expr.clone(), AttributeParameters::List));
            //         premises.push(EggExpr::Call("Avaliable".to_string(), vec![egg_expr]));
            //     }

            //     decls.push(EggStatement::Rule(
            //         premises,
            //         vec![
            //             to_egg_expr(shape, &sorted_vars, &mut EggFunctions::default(), false)
            //                 .unwrap(),
            //         ],
            //     ));
            // }
        } else {
            if let Some(default_val) = constant.get(func) {
                if let Some(DeclAttr::RightAssocNil(nil)) =
                    default_val.attrs.iter().find(|x| match x {
                        DeclAttr::RightAssocNil(_) => true,
                        _ => false,
                    })
                {
                    decls.push(EggStatement::Rewrite(
                        Box::new(EggExpr::Call(format!("@{}", func), vec![EggExpr::Empty()])),
                        Box::new(
                            to_egg_expr(
                                nil,
                                &IndexMap::default(),
                                &mut EggFunctions::default(),
                                var_map,
                                false,
                            )
                            .unwrap(),
                        ),
                        vec![],
                    ));
                }
            }
        }
    }

    // Note: @+ computation rule is now in arith_poly_norm.egglog

    decls
}

pub fn run_egglog(
    pool: &mut PrimitivePool,
    conclusion: Rc<Term>,
    root: &Rc<ProofNode>,
    database: &Rules,
) -> Result<EGraph, String> {
    let mut egg_functions = EggFunctions::default();
    let mut var_map = HashMap::new();

    let mut rules: Vec<RuleDefinition> = vec![];

    for (_, rule) in database.rules.iter() {
        rules.extend(elaborate_rule(
            pool,
            rule,
            &database.programs,
            &database.consts,
            &rule.name,
        ));
    }

    let rules = construct_rules(&rules, &mut egg_functions, &mut var_map);

    let premises = construct_premises(pool, root, &mut var_map, &mut egg_functions);
    let goal = set_goal(&conclusion, &mut var_map, &mut egg_functions);

    let mut declarations = declare_functions(&mut egg_functions, &database.consts, &mut var_map);

    declare_special_eunoia_eliminations(&mut declarations, &egg_functions);

    // Partition declarations: constructors first, then everything else
    let (constructors, other_decls): (Vec<_>, Vec<_>) = declarations
        .into_iter()
        .partition(|stmt| matches!(stmt, EggStatement::Constructor(_, _, _)));

    let mut ast = create_headers();

    ast.extend(constructors);
    ast.extend(other_decls);
    ast.extend(rules);
    ast.extend(premises);

    if goal.is_none() {
        return Err("Failed to set goal".to_string());
    }

    ast.append(&mut goal.unwrap());
    let mut egraph = EGraph::default();

    egraph.add_primitive(CustomPrimitive {
        name: Symbol::from("ineq"),
        input: vec![
            Arc::new(EqSort { name: Symbol::from("Term") }),
            Arc::new(EqSort { name: Symbol::from("Term") }),
        ],
        output: Arc::new(BoolSort),
        f: |x| Some(Value::from(x[0] != x[1])),
    });

    let egglog = lower_egg_language(ast);

    // for rule in egglog.iter() {
    //     println!("{}", rule);
    // }

    egraph.run_program(egglog).map_err(|e| e.to_string())?;
    Ok(egraph)
}

pub fn reconstruct_rule(
    pool: &mut PrimitivePool,
    conclusion: Rc<Term>,
    root: &Rc<ProofNode>,
    database: &Rules,
) {
    println!("Elaborating {:?}", conclusion);
    let result = run_egglog(pool, conclusion, root, database);
    match result {
        Ok(_) => println!("Elaboration succeeded"),
        Err(error) => println!("Elaboration failed: {}", error),
    }
}
