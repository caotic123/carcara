use std::{
    collections::HashMap,
    iter::once,
    panic::{catch_unwind, AssertUnwindSafe},
    sync::Arc,
    time::Instant,
};

use crate::{
    ast::{
        rare_rules::{AttributeParameters, DeclAttr, DeclConst, RuleDefinition, Rules},
        Binder, Constant, Operator, PrimitivePool, ProofNode, Rc, Sort, Term,
    },
    rare::{
        computational::{
            aci_norm::singleton_operators, arith_poly_norm, arith_poly_norm_rel,
            core::declare_special_eunoia_eliminations, defunctionalization::elaborate_rule,
            distinct_elim::declare_logic_operators, evaluation,
        },
        language::*,
        meta::lower_egg_language,
        util::{
            clauses_to_or, collect_subterms, collect_vars, get_equational_terms, hash_var_name,
        },
    },
};
use egg::Symbol;
use egglog::{
    self,
    ast::{Command, Span},
    constraint::{SimpleTypeConstraint, TypeConstraint},
    sort::{BoolSort, EqSort},
    ArcSort, EGraph, PrimitiveLike, Value,
};
use indexmap::{IndexMap, IndexSet};

#[derive(Debug, Default)]
pub struct EggFunctions {
    pub names: IndexMap<String, (bool, usize, Option<Sort>)>,
    pub shapes: IndexMap<String, IndexSet<Rc<Term>>>,
    pub assoc_calls: IndexMap<String, IndexSet<EggExpr>>,
}

impl EggFunctions {
    /// Merge `other` into `self`, with the same per-name semantics as
    /// `register_function_call`.
    fn absorb(&mut self, other: EggFunctions) {
        for (name, (is_op, arity, result_sort)) in other.names {
            self.names
                .entry(name)
                .and_modify(|info| {
                    info.0 = is_op;
                    info.1 = arity;
                    if info.2.is_none() {
                        info.2 = result_sort.clone();
                    }
                })
                .or_insert((is_op, arity, result_sort));
        }
        for (name, shapes) in other.shapes {
            self.shapes.entry(name).or_default().extend(shapes);
        }
        for (name, calls) in other.assoc_calls {
            self.assoc_calls.entry(name).or_default().extend(calls);
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RunEgglogOptions {
    pub max_goal_schedule_rounds: usize,
    pub continuous_saturation: bool,
    /// If `true`, print the egglog program generated for each proof step.
    pub print_egglog: bool,
}

impl Default for RunEgglogOptions {
    fn default() -> Self {
        Self {
            max_goal_schedule_rounds: 3,
            continuous_saturation: false,
            print_egglog: false,
        }
    }
}

impl RunEgglogOptions {
    fn normalized_max_goal_schedule_rounds(self) -> usize {
        self.max_goal_schedule_rounds.max(1)
    }
}

fn application_result_sort(head: &Rc<Term>) -> Option<Sort> {
    let Term::Var(_, sort_term) = head.as_ref() else {
        return None;
    };
    let Sort::Function(parts) = sort_term.as_sort()? else {
        return None;
    };
    parts.last()?.as_sort().cloned()
}

fn register_function_call(
    functions: &mut EggFunctions,
    name: &str,
    is_op: bool,
    arity: usize,
    result_sort: Option<Sort>,
) {
    functions
        .names
        .entry(name.to_string())
        .and_modify(|info| {
            info.0 = is_op;
            info.1 = arity;
            if info.2.is_none() {
                info.2 = result_sort.clone();
            }
        })
        .or_insert((is_op, arity, result_sort));
}

fn bigrat_expr(numer: &rug::Integer, denom: &rug::Integer) -> EggExpr {
    EggExpr::Call(
        "bigrat".to_string(),
        vec![
            EggExpr::Call(
                "from-string".to_string(),
                vec![EggExpr::RawString(numer.to_string())],
            ),
            EggExpr::Call(
                "from-string".to_string(),
                vec![EggExpr::RawString(denom.to_string())],
            ),
        ],
    )
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
                    constr: ("Const".to_string(), vec![ConstType::Operator]),
                },
                Constructor {
                    constr: (
                        "Var".to_string(),
                        vec![ConstType::Var, ConstType::ConstrType("Term".to_string())],
                    ),
                },
                Constructor {
                    constr: ("Bool".to_string(), vec![ConstType::Bool]),
                },
                Constructor {
                    constr: ("Num".to_string(), vec![ConstType::Integer]),
                },
                Constructor {
                    constr: (
                        "Real".to_string(),
                        vec![ConstType::Integer, ConstType::Integer],
                    ),
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
        EggStatement::Constructor(
            "RatConst".to_string(),
            vec![ConstType::ConstrType("BigRat".to_string())],
            ConstType::ConstrType("Term".to_string()),
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
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_string(),
                vec![EggExpr::Mk(Box::new(EggExpr::Literal("t".to_string())))],
            )],
            head: vec![EggExpr::Call(
                "Avaliable".to_string(),
                vec![EggExpr::Literal("t".to_string())],
            )],
        },
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_string(),
                vec![EggExpr::Args(
                    Box::new(EggExpr::Literal("head".to_string())),
                    Box::new(EggExpr::Literal("tail".to_string())),
                )],
            )],
            head: vec![
                EggExpr::Call(
                    "Avaliable".to_string(),
                    vec![EggExpr::Literal("head".to_string())],
                ),
                EggExpr::Call(
                    "Avaliable".to_string(),
                    vec![EggExpr::Literal("tail".to_string())],
                ),
            ],
        },
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_string(),
                vec![EggExpr::Call(
                    "App".to_string(),
                    vec![
                        EggExpr::Literal("fn_term".to_string()),
                        EggExpr::Literal("arg_term".to_string()),
                    ],
                )],
            )],
            head: vec![
                EggExpr::Call(
                    "Avaliable".to_string(),
                    vec![EggExpr::Literal("fn_term".to_string())],
                ),
                EggExpr::Call(
                    "Avaliable".to_string(),
                    vec![EggExpr::Literal("arg_term".to_string())],
                ),
            ],
        },
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_string(),
                vec![EggExpr::Call(
                    "Var".to_string(),
                    vec![
                        EggExpr::Literal("var_id".to_string()),
                        EggExpr::Literal("sort_term".to_string()),
                    ],
                )],
            )],
            head: vec![EggExpr::Call(
                "Avaliable".to_string(),
                vec![EggExpr::Literal("sort_term".to_string())],
            )],
        },
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_string(),
                vec![EggExpr::Call(
                    "Forall".to_string(),
                    vec![EggExpr::Literal("body".to_string())],
                )],
            )],
            head: vec![EggExpr::Call(
                "Avaliable".to_string(),
                vec![EggExpr::Literal("body".to_string())],
            )],
        },
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_string(),
                vec![EggExpr::Call(
                    "Exists".to_string(),
                    vec![EggExpr::Literal("body".to_string())],
                )],
            )],
            head: vec![EggExpr::Call(
                "Avaliable".to_string(),
                vec![EggExpr::Literal("body".to_string())],
            )],
        },
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_string(),
                vec![EggExpr::Call(
                    "Lambda".to_string(),
                    vec![EggExpr::Literal("body".to_string())],
                )],
            )],
            head: vec![EggExpr::Call(
                "Avaliable".to_string(),
                vec![EggExpr::Literal("body".to_string())],
            )],
        },
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_string(),
                vec![EggExpr::Call(
                    "Choice".to_string(),
                    vec![EggExpr::Literal("body".to_string())],
                )],
            )],
            head: vec![EggExpr::Call(
                "Avaliable".to_string(),
                vec![EggExpr::Literal("body".to_string())],
            )],
        },
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_string(),
                vec![EggExpr::Call(
                    "Sort".to_string(),
                    vec![EggExpr::Literal("sort_term".to_string())],
                )],
            )],
            head: vec![EggExpr::Call(
                "Avaliable".to_string(),
                vec![EggExpr::Literal("sort_term".to_string())],
            )],
        },
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
    fn build_args_list<I: IntoIterator<Item = Option<EggExpr>>>(it: I) -> Option<EggExpr> {
        let v: Vec<EggExpr> = it.into_iter().collect::<Option<Vec<EggExpr>>>()?;
        if v.is_empty() {
            return Some(EggExpr::Empty());
        }
        let mut it = v.into_iter().rev();
        let first = it.next().unwrap();
        let mut acc = EggExpr::Args(Box::new(first), Box::new(EggExpr::Empty()));
        for e in it {
            acc = EggExpr::Args(Box::new(e), Box::new(acc));
        }
        Some(acc)
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
                Constant::Real(d) => {
                    let (numer, denom) = d.clone().into_numer_denom();
                    if numer.to_i64().is_some() && denom.to_i64().is_some() {
                        Some(EggExpr::Real((numer, denom)))
                    } else {
                        Some(EggExpr::Call(
                            "RatConst".to_string(),
                            vec![bigrat_expr(&numer, &denom)],
                        ))
                    }
                }
            },
            Term::Var(name, sort) => {
                if let Some(argument) = subs.get(name) {
                    Some(argument.0.clone())
                } else {
                    let sort =
                        to_raw_egg(sort, subs, func_cache, var_map, collect_functions_shape)?;
                    Some(EggExpr::Var(hash_var_name(var_map, name), Box::new(sort)))
                }
            }
            Term::App(head, args) => {
                let func_name = head.to_string();
                register_function_call(
                    func_cache,
                    &func_name,
                    false,
                    args.len(),
                    application_result_sort(head),
                );
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
                let args =
                    build_args_list(args.clone().iter().map(|x| {
                        to_egg_expr(x, subs, func_cache, var_map, collect_functions_shape)
                    }))?;

                Some(EggExpr::Call(format!("@{}", func_name), vec![args]))
            }
            Term::Op(Operator::RareList, args) => {
                let args =
                    build_args_list(args.clone().iter().map(|x| {
                        to_egg_expr(x, subs, func_cache, var_map, collect_functions_shape)
                    }))?;

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

                register_function_call(func_cache, &head.to_string(), true, args.len(), None);
                let arg_exprs = args
                    .iter()
                    .map(|x| to_egg_expr(x, subs, func_cache, var_map, collect_functions_shape))
                    .collect::<Option<Vec<_>>>()?;
                let args_list = build_args_list(arg_exprs.iter().cloned().map(Some))?;

                let op_with_at = format!("@{}", head.to_string());
                if singleton_operators(*head).is_some() {
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
                let vars_list = build_args_list(bindings.0.iter().map(|(name, sort)| {
                    let sort =
                        to_egg_expr(sort, subs, func_cache, var_map, collect_functions_shape)?;
                    Some(EggExpr::Var(hash_var_name(var_map, name), Box::new(sort)))
                }))?;

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
                        Sort::Var(name) => Some(EggExpr::Var(
                            hash_var_name(var_map, name),
                            Box::new(EggExpr::Const("Type".to_string())),
                        )),
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
                            build_args_list(vec![Some(tag), Some(width)])
                        }

                        Sort::Array(x, y) => {
                            let tag = EggExpr::Const("Array".to_string());
                            let xs = to_egg_expr(x, subs, func_cache, var_map, collect_shapes)?;
                            let ys = to_egg_expr(y, subs, func_cache, var_map, collect_shapes)?;
                            build_args_list(vec![Some(tag), Some(xs), Some(ys)])
                        }

                        Sort::Function(parts) => {
                            let mut v = Vec::with_capacity(1 + parts.len());
                            v.push(Some(EggExpr::Const("Function".to_string())));
                            for p in parts {
                                v.push(to_egg_expr(p, subs, func_cache, var_map, collect_shapes));
                            }
                            build_args_list(v)
                        }

                        Sort::Atom(name, args) => {
                            let mut v = Vec::with_capacity(1 + args.len());
                            v.push(Some(EggExpr::Const(name.clone())));
                            for a in args {
                                v.push(to_egg_expr(a, subs, func_cache, var_map, collect_shapes));
                            }
                            Some(build_args_list(v)?)
                        }

                        Sort::ParamSort(vars, inner) => {
                            // list of vars
                            let mut vs = Vec::with_capacity(vars.len());
                            for v in vars {
                                vs.push(to_egg_expr(v, subs, func_cache, var_map, collect_shapes));
                            }
                            let vars_list = build_args_list(vs)?;

                            // body sort
                            let body =
                                to_egg_expr(inner, subs, func_cache, var_map, collect_shapes)?;

                            let tag = EggExpr::Const("ParamSort".to_string());
                            build_args_list(vec![Some(tag), Some(vars_list), Some(body)])
                        }
                    }
                }

                let encoded =
                    sort_to_egg(sort, subs, func_cache, var_map, collect_functions_shape)?;
                // Wrap the encoded sort with the "Sort" constructor (as declared in create_headers)
                Some(EggExpr::Call("Sort".to_string(), vec![encoded]))
            }
            Term::Let(bindings, body) => {
                // Build list of variable *names* (ignore bound values here)
                let vars_list = build_args_list(bindings.0.iter().map(|(name, sort)| {
                    let sort =
                        to_egg_expr(sort, subs, func_cache, var_map, collect_functions_shape)?;
                    Some(EggExpr::Var(hash_var_name(var_map, name), Box::new(sort)))
                }))?;

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
                    let val_e =
                        to_egg_expr(val_term, subs, func_cache, var_map, collect_functions_shape)?;
                    applied = EggExpr::Call("App".to_string(), vec![applied, val_e]);
                }

                Some(applied)
            }

            Term::ParamOp { op, op_args, args } => {
                // Register the symbol; we treat param-ops as operators.
                // Arity here is "parameters + arguments" because we flatten them below.
                register_function_call(
                    func_cache,
                    &op.to_string(),
                    true,
                    op_args.len() + args.len(),
                    None,
                );

                // Encode parameters (indexed or qualified) *first*,
                // then the regular arguments, all in a single Args list.
                let mut flat = Vec::with_capacity(op_args.len() + args.len());

                for p in op_args {
                    flat.push(to_egg_expr(
                        p,
                        subs,
                        func_cache,
                        var_map,
                        collect_functions_shape,
                    ));
                }
                for a in args {
                    flat.push(to_egg_expr(
                        a,
                        subs,
                        func_cache,
                        var_map,
                        collect_functions_shape,
                    ));
                }

                let packed = build_args_list(flat);

                // Call as @<param-op> with the single packed argument,
                // consistent with how Op/App are encoded elsewhere.
                Some(EggExpr::Call(format!("@{}", op.to_string()), vec![packed?]))
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
    nodes: &[(Rc<Term>, &Rc<ProofNode>)],
    var_map: &mut HashMap<String, u64>,
    func_cache: &mut EggFunctions,
) -> EggLanguage {
    let mut grounds_terms = IndexSet::new();

    for (_, node) in nodes {
        for premise in node.get_assumptions() {
            let clause: Option<Rc<Term>> = clauses_to_or(pool, premise.clause());
            if let Some(clause) = clause {
                let expr = get_equational_terms(&clause);
                if let Some((Operator::Equals, lhs, rhs)) = expr {
                    grounds_terms.insert(EggStatement::Union(
                        Box::new(
                            to_egg_expr(lhs, &IndexMap::new(), func_cache, var_map, false).unwrap(),
                        ),
                        Box::new(
                            to_egg_expr(rhs, &IndexMap::new(), func_cache, var_map, false).unwrap(),
                        ),
                    ));
                }

                if let Some(ground) = create_avaliable_premise(&clause, func_cache, var_map, false)
                {
                    grounds_terms.insert(ground);
                }
            }
        }
    }

    grounds_terms.into_iter().collect()
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

        let mut premise_available_args = IndexSet::new();

        let (_, conclusion_lhs, _) = get_equational_terms(&definition.conclusion).unwrap();
        premise_available_args.extend(collect_vars(conclusion_lhs, false).into_keys());

        for premise in definition.premises.iter() {
            let (op, lhs, rhs) = get_equational_terms(&premise).unwrap();
            match op {
                Operator::Equals => {
                    if let Some(lhs) = create_avaliable_premise(lhs, func_cache, var_map, true) {
                        rules.insert(lhs);
                    }

                    let lhs = Box::new(
                        to_egg_expr(lhs, &subs, func_cache, var_map, definition.is_elaborated)
                            .unwrap(),
                    );

                    if let Some(rhs) = create_avaliable_premise(rhs, func_cache, var_map, true) {
                        rules.insert(rhs);
                    }
                    let rhs = Box::new(
                        to_egg_expr(rhs, &subs, func_cache, var_map, definition.is_elaborated)
                            .unwrap(),
                    );

                    premises.push(EggExpr::Equal(lhs, rhs))
                }

                Operator::Distinct => {
                    if let Some(lhs) = create_avaliable_premise(lhs, func_cache, var_map, true) {
                        rules.insert(lhs);
                    }

                    let lhs = Box::new(
                        to_egg_expr(lhs, &subs, func_cache, var_map, definition.is_elaborated)
                            .unwrap(),
                    );

                    if let Some(rhs) = create_avaliable_premise(rhs, func_cache, var_map, true) {
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
        if !premises.is_empty() {
            let lhs_available =
                EggExpr::Call("Avaliable".to_string(), vec![(*egg_equations.0).clone()]);
            let mut availability_premises = premises.clone();
            availability_premises.push(lhs_available.clone());
            rules.insert(EggStatement::Rule {
                ruleset: None,
                body: availability_premises,
                head: vec![EggExpr::Call(
                    "Avaliable".to_string(),
                    vec![(*egg_equations.1).clone()],
                )],
            });

            let mut seen_body = vec![lhs_available];
            let mut available_args = premise_available_args;
            for premise in definition.premises.iter() {
                let (premise_op, premise_lhs, premise_rhs) = get_equational_terms(premise).unwrap();
                seen_body.push(match premise_op {
                    Operator::Equals => EggExpr::Equal(
                        Box::new(
                            to_egg_expr(
                                premise_lhs,
                                &subs,
                                func_cache,
                                var_map,
                                definition.is_elaborated,
                            )
                            .unwrap(),
                        ),
                        Box::new(
                            to_egg_expr(
                                premise_rhs,
                                &subs,
                                func_cache,
                                var_map,
                                definition.is_elaborated,
                            )
                            .unwrap(),
                        ),
                    ),
                    Operator::Distinct => EggExpr::Distinct(
                        Box::new(
                            to_egg_expr(
                                premise_lhs,
                                &subs,
                                func_cache,
                                var_map,
                                definition.is_elaborated,
                            )
                            .unwrap(),
                        ),
                        Box::new(
                            to_egg_expr(
                                premise_rhs,
                                &subs,
                                func_cache,
                                var_map,
                                definition.is_elaborated,
                            )
                            .unwrap(),
                        ),
                    ),
                    _ => unreachable!(),
                });

                let premise_args = collect_vars(premise_lhs, false)
                    .into_keys()
                    .chain(collect_vars(premise_rhs, false).into_keys())
                    .collect::<IndexSet<_>>();

                for arg in premise_args {
                    if available_args.insert(arg.clone()) {
                        rules.insert(EggStatement::Rule {
                            ruleset: None,
                            body: seen_body.clone(),
                            head: vec![EggExpr::Call(
                                "Avaliable".to_string(),
                                vec![EggExpr::Literal(arg)],
                            )],
                        });
                    }
                }
            }
        }
    }
    rules
}

const GOAL_LHS_NAME: &str = "goal_lhs";
const GOAL_RHS_NAME: &str = "goal_rhs";

fn set_goal(lhs_expr: EggExpr, rhs_expr: EggExpr) -> Vec<EggStatement> {
    let mut goal = vec![];
    goal.push(EggStatement::Let(
        GOAL_LHS_NAME.to_string(),
        Box::new(lhs_expr),
    ));
    goal.push(EggStatement::Let(
        GOAL_RHS_NAME.to_string(),
        Box::new(rhs_expr),
    ));
    goal.push(EggStatement::Premise(
        "Avaliable".to_string(),
        Box::new(EggExpr::Literal(GOAL_LHS_NAME.to_string())),
    ));
    goal.push(EggStatement::Premise(
        "Avaliable".to_string(),
        Box::new(EggExpr::Literal(GOAL_RHS_NAME.to_string())),
    ));
    goal
}

fn available_subterm_premises(
    term: &Rc<Term>,
    func_cache: &mut EggFunctions,
    var_map: &mut HashMap<String, u64>,
) -> Vec<EggStatement> {
    let subs = IndexMap::new();
    collect_subterms(term)
        .into_iter()
        .filter(|subterm| subterm != term && !subterm.is_var())
        .filter_map(|subterm| {
            to_egg_expr(&subterm, &subs, func_cache, var_map, false)
                .map(|expr| EggStatement::Premise("Avaliable".to_string(), Box::new(expr)))
        })
        .collect()
}

fn goal_run_schedule(iter: i16) -> Vec<EggStatement> {
    let mut schedule = vec![
        EggStatement::Run {
            ruleset: Some("list-ruleset".to_string()),
            iterations: iter,
        },
        EggStatement::Run {
            ruleset: Some("evaluation".to_string()),
            iterations: iter,
        },
    ];
    schedule.push(EggStatement::Run { ruleset: None, iterations: iter });
    schedule
}

fn should_deduplicate_statement(statement: &EggStatement) -> bool {
    matches!(
        statement,
        EggStatement::Sort(..)
            | EggStatement::DataType(..)
            | EggStatement::Relation(..)
            | EggStatement::Function { .. }
            | EggStatement::Ruleset(..)
            | EggStatement::Constructor(..)
    )
}

fn should_deduplicate_command(command: &Command) -> bool {
    !matches!(command, Command::RunSchedule(..) | Command::Check(..))
}

fn compile_program(ast: Vec<EggStatement>) -> (Vec<Command>, String) {
    let mut seen = std::collections::HashSet::new();
    let ast: Vec<_> = ast
        .into_iter()
        .filter(|statement| {
            !should_deduplicate_statement(statement) || seen.insert(statement.clone())
        })
        .collect();

    let mut seen = std::collections::HashSet::new();
    let program: Vec<_> = lower_egg_language(ast)
        .into_iter()
        .filter(|command| !should_deduplicate_command(command) || seen.insert(command.to_string()))
        .collect();

    let code = program
        .iter()
        .map(|cmd| cmd.to_string())
        .collect::<Vec<_>>()
        .join("\n");

    (program, code)
}

fn run_statements(egraph: &mut EGraph, ast: Vec<EggStatement>) -> (Result<(), String>, String) {
    let (program, code) = compile_program(ast);
    (run_program(egraph, program), code)
}

fn run_program(egraph: &mut EGraph, program: Vec<Command>) -> Result<(), String> {
    catch_unwind(AssertUnwindSafe(|| egraph.run_program(program)))
        .map_err(|panic| {
            if let Some(message) = panic.downcast_ref::<&str>() {
                format!("egglog panic: {message}")
            } else if let Some(message) = panic.downcast_ref::<String>() {
                format!("egglog panic: {message}")
            } else {
                "egglog panic: unknown panic payload".to_string()
            }
        })
        .and_then(|result| result.map_err(|e| e.to_string()))
        .map(|_| ())
}

fn equal_terms() -> (EggExpr, EggExpr) {
    (
        EggExpr::Literal(GOAL_LHS_NAME.to_string()),
        EggExpr::Literal(GOAL_RHS_NAME.to_string()),
    )
}

fn check(
    egraph: &mut EGraph,
    lhs_expr: EggExpr,
    rhs_expr: EggExpr,
) -> (Result<(), String>, String) {
    run_statements(
        egraph,
        vec![EggStatement::Check(Box::new(EggExpr::Equal(
            Box::new(lhs_expr),
            Box::new(rhs_expr),
        )))],
    )
}

fn append_generated_code(code_str: &mut String, new_code: &str) {
    if new_code.is_empty() {
        return;
    }
    if !code_str.is_empty() {
        code_str.push('\n');
    }
    code_str.push_str(new_code);
}

fn run_and_record_statements(
    egraph: &mut EGraph,
    code_str: &mut String,
    ast: Vec<EggStatement>,
) -> Result<(), String> {
    let (result, code) = run_statements(egraph, ast);
    append_generated_code(code_str, &code);
    result
}

fn run_and_record_check(
    egraph: &mut EGraph,
    code_str: &mut String,
    lhs_expr: EggExpr,
    rhs_expr: EggExpr,
) -> Result<(), String> {
    let (result, code) = check(egraph, lhs_expr, rhs_expr);
    append_generated_code(code_str, &code);
    result
}

fn run_goal_schedule_round(
    egraph: &mut EGraph,
    code_str: &mut String,
    iter: i16,
) -> Result<(), String> {
    run_and_record_statements(egraph, code_str, goal_run_schedule(iter))
}

#[derive(Clone)]
struct GoalFallbackPlan {
    label: &'static str,
    guard_setup: Vec<EggStatement>,
    guard: EggExpr,
    setup: Vec<EggStatement>,
    lhs: EggExpr,
    rhs: EggExpr,
}

impl GoalFallbackPlan {
    fn new(
        label: &'static str,
        guard_setup: Vec<EggStatement>,
        guard: EggExpr,
        (setup, lhs, rhs): (Vec<EggStatement>, EggExpr, EggExpr),
    ) -> Self {
        Self {
            label,
            guard_setup,
            guard,
            setup,
            lhs,
            rhs,
        }
    }
}

fn run_goal_fallback_attempt(
    egraph: &mut EGraph,
    code_str: &mut String,
    fallback: &GoalFallbackPlan,
) -> Result<(), String> {
    run_and_record_statements(egraph, code_str, fallback.guard_setup.clone())?;
    run_and_record_check(
        egraph,
        code_str,
        fallback.guard.clone(),
        EggExpr::NativeBool(true),
    )?;
    run_and_record_statements(egraph, code_str, fallback.setup.clone())?;
    run_and_record_check(egraph, code_str, fallback.lhs.clone(), fallback.rhs.clone())
}

fn run_goal_fallback_attempts(
    egraph: &mut EGraph,
    code_str: &mut String,
    fallback_plans: &[GoalFallbackPlan],
) -> Result<(), String> {
    let mut errors = Vec::with_capacity(fallback_plans.len());

    for fallback in fallback_plans {
        match run_goal_fallback_attempt(egraph, code_str, fallback) {
            Ok(()) => return Ok(()),
            Err(error) => errors.push(format!("{} fallback failed:\n{}", fallback.label, error)),
        }
    }

    Err(errors.join("\n"))
}

fn check_goal_against_current_state(
    egraph: &mut EGraph,
    code_str: &mut String,
    lhs_expr: &EggExpr,
    rhs_expr: &EggExpr,
    fallback_plans: &[GoalFallbackPlan],
) -> Result<(), String> {
    match run_and_record_check(egraph, code_str, lhs_expr.clone(), rhs_expr.clone()) {
        Ok(()) => Ok(()),
        Err(raw_error) => {
            if fallback_plans.is_empty() {
                return Err(raw_error);
            }

            run_goal_fallback_attempts(egraph, code_str, fallback_plans)
                .map_err(|fallback_error| format!("{raw_error}\n{fallback_error}"))
        }
    }
}

#[derive(Clone)]
struct GoalCheckTarget {
    goal_label: String,
    lhs_expr: EggExpr,
    rhs_expr: EggExpr,
    fallback_plans: Vec<GoalFallbackPlan>,
}

fn check_goal_with_retry_rounds(
    egraph: &mut EGraph,
    code_str: &mut String,
    goal: &GoalCheckTarget,
    options: RunEgglogOptions,
) -> Result<(), String> {
    let mut last_error = None;

    let mut round = 0;
    loop {
        if !options.continuous_saturation && round >= options.normalized_max_goal_schedule_rounds()
        {
            break;
        }

        round += 1;
        let iterations = if options.continuous_saturation {
            1
        } else {
            round as i16
        };
        println!("Running goal check schedule round {}...", round);
        run_goal_schedule_round(egraph, code_str, iterations)?;

        match check_goal_against_current_state(
            egraph,
            code_str,
            &goal.lhs_expr,
            &goal.rhs_expr,
            &goal.fallback_plans,
        ) {
            Ok(()) => {
                return Ok(());
            }
            Err(error) => last_error = Some(error),
        }
    }

    Err(format!(
        "Elaboration failed {} failed:\n{}",
        goal.goal_label,
        last_error.unwrap_or_else(|| "goal equality check failed".to_string())
    ))
}

fn declare_functions(
    functions: &mut EggFunctions,
    constant: &IndexMap<String, DeclConst>,
    var_map: &mut HashMap<String, u64>,
) -> Vec<EggStatement> {
    let mut decls = Vec::new();
    declare_logic_operators(functions);

    for (func, (is_op, _arity, _result_sort)) in functions.names.iter() {
        // 1) always declare the function symbol
        decls.push(EggStatement::Constructor(
            format!("@{}", func),
            vec![ConstType::ConstrType("Term".to_string())],
            ConstType::ConstrType("Term".to_string()),
        ));
        decls.push(EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_string(),
                vec![EggExpr::Call(
                    format!("@{}", func),
                    vec![EggExpr::Literal("args".to_string())],
                )],
            )],
            head: vec![EggExpr::Call(
                "Avaliable".to_string(),
                vec![EggExpr::Literal("args".to_string())],
            )],
        });

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

fn get_fallback_plans(enable_arith_poly: bool) -> Vec<GoalFallbackPlan> {
    if !enable_arith_poly {
        return Vec::new();
    }

    let (goal_lhs, goal_rhs) = equal_terms();
    vec![
        GoalFallbackPlan::new(
            "arithPolyNfOf",
            vec![
                EggStatement::Call(Box::new(EggExpr::Call(
                    "arithGoalPolyNfOf-demand".to_string(),
                    vec![goal_lhs.clone()],
                ))),
                EggStatement::Run {
                    ruleset: Some("arith_poly_guard".to_string()),
                    iterations: 1,
                },
            ],
            arith_poly_norm::poly_goal_guard_term(goal_lhs.clone()),
            arith_poly_norm::poly_goal_check_terms(goal_lhs.clone(), goal_rhs.clone()),
        ),
        GoalFallbackPlan::new(
            "arithRelBoolKeyOf",
            vec![
                EggStatement::Call(Box::new(EggExpr::Call(
                    "arithRelBoolKeyOf-demand".to_string(),
                    vec![goal_lhs.clone()],
                ))),
                EggStatement::Run {
                    ruleset: Some("arith_poly_guard".to_string()),
                    iterations: 1,
                },
            ],
            arith_poly_norm_rel::relation_bool_goal_guard_term(goal_lhs.clone()),
            arith_poly_norm_rel::relation_bool_goal_check_terms(goal_lhs, goal_rhs),
        ),
    ]
}

fn goal_log_label(node: &Rc<ProofNode>, conclusion: &Rc<Term>) -> String {
    format!("{}: {:?}", node.id(), conclusion)
}

pub fn run_egglog(
    pool: &mut PrimitivePool,
    node: (Rc<Term>, &Rc<ProofNode>),
    database: &Rules,
    options: RunEgglogOptions,
) -> (Result<EGraph, String>, String) {
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

    // Functions coming from the premises and the goal are collected separately
    // from the ones coming from the RARE rule database, so that the arith poly
    // norm machinery is only enabled when the proof step itself involves
    // arithmetic, and not just because some rule in the database does.
    let mut goal_functions = EggFunctions::default();
    let premises = construct_premises(
        pool,
        std::slice::from_ref(&node),
        &mut var_map,
        &mut goal_functions,
    );

    let (conclusion, proof_node) = node.clone();
    let goal_label = goal_log_label(proof_node, &conclusion);
    println!("Elaborating {}", goal_label);

    let Some((_, lhs, rhs)) = get_equational_terms(&conclusion) else {
        return (Err("Failed to set goal".to_string()), String::new());
    };

    let goal_lhs_expr = to_egg_expr(
        lhs,
        &IndexMap::new(),
        &mut goal_functions,
        &mut var_map,
        false,
    )
    .unwrap();
    let goal_rhs_expr = to_egg_expr(
        rhs,
        &IndexMap::new(),
        &mut goal_functions,
        &mut var_map,
        false,
    )
    .unwrap();

    let mut goals_ast = set_goal(goal_lhs_expr, goal_rhs_expr);
    goals_ast.extend(available_subterm_premises(
        lhs,
        &mut goal_functions,
        &mut var_map,
    ));
    goals_ast.extend(available_subterm_premises(
        rhs,
        &mut goal_functions,
        &mut var_map,
    ));

    let (raw_lhs, raw_rhs) = equal_terms();
    let mut goal = GoalCheckTarget {
        goal_label,
        lhs_expr: raw_lhs,
        rhs_expr: raw_rhs,
        fallback_plans: Vec::new(),
    };

    let enable_arith_poly = arith_poly_norm::uses_arith_machinery(&goal_functions);
    goal.fallback_plans = get_fallback_plans(enable_arith_poly);

    egg_functions.absorb(goal_functions);

    let mut declarations = declare_functions(&mut egg_functions, &database.consts, &mut var_map);

    declare_special_eunoia_eliminations(&mut declarations, &egg_functions, enable_arith_poly);
    if enable_arith_poly {
        declarations.extend(arith_poly_norm::declare_opaque_arith_poly_rules(
            &egg_functions,
        ));
    }

    let mut ast = create_headers();

    ast.extend(declarations);
    ast.extend(rules);
    ast.extend(premises);
    ast.extend(goals_ast);

    let (egglog, mut code_str) = compile_program(ast);

    let mut egraph = EGraph::default();
    evaluation::register_evaluation_primitives(&mut egraph);
    if enable_arith_poly {
        arith_poly_norm::register_arith_poly_primitives(&mut egraph);
    }

    egraph.add_primitive(CustomPrimitive {
        name: Symbol::from("ineq"),
        input: vec![
            Arc::new(EqSort { name: Symbol::from("Term") }),
            Arc::new(EqSort { name: Symbol::from("Term") }),
        ],
        output: Arc::new(BoolSort),
        f: |x| Some(Value::from(x[0] != x[1])),
    });

    let result = run_program(&mut egraph, egglog)
        .and_then(|_| check_goal_with_retry_rounds(&mut egraph, &mut code_str, &goal, options));

    (result.map(|_| egraph), code_str)
}

fn format_seconds(duration: std::time::Duration) -> String {
    format!("{:.6}s", duration.as_secs_f64())
}

pub fn reconstruct_rule(
    pool: &mut PrimitivePool,
    conclusion: Rc<Term>,
    node: &Rc<ProofNode>,
    database: &Rules,
    options: RunEgglogOptions,
) {
    let egglog_start = Instant::now();
    let (result, egglogcode) = run_egglog(pool, (conclusion, node), database, options);
    let egglog_time = egglog_start.elapsed();
    if options.print_egglog {
        println!("{}", egglogcode);
    }
    match result {
        Ok(_) => println!("Elaboration succeeded in {}", format_seconds(egglog_time)),
        Err(error) => println!(
            "Elaboration failed in {}: {}",
            format_seconds(egglog_time),
            error
        ),
    }
}
