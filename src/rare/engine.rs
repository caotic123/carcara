use std::{
    cell::OnceCell,
    collections::{HashMap, HashSet},
    iter::once,
    panic::{AssertUnwindSafe, catch_unwind},
    sync::Arc,
    time::Instant,
};

use crate::{
    ast::{
        Binder, Constant, Operator, ProofNode, Rc, Sort, Term,
        pool::TermPool,
        rare_rules::{AttributeParameters, RuleDefinition, Rules},
    },
    checker::{ListEncoding, RunEgglogOptions},
    rare::{
        computational::{
            aci_norm::singleton_operators,
            arith_poly_norm, arith_poly_norm_rel,
            core::{declare_database_eliminations, declare_goal_eliminations},
            distinct_elim::declare_logic_operators,
            evaluation,
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
    self, ArcSort, EGraph, PrimitiveLike, Value,
    ast::{Command, Span},
    constraint::{SimpleTypeConstraint, TypeConstraint},
    sort::{BoolSort, EqSort},
};
use indexmap::{IndexMap, IndexSet};

#[derive(Clone, Debug, Default)]
pub struct EggFunctions {
    pub names: IndexMap<String, (bool, usize, Option<Sort>)>,
    pub shapes: IndexMap<String, IndexSet<Rc<Term>>>,
    pub assoc_calls: IndexMap<String, IndexSet<EggExpr>>,
}

impl RunEgglogOptions {
    fn normalized_max_goal_schedule_rounds(self) -> usize {
        self.max_goal_schedule_rounds.max(1)
    }
}

pub struct RareCtx<'a> {
    database: &'a Rules,
    baseline: OnceCell<Result<RareDatabaseBaseline, String>>,
}

impl<'a> RareCtx<'a> {
    pub fn new(database: &'a Rules) -> Self {
        Self { database, baseline: OnceCell::new() }
    }

    /// The prepared database, built on first use with the given seeding
    /// (see `RunEgglogOptions::seed_from_goal`) and list encoding; one
    /// context serves one setting.
    fn baseline(
        &self,
        seed_from_goal: bool,
        sort_guards: bool,
        list_encoding: ListEncoding,
    ) -> Result<&RareDatabaseBaseline, String> {
        self.baseline
            .get_or_init(|| {
                prepare_database_safely(self.database, seed_from_goal, sort_guards, list_encoding)
            })
            .as_ref()
            .map_err(Clone::clone)
    }

    #[cfg(test)]
    fn is_prepared(&self) -> bool {
        self.baseline.get().is_some()
    }
}

#[derive(Clone)]
struct RareDatabaseBaseline {
    egraph: EGraph,
    functions: EggFunctions,
    var_map: HashMap<String, u64>,
    code: String,
    has_distinct: bool,
    commands: HashSet<String>,
}

fn application_result_sort(head: &Rc<Term>) -> Option<Sort> {
    let Term::Var(_, sort_term) = head.as_ref() else {
        return None;
    };
    let Sort::Function(parts) = sort_term.as_ref() else {
        return None;
    };
    Some(parts.last()?.as_ref().clone())
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
        .entry(name.to_owned())
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
        "bigrat".to_owned(),
        vec![
            EggExpr::Call(
                "from-string".to_owned(),
                vec![EggExpr::RawString(numer.to_string())],
            ),
            EggExpr::Call(
                "from-string".to_owned(),
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
        EggStatement::Ruleset("list-ruleset".to_owned()),
        EggStatement::DataType(
            "Term".to_owned(),
            vec![
                Constructor {
                    constr: (
                        "App".to_owned(),
                        vec![
                            ConstType::ConstrType("Term".to_owned()),
                            ConstType::ConstrType("Term".to_owned()),
                        ],
                    ),
                },
                Constructor {
                    constr: ("Const".to_owned(), vec![ConstType::Operator]),
                },
                Constructor {
                    constr: (
                        "Var".to_owned(),
                        vec![ConstType::Var, ConstType::ConstrType("Term".to_owned())],
                    ),
                },
                Constructor {
                    constr: ("Bool".to_owned(), vec![ConstType::Bool]),
                },
                Constructor {
                    constr: ("Num".to_owned(), vec![ConstType::Integer]),
                },
                Constructor {
                    constr: (
                        "Real".to_owned(),
                        vec![ConstType::Integer, ConstType::Integer],
                    ),
                },
                Constructor {
                    constr: (
                        "BitVec".to_owned(),
                        vec![ConstType::Operator, ConstType::Operator],
                    ),
                },
                Constructor {
                    constr: ("Op".to_owned(), vec![ConstType::Operator]),
                },
                Constructor {
                    constr: ("@String".to_owned(), vec![ConstType::Operator]),
                },
                Constructor {
                    constr: (
                        "Forall".to_owned(),
                        vec![ConstType::ConstrType("Term".to_owned())],
                    ),
                },
                Constructor {
                    constr: (
                        "Exists".to_owned(),
                        vec![ConstType::ConstrType("Term".to_owned())],
                    ),
                },
                Constructor {
                    constr: (
                        "Lambda".to_owned(),
                        vec![ConstType::ConstrType("Term".to_owned())],
                    ),
                },
                Constructor {
                    constr: (
                        "Choice".to_owned(),
                        vec![ConstType::ConstrType("Term".to_owned())],
                    ),
                },
                Constructor {
                    constr: (
                        "Sort".to_owned(),
                        vec![ConstType::ConstrType("Term".to_owned())],
                    ),
                },
                Constructor {
                    constr: ("Empty".to_owned(), vec![]),
                },
                Constructor {
                    constr: (
                        "Args".to_owned(),
                        vec![
                            ConstType::ConstrType("Term".to_owned()),
                            ConstType::ConstrType("Term".to_owned()),
                        ],
                    ),
                },
                Constructor {
                    constr: (
                        "Mk".to_owned(),
                        vec![ConstType::ConstrType("Term".to_owned())],
                    ),
                },
            ],
        ),
        EggStatement::Constructor(
            "RatConst".to_owned(),
            vec![ConstType::ConstrType("BigRat".to_owned())],
            ConstType::ConstrType("Term".to_owned()),
        ),
        EggStatement::Sort(
            "AssocArgs".to_owned(),
            "Set".to_owned(),
            Box::new(EggExpr::Literal("Term".to_owned())),
        ),
        EggStatement::Constructor(
            "Assoc".to_owned(),
            vec![ConstType::ConstrType("AssocArgs".to_owned())],
            ConstType::ConstrType("Term".to_owned()),
        ),
        EggStatement::Relation(
            "Avaliable".to_owned(),
            vec![ConstType::ConstrType("Term".to_owned())],
        ),
        // The goal's and the proof premises' own subterms, asserted per goal
        // and never propagated: what conditional rules' premise instances
        // range over under `seed_from_goal`.
        EggStatement::Relation(
            ORIGIN_RELATION.to_owned(),
            vec![ConstType::ConstrType("Term".to_owned())],
        ),
        // The sort of a class, for `sort_guards`: seeded from the goal's
        // terms, propagated by operator heads and declared function sorts.
        EggStatement::Relation(
            SORT_INT.to_owned(),
            vec![ConstType::ConstrType("Term".to_owned())],
        ),
        EggStatement::Relation(
            SORT_REAL.to_owned(),
            vec![ConstType::ConstrType("Term".to_owned())],
        ),
        EggStatement::Relation(
            SORT_BOOL.to_owned(),
            vec![ConstType::ConstrType("Term".to_owned())],
        ),
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Mk(Box::new(EggExpr::Literal("t".to_owned())))],
            )],
            head: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Literal("t".to_owned())],
            )],
        },
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Args(
                    Box::new(EggExpr::Literal("head".to_owned())),
                    Box::new(EggExpr::Literal("tail".to_owned())),
                )],
            )],
            head: vec![
                EggExpr::Call(
                    "Avaliable".to_owned(),
                    vec![EggExpr::Literal("head".to_owned())],
                ),
                EggExpr::Call(
                    "Avaliable".to_owned(),
                    vec![EggExpr::Literal("tail".to_owned())],
                ),
            ],
        },
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Call(
                    "App".to_owned(),
                    vec![
                        EggExpr::Literal("fn_term".to_owned()),
                        EggExpr::Literal("arg_term".to_owned()),
                    ],
                )],
            )],
            head: vec![
                EggExpr::Call(
                    "Avaliable".to_owned(),
                    vec![EggExpr::Literal("fn_term".to_owned())],
                ),
                EggExpr::Call(
                    "Avaliable".to_owned(),
                    vec![EggExpr::Literal("arg_term".to_owned())],
                ),
            ],
        },
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Call(
                    "Var".to_owned(),
                    vec![
                        EggExpr::Literal("var_id".to_owned()),
                        EggExpr::Literal("sort_term".to_owned()),
                    ],
                )],
            )],
            head: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Literal("sort_term".to_owned())],
            )],
        },
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Call(
                    "Forall".to_owned(),
                    vec![EggExpr::Literal("body".to_owned())],
                )],
            )],
            head: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Literal("body".to_owned())],
            )],
        },
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Call(
                    "Exists".to_owned(),
                    vec![EggExpr::Literal("body".to_owned())],
                )],
            )],
            head: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Literal("body".to_owned())],
            )],
        },
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Call(
                    "Lambda".to_owned(),
                    vec![EggExpr::Literal("body".to_owned())],
                )],
            )],
            head: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Literal("body".to_owned())],
            )],
        },
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Call(
                    "Choice".to_owned(),
                    vec![EggExpr::Literal("body".to_owned())],
                )],
            )],
            head: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Literal("body".to_owned())],
            )],
        },
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Call(
                    "Sort".to_owned(),
                    vec![EggExpr::Literal("sort_term".to_owned())],
                )],
            )],
            head: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Literal("sort_term".to_owned())],
            )],
        },
        EggStatement::Rewrite(
            Box::new(EggExpr::Args(
                Box::new(EggExpr::Args(
                    Box::new(EggExpr::Literal("t1".to_owned())),
                    Box::new(EggExpr::Literal("t2".to_owned())),
                )),
                Box::new(EggExpr::Literal("t3".to_owned())),
            )),
            Box::new(EggExpr::Args(
                Box::new(EggExpr::Literal("t1".to_owned())),
                Box::new(EggExpr::Args(
                    Box::new(EggExpr::Literal("t2".to_owned())),
                    Box::new(EggExpr::Literal("t3".to_owned())),
                )),
            )),
            vec![],
        ),
        EggStatement::Rewrite(
            Box::new(EggExpr::Args(
                Box::new(EggExpr::Literal("t1".to_owned())),
                Box::new(EggExpr::Args(
                    Box::new(EggExpr::Literal("t2".to_owned())),
                    Box::new(EggExpr::Literal("t3".to_owned())),
                )),
            )),
            Box::new(EggExpr::Args(
                Box::new(EggExpr::Args(
                    Box::new(EggExpr::Literal("t1".to_owned())),
                    Box::new(EggExpr::Literal("t2".to_owned())),
                )),
                Box::new(EggExpr::Literal("t3".to_owned())),
            )),
            vec![],
        ),
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Equal(
                Box::new(EggExpr::Mk(Box::new(EggExpr::Literal("x".to_owned())))),
                Box::new(EggExpr::Mk(Box::new(EggExpr::Literal("y".to_owned())))),
            )],
            head: vec![EggExpr::Union(
                Box::new(EggExpr::Literal("x".to_owned())),
                Box::new(EggExpr::Literal("y".to_owned())),
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
    seed: &str,
    context: &str,
) -> Result<Option<EggStatement>, String> {
    if term.is_var() {
        return Ok(None);
    }

    let mut premises = Vec::new();
    let mut sorted_vars = IndexMap::new();
    let vars = if recognize_vars {
        collect_vars(term, false)
    } else {
        IndexMap::default()
    };

    for (name, _sort) in &vars {
        let egg_expr = EggExpr::Literal(name.clone());
        sorted_vars.insert(name, (egg_expr.clone(), AttributeParameters::List));
        premises.push(EggExpr::Call(seed.to_owned(), vec![egg_expr]));
    }

    let head = translate_term(term, &sorted_vars, func_cache, var_map, false, context)?;
    Ok(Some(EggStatement::Rule {
        ruleset: None,
        body: premises,
        head: vec![head],
    }))
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
        let first = it.next()?;
        let mut acc = EggExpr::Args(Box::new(first), Box::new(EggExpr::Empty()));
        for e in it {
            acc = EggExpr::Args(Box::new(e), Box::new(acc));
        }
        Some(acc)
    }

    pub fn encapluse(egg_term: EggExpr) -> EggExpr {
        EggExpr::Mk(Box::new(egg_term))
    }

    fn sort_to_egg(
        sort: &Rc<Sort>,
        _subs: &IndexMap<&String, (EggExpr, AttributeParameters)>,
        func_cache: &mut EggFunctions,
        var_map: &mut HashMap<String, u64>,
        _collect_shapes: bool,
    ) -> Option<EggExpr> {
        let encode = |sort, func_cache: &mut EggFunctions, var_map: &mut HashMap<String, u64>| {
            sort_to_egg(sort, _subs, func_cache, var_map, _collect_shapes)
        };
        match sort.as_ref() {
            Sort::Var(name) => Some(EggExpr::Var(
                hash_var_name(var_map, name),
                Box::new(EggExpr::Const("Type".to_owned())),
            )),
            Sort::Bool => Some(EggExpr::Const("Bool".to_owned())),
            Sort::Int => Some(EggExpr::Const("Int".to_owned())),
            Sort::Real => Some(EggExpr::Const("Real".to_owned())),
            Sort::String => Some(EggExpr::Const("String".to_owned())),
            Sort::RegLan => Some(EggExpr::Const("RegLan".to_owned())),
            Sort::Type => Some(EggExpr::Const("Type".to_owned())),
            Sort::ParamBitVec => Some(EggExpr::Const("ParamBitVec".to_owned())),
            Sort::BitVec(width) => build_args_list(vec![
                Some(EggExpr::Const("BitVec".to_owned())),
                Some(EggExpr::Num((*width).into())),
            ]),
            Sort::Array(index, element) => build_args_list(vec![
                Some(EggExpr::Const("Array".to_owned())),
                encode(index, func_cache, var_map),
                encode(element, func_cache, var_map),
            ]),
            Sort::Function(parts) => {
                let mut encoded = vec![Some(EggExpr::Const("Function".to_owned()))];
                encoded.extend(parts.iter().map(|part| encode(part, func_cache, var_map)));
                build_args_list(encoded)
            }
            Sort::Atom(name, args) => {
                let mut encoded = vec![Some(EggExpr::Const(name.to_string()))];
                encoded.extend(args.iter().map(|arg| encode(arg, func_cache, var_map)));
                build_args_list(encoded)
            }
            Sort::Datatype { name, args } => {
                let mut encoded = vec![Some(EggExpr::Const(name.to_string()))];
                encoded.extend(args.iter().map(|arg| encode(arg, func_cache, var_map)));
                build_args_list(encoded)
            }
            Sort::Par(vars, inner) => {
                let vars = build_args_list(vars.iter().map(|name| {
                    Some(EggExpr::Var(
                        hash_var_name(var_map, name),
                        Box::new(EggExpr::Const("Type".to_owned())),
                    ))
                }))?;
                build_args_list(vec![
                    Some(EggExpr::Const("Par".to_owned())),
                    Some(vars),
                    encode(inner, func_cache, var_map),
                ])
            }
            Sort::Set(inner) => build_args_list(vec![
                Some(EggExpr::Const("Set".to_owned())),
                encode(inner, func_cache, var_map),
            ]),
            Sort::Tuple(parts) => {
                let mut encoded = vec![Some(EggExpr::Const("Tuple".to_owned()))];
                encoded.extend(parts.iter().map(|part| encode(part, func_cache, var_map)));
                build_args_list(encoded)
            }
        }
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
                Constant::BitVec(i, j) => Some(EggExpr::BitVec(i.clone(), (*j).into())),
                Constant::Real(d) => {
                    let (numer, denom) = d.clone().into_numer_denom();
                    if numer.to_i64().is_some() && denom.to_i64().is_some() {
                        Some(EggExpr::Real((numer, denom)))
                    } else {
                        Some(EggExpr::Call(
                            "RatConst".to_owned(),
                            vec![bigrat_expr(&numer, &denom)],
                        ))
                    }
                }
                // Egglog has no encoding for automata-backed regular-language constants.
                Constant::RegLan(_, _) => None,
            },
            Term::Var(name, sort) => {
                if let Some(argument) = subs.get(name) {
                    Some(argument.0.clone())
                } else {
                    let sort =
                        sort_to_egg(sort, subs, func_cache, var_map, collect_functions_shape)?;
                    Some(EggExpr::Var(
                        hash_var_name(var_map, name),
                        Box::new(EggExpr::Call("Sort".to_owned(), vec![sort])),
                    ))
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
                        .entry(func_name.clone())
                        .and_modify(|v| {
                            v.insert(term_rc.clone());
                        })
                        .or_insert({
                            let mut v = IndexSet::new();
                            v.insert(term_rc.clone());
                            v
                        });
                }

                if args.is_empty() {
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
                if args.is_empty() {
                    if head == &Operator::True || head == &Operator::False {
                        return Some(EggExpr::Bool(head == &Operator::True));
                    }
                    return Some(EggExpr::Op(head.to_string()));
                }

                register_function_call(func_cache, &head.to_string(), true, args.len(), None);
                let arg_exprs = args
                    .iter()
                    .map(|x| to_egg_expr(x, subs, func_cache, var_map, collect_functions_shape))
                    .collect::<Option<Vec<_>>>()?;
                let args_list = build_args_list(arg_exprs.iter().cloned().map(Some))?;

                let op_with_at = format!("@{}", head);
                if singleton_operators(*head).is_some() {
                    func_cache
                        .assoc_calls
                        .entry(op_with_at.clone())
                        .or_default()
                        .insert(args_list.clone());
                    Some(EggExpr::Call(op_with_at, vec![args_list]))
                } else {
                    Some(EggExpr::Call(format!("@{0}", head), vec![args_list]))
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
                .to_owned();

                // encode the bound variable list
                let vars_list = build_args_list(bindings.0.iter().map(|(name, sort)| {
                    let sort =
                        sort_to_egg(sort, subs, func_cache, var_map, collect_functions_shape)?;
                    Some(EggExpr::Var(
                        hash_var_name(var_map, name),
                        Box::new(EggExpr::Call("Sort".to_owned(), vec![sort])),
                    ))
                }))?;

                // encode the body
                let body_e = to_egg_expr(body, subs, func_cache, var_map, collect_functions_shape)?;

                // single Term parameter: Args(vars_list, body_e)
                let packed = EggExpr::Args(Box::new(vars_list), Box::new(body_e));

                Some(EggExpr::Call(ctor, vec![packed]))
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
                    "Lambda".to_owned(),
                    vec![EggExpr::Args(Box::new(vars_list), Box::new(body_e))],
                );

                // Now apply the lambda to each bound value using nested `App`:
                //   App(App(... App(lambda_e, v1), v2), ... vn)
                let mut applied = lambda_e;
                for (_name, val_term) in &bindings.0 {
                    let val_e =
                        to_egg_expr(val_term, subs, func_cache, var_map, collect_functions_shape)?;
                    applied = EggExpr::Call("App".to_owned(), vec![applied, val_e]);
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
                Some(EggExpr::Call(format!("@{}", op), vec![packed?]))
            }
            // The RARE encoding does not currently model SMT-LIB datatype match expressions.
            // Reject them conservatively so the enclosing proof step remains a hole.
            Term::Match(_, _) => None,
            // Qualified operators carry a sort argument; the RARE encoding does not model them.
            Term::AsOp(_, _, _) => None,
        }
    }

    to_raw_egg(term_rc, subs, func_cache, var_map, collect_functions_shape).map(|x| {
        if let EggExpr::Literal(name) = &x
            && let Some(argument) = subs.get(name)
        {
            if argument.1 != AttributeParameters::List {
                return encapluse(x);
            }
            return x;
        }

        encapluse(x)
    })
}

fn translate_term(
    term: &Rc<Term>,
    subs: &IndexMap<&String, (EggExpr, AttributeParameters)>,
    func_cache: &mut EggFunctions,
    var_map: &mut HashMap<String, u64>,
    collect_functions_shape: bool,
    context: &str,
) -> Result<EggExpr, String> {
    to_egg_expr(term, subs, func_cache, var_map, collect_functions_shape)
        .ok_or_else(|| format!("cannot translate term '{term}' while {context}"))
}

fn construct_premises(
    pool: &mut dyn TermPool,
    premise_clauses: &[&[Rc<Term>]],
    var_map: &mut HashMap<String, u64>,
    func_cache: &mut EggFunctions,
) -> Result<EggLanguage, String> {
    let mut grounds_terms = IndexSet::new();

    for premise_clause in premise_clauses {
        let clause: Option<Rc<Term>> = clauses_to_or(pool, premise_clause);
        if let Some(clause) = clause {
            let expr = get_equational_terms(&clause);
            if let Some((Operator::Equals, lhs, rhs)) = expr {
                grounds_terms.insert(EggStatement::Union(
                    Box::new(translate_term(
                        lhs,
                        &IndexMap::new(),
                        func_cache,
                        var_map,
                        false,
                        "translating a proof premise",
                    )?),
                    Box::new(translate_term(
                        rhs,
                        &IndexMap::new(),
                        func_cache,
                        var_map,
                        false,
                        "translating a proof premise",
                    )?),
                ));
            }

            if let Some(ground) = create_avaliable_premise(
                &clause,
                func_cache,
                var_map,
                false,
                "Avaliable",
                "translating a proof premise",
            )? {
                grounds_terms.insert(ground);
            }
        }
    }

    Ok(grounds_terms.into_iter().collect())
}

/// A RARE rule whose n-ary operator has a set form, compiled against that
/// form instead of against the argument chain.
///
/// A `:list` parameter stands for a possibly empty sequence of arguments,
/// which the chain encoding cannot express: the parameter gets one slot of
/// the chain, and a slot has to be filled, so the rule only matches when
/// every list is non-empty.  Filling the gap on the chain costs either one
/// rule per emptiness pattern or an e-node per chain cell, and the cells are
/// re-associated, which multiplies the bracketings of a long `and`/`or`.
///
/// On the set form there are no positions at all: the rule says that the set
/// contains the fixed elements, and the lists are whatever else is in it.
/// One rule covers every arity and every arrangement, including the empty
/// lists, and it adds nothing to the e-graph.  `and` and `or` qualify
/// because they are idempotent, so dropping the multiplicity a set loses is
/// sound; `+` and `*` are n-ary too but are not, and keep the chain form.
fn set_form_rule(
    definition: &RuleDefinition,
    subs: &IndexMap<&String, (EggExpr, AttributeParameters)>,
    func_cache: &mut EggFunctions,
    var_map: &mut HashMap<String, u64>,
    guards: &[EggExpr],
    conclusion_lhs: &Rc<Term>,
    conclusion_rhs: &Rc<Term>,
) -> Result<Option<EggStatement>, String> {
    let is_list = |term: &Rc<Term>| {
        term.as_var().is_some_and(|name| {
            definition
                .parameters
                .get(name)
                .is_some_and(|parameter| parameter.attribute == AttributeParameters::List)
        })
    };
    let elements = |term: &Rc<Term>| -> Option<(&'static str, Vec<Rc<Term>>, Vec<Rc<Term>>)> {
        let Term::Op(operator, arguments) = term.as_ref() else {
            return None;
        };
        let operator = match operator {
            Operator::And => "@and",
            Operator::Or => "@or",
            _ => return None,
        };
        let (lists, fixed): (Vec<_>, Vec<_>) = arguments.iter().cloned().partition(&is_list);
        Some((operator, lists, fixed))
    };

    let Some((operator, lists, fixed)) = elements(conclusion_lhs) else {
        return Ok(None);
    };
    if lists.is_empty() || fixed.is_empty() {
        return Ok(None);
    }
    let context = format!("translating RARE rule '{}' against the set form", definition.name);
    let set = EggExpr::Literal("elements".to_owned());
    let call = |set: EggExpr| {
        EggExpr::Call(
            operator.to_owned(),
            vec![EggExpr::Call("Assoc".to_owned(), vec![set])],
        )
    };
    let result = EggExpr::Literal("result".to_owned());

    let mut body = vec![EggExpr::Equal(
        Box::new(call(set.clone())),
        Box::new(result.clone()),
    )];
    for element in &fixed {
        let element = translate_term(element, subs, func_cache, var_map, false, &context)?;
        body.push(EggExpr::Call(
            "set-contains".to_owned(),
            vec![set.clone(), element],
        ));
    }
    body.extend(guards.iter().cloned());

    // The right-hand side: a term that does not mention the lists is stated
    // as it is; one that reuses them is the same set with the left-hand
    // side's own elements taken out and its own put in.
    let rhs_mentions_list = collect_vars(conclusion_rhs, false)
        .keys()
        .any(|name| {
            definition
                .parameters
                .get(name)
                .is_some_and(|parameter| parameter.attribute == AttributeParameters::List)
        });
    let head = if !rhs_mentions_list {
        translate_term(conclusion_rhs, subs, func_cache, var_map, false, &context)?
    } else {
        let Some((rhs_operator, rhs_lists, rhs_fixed)) = elements(conclusion_rhs) else {
            return Ok(None);
        };
        let same_lists = |a: &[Rc<Term>], b: &[Rc<Term>]| {
            a.len() == b.len() && a.iter().all(|term| b.contains(term))
        };
        if rhs_operator != operator || !same_lists(&lists, &rhs_lists) {
            return Ok(None);
        }
        let mut rebuilt = set.clone();
        for element in &fixed {
            let element = translate_term(element, subs, func_cache, var_map, false, &context)?;
            rebuilt = EggExpr::Call("set-remove".to_owned(), vec![rebuilt, element]);
        }
        for element in &rhs_fixed {
            let element = translate_term(element, subs, func_cache, var_map, false, &context)?;
            rebuilt = EggExpr::Call("set-insert".to_owned(), vec![rebuilt, element]);
        }
        call(rebuilt)
    };

    Ok(Some(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_owned()),
        body,
        head: vec![EggExpr::Union(Box::new(result), Box::new(head))],
    }))
}

fn construct_rules(
    database: &[RuleDefinition],
    func_cache: &mut EggFunctions,
    var_map: &mut HashMap<String, u64>,
    seed_from_goal: bool,
    sort_guards: bool,
    list_encoding: ListEncoding,
) -> Result<IndexSet<EggStatement>, String> {
    // The relation a conditional rule's premise instances range over: every
    // available term, or only the goal's and the proof premises' subterms.
    let seed = if seed_from_goal { ORIGIN_RELATION } else { "Avaliable" };
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
                            .map_or(AttributeParameters::None, |x| x.attribute),
                    ),
                )
            })
            .collect::<IndexMap<_, _>>();

        let mut premise_available_args = IndexSet::new();

        let Some((Operator::Equals, conclusion_lhs, conclusion_rhs)) =
            get_equational_terms(&definition.conclusion)
        else {
            return Err(format!(
                "RARE rule '{}' must have a binary equality as its conclusion",
                definition.name
            ));
        };
        premise_available_args.extend(collect_vars(conclusion_lhs, false).into_keys());
        let guards = if sort_guards {
            sort_guard_premises(definition, &premise_available_args)
        } else {
            Vec::new()
        };

        let context = format!("translating RARE rule '{}'", definition.name);

        for premise in &definition.premises {
            let Some((op @ (Operator::Equals | Operator::Distinct), lhs, rhs)) =
                get_equational_terms(premise)
            else {
                return Err(format!(
                    "RARE rule '{}' has a premise that is not a binary equality or disequality: {}",
                    definition.name, premise
                ));
            };
            match op {
                Operator::Equals => {
                    if let Some(lhs) =
                        create_avaliable_premise(lhs, func_cache, var_map, true, seed, &context)?
                    {
                        rules.insert(lhs);
                    }

                    let lhs = Box::new(translate_term(
                        lhs,
                        &subs,
                        func_cache,
                        var_map,
                        definition.is_elaborated,
                        &context,
                    )?);

                    if let Some(rhs) =
                        create_avaliable_premise(rhs, func_cache, var_map, true, seed, &context)?
                    {
                        rules.insert(rhs);
                    }
                    let rhs = Box::new(translate_term(
                        rhs,
                        &subs,
                        func_cache,
                        var_map,
                        definition.is_elaborated,
                        &context,
                    )?);

                    premises.push(EggExpr::Equal(lhs, rhs));
                }

                Operator::Distinct => {
                    if let Some(lhs) =
                        create_avaliable_premise(lhs, func_cache, var_map, true, seed, &context)?
                    {
                        rules.insert(lhs);
                    }

                    let lhs = Box::new(translate_term(
                        lhs,
                        &subs,
                        func_cache,
                        var_map,
                        definition.is_elaborated,
                        &context,
                    )?);

                    if let Some(rhs) =
                        create_avaliable_premise(rhs, func_cache, var_map, true, seed, &context)?
                    {
                        rules.insert(rhs);
                    }

                    let rhs = Box::new(translate_term(
                        rhs,
                        &subs,
                        func_cache,
                        var_map,
                        definition.is_elaborated,
                        &context,
                    )?);

                    premises.push(EggExpr::Distinct(lhs, rhs));
                }
                _ => {
                    return Err(format!(
                        "RARE rule '{}' has an unsupported premise operator: {}",
                        definition.name, premise
                    ));
                }
            }
        }

        let egg_equations: (Box<EggExpr>, Box<EggExpr>) = (
            Box::new(translate_term(
                conclusion_lhs,
                &subs,
                func_cache,
                var_map,
                definition.is_elaborated,
                &context,
            )?),
            Box::new(translate_term(
                conclusion_rhs,
                &subs,
                func_cache,
                var_map,
                definition.is_elaborated,
                &context,
            )?),
        );

        // An unconditional rewrite carries the RARE name into the program
        // as a unique egglog rule name (the suffix keeps several
        // instantiations of one rule apart), so reconstruction can cite the
        // rule.  Conditional rewrites are never reconstructed and stay plain.
        // Sort guards are conditions too, but a rule that is unconditional
        // apart from them stays a named rewrite: reconstruction ignores the
        // guards (they do not change what the rule rewrites) and needs the
        // name.
        // A `:list` parameter stands for a possibly empty sequence of
        // arguments, but the translation gives it one slot of the `Args`
        // chain, which the chain re-association lets bind several elements
        // and never none.  So the rule as translated only matches when every
        // list is non-empty: `bool-or-taut` proved `(or a p b (not p) c)`
        // and never `(or p (not p))`.  One variant per subset of the list
        // parameters, with those dropped from the argument chains, covers
        // the empty cases; a variant whose chain would end up without
        // arguments is not emitted.
        // An `and`/`or` rule with `:list` parameters is compiled against the
        // set form, where the lists need no positions; only the operators
        // without one still need the chain variants below.
        let set_form = match list_encoding {
            ListEncoding::Chain => None,
            ListEncoding::SetForm => set_form_rule(
                definition,
                &subs,
                func_cache,
                var_map,
                &guards,
                conclusion_lhs,
                conclusion_rhs,
            )?,
        };
        let on_the_set_form = set_form.is_some();
        if let Some(statement) = set_form {
            rules.insert(statement);
        }

        let list_slots: Vec<String> = definition
            .parameters
            .iter()
            .filter(|(name, parameter)| {
                parameter.attribute == AttributeParameters::List
                    && mentions_slot(&egg_equations.0, name)
            })
            .map(|(name, _)| name.clone())
            .collect();
        let variants: Vec<(EggExpr, EggExpr)> = if on_the_set_form {
            Vec::new()
        } else if list_slots.len() <= MAX_LIST_SLOTS {
            (1..(1u32 << list_slots.len()))
                .filter_map(|mask| {
                    let dropped: Vec<&str> = list_slots
                        .iter()
                        .enumerate()
                        .filter(|(index, _)| mask & (1 << index) != 0)
                        .map(|(_, name)| name.as_str())
                        .collect();
                    let lhs = drop_list_slots(&egg_equations.0, &dropped)?;
                    let rhs = drop_list_slots(&egg_equations.1, &dropped)?;
                    (lhs != *egg_equations.0).then_some((lhs, rhs))
                })
                .collect()
        } else {
            Vec::new()
        };

        let conditional = !premises.is_empty();
        premises.extend(guards.iter().cloned());
        for (lhs, rhs) in variants {
            let statement = if !conditional {
                EggStatement::NamedRewrite {
                    name: format!("rare:{}#{}", definition.name, rules.len()),
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    conditions: guards.clone(),
                }
            } else {
                EggStatement::Rewrite(Box::new(lhs), Box::new(rhs), premises.clone())
            };
            rules.insert(statement);
        }
        // The generated name carries the rule's `:list` parameters, so that
        // the reconstruction can recover an instantiation the chain pattern
        // cannot e-match: a list parameter stands for a segment of the
        // arguments, which is a sequence match rather than a structural one.
        let list_parameters: Vec<&str> = definition
            .parameters
            .iter()
            .filter(|(_, parameter)| parameter.attribute == AttributeParameters::List)
            .map(|(name, _)| name.as_str())
            .collect();
        let name_suffix = if list_parameters.is_empty() {
            String::new()
        } else {
            format!(":lists={}", list_parameters.join(","))
        };
        rules.insert(if !conditional {
            EggStatement::NamedRewrite {
                name: format!("rare:{}#{}{}", definition.name, rules.len(), name_suffix),
                lhs: egg_equations.0.clone(),
                rhs: egg_equations.1.clone(),
                conditions: guards.clone(),
            }
        } else {
            EggStatement::Rewrite(
                egg_equations.0.clone(),
                egg_equations.1.clone(),
                premises.clone(),
            )
        });
        if conditional {
            let lhs_available =
                EggExpr::Call("Avaliable".to_owned(), vec![(*egg_equations.0).clone()]);
            let mut availability_premises = premises.clone();
            availability_premises.push(lhs_available.clone());
            rules.insert(EggStatement::Rule {
                ruleset: None,
                body: availability_premises,
                head: vec![EggExpr::Call(
                    "Avaliable".to_owned(),
                    vec![(*egg_equations.1).clone()],
                )],
            });

            let mut seen_body = vec![lhs_available];
            let mut available_args = premise_available_args;
            for premise in &definition.premises {
                let Some((premise_op, premise_lhs, premise_rhs)) = get_equational_terms(premise)
                else {
                    return Err(format!(
                        "RARE rule '{}' has a malformed premise: {}",
                        definition.name, premise
                    ));
                };
                seen_body.push(match premise_op {
                    Operator::Equals => EggExpr::Equal(
                        Box::new(translate_term(
                            premise_lhs,
                            &subs,
                            func_cache,
                            var_map,
                            definition.is_elaborated,
                            &context,
                        )?),
                        Box::new(translate_term(
                            premise_rhs,
                            &subs,
                            func_cache,
                            var_map,
                            definition.is_elaborated,
                            &context,
                        )?),
                    ),
                    Operator::Distinct => EggExpr::Distinct(
                        Box::new(translate_term(
                            premise_lhs,
                            &subs,
                            func_cache,
                            var_map,
                            definition.is_elaborated,
                            &context,
                        )?),
                        Box::new(translate_term(
                            premise_rhs,
                            &subs,
                            func_cache,
                            var_map,
                            definition.is_elaborated,
                            &context,
                        )?),
                    ),
                    _ => {
                        return Err(format!(
                        "RARE rule '{}' has a premise that is not an equality or disequality: {}",
                        definition.name, premise
                    ))
                    }
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
                                "Avaliable".to_owned(),
                                vec![EggExpr::Literal(arg)],
                            )],
                        });
                    }
                }
            }
        }
    }
    Ok(rules)
}

const ORIGIN_RELATION: &str = "Origin";
const SORT_INT: &str = "SortInt";
const SORT_REAL: &str = "SortReal";
const SORT_BOOL: &str = "SortBool";
const GOAL_LHS_NAME: &str = "goal_lhs";
const GOAL_RHS_NAME: &str = "goal_rhs";

fn set_goal(lhs_expr: EggExpr, rhs_expr: EggExpr) -> Vec<EggStatement> {
    vec![
        EggStatement::Let(GOAL_LHS_NAME.to_owned(), Box::new(lhs_expr)),
        EggStatement::Let(GOAL_RHS_NAME.to_owned(), Box::new(rhs_expr)),
        EggStatement::Premise(
            "Avaliable".to_owned(),
            Box::new(EggExpr::Literal(GOAL_LHS_NAME.to_owned())),
        ),
        EggStatement::Premise(
            "Avaliable".to_owned(),
            Box::new(EggExpr::Literal(GOAL_RHS_NAME.to_owned())),
        ),
    ]
}

fn available_subterm_premises(
    term: &Rc<Term>,
    func_cache: &mut EggFunctions,
    var_map: &mut HashMap<String, u64>,
) -> Result<Vec<EggStatement>, String> {
    let subs = IndexMap::new();
    let mut premises = Vec::new();
    for subterm in collect_subterms(term)
        .into_iter()
        .filter(|subterm| subterm != term && !subterm.is_var())
    {
        let expr = translate_term(
            &subterm,
            &subs,
            func_cache,
            var_map,
            false,
            "translating a goal subterm",
        )?;
        premises.push(EggStatement::Premise(
            "Avaliable".to_owned(),
            Box::new(expr),
        ));
    }
    Ok(premises)
}

/// `Origin` facts for a goal-side or premise term and every subterm of it,
/// variables included: the seeds of conditional rules' premise instances
/// under `seed_from_goal`.
fn origin_premises(
    term: &Rc<Term>,
    func_cache: &mut EggFunctions,
    var_map: &mut HashMap<String, u64>,
) -> Result<Vec<EggStatement>, String> {
    let subs = IndexMap::new();
    let mut premises = Vec::new();
    for subterm in collect_subterms(term) {
        let expr = translate_term(
            &subterm,
            &subs,
            func_cache,
            var_map,
            false,
            "translating a goal subterm",
        )?;
        premises.push(EggStatement::Premise(
            ORIGIN_RELATION.to_owned(),
            Box::new(expr),
        ));
    }
    Ok(premises)
}

/// The computational solvers step per iteration and are useless until they
/// finish — e.g. a nine-element distinct only unions its expansion after
/// ~50 iterations — so their rulesets run to fixpoint.  They terminate by
/// construction (structural recursion over finite seeded lists); only the
/// open-ended rewrite ruleset needs the per-round iteration budget.
fn goal_run_schedule(iterations: i16) -> Vec<EggStatement> {
    vec![
        EggStatement::Saturate {
            ruleset: Some("list-ruleset".to_owned()),
        },
        EggStatement::Saturate {
            ruleset: Some("evaluation".to_owned()),
        },
        EggStatement::Run { ruleset: None, iterations },
    ]
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

    let code = render_program(&program);

    (program, code)
}

fn render_program(program: &[Command]) -> String {
    program
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join("\n")
}

fn run_statements(egraph: &mut EGraph, ast: Vec<EggStatement>) -> (Result<(), String>, String) {
    let (program, code) = compile_program(ast);
    (run_program(egraph, program), code)
}

fn run_program(egraph: &mut EGraph, program: Vec<Command>) -> Result<(), String> {
    catch_unwind(AssertUnwindSafe(|| egraph.run_program(program)))
        .map_err(|panic| format!("egglog panic: {}", panic_message(panic)))
        .and_then(|result| result.map_err(|e| e.to_string()))
        .map(|_| ())
}

fn panic_message(panic: Box<dyn std::any::Any + Send>) -> String {
    if let Some(message) = panic.downcast_ref::<&str>() {
        (*message).to_owned()
    } else if let Some(message) = panic.downcast_ref::<String>() {
        message.clone()
    } else {
        "unknown panic payload".to_owned()
    }
}

fn equal_terms() -> (EggExpr, EggExpr) {
    (
        EggExpr::Literal(GOAL_LHS_NAME.to_owned()),
        EggExpr::Literal(GOAL_RHS_NAME.to_owned()),
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

/// Maximum single-iteration steps used to approach a ruleset's fixpoint while
/// a deadline is in force.  Generous enough that a ruleset which really does
/// saturate gets there, bounded so a diverging one cannot run forever.
const BOUNDED_SATURATION_STEPS: usize = 500;

/// Soft cap on the e-graph size reached while saturating under a deadline.
///
/// The budget bounds saturation and the certificate search, but the snapshot
/// taken between them is one uninterruptible serialization whose cost is
/// proportional to the e-graph.  Letting saturation spend its whole budget can
/// therefore build an e-graph that takes many times the budget merely to copy.
/// Stopping growth here keeps that last phase bounded too.  Only the deadline
/// path is capped; an untimed run saturates as before.
const MAX_SATURATION_TUPLES: usize = 4_000_000;

/// Runs one statement, observing `deadline`.
///
/// egglog executes a `(saturate ...)` to its fixpoint in a single call that
/// cannot be interrupted, so a saturation that blows up ignores the budget
/// entirely.  Under a deadline the fixpoint is therefore approached one
/// iteration at a time, with the budget checked between iterations and the
/// loop stopping as soon as the database stops growing (its fixpoint) or the
/// step bound is reached.  With no deadline the original single saturating
/// call is kept, so untimed runs behave exactly as before.
/// The caps a goal runs under: on the e-graph's tuples and on the process's
/// resident memory.
#[derive(Clone, Copy, Default)]
struct GrowthCaps {
    tuples: Option<usize>,
    memory_mb: Option<usize>,
}

/// The process's resident set in megabytes, from `/proc/self/statm`; `None`
/// where that is unavailable.
fn resident_mb() -> Option<usize> {
    let statm = std::fs::read_to_string("/proc/self/statm").ok()?;
    let pages: usize = statm.split_whitespace().nth(1)?.parse().ok()?;
    Some(pages.saturating_mul(4096) / (1024 * 1024))
}

/// Fails when the e-graph has grown past the tuple cap or the process past
/// the memory cap.
fn check_growth(egraph: &EGraph, caps: GrowthCaps, goal_label: &str) -> Result<(), String> {
    if let Some(cap) = caps.tuples
        && egraph.num_tuples() > cap
    {
        return Err(format!(
            "egglog check for {goal_label} stopped: the e-graph grew past the bound ({} tuples, cap {cap})",
            egraph.num_tuples()
        ));
    }
    if let Some(cap) = caps.memory_mb
        && let Some(resident) = resident_mb()
        && resident > cap
    {
        return Err(format!(
            "egglog check for {goal_label} stopped: the worker grew past the memory cap ({resident} MB resident, cap {cap} MB)"
        ));
    }
    Ok(())
}

fn run_statement_within_deadline(
    egraph: &mut EGraph,
    code_str: &mut String,
    statement: &EggStatement,
    deadline: Option<Instant>,
    caps: GrowthCaps,
    goal_label: &str,
) -> Result<(), String> {
    let EggStatement::Saturate { ruleset } = statement else {
        check_timeout(deadline, goal_label)?;
        run_and_record_statements(egraph, code_str, vec![statement.clone()])?;
        check_growth(egraph, caps, goal_label)?;
        return check_timeout(deadline, goal_label);
    };
    if deadline.is_none() && caps.tuples.is_none() && caps.memory_mb.is_none() {
        return run_and_record_statements(egraph, code_str, vec![statement.clone()]);
    }
    for _ in 0..BOUNDED_SATURATION_STEPS {
        check_timeout(deadline, goal_label)?;
        let before = egraph.num_tuples();
        run_and_record_statements(
            egraph,
            code_str,
            vec![EggStatement::Run {
                ruleset: ruleset.clone(),
                iterations: 1,
            }],
        )?;
        check_timeout(deadline, goal_label)?;
        check_growth(egraph, caps, goal_label)?;
        let after = egraph.num_tuples();
        if after == before || after > MAX_SATURATION_TUPLES {
            break;
        }
    }
    Ok(())
}

fn run_goal_schedule_round(
    egraph: &mut EGraph,
    code_str: &mut String,
    iterations: i16,
    deadline: Option<Instant>,
    tuple_cap: GrowthCaps,
    goal_label: &str,
) -> Result<(), String> {
    for statement in goal_run_schedule(1) {
        // Saturating statements reach their fixpoint in one execution (or, under
        // a deadline, in bounded steps); only the bounded default run is stepped
        // per iteration, keeping a timeout checkpoint between iterations.
        let repeats = if matches!(statement, EggStatement::Saturate { .. }) {
            1
        } else {
            iterations
        };
        for _ in 0..repeats {
            run_statement_within_deadline(
                egraph, code_str, &statement, deadline, tuple_cap, goal_label,
            )?;
        }
    }
    Ok(())
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
    deadline: Option<Instant>,
    tuple_cap: GrowthCaps,
    goal_label: &str,
) -> Result<(), String> {
    for statement in &fallback.guard_setup {
        run_statement_within_deadline(egraph, code_str, statement, deadline, tuple_cap, goal_label)?;
    }
    check_timeout(deadline, goal_label)?;
    run_and_record_check(
        egraph,
        code_str,
        fallback.guard.clone(),
        EggExpr::NativeBool(true),
    )?;
    for statement in &fallback.setup {
        run_statement_within_deadline(egraph, code_str, statement, deadline, tuple_cap, goal_label)?;
    }
    check_timeout(deadline, goal_label)?;
    let result = run_and_record_check(egraph, code_str, fallback.lhs.clone(), fallback.rhs.clone());
    check_timeout(deadline, goal_label)?;
    result
}

fn run_goal_fallback_attempts(
    egraph: &mut EGraph,
    code_str: &mut String,
    fallback_plans: &[GoalFallbackPlan],
    deadline: Option<Instant>,
    tuple_cap: GrowthCaps,
    goal_label: &str,
) -> Result<(), String> {
    let mut errors = Vec::with_capacity(fallback_plans.len());

    for fallback in fallback_plans {
        match run_goal_fallback_attempt(egraph, code_str, fallback, deadline, tuple_cap, goal_label)
        {
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
    deadline: Option<Instant>,
    tuple_cap: GrowthCaps,
    goal_label: &str,
) -> Result<(), String> {
    check_timeout(deadline, goal_label)?;
    match run_and_record_check(egraph, code_str, lhs_expr.clone(), rhs_expr.clone()) {
        Ok(()) => Ok(()),
        Err(raw_error) => {
            if fallback_plans.is_empty() {
                return Err(raw_error);
            }

            run_goal_fallback_attempts(
                egraph,
                code_str,
                fallback_plans,
                deadline,
                tuple_cap,
                goal_label,
            )
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
    deadline: Option<Instant>,
) -> Result<(), String> {
    let mut last_error = None;
    let base = egraph.num_tuples();
    let tuple_cap = growth_cap(runs_polynomial_normalizer(goal), options);

    let mut round = 0;
    loop {
        check_timeout(deadline, &goal.goal_label)?;
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
        run_goal_schedule_round(
            egraph,
            code_str,
            iterations,
            deadline,
            tuple_cap,
            &goal.goal_label,
        )?;
        check_timeout(deadline, &goal.goal_label)?;

        let check_result = check_goal_against_current_state(
            egraph,
            code_str,
            &goal.lhs_expr,
            &goal.rhs_expr,
            &goal.fallback_plans,
            deadline,
            tuple_cap,
            &goal.goal_label,
        );
        check_timeout(deadline, &goal.goal_label)?;

        match check_result {
            Ok(()) => {
                if tuple_cap.tuples.is_some() {
                    log::info!(
                        "growth: {} base {base} final {} rounds {round} reached",
                        goal_class(goal),
                        egraph.num_tuples()
                    );
                }
                return Ok(());
            }
            Err(error) => last_error = Some(error),
        }
    }
    if tuple_cap.tuples.is_some() {
        log::info!(
            "growth: {} base {base} final {} rounds {round} unreached",
            goal_class(goal),
            egraph.num_tuples()
        );
    }

    Err(format!(
        "egglog check for {} failed:\n{}",
        goal.goal_label,
        last_error.unwrap_or_else(|| "goal equality check failed".to_owned())
    ))
}

/// Whether a goal runs the polynomial normalizer, which is what the
/// arithmetic fallback plans stand for; such goals grow by construction.
/// The set-form fallback is not one of them and leaves the goal plain.
fn runs_polynomial_normalizer(goal: &GoalCheckTarget) -> bool {
    goal.fallback_plans
        .iter()
        .any(|plan| plan.label.starts_with("arith"))
}

fn goal_class(goal: &GoalCheckTarget) -> &'static str {
    if runs_polynomial_normalizer(goal) {
        "arith"
    } else {
        "plain"
    }
}

/// The caps of a goal, by whether it runs the polynomial normalizer.
fn growth_cap(arith: bool, options: RunEgglogOptions) -> GrowthCaps {
    let tuples = if arith {
        options.growth_cap_arith
    } else {
        options.growth_cap_plain
    };
    GrowthCaps {
        tuples: (tuples > 0).then_some(tuples),
        memory_mb: (options.memory_soft_cap_mb > 0).then_some(options.memory_soft_cap_mb),
    }
}

fn check_timeout(deadline: Option<Instant>, goal_label: &str) -> Result<(), String> {
    if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
        Err(format!("egglog check for {goal_label} timed out"))
    } else {
        Ok(())
    }
}

/// The guard premises of a RARE rule under `sort_guards`: one sort fact per
/// non-list parameter declared Int, Real or Bool that the left-hand side
/// binds, on the class the parameter stands for.
/// The most `:list` parameters a rule may have for its empty-list variants
/// to be generated: the count doubles the variants, and no rule of the
/// database has more than three.
const MAX_LIST_SLOTS: usize = 4;

/// Whether `expr` has an argument slot holding the bare variable `name`,
/// which is how a `:list` parameter is translated.
fn mentions_slot(expr: &EggExpr, name: &str) -> bool {
    match expr {
        EggExpr::Literal(literal) => literal == name,
        EggExpr::Mk(inner) | EggExpr::Ground(inner) => mentions_slot(inner, name),
        EggExpr::App(a, b)
        | EggExpr::Args(a, b)
        | EggExpr::Equal(a, b)
        | EggExpr::Distinct(a, b)
        | EggExpr::Union(a, b)
        | EggExpr::Set(a, b) => mentions_slot(a, name) || mentions_slot(b, name),
        EggExpr::Call(_, arguments) => arguments.iter().any(|a| mentions_slot(a, name)),
        _ => false,
    }
}

/// `expr` with the argument slots holding one of the `dropped` list
/// variables removed from their chains.  `None` when that would leave an
/// argument chain empty, which is not a term.
fn drop_list_slots(expr: &EggExpr, dropped: &[&str]) -> Option<EggExpr> {
    let is_dropped = |expr: &EggExpr| {
        matches!(expr, EggExpr::Literal(literal) if dropped.contains(&literal.as_str()))
    };
    Some(match expr {
        EggExpr::Args(head, tail) => {
            let tail = drop_list_slots(tail, dropped)?;
            if is_dropped(head) {
                tail
            } else {
                EggExpr::Args(Box::new(drop_list_slots(head, dropped)?), Box::new(tail))
            }
        }
        EggExpr::Mk(inner) => EggExpr::Mk(Box::new(drop_list_slots(inner, dropped)?)),
        EggExpr::Ground(inner) => EggExpr::Ground(Box::new(drop_list_slots(inner, dropped)?)),
        EggExpr::App(a, b) => EggExpr::App(
            Box::new(drop_list_slots(a, dropped)?),
            Box::new(drop_list_slots(b, dropped)?),
        ),
        EggExpr::Call(name, arguments) => {
            let rebuilt = arguments
                .iter()
                .map(|argument| drop_list_slots(argument, dropped))
                .collect::<Option<Vec<_>>>()?;
            // An operator whose whole argument list was dropped is not a
            // term, so that variant is not generated.
            for (before, after) in arguments.iter().zip(&rebuilt) {
                if matches!(after, EggExpr::Empty()) && !matches!(before, EggExpr::Empty()) {
                    return None;
                }
            }
            EggExpr::Call(name.clone(), rebuilt)
        }
        other => other.clone(),
    })
}

fn sort_guard_premises(
    definition: &RuleDefinition,
    lhs_vars: &IndexSet<String>,
) -> Vec<EggExpr> {
    definition
        .parameters
        .iter()
        .filter(|(name, parameter)| {
            parameter.attribute != AttributeParameters::List && lhs_vars.contains(*name)
        })
        .filter_map(|(name, parameter)| {
            let relation = sort_relation(&parameter.sort)?;
            Some(EggExpr::Call(
                relation.to_owned(),
                vec![EggExpr::Mk(Box::new(EggExpr::Literal(name.clone())))],
            ))
        })
        .collect()
}

fn sort_relation(sort: &Sort) -> Option<&'static str> {
    match sort {
        Sort::Int => Some(SORT_INT),
        Sort::Real => Some(SORT_REAL),
        Sort::Bool => Some(SORT_BOOL),
        _ => None,
    }
}

fn sort_rule(body: Vec<EggExpr>, relation: &str) -> EggStatement {
    EggStatement::Rule {
        ruleset: None,
        body,
        head: vec![EggExpr::Call(
            relation.to_owned(),
            vec![EggExpr::Literal("e".to_owned())],
        )],
    }
}

/// Sort facts for the constants the rewrites produce.
fn constant_sort_rules() -> Vec<EggStatement> {
    let e = || EggExpr::Literal("e".to_owned());
    let mk = |name: &str, args: Vec<&str>| {
        EggExpr::Mk(Box::new(EggExpr::Call(
            name.to_owned(),
            args.into_iter().map(|a| EggExpr::Literal(a.to_owned())).collect(),
        )))
    };
    vec![
        sort_rule(vec![EggExpr::Equal(Box::new(e()), Box::new(mk("Num", vec!["n"])))], SORT_INT),
        sort_rule(vec![EggExpr::Equal(Box::new(e()), Box::new(mk("Real", vec!["n", "d"])))], SORT_REAL),
        sort_rule(vec![EggExpr::Equal(Box::new(e()), Box::new(mk("RatConst", vec!["q"])))], SORT_REAL),
        sort_rule(vec![EggExpr::Equal(Box::new(e()), Box::new(mk("Bool", vec!["b"])))], SORT_BOOL),
    ]
}

/// The sort propagation rules of one declared function: the sort of an
/// application from its head (operators) or its declared result sort
/// (uninterpreted functions), the sort-preserving operators from their
/// first argument, `ite` from its branch.
fn function_sort_rules(name: &str, is_op: bool, result: Option<&Sort>) -> Vec<EggStatement> {
    let e = || EggExpr::Literal("e".to_owned());
    let lit = |s: &str| EggExpr::Literal(s.to_owned());
    let call = |args: EggExpr| EggExpr::Mk(Box::new(EggExpr::Call(format!("@{name}"), vec![args])));
    let whole = |relation: &str| {
        sort_rule(vec![EggExpr::Equal(Box::new(e()), Box::new(call(lit("args"))))], relation)
    };
    let from_first = |relation: &str| {
        sort_rule(
            vec![
                EggExpr::Equal(
                    Box::new(e()),
                    Box::new(call(EggExpr::Args(Box::new(lit("a")), Box::new(lit("rest"))))),
                ),
                EggExpr::Call(relation.to_owned(), vec![lit("a")]),
            ],
            relation,
        )
    };
    let from_branch = |relation: &str| {
        sort_rule(
            vec![
                EggExpr::Equal(
                    Box::new(e()),
                    Box::new(call(EggExpr::Args(
                        Box::new(lit("c")),
                        Box::new(EggExpr::Args(Box::new(lit("t")), Box::new(lit("rest")))),
                    ))),
                ),
                EggExpr::Call(relation.to_owned(), vec![lit("t")]),
            ],
            relation,
        )
    };
    if !is_op {
        return match result.and_then(sort_relation) {
            Some(relation) => vec![whole(relation)],
            None => Vec::new(),
        };
    }
    match name {
        "and" | "or" | "not" | "=>" | "xor" | "=" | "distinct" | "<" | "<=" | ">" | ">="
        | "is_int" => vec![whole(SORT_BOOL)],
        "/" | "to_real" => vec![whole(SORT_REAL)],
        "to_int" | "div" | "mod" => vec![whole(SORT_INT)],
        "+" | "-" | "*" | "abs" => vec![from_first(SORT_INT), from_first(SORT_REAL)],
        "ite" => vec![from_branch(SORT_INT), from_branch(SORT_REAL), from_branch(SORT_BOOL)],
        _ => Vec::new(),
    }
}

/// The sort relation of a term as far as the guards need it: Int, Real or
/// Bool, or `None` for any other sort.  Computed from the term itself, not
/// from a pool: a hole worker's pool holds only what it parsed.
fn guard_sort(term: &Rc<Term>) -> Option<&'static str> {
    match term.as_ref() {
        Term::Const(constant) => sort_relation(&constant.sort()),
        Term::Var(_, sort) => sort_relation(sort.as_ref()),
        Term::App(head, _) => application_result_sort(head)
            .as_ref()
            .and_then(sort_relation),
        Term::Op(operator, args) => match operator {
            Operator::True
            | Operator::False
            | Operator::Not
            | Operator::Implies
            | Operator::And
            | Operator::Or
            | Operator::Xor
            | Operator::Equals
            | Operator::Distinct
            | Operator::LessThan
            | Operator::GreaterThan
            | Operator::LessEq
            | Operator::GreaterEq
            | Operator::IsInt => Some(SORT_BOOL),
            Operator::ToReal | Operator::RealDiv => Some(SORT_REAL),
            Operator::ToInt | Operator::IntDiv | Operator::Mod => Some(SORT_INT),
            Operator::Add | Operator::Sub | Operator::Mult | Operator::Abs => {
                args.first().and_then(guard_sort)
            }
            Operator::Ite => args.get(1).and_then(guard_sort),
            _ => None,
        },
        Term::Binder(Binder::Forall | Binder::Exists, ..) => Some(SORT_BOOL),
        Term::Let(_, body) => guard_sort(body),
        _ => None,
    }
}

/// Sort facts for a goal-side or premise term and every subterm of it: the
/// seeds of `sort_guards`.
fn sort_premises(
    term: &Rc<Term>,
    func_cache: &mut EggFunctions,
    var_map: &mut HashMap<String, u64>,
) -> Result<Vec<EggStatement>, String> {
    let subs = IndexMap::new();
    let mut premises = Vec::new();
    for subterm in collect_subterms(term) {
        let Some(relation) = guard_sort(&subterm) else {
            continue;
        };
        let expr = translate_term(
            &subterm,
            &subs,
            func_cache,
            var_map,
            false,
            "translating a goal subterm",
        )?;
        premises.push(EggStatement::Premise(relation.to_owned(), Box::new(expr)));
    }
    Ok(premises)
}

fn declare_functions(functions: &EggFunctions, sort_guards: bool) -> Vec<EggStatement> {
    let mut decls = Vec::new();

    for (func, (is_op, _, result_sort)) in &functions.names {
        decls.push(EggStatement::Constructor(
            format!("@{}", func),
            vec![ConstType::ConstrType("Term".to_owned())],
            ConstType::ConstrType("Term".to_owned()),
        ));
        decls.push(EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Call(
                    format!("@{}", func),
                    vec![EggExpr::Literal("args".to_owned())],
                )],
            )],
            head: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Literal("args".to_owned())],
            )],
        });
        // After the constructor, which the rules mention.
        if sort_guards {
            decls.extend(function_sort_rules(func, *is_op, result_sort.as_ref()));
        }
    }

    // Note: @+ computation rule is now in arith_poly_norm.egglog

    decls
}

/// The ACI operators a goal actually mentions: the only ones whose set-form
/// conversion is worth declaring, and the only ones whose constructors the
/// generated program has.
fn present_aci_operators(functions: &EggFunctions) -> Vec<&'static str> {
    crate::rare::computational::aci_norm::aci_operators()
        .filter(|(_, name, _, _, _)| functions.names.contains_key(*name))
        .map(|(_, _, op_with_at, _, _)| op_with_at)
        .collect()
}

fn get_fallback_plans(
    enable_arith_poly: bool,
    aci_operators: &[&'static str],
) -> Vec<GoalFallbackPlan> {
    let (goal_lhs, goal_rhs) = equal_terms();
    get_fallback_plans_for(enable_arith_poly, aci_operators, goal_lhs, goal_rhs)
}

/// The fallback plans for a goal bound to the given names, so that several
/// goals can live in one e-graph.
fn get_fallback_plans_for(
    enable_arith_poly: bool,
    aci_operators: &[&'static str],
    goal_lhs: EggExpr,
    goal_rhs: EggExpr,
) -> Vec<GoalFallbackPlan> {
    let mut plans = Vec::new();
    if enable_arith_poly {
        plans.extend(vec![
        GoalFallbackPlan::new(
            "arithPolyNfOf",
            vec![
                EggStatement::Call(Box::new(EggExpr::Call(
                    "arithGoalPolyNfOf-demand".to_owned(),
                    vec![goal_lhs.clone()],
                ))),
                EggStatement::Run {
                    ruleset: Some("arith_poly_guard".to_owned()),
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
                    "arithRelBoolKeyOf-demand".to_owned(),
                    vec![goal_lhs.clone()],
                ))),
                EggStatement::Run {
                    ruleset: Some("arith_poly_guard".to_owned()),
                    iterations: 1,
                },
            ],
            arith_poly_norm_rel::relation_bool_goal_guard_term(goal_lhs.clone()),
            arith_poly_norm_rel::relation_bool_goal_check_terms(goal_lhs.clone(), goal_rhs.clone()),
        ),
        // Last resort: the relation keys of every relation atom, the atoms
        // with equal keys unioned, then one more round of the main rules over
        // the merged e-graph and the goal checked as it is.  Only a goal the
        // other checks failed pays for it.
        GoalFallbackPlan::new(
            "arithRelAll",
            Vec::new(),
            EggExpr::NativeBool(true),
            (
                {
                    let mut setup = arith_poly_norm_rel::relation_all_setup();
                    setup.extend(goal_run_schedule(1));
                    setup
                },
                goal_lhs.clone(),
                goal_rhs.clone(),
            ),
        ),
        ]);
    }
    // The set form of every `and`/`or` term, not only of the calls the step
    // spells out.  It is what lets a rule's `:list` parameters apply to a
    // term the rewriting derived, the empty lists included, and it replaces
    // the argument chain rather than adding to it, so it costs one node per
    // argument instead of one per bracketing.  It is a fallback because a
    // goal the ordinary rules prove needs none of it, and because the set
    // form of a class is one more shape the certificate search has to step
    // around.
    if !aci_operators.is_empty() {
        let mut setup = vec![EggStatement::Saturate {
            ruleset: Some("set-ruleset".to_owned()),
        }];
        setup.extend(goal_run_schedule(1));
        plans.push(GoalFallbackPlan::new(
            "aciSets",
            Vec::new(),
            EggExpr::NativeBool(true),
            (setup, goal_lhs.clone(), goal_rhs.clone()),
        ));
    }
    plans
}

fn goal_log_label(node: &Rc<ProofNode>, conclusion: &Rc<Term>) -> String {
    format!("{}: {:?}", node.id(), conclusion)
}

fn register_ineq_primitive(egraph: &mut EGraph) {
    egraph.add_primitive(CustomPrimitive {
        name: Symbol::from("ineq"),
        input: vec![
            Arc::new(EqSort { name: Symbol::from("Term") }),
            Arc::new(EqSort { name: Symbol::from("Term") }),
        ],
        output: Arc::new(BoolSort),
        f: |x| Some(Value::from(x[0] != x[1])),
    });
}

fn prepare_database(
    database: &Rules,
    seed_from_goal: bool,
    sort_guards: bool,
    list_encoding: ListEncoding,
) -> Result<RareDatabaseBaseline, String> {
    let mut functions = EggFunctions::default();
    let mut var_map = HashMap::new();
    let definitions: Vec<_> = database.rules.values().cloned().collect();
    let rules = construct_rules(
        &definitions,
        &mut functions,
        &mut var_map,
        seed_from_goal,
        sort_guards,
        list_encoding,
    )?;
    let has_distinct = functions.names.contains_key("distinct");

    // Logic operators and all database-derived rules belong to the immutable
    // baseline. Every proof step starts by cloning this fully initialized EGraph.
    declare_logic_operators(&mut functions);
    let mut declarations = declare_functions(&functions, sort_guards);
    declare_database_eliminations(&mut declarations, &functions, list_encoding);
    // The polynomial normalizer's rules are goal-independent, but preparing
    // them in the baseline was measured (2026-09-17) to cost every hole a
    // bigger baseline clone (~0.1 s) and to save the arithmetic holes
    // nothing: their cost is the normalizer's iterations, not its
    // declaration.  They stay per goal.

    let mut ast = create_headers();
    if sort_guards {
        ast.extend(constant_sort_rules());
    }
    ast.extend(declarations);
    ast.extend(rules);
    let (program, code) = compile_program(ast);
    let baseline_commands = program
        .iter()
        .filter(|command| should_deduplicate_command(command))
        .map(ToString::to_string)
        .collect();

    let mut egraph = EGraph::default();
    evaluation::register_evaluation_primitives(&mut egraph);
    register_ineq_primitive(&mut egraph);
    run_program(&mut egraph, program)?;

    Ok(RareDatabaseBaseline {
        egraph,
        functions,
        var_map,
        code,
        has_distinct,
        commands: baseline_commands,
    })
}

fn prepare_database_safely(
    database: &Rules,
    seed_from_goal: bool,
    sort_guards: bool,
    list_encoding: ListEncoding,
) -> Result<RareDatabaseBaseline, String> {
    catch_unwind(AssertUnwindSafe(|| {
        prepare_database(database, seed_from_goal, sort_guards, list_encoding)
    }))
    .map_err(|panic| {
        format!(
            "preparing the RARE database panicked: {}",
            panic_message(panic)
        )
    })?
}

fn run_egglog_with_premises_inner(
    pool: &mut dyn TermPool,
    conclusion: Rc<Term>,
    premise_clauses: &[&[Rc<Term>]],
    goal_label: String,
    context: &RareCtx<'_>,
    options: RunEgglogOptions,
) -> (Result<EGraph, String>, String) {
    let deadline = match options.timeout {
        Some(timeout) => match Instant::now().checked_add(timeout) {
            Some(deadline) => Some(deadline),
            None => {
                return (
                    Err(format!(
                        "egglog check for {goal_label} has an invalid timeout"
                    )),
                    String::new(),
                );
            }
        },
        None => None,
    };
    if let Err(error) = check_timeout(deadline, &goal_label) {
        return (Err(error), String::new());
    }

    let baseline = match context.baseline(
        options.seed_from_goal,
        options.sort_guards,
        options.list_encoding,
    ) {
        Ok(baseline) => baseline,
        Err(error) => return (Err(error), String::new()),
    };
    let mut code_str = baseline.code.clone();
    if let Err(error) = check_timeout(deadline, &goal_label) {
        return (Err(error), code_str);
    }

    let mut egraph = baseline.egraph.clone();
    let mut var_map = baseline.var_map.clone();

    // Functions coming from the premises and the goal are collected separately
    // from the ones coming from the RARE rule database, so that the arith poly
    // norm machinery is only enabled when the proof step itself involves
    // arithmetic, and not just because some rule in the database does.
    let mut goal_functions = EggFunctions::default();
    let premises =
        match construct_premises(pool, premise_clauses, &mut var_map, &mut goal_functions) {
            Ok(premises) => premises,
            Err(error) => return (Err(error), code_str),
        };

    let Some((Operator::Equals, lhs, rhs)) = get_equational_terms(&conclusion) else {
        return (
            Err(format!(
                "egglog check for {goal_label} requires a binary equality goal"
            )),
            code_str,
        );
    };

    let goal_lhs_expr = match translate_term(
        lhs,
        &IndexMap::new(),
        &mut goal_functions,
        &mut var_map,
        false,
        "translating the goal's left-hand side",
    ) {
        Ok(expr) => expr,
        Err(error) => return (Err(error), code_str),
    };
    let goal_rhs_expr = match translate_term(
        rhs,
        &IndexMap::new(),
        &mut goal_functions,
        &mut var_map,
        false,
        "translating the goal's right-hand side",
    ) {
        Ok(expr) => expr,
        Err(error) => return (Err(error), code_str),
    };

    let mut goals_ast = set_goal(goal_lhs_expr, goal_rhs_expr);
    let lhs_subterms = match available_subterm_premises(lhs, &mut goal_functions, &mut var_map) {
        Ok(premises) => premises,
        Err(error) => return (Err(error), code_str),
    };
    goals_ast.extend(lhs_subterms);
    let rhs_subterms = match available_subterm_premises(rhs, &mut goal_functions, &mut var_map) {
        Ok(premises) => premises,
        Err(error) => return (Err(error), code_str),
    };
    goals_ast.extend(rhs_subterms);
    if options.seed_from_goal {
        let mut origins = Vec::new();
        for term in [lhs, rhs] {
            match origin_premises(term, &mut goal_functions, &mut var_map) {
                Ok(premises) => origins.extend(premises),
                Err(error) => return (Err(error), code_str),
            }
        }
        for clause in premise_clauses {
            if let Some(clause) = clauses_to_or(pool, clause) {
                match origin_premises(&clause, &mut goal_functions, &mut var_map) {
                    Ok(premises) => origins.extend(premises),
                    Err(error) => return (Err(error), code_str),
                }
            }
        }
        goals_ast.extend(origins);
    }
    if options.sort_guards {
        let mut sorts = Vec::new();
        for term in [lhs, rhs] {
            match sort_premises(term, &mut goal_functions, &mut var_map) {
                Ok(premises) => sorts.extend(premises),
                Err(error) => return (Err(error), code_str),
            }
        }
        for clause in premise_clauses {
            if let Some(clause) = clauses_to_or(pool, clause) {
                match sort_premises(&clause, &mut goal_functions, &mut var_map) {
                    Ok(premises) => sorts.extend(premises),
                    Err(error) => return (Err(error), code_str),
                }
            }
        }
        goals_ast.extend(sorts);
    }

    let (raw_lhs, raw_rhs) = equal_terms();
    let mut goal = GoalCheckTarget {
        goal_label,
        lhs_expr: raw_lhs,
        rhs_expr: raw_rhs,
        fallback_plans: Vec::new(),
    };

    let enable_arith_poly = arith_poly_norm::uses_arith_machinery(&goal_functions);
    // The set-form fallback exists only under that encoding; with the chain
    // encoding there are no set forms to build, and the rules that would
    // read them were never compiled.
    let aci_operators = match options.list_encoding {
        ListEncoding::SetForm => present_aci_operators(&goal_functions),
        ListEncoding::Chain => Vec::new(),
    };
    goal.fallback_plans = get_fallback_plans(enable_arith_poly, &aci_operators);

    // Only constructors absent from the baseline need declaring in the clone.
    // Goal-specific rules still receive the complete local function/call set.
    let mut new_functions = goal_functions.clone();
    new_functions
        .names
        .retain(|name, _| !baseline.functions.names.contains_key(name));
    let mut declarations = declare_functions(&new_functions, options.sort_guards);
    declare_goal_eliminations(
        &mut declarations,
        &goal_functions,
        enable_arith_poly,
        baseline.has_distinct,
    );
    if enable_arith_poly {
        declarations.extend(arith_poly_norm::declare_opaque_arith_poly_rules(
            &goal_functions,
        ));
    }

    let mut ast = declarations;
    ast.extend(premises);
    ast.extend(goals_ast);

    let (mut egglog, _) = compile_program(ast);
    egglog.retain(|command| {
        !should_deduplicate_command(command) || !baseline.commands.contains(&command.to_string())
    });
    let local_code = render_program(&egglog);
    append_generated_code(&mut code_str, &local_code);
    if enable_arith_poly {
        arith_poly_norm::register_arith_poly_primitives(&mut egraph);
    }

    let result = check_timeout(deadline, &goal.goal_label)
        .and_then(|_| run_program(&mut egraph, egglog))
        .and_then(|_| check_timeout(deadline, &goal.goal_label))
        .and_then(|_| {
            check_goal_with_retry_rounds(&mut egraph, &mut code_str, &goal, options, deadline)
        });

    (result.map(|_| egraph), code_str)
}

fn run_egglog_with_premises(
    pool: &mut dyn TermPool,
    conclusion: Rc<Term>,
    premise_clauses: &[&[Rc<Term>]],
    goal_label: String,
    context: &RareCtx<'_>,
    options: RunEgglogOptions,
) -> (Result<EGraph, String>, String) {
    match catch_unwind(AssertUnwindSafe(|| {
        run_egglog_with_premises_inner(
            pool,
            conclusion,
            premise_clauses,
            goal_label,
            context,
            options,
        )
    })) {
        Ok(result) => result,
        Err(panic) => (
            Err(format!(
                "RARE/egglog checking panicked: {}",
                panic_message(panic)
            )),
            String::new(),
        ),
    }
}

/// One hole of a batch: a label for the log, the equality to prove, and the
/// premise clauses in scope for it.
pub struct BatchGoal {
    pub label: String,
    pub conclusion: Rc<Term>,
    pub premise_clauses: Vec<Vec<Rc<Term>>>,
}

/// Checks several holes in one e-graph: one baseline clone, one program, one
/// saturation, then every goal checked against the shared saturated state.
/// The result is one verdict per goal, in the order given.  The batch shares
/// its premises, so the caller must only batch holes whose premises agree
/// (in practice: holes under the same assumptions).  `options.timeout` is
/// the budget of the whole batch.
pub fn check_hole_rewrites_batched(
    pool: &mut dyn TermPool,
    goals: &[BatchGoal],
    context: &RareCtx<'_>,
    options: RunEgglogOptions,
) -> Vec<Result<(), String>> {
    match catch_unwind(AssertUnwindSafe(|| {
        check_hole_rewrites_batched_inner(pool, goals, context, options)
    })) {
        Ok(results) => results,
        Err(panic) => {
            let message = format!("RARE/egglog checking panicked: {}", panic_message(panic));
            goals.iter().map(|_| Err(message.clone())).collect()
        }
    }
}

fn check_hole_rewrites_batched_inner(
    pool: &mut dyn TermPool,
    goals: &[BatchGoal],
    context: &RareCtx<'_>,
    options: RunEgglogOptions,
) -> Vec<Result<(), String>> {
    let label = format!("batch of {} holes", goals.len());
    let mut results: Vec<Option<Result<(), String>>> = goals.iter().map(|_| None).collect();
    let fill = |results: &mut Vec<Option<Result<(), String>>>, error: String| {
        for slot in results.iter_mut() {
            if slot.is_none() {
                *slot = Some(Err(error.clone()));
            }
        }
    };
    let finish = |results: Vec<Option<Result<(), String>>>| -> Vec<Result<(), String>> {
        results
            .into_iter()
            .map(|slot| slot.unwrap_or_else(|| Err("batch: no verdict".to_owned())))
            .collect()
    };

    let deadline = match options.timeout {
        Some(timeout) => match Instant::now().checked_add(timeout) {
            Some(deadline) => Some(deadline),
            None => {
                fill(&mut results, format!("egglog check for {label} has an invalid timeout"));
                return finish(results);
            }
        },
        None => None,
    };
    let baseline = match context.baseline(
        options.seed_from_goal,
        options.sort_guards,
        options.list_encoding,
    ) {
        Ok(baseline) => baseline,
        Err(error) => {
            fill(&mut results, error);
            return finish(results);
        }
    };
    let mut code_str = baseline.code.clone();
    let mut egraph = baseline.egraph.clone();
    let mut var_map = baseline.var_map.clone();
    let mut goal_functions = EggFunctions::default();

    // Per goal: its premises, its two bound names, and its subterm
    // availability, all in the one program.
    let mut premises_ast = Vec::new();
    let mut goals_ast = Vec::new();
    let mut targets: Vec<Option<(EggExpr, EggExpr)>> = Vec::with_capacity(goals.len());
    for (index, goal) in goals.iter().enumerate() {
        let mut setup = || -> Result<(EggExpr, EggExpr), String> {
            let clauses: Vec<&[Rc<Term>]> =
                goal.premise_clauses.iter().map(Vec::as_slice).collect();
            premises_ast.extend(construct_premises(
                pool,
                &clauses,
                &mut var_map,
                &mut goal_functions,
            )?);
            let Some((Operator::Equals, lhs, rhs)) = get_equational_terms(&goal.conclusion)
            else {
                return Err(format!(
                    "egglog check for {} requires a binary equality goal",
                    goal.label
                ));
            };
            let lhs_expr = translate_term(
                lhs,
                &IndexMap::new(),
                &mut goal_functions,
                &mut var_map,
                false,
                "translating the goal's left-hand side",
            )?;
            let rhs_expr = translate_term(
                rhs,
                &IndexMap::new(),
                &mut goal_functions,
                &mut var_map,
                false,
                "translating the goal's right-hand side",
            )?;
            let lhs_name = format!("{GOAL_LHS_NAME}_{index}");
            let rhs_name = format!("{GOAL_RHS_NAME}_{index}");
            goals_ast.push(EggStatement::Let(lhs_name.clone(), Box::new(lhs_expr)));
            goals_ast.push(EggStatement::Let(rhs_name.clone(), Box::new(rhs_expr)));
            goals_ast.push(EggStatement::Premise(
                "Avaliable".to_owned(),
                Box::new(EggExpr::Literal(lhs_name.clone())),
            ));
            goals_ast.push(EggStatement::Premise(
                "Avaliable".to_owned(),
                Box::new(EggExpr::Literal(rhs_name.clone())),
            ));
            goals_ast.extend(available_subterm_premises(
                lhs,
                &mut goal_functions,
                &mut var_map,
            )?);
            goals_ast.extend(available_subterm_premises(
                rhs,
                &mut goal_functions,
                &mut var_map,
            )?);
            if options.seed_from_goal {
                for term in [lhs, rhs] {
                    goals_ast.extend(origin_premises(term, &mut goal_functions, &mut var_map)?);
                }
                for clause in &clauses {
                    if let Some(clause) = clauses_to_or(pool, clause) {
                        goals_ast.extend(origin_premises(
                            &clause,
                            &mut goal_functions,
                            &mut var_map,
                        )?);
                    }
                }
            }
            if options.sort_guards {
                for term in [lhs, rhs] {
                    goals_ast.extend(sort_premises(term, &mut goal_functions, &mut var_map)?);
                }
                for clause in &clauses {
                    if let Some(clause) = clauses_to_or(pool, clause) {
                        goals_ast.extend(sort_premises(
                            &clause,
                            &mut goal_functions,
                            &mut var_map,
                        )?);
                    }
                }
            }
            Ok((EggExpr::Literal(lhs_name), EggExpr::Literal(rhs_name)))
        };
        match setup() {
            Ok(target) => targets.push(Some(target)),
            Err(error) => {
                results[index] = Some(Err(error));
                targets.push(None);
            }
        }
    }

    let enable_arith_poly = arith_poly_norm::uses_arith_machinery(&goal_functions);
    let aci_operators = match options.list_encoding {
        ListEncoding::SetForm => present_aci_operators(&goal_functions),
        ListEncoding::Chain => Vec::new(),
    };
    let mut new_functions = goal_functions.clone();
    new_functions
        .names
        .retain(|name, _| !baseline.functions.names.contains_key(name));
    let mut declarations = declare_functions(&new_functions, options.sort_guards);
    declare_goal_eliminations(
        &mut declarations,
        &goal_functions,
        enable_arith_poly,
        baseline.has_distinct,
    );
    if enable_arith_poly {
        declarations.extend(arith_poly_norm::declare_opaque_arith_poly_rules(
            &goal_functions,
        ));
    }
    let mut ast = declarations;
    ast.extend(premises_ast);
    ast.extend(goals_ast);
    let (mut egglog, _) = compile_program(ast);
    egglog.retain(|command| {
        !should_deduplicate_command(command) || !baseline.commands.contains(&command.to_string())
    });
    let local_code = render_program(&egglog);
    append_generated_code(&mut code_str, &local_code);
    if enable_arith_poly {
        arith_poly_norm::register_arith_poly_primitives(&mut egraph);
    }
    if let Err(error) = check_timeout(deadline, &label).and_then(|_| run_program(&mut egraph, egglog))
    {
        fill(&mut results, error);
        return finish(results);
    }

    // The same rounds as a single goal, but every round checks all the goals
    // still open, and the batch stops as soon as none is.
    let tuple_cap = growth_cap(enable_arith_poly, options);
    let mut round = 0;
    loop {
        let pending: Vec<usize> = (0..goals.len())
            .filter(|&index| results[index].is_none())
            .collect();
        if pending.is_empty() {
            break;
        }
        if let Err(error) = check_timeout(deadline, &label) {
            fill(&mut results, error);
            break;
        }
        if !options.continuous_saturation && round >= options.normalized_max_goal_schedule_rounds()
        {
            fill(
                &mut results,
                format!("egglog check for {label} failed: goal not reached after {round} rounds"),
            );
            break;
        }
        round += 1;
        let iterations = if options.continuous_saturation {
            1
        } else {
            round as i16
        };
        if let Err(error) =
            run_goal_schedule_round(
                &mut egraph,
                &mut code_str,
                iterations,
                deadline,
                tuple_cap,
                &label,
            )
        {
            fill(&mut results, error);
            break;
        }
        for index in pending {
            let Some((lhs, rhs)) = targets[index].clone() else {
                continue;
            };
            let plans =
                get_fallback_plans_for(enable_arith_poly, &aci_operators, lhs.clone(), rhs.clone());
            match check_goal_against_current_state(
                &mut egraph,
                &mut code_str,
                &lhs,
                &rhs,
                &plans,
                deadline,
                tuple_cap,
                &goals[index].label,
            ) {
                Ok(()) => results[index] = Some(Ok(())),
                // Not yet: the next round may get there.  A timeout is caught
                // at the top of the loop.
                Err(_) => {}
            }
        }
    }
    finish(results)
}

pub fn check_hole_rewrite_with_context(
    pool: &mut dyn TermPool,
    step_id: &str,
    conclusion: Rc<Term>,
    premise_clauses: &[&[Rc<Term>]],
    context: &RareCtx<'_>,
    options: RunEgglogOptions,
) -> (Result<EGraph, String>, String) {
    let goal_label = format!("{}: {:?}", step_id, conclusion);
    run_egglog_with_premises(
        pool,
        conclusion,
        premise_clauses,
        goal_label,
        context,
        options,
    )
}

pub fn check_hole_rewrite(
    pool: &mut dyn TermPool,
    step_id: &str,
    conclusion: Rc<Term>,
    premise_clauses: &[&[Rc<Term>]],
    database: &Rules,
    options: RunEgglogOptions,
) -> (Result<EGraph, String>, String) {
    let context = RareCtx::new(database);
    check_hole_rewrite_with_context(
        pool,
        step_id,
        conclusion,
        premise_clauses,
        &context,
        options,
    )
}

pub fn run_egglog(
    pool: &mut dyn TermPool,
    node: (Rc<Term>, &Rc<ProofNode>),
    database: &Rules,
    options: RunEgglogOptions,
) -> (Result<EGraph, String>, String) {
    let (conclusion, proof_node) = node;
    let assumptions = proof_node.get_assumptions();
    let premise_clauses = assumptions
        .iter()
        .map(|premise| premise.clause())
        .collect::<Vec<_>>();
    let goal_label = goal_log_label(proof_node, &conclusion);
    let context = RareCtx::new(database);
    run_egglog_with_premises(
        pool,
        conclusion,
        &premise_clauses,
        goal_label,
        &context,
        options,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{pool::PrimitivePool, rare_rules::RareStatements};

    fn evaluation_goal(pool: &mut PrimitivePool) -> Rc<Term> {
        let truth = pool.add(Term::Op(Operator::True, vec![]));
        let falsity = pool.add(Term::Op(Operator::False, vec![]));
        let not_truth = pool.add(Term::Op(Operator::Not, vec![truth]));
        pool.add(Term::Op(Operator::Equals, vec![not_truth, falsity]))
    }

    #[test]
    fn rare_database_baseline_is_initialized_once_and_reused() {
        let mut pool = PrimitivePool::new();
        let goal = evaluation_goal(&mut pool);
        let database = RareStatements::default();
        let context = RareCtx::new(&database);
        assert!(!context.is_prepared());

        let (first, _) = check_hole_rewrite_with_context(
            &mut pool,
            "first",
            goal.clone(),
            &[],
            &context,
            RunEgglogOptions::default(),
        );
        assert!(first.is_ok(), "first check failed: {:?}", first.err());
        assert!(context.is_prepared());

        let baseline = context
            .baseline
            .get()
            .expect("baseline should have been initialized") as *const _;
        let (second, _) = check_hole_rewrite_with_context(
            &mut pool,
            "second",
            goal,
            &[],
            &context,
            RunEgglogOptions::default(),
        );
        assert!(second.is_ok(), "second check failed: {:?}", second.err());
        assert_eq!(
            baseline,
            context
                .baseline
                .get()
                .expect("baseline should remain initialized") as *const _
        );
    }

    /// A distinct with a repeated element is false.  Its expansion is the
    /// conjunction of the pairwise disequalities, one of which is `(not
    /// (= a a))`; the list re-association rewrites used to make the solver
    /// bind a sublist as an element and abort the whole run with an
    /// "Illegal merge" on `to_formula`.
    #[test]
    fn distinct_with_a_repeated_element_is_false() {
        let mut pool = PrimitivePool::new();
        let truth = pool.add(Term::Op(Operator::True, vec![]));
        let falsity = pool.add(Term::Op(Operator::False, vec![]));
        let distinct = pool.add(Term::Op(
            Operator::Distinct,
            vec![truth.clone(), falsity.clone(), truth],
        ));
        let goal = pool.add(Term::Op(Operator::Equals, vec![distinct, falsity]));
        let database = RareStatements::default();
        let context = RareCtx::new(&database);

        let (result, _) = check_hole_rewrite_with_context(
            &mut pool,
            "distinct",
            goal,
            &[],
            &context,
            RunEgglogOptions::default(),
        );
        assert!(result.is_ok(), "check failed: {:?}", result.err());
    }

    /// Mirrored inequalities inside a conjunction: `(<= 1 x)` and `(>= x 1)`
    /// have the same relation key but are different terms, and the goal-level
    /// relation check does not look inside the `and`; the all-relations
    /// fallback unions them, and the two conjunctions meet.
    #[test]
    fn mirrored_inequalities_meet_inside_a_conjunction() {
        let mut pool = PrimitivePool::new();
        let int = pool.add_sort(Sort::Int);
        let x = pool.add(Term::Var("x".to_owned(), int));
        let one = pool.add(Term::new_int(1));
        let le_x1 = pool.add(Term::Op(Operator::LessEq, vec![x.clone(), one.clone()]));
        let le_1x = pool.add(Term::Op(Operator::LessEq, vec![one.clone(), x.clone()]));
        let ge_x1 = pool.add(Term::Op(Operator::GreaterEq, vec![x, one]));
        let lhs = pool.add(Term::Op(Operator::And, vec![le_x1.clone(), le_1x]));
        let rhs = pool.add(Term::Op(Operator::And, vec![ge_x1, le_x1]));
        let goal = pool.add(Term::Op(Operator::Equals, vec![lhs, rhs]));
        let database = RareStatements::default();
        let context = RareCtx::new(&database);

        let (result, _) = check_hole_rewrite_with_context(
            &mut pool,
            "mirrored",
            goal,
            &[],
            &context,
            RunEgglogOptions::default(),
        );
        assert!(result.is_ok(), "check failed: {:?}", result.err());
    }

    /// A literal and its negation in an `and`/`or` make the connective's
    /// absorbing element, whatever the arity and the positions.  The RARE
    /// rules that state this (`bool-or-taut`, `bool-and-conf`) have `:list`
    /// parameters, and on the argument chain each would need one slot
    /// filled, so the two-element case would not match; compiled against the
    /// set form they carry no positions and match it.
    #[test]
    fn a_complementary_pair_absorbs_its_connective() {
        for (operator, absorbing) in [(Operator::Or, true), (Operator::And, false)] {
            let mut pool = PrimitivePool::new();
            let bool_sort = pool.add_sort(Sort::Bool);
            let p = pool.add(Term::Var("p".to_owned(), bool_sort));
            let not_p = pool.add(Term::Op(Operator::Not, vec![p.clone()]));
            let formula = pool.add(Term::Op(operator, vec![p, not_p]));
            let constant = pool.add(Term::new_bool(absorbing));
            let goal = pool.add(Term::Op(Operator::Equals, vec![formula, constant]));
            let database = complement_rules(&mut pool);
            let context = RareCtx::new(&database);

            let (result, _) = check_hole_rewrite_with_context(
                &mut pool,
                "complement",
                goal,
                &[],
                &context,
                RunEgglogOptions::default(),
            );
            assert!(result.is_ok(), "check failed: {:?}", result.err());
        }
    }

    /// The two complement rules, as the database states them.
    fn complement_rules(pool: &mut PrimitivePool) -> RareStatements {
        const RULES: &str = "
            (declare-rare-rule bool-or-taut ((xs Bool :list) (w Bool) (ys Bool :list) (zs Bool :list))
              :args (xs w ys zs)
              :conclusion (= (or xs w ys (not w) zs) true))
            (declare-rare-rule bool-and-conf ((xs Bool :list) (w Bool) (ys Bool :list) (zs Bool :list))
              :args (xs w ys zs)
              :conclusion (= (and xs w ys (not w) zs) false))
        ";
        let mut parser = crate::parser::Parser::new(
            pool,
            crate::parser::Config::new(),
            crate::parser::Source::new(std::path::Path::new("<rules>"), RULES),
        )
        .expect("the rules should open");
        parser.parse_rare().expect("the rules should parse")
    }

    /// A distinct without repeats is not false; the solver must say so
    /// instead of aborting once the argument lists are re-associated.
    #[test]
    fn distinct_without_repeats_is_reported_unproved() {
        let mut pool = PrimitivePool::new();
        let numbers: Vec<_> = (1..=3)
            .map(|i| pool.add(Term::Const(Constant::Integer(i.into()))))
            .collect();
        let falsity = pool.add(Term::Op(Operator::False, vec![]));
        let distinct = pool.add(Term::Op(Operator::Distinct, numbers));
        let goal = pool.add(Term::Op(Operator::Equals, vec![distinct, falsity]));
        let database = RareStatements::default();
        let context = RareCtx::new(&database);

        let (result, _) = check_hole_rewrite_with_context(
            &mut pool,
            "distinct",
            goal,
            &[],
            &context,
            RunEgglogOptions::default(),
        );
        let error = match result {
            Ok(_) => panic!("a distinct of three constants is not false"),
            Err(error) => error,
        };
        assert!(
            !error.contains("Illegal merge") && !error.contains("panic"),
            "the solver aborted instead of failing: {error}"
        );
    }

    #[test]
    fn malformed_programmatic_rare_rule_returns_an_error() {
        let mut pool = PrimitivePool::new();
        let truth = pool.add(Term::Op(Operator::True, vec![]));
        let goal = pool.add(Term::Op(
            Operator::Equals,
            vec![truth.clone(), truth.clone()],
        ));
        let malformed = RuleDefinition {
            name: "malformed".to_owned(),
            parameters: IndexMap::new(),
            arguments: vec![],
            premises: vec![],
            conclusion: truth,
            is_elaborated: false,
        };
        let database = RareStatements {
            rules: [(malformed.name.clone(), malformed)].into_iter().collect(),
        };
        let context = RareCtx::new(&database);

        let (result, _) = check_hole_rewrite_with_context(
            &mut pool,
            "malformed",
            goal,
            &[],
            &context,
            RunEgglogOptions::default(),
        );
        let error = match result {
            Ok(_) => panic!("malformed database must not be accepted"),
            Err(error) => error,
        };
        assert!(
            error.contains("binary equality"),
            "unexpected error: {error}"
        );
    }
}
