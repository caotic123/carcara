use crate::rare::language::*;
use egglog::{ast::*, span, EGraph};

type EggLanguage = Vec<EggStatement>;

#[inline]
fn dummy_span() -> Span {
    span!()
}

fn ct_to_sort(ct: &ConstType) -> Symbol {
    match ct {
        ConstType::Var => Symbol::from("i64"),
        ConstType::Bool => Symbol::from("bool"),
        ConstType::Integer => Symbol::from("i64"),
        ConstType::Operator => Symbol::from("String"),
        ConstType::ConstrType(s) => Symbol::from(s.as_str()),
    }
}

fn ctor_to_variant(c: Constructor) -> Variant {
    let (name, fields) = c.constr;
    Variant {
        span: dummy_span(),
        name: Symbol::from(name.as_str()),
        types: fields.iter().map(ct_to_sort).collect(),
        cost: None,
    }
}

fn to_expr(e: EggExpr) -> Expr {
    use EggExpr::*;
    match e {
        Var(v) => Expr::Call(
            dummy_span(),
            Symbol::from("Var"),
            vec![Expr::Lit(
                dummy_span(),
                egglog::ast::Literal::Int(v as i64),
            )],
        ),

        Bool(b) => Expr::Call(
            dummy_span(),
            Symbol::from("Bool"),
            vec![Expr::Lit(dummy_span(), egglog::ast::Literal::Bool(b))],
        ),

        Num(i) => Expr::Call(
            dummy_span(),
            Symbol::from("Num"),
            vec![Expr::Lit(
                dummy_span(),
                egglog::ast::Literal::Int(i.to_i64_wrapping()),
            )],
        ),
        String(s) => Expr::Call(
            dummy_span(),
            Symbol::from("@String"),
            vec![Expr::Lit(
                dummy_span(),
                egglog::ast::Literal::String(s.into()),
            )],
        ),

        Real(r) => Expr::Call(
            dummy_span(),
            Symbol::from("Real"),
            vec![Expr::Lit(
                dummy_span(),
                egglog::ast::Literal::Int(r.0.to_i64_wrapping()),
            ), Expr::Lit(
                dummy_span(),
                egglog::ast::Literal::Int(r.1.to_i64_wrapping()),
            )],
        ),

        BitVec(w, v) => Expr::Call(
            dummy_span(),
            Symbol::from("Bitvec"),
            vec![
                Expr::Lit(dummy_span(), egglog::ast::Literal::Int(w.to_i64_wrapping())),
                Expr::Lit(dummy_span(), egglog::ast::Literal::Int(v.to_i64_wrapping())),
            ],
        ),
        Op(op) => Expr::Call(
            dummy_span(),
            Symbol::from("Op"),
            vec![Expr::Lit(
                dummy_span(),
                egglog::ast::Literal::String(op.into()),
            )],
        ),
        Const(op) => Expr::Call(
            dummy_span(),
            Symbol::from("Const"),
            vec![Expr::Lit(
                dummy_span(),
                egglog::ast::Literal::String(op.into()),
            )],
        ),
        Literal(s) => Expr::Var(dummy_span(), Symbol::from(s.as_str())),
        Ground(e1) => Expr::Call(dummy_span(), Symbol::from("Ground"), vec![to_expr(*e1)]),
        App(f, x) => Expr::Call(
            dummy_span(),
            Symbol::from("App"),
            vec![to_expr(*f), to_expr(*x)],
        ),
        Call(name, args) => Expr::Call(
            dummy_span(),
            Symbol::from(name),
            args.into_iter().map(|x| to_expr(x)).collect(),
        ),
        Args(x, xs) => Expr::Call(
            dummy_span(),
            Symbol::from("Args"),
            vec![to_expr(*x), to_expr(*xs)],
        ),
        Mk(term) => Expr::Call(dummy_span(), Symbol::from("Mk"), vec![to_expr(*term)]),
        Equal(l, r) => Expr::Call(
            dummy_span(),
            Symbol::from("="),
            vec![to_expr(*l), to_expr(*r)],
        ),
        Distinct(l, r) => Expr::Call(
            dummy_span(),
            Symbol::from("="),
            vec![
                Expr::Call(
                    dummy_span(),
                    Symbol::from("ineq"),
                    vec![to_expr(*l), to_expr(*r)],
                ),
                Expr::Lit(dummy_span(), egglog::ast::Literal::Bool(true)),
            ],
        ),
        Union(l, r) => Expr::Call(
            dummy_span(),
            Symbol::from("union"),
            vec![to_expr(*l), to_expr(*r)],
        ),
        Empty() => Expr::Call(dummy_span(), Symbol::from("Empty"), vec![]),
        Set(_, _) => panic!("Set expressions should only be used in rule actions"),
    }
}

fn eggexpr_to_fact(e: EggExpr) -> Fact {
    match e {
        EggExpr::Equal(l, r) => Fact::Eq(
            dummy_span(),
            to_expr(*l), // normal expression conversion
            to_expr(*r),
        ),
        EggExpr::Distinct(l, r) => Fact::Eq(
            dummy_span(),
            Expr::Call(
                dummy_span(),
                Symbol::from("ineq"),
                vec![to_expr(*l), to_expr(*r)],
            ),
            Expr::Lit(dummy_span(), egglog::ast::Literal::Bool(true)),
        ),
        other => Fact::Fact(to_expr(other)),
    }
}

fn facts(es: Vec<EggExpr>) -> Vec<Fact> {
    es.into_iter().map(eggexpr_to_fact).collect()
}

fn eggexpr_to_action(e: EggExpr) -> Action {
    match e {
        EggExpr::Set(lhs, rhs) => match *lhs {
            EggExpr::Call(name, args) => Action::Set(
                dummy_span(),
                Symbol::from(name.as_str()),
                args.into_iter().map(to_expr).collect(),
                to_expr(*rhs),
            ),
            other => panic!("Expected function call in set action, got {:?}", other),
        },
        EggExpr::Union(l, r) => Action::Union(dummy_span(), to_expr(*l), to_expr(*r)),
        other => Action::Expr(dummy_span(), to_expr(other)),
    }
}

fn acts(v: Vec<EggExpr>) -> Vec<Action> {
    v.into_iter().map(eggexpr_to_action).collect()
}

pub fn lower_egg_language(lang: EggLanguage) -> Vec<Command> {
    lang.into_iter()
        .flat_map(|stmt| {
            match stmt {
                EggStatement::Constructor(name, inputs, out) => vec![Command::Constructor {
                    span: dummy_span(),
                    name: Symbol::from(name.as_str()),
                    schema: Schema {
                        input: inputs.iter().map(|x| ct_to_sort(x)).collect(),
                        output: ct_to_sort(&out),
                    },
                    cost: None,
                    unextractable: false,
                }],

                /* ------------ datatype ------------- */
                EggStatement::DataType(name, ctors) => vec![Command::Datatype {
                    span: dummy_span(),
                    name: Symbol::from(name.as_str()),
                    variants: ctors.into_iter().map(ctor_to_variant).collect(),
                }],

                EggStatement::Sort(name, sort_symbol, expr) => vec![Command::Sort(
                    dummy_span(),
                    Symbol::from(name.as_str()),
                    Some((Symbol::from(sort_symbol.as_str()), vec![to_expr(*expr)])),
                )],

                /* ------------ relation ------------- */
                EggStatement::Relation(con, ctypes) => vec![Command::Relation {
                    span: dummy_span(),
                    name: Symbol::from(con.as_str()),
                    inputs: ctypes.iter().map(ct_to_sort).collect(),
                }],

                EggStatement::Function { name, inputs, output, merge } => {
                    vec![Command::Function {
                        span: dummy_span(),
                        name: Symbol::from(name.as_str()),
                        schema: Schema::new(
                            inputs.iter().map(ct_to_sort).collect(),
                            ct_to_sort(&output),
                        ),
                        merge: merge.map(to_expr),
                    }]
                }

                EggStatement::Ruleset(name) => {
                    vec![Command::AddRuleset(Symbol::from(name.as_str()))]
                }

                /* ------------ premise -------------- */
                EggStatement::Premise(rel, arg) => vec![Command::Action(Action::Expr(
                    dummy_span(),
                    Expr::Call(
                        dummy_span(),
                        Symbol::from(rel.as_str()),
                        vec![to_expr(*arg)],
                    ),
                ))],

                /* ------------ rewrite -------------- */
                EggStatement::Rewrite(lhs, rhs, conds) => vec![Command::Rewrite(
                    Symbol::from(""), // ruleset
                    Rewrite {
                        span: dummy_span(),
                        lhs: to_expr(*lhs),
                        rhs: to_expr(*rhs),
                        conditions: facts(conds),
                    },
                    false, /* subsume = false */
                )],

                /* -------------- rule --------------- */
                EggStatement::Rule { ruleset, body, head } => vec![Command::Rule {
                    ruleset: Symbol::from(ruleset.as_deref().unwrap_or("")),
                    name: Symbol::from(""),
                    rule: Rule {
                        span: dummy_span(),
                        body: facts(body),
                        head: GenericActions(acts(head)),
                    },
                }],

                /* -------------- check -------------- */
                EggStatement::Check(e) => {
                    vec![Command::Check(dummy_span(), facts(vec![*e]))]
                }

                /* --------------- run --------------- */
                EggStatement::Run { ruleset, iterations } => {
                    let rcfg = RunConfig {
                        ruleset: Symbol::from(ruleset.as_deref().unwrap_or("")),
                        until: None,
                    };
                    let sched = Schedule::Repeat(
                        dummy_span(),
                        iterations as usize,
                        Box::new(Schedule::Run(dummy_span(), rcfg)),
                    );
                    vec![Command::RunSchedule(sched)]
                }
                EggStatement::Saturate { ruleset } => {
                    let rcfg = RunConfig {
                        ruleset: Symbol::from(ruleset.as_deref().unwrap_or("")),
                        until: None,
                    };
                    let sched = Schedule::Saturate(
                        dummy_span(),
                        Box::new(Schedule::Run(dummy_span(), rcfg)),
                    );
                    vec![Command::RunSchedule(sched)]
                }
                EggStatement::Let(name, expr) => vec![Command::Action(GenericAction::Let(
                    dummy_span(),
                    Symbol::from(name),
                    to_expr(*expr),
                ))],
                EggStatement::Call(expr) => vec![Command::Action(GenericAction::Expr(
                    dummy_span(),
                    to_expr(*expr),
                ))],
                EggStatement::Union(expr, expr2) => vec![Command::Action(GenericAction::Union(
                    dummy_span(),
                    to_expr(*expr),
                    to_expr(*expr2),
                ))],

                EggStatement::Raw(code) => {
                    // Parse raw egglog code into commands
                    let mut egraph = EGraph::default();
                    match egraph.parser.get_program_from_string(None, &code) {
                        Ok(commands) => {
                            // Filter out datatype and constructor declarations
                            // (already declared in main program by create_headers and arith_constructors)
                            commands.into_iter().filter(|cmd| {
                                !matches!(cmd, Command::Datatype { .. } | Command::Constructor { .. })
                            }).collect()
                        },
                        Err(e) => {
                            eprintln!("Error parsing raw egglog code: {}", e);
                            vec![]
                        }
                    }
                }
            }
        })
        .collect()
}
