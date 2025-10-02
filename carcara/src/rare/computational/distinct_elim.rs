use crate::{
    args_chain, call_expr, empty_expr, literal_expr, mk_expr,
    rare::{
        engine::EggFunctions,
        language::{ConstType, EggExpr, EggStatement},
    },
};

fn set_action(call: EggExpr, value: EggExpr) -> EggExpr {
    EggExpr::Set(Box::new(call), Box::new(value))
}

pub fn distinct_solver_statements() -> Vec<EggStatement> {
    let term = ConstType::ConstrType("Term".to_string());
    let mut stmts = vec![
        EggStatement::Function {
            name: "to_formula".to_string(),
            inputs: vec![term.clone(), term.clone(), term.clone()],
            output: term.clone(),
            merge: None,
        },
        EggStatement::Relation(
            "to_formula_rel".to_string(),
            vec![term.clone(), term.clone(), term],
        ),
    ];

    stmts.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_string()),
        body: vec![call_expr!(
            "to_formula_rel";
            empty_expr!(),
            literal_expr!("k"),
            empty_expr!()
        )],
        head: vec![set_action(
            call_expr!("to_formula"; empty_expr!(), literal_expr!("k"), empty_expr!()),
            empty_expr!(),
        )],
    });

    stmts.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_string()),
        body: vec![
            EggExpr::Equal(
                Box::new(literal_expr!("res")),
                Box::new(args_chain!(literal_expr!("r"); literal_expr!("rs"))),
            ),
            call_expr!(
                "to_formula_rel";
                literal_expr!("res"),
                literal_expr!("y"),
                empty_expr!()
            ),
        ],
        head: vec![call_expr!(
            "to_formula_rel";
            literal_expr!("rs"),
            literal_expr!("r"),
            literal_expr!("rs")
        )],
    });

    stmts.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_string()),
        body: vec![
            EggExpr::Equal(
                Box::new(literal_expr!("xs")),
                Box::new(args_chain!(literal_expr!("x"); literal_expr!("rxs"))),
            ),
            call_expr!(
                "to_formula_rel";
                literal_expr!("res"),
                literal_expr!("y"),
                literal_expr!("xs")
            ),
        ],
        head: vec![call_expr!(
            "to_formula_rel";
            literal_expr!("res"),
            literal_expr!("y"),
            literal_expr!("rxs")
        )],
    });

    let args_x_rxs = args_chain!(literal_expr!("x"); literal_expr!("rxs"));
    let eq_inner = mk_expr!(call_expr!(
        "@=";
        args_chain!(literal_expr!("y"), literal_expr!("x"); empty_expr!())
    ));
    let not_term = mk_expr!(call_expr!(
        "@not";
        args_chain!(eq_inner.clone(); empty_expr!())
    ));
    let set_rhs = args_chain!(not_term.clone(); literal_expr!("f"));
    stmts.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_string()),
        body: vec![
            call_expr!(
                "to_formula_rel";
                literal_expr!("res"),
                literal_expr!("y"),
                args_x_rxs.clone()
            ),
            EggExpr::Equal(
                Box::new(call_expr!(
                    "to_formula";
                    literal_expr!("res"),
                    literal_expr!("y"),
                    literal_expr!("rxs")
                )),
                Box::new(literal_expr!("f")),
            ),
        ],
        head: vec![set_action(
            call_expr!(
                "to_formula";
                literal_expr!("res"),
                literal_expr!("y"),
                args_x_rxs
            ),
            set_rhs,
        )],
    });

    let args_r_res = args_chain!(literal_expr!("r"); literal_expr!("res"));
    stmts.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_string()),
        body: vec![
            call_expr!(
                "to_formula_rel";
                args_r_res.clone(),
                literal_expr!("y"),
                empty_expr!()
            ),
            EggExpr::Equal(
                Box::new(call_expr!(
                    "to_formula";
                    literal_expr!("res"),
                    literal_expr!("r"),
                    literal_expr!("res")
                )),
                Box::new(literal_expr!("f")),
            ),
        ],
        head: vec![set_action(
            call_expr!(
                "to_formula";
                args_r_res,
                literal_expr!("y"),
                empty_expr!()
            ),
            literal_expr!("f"),
        )],
    });

    let distinct_term = mk_expr!(call_expr!(
        "@distinct";
        args_chain!(literal_expr!("x"); literal_expr!("xs"))
    ));
    stmts.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_string()),
        body: vec![
            call_expr!("Avaliable"; distinct_term.clone()),
            EggExpr::Equal(
                Box::new(call_expr!(
                    "to_formula";
                    literal_expr!("xs"),
                    literal_expr!("x"),
                    literal_expr!("xs")
                )),
                Box::new(literal_expr!("f")),
            ),
        ],
        head: vec![EggExpr::Union(
            Box::new(mk_expr!(call_expr!("@and"; literal_expr!("f")))),
            Box::new(distinct_term.clone()),
        )],
    });

    let distinct_term = mk_expr!(call_expr!(
        "@distinct";
        args_chain!(literal_expr!("x"); literal_expr!("xs"))
    ));
    stmts.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_string()),
        body: vec![call_expr!("Avaliable"; distinct_term.clone())],
        head: vec![call_expr!(
            "to_formula_rel";
            literal_expr!("xs"),
            literal_expr!("x"),
            literal_expr!("xs")
        )],
    });

    stmts
}

pub fn declare_logic_operators(functions: &mut EggFunctions) {
    let functions_needed = vec!["not", "and", "or", "="];
    for func in functions_needed {
        functions.names.entry(func.to_string()).or_insert((true, 1));
    }
}
