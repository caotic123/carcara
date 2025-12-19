use crate::{
    egg_expr,
    rare::{
        engine::EggFunctions,
        language::{ConstType, EggExpr, EggStatement},
    },
};

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

    // Rule 1: base case for to_formula
    stmts.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_string()),
        body: vec![egg_expr!(("to_formula_rel" () "k" ()))],
        head: vec![egg_expr!((set ("to_formula" () "k" ()) ()))],
    });

    // Rule 2: decompose result into (r . rs)
    stmts.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_string()),
        body: vec![
            egg_expr!((= "res" (args "r" "rs"))),
            egg_expr!(("to_formula_rel" "res" "y" ())),
        ],
        head: vec![egg_expr!(("to_formula_rel" "rs" "r" "rs"))],
    });

    // Rule 3: decompose xs into (x . rxs)
    stmts.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_string()),
        body: vec![
            egg_expr!((= "xs" (args "x" "rxs"))),
            egg_expr!(("to_formula_rel" "res" "y" "xs")),
        ],
        head: vec![egg_expr!(("to_formula_rel" "res" "y" "rxs"))],
    });

    // Rule 4: build formula with (not (= y x))
    let args_x_rxs = egg_expr!((args "x" "rxs"));
    let eq_inner = egg_expr!((mk (_eq (args "y" (args "x" ())))));
    let not_term = egg_expr!((mk (_not (args {eq_inner.clone()} ()))));
    let set_rhs = egg_expr!((args {not_term.clone()} "f"));
    stmts.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_string()),
        body: vec![
            egg_expr!(("to_formula_rel" "res" "y" {args_x_rxs.clone()})),
            egg_expr!((= ("to_formula" "res" "y" "rxs") "f")),
        ],
        head: vec![egg_expr!((set ("to_formula" "res" "y" {args_x_rxs}) {set_rhs}))],
    });

    // Rule 5: handle (r . res) case
    let args_r_res = egg_expr!((args "r" "res"));
    stmts.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_string()),
        body: vec![
            egg_expr!(("to_formula_rel" {args_r_res.clone()} "y" ())),
            egg_expr!((= ("to_formula" "res" "r" "res") "f")),
        ],
        head: vec![egg_expr!((set ("to_formula" {args_r_res} "y" ()) "f"))],
    });

    // Rule 6: distinct elimination - union with and
    let distinct_term = egg_expr!((mk (_distinct (args "x" "xs"))));
    stmts.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_string()),
        body: vec![
            egg_expr!(("Avaliable" {distinct_term.clone()})),
            egg_expr!((= ("to_formula" "xs" "x" "xs") "f")),
        ],
        head: vec![egg_expr!((union (mk (_and (args "f" ()))) {distinct_term.clone()}))],
    });

    // Rule 7: trigger to_formula_rel from distinct availability
    let distinct_term = egg_expr!((mk (_distinct (args "x" "xs"))));
    stmts.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_string()),
        body: vec![egg_expr!(("Avaliable" {distinct_term.clone()}))],
        head: vec![egg_expr!(("to_formula_rel" "xs" "x" "xs"))],
    });

    stmts
}

pub fn declare_logic_operators(functions: &mut EggFunctions) {
    let functions_needed = vec!["not", "and", "or", "="];
    for func in functions_needed {
        functions.names.entry(func.to_string()).or_insert((true, 1));
    }
}
