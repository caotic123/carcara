use crate::{
    egg_expr,
    rare::{
        engine::EggFunctions,
        language::{ConstType, EggStatement},
    },
};

pub fn distinct_solver_statements() -> Vec<EggStatement> {
    let term = ConstType::ConstrType("Term".to_owned());
    let mut stmts = vec![
        EggStatement::Function {
            name: "to_formula".to_owned(),
            inputs: vec![term.clone(), term.clone(), term.clone()],
            output: term.clone(),
            merge: None,
        },
        EggStatement::Relation(
            "to_formula_rel".to_owned(),
            vec![term.clone(), term.clone(), term.clone()],
        ),
        // The conjunct lists the solver builds, and those among them that
        // hold `false` (rules 8-10).
        EggStatement::Relation("distinct_conjuncts".to_owned(), vec![term.clone()]),
        EggStatement::Relation("distinct_conjuncts_false".to_owned(), vec![term]),
    ];

    // The list re-association rewrites of the base program (`(Args (Args
    // t1 t2) t3)` <-> `(Args t1 (Args t2 t3))`, the encoding behind RARE's
    // list-segment variables) put nodes whose "head" is an improper sublist
    // into every argument list's class.  Every element position below is
    // therefore matched as `(Mk _)`, the shape of a translated term: without
    // the guard the decomposition rules also bind a sublist as an element,
    // set a second, different value for the same `to_formula` key and
    // egglog aborts the run ("Illegal merge attempted for function
    // to_formula") -- which killed every distinct with three or more
    // elements not proved in the first round.

    // Rule 1: base case for to_formula
    stmts.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_owned()),
        body: vec![egg_expr!(("to_formula_rel" () "k" ()))],
        head: vec![egg_expr!((set ("to_formula" () "k" ()) ()))],
    });

    // Rule 2: decompose result into (r . rs)
    stmts.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_owned()),
        body: vec![
            egg_expr!((= "res" (args (mk "r") "rs"))),
            egg_expr!(("to_formula_rel" "res" "y" ())),
        ],
        head: vec![egg_expr!(("to_formula_rel" "rs" (mk "r") "rs"))],
    });

    // Rule 3: decompose xs into (x . rxs)
    stmts.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_owned()),
        body: vec![
            egg_expr!((= "xs" (args (mk "x") "rxs"))),
            egg_expr!(("to_formula_rel" "res" "y" "xs")),
        ],
        head: vec![egg_expr!(("to_formula_rel" "res" "y" "rxs"))],
    });

    // Rule 4: build formula with (not (= y x))
    let args_x_rxs = egg_expr!((args (mk "x") "rxs"));
    let eq_inner = egg_expr!((mk (_eq (args "y" (args (mk "x") ())))));
    let not_term = egg_expr!((mk (_not (args {eq_inner.clone()} ()))));
    let set_rhs = egg_expr!((args {not_term.clone()} "f"));
    stmts.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_owned()),
        body: vec![
            egg_expr!(("to_formula_rel" "res" "y" {args_x_rxs.clone()})),
            egg_expr!((= ("to_formula" "res" "y" "rxs") "f")),
        ],
        head: vec![
            egg_expr!((set ("to_formula" "res" "y" {args_x_rxs}) {set_rhs.clone()})),
            egg_expr!(("distinct_conjuncts" {set_rhs})),
        ],
    });

    // Rule 5: handle (r . res) case
    let args_r_res = egg_expr!((args (mk "r") "res"));
    stmts.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_owned()),
        body: vec![
            egg_expr!(("to_formula_rel" {args_r_res.clone()} "y" ())),
            egg_expr!((= ("to_formula" "res" (mk "r") "res") "f")),
        ],
        head: vec![egg_expr!((set ("to_formula" {args_r_res} "y" ()) "f"))],
    });

    // Rule 6: distinct elimination - union with and
    let distinct_term = egg_expr!((mk (_distinct (args (mk "x") "xs"))));
    stmts.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_owned()),
        body: vec![
            egg_expr!(("Avaliable" {distinct_term.clone()})),
            egg_expr!((= ("to_formula" "xs" (mk "x") "xs") "f")),
        ],
        // `f` is already the `Args` list of conjuncts built by `to_formula`,
        // so it is passed to `@and` directly -- wrapping it in another list
        // cell would nest a list inside a list and never meet the
        // well-formed `(and ...)` the rest of the system builds.
        head: vec![egg_expr!((union (mk (_and "f")) {distinct_term.clone()}))],
    });

    // Rule 7: trigger to_formula_rel from distinct availability
    let distinct_term = egg_expr!((mk (_distinct (args (mk "x") "xs"))));
    stmts.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_owned()),
        body: vec![egg_expr!(("Avaliable" {distinct_term.clone()}))],
        head: vec![egg_expr!(("to_formula_rel" "xs" (mk "x") "xs"))],
    });

    // Rules 8-10: a conjunction with a false conjunct is false.  A distinct
    // with a repeated element expands to a list holding `(not (= a a))`,
    // which the rewrite rules turn into false, but the list form of `and`
    // only reaches the ACI set form (and its absorbing-element rule) for the
    // calls of the proof step, not for a list built here.  The walk is
    // restricted to the solver's own lists so it costs nothing elsewhere.
    stmts.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_owned()),
        body: vec![
            egg_expr!(("distinct_conjuncts" "l")),
            egg_expr!((= "l" (args (mk false) "rest"))),
        ],
        head: vec![egg_expr!(("distinct_conjuncts_false" "l"))],
    });
    stmts.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_owned()),
        body: vec![
            egg_expr!(("distinct_conjuncts" "l")),
            egg_expr!((= "l" (args (mk "x") "rest"))),
            egg_expr!(("distinct_conjuncts_false" "rest")),
        ],
        head: vec![egg_expr!(("distinct_conjuncts_false" "l"))],
    });
    stmts.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_owned()),
        body: vec![
            egg_expr!((= "result" (mk (_and "l")))),
            egg_expr!(("distinct_conjuncts_false" "l")),
        ],
        head: vec![egg_expr!((union "result" (mk false)))],
    });

    stmts
}

pub fn declare_logic_operators(functions: &mut EggFunctions) {
    let functions_needed = vec!["not", "and", "or", "="];
    for func in functions_needed {
        functions
            .names
            .entry(func.to_owned())
            .or_insert((true, 1, None));
    }
}
