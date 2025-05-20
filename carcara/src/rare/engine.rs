use crate::{
    ast::{
        rules::Rules,
        PrimitivePool, ProofNode, Rc, Term,
    },
    rare::util::collect_vars,
};
use indexmap::{IndexMap, IndexSet};

use egg::*;

use super::{
    language::*,
    meta::*,
    util::clauses_to_or,
};

fn construct_egg_rules_database(rules: &Rules) -> Vec<Rewrite<Rare, ()>> {
    let mut top = RecExpr::default();
    top.add(ENodeOrVar::ENode(Rare::Symbol("⊤".to_string())));

    let mut db = vec![
        rewrite!("func-dependency"; "(=> ?v (~ ?x ?y))" => "(=> (Mk ?v) (~ ?x ?y))"),
        rewrite!("func-reduction1"; "(=> ⊤ (~ ?x ?y))" => "⊤"),
//        rewrite!("func-reduction2"; "(-> (-> ⊤ (~ ?a ?b)) (~ ?c ?d))" => "(-> (~ ?a ?b) (~ ?c ?d))"),

        // Some axioms to state that we have booleans freely
        rewrite!("true-ground"; "any" => "(Inhabitant Free (Op true) (Sort Bool))"),
        rewrite!("true-type"; "(Ground (Op true))" => "(Inhabitant Ground (Op true) (Sort Bool))"),
        rewrite!("false-ground"; "any" => "(Inhabitant Free (Op false) (Sort Bool))"),
        rewrite!("false-type"; "(Ground (Op false))" => "(Inhabitant Ground (Op false) (Sort Bool))"),
        
        //Works but need to be fixed (using Ground between arguments) (also add named rules in the first arg)
        rewrite!("add-inst"; "(Ground (App (Op +) ?x2 ?y2)))"
            => "(Inhabitant Ground (App (Op +) ?x2 ?y2) (Sort Int))"),
        rewrite!("add-any"; "any" => "(Inhabitant Free (App (Op +) any any) (Sort Int))"),

        rewrite!("eq-inst"; "(Ground (~ ?x2 ?y2)))"
            => "(Inhabitant Ground (~ ?x2 ?y2) (Sort Bool))"),
        rewrite!("eq-any"; "any" => "(Inhabitant Free (~ any any) (Sort Bool))"),

        rewrite!("or-inst"; "(Ground (App (Op or) ?x2 ?y2)))"
            => "(Inhabitant Ground (App (Op or) ?x2 ?y2) (Sort Bool))"),
        rewrite!("or-any"; "any" => "(Inhabitant Free (App (Op or) any any) (Sort Bool))"),

        rewrite!("not-inst"; "(Ground (App (Op not) ?x2)))"
            => "(Inhabitant Ground (App (Op not) ?x2) (Sort Bool))"),
        rewrite!("not-any"; "any" => "(Inhabitant Free (App (Op not) any) (Sort Bool))"),

        rewrite!("any"; "(Ground 1)" => "(Inhabitant Ground 1 (Sort Int))"),
        rewrite!("any"; "any" => "(Inhabitant Free 1 (Sort Int))"),

        //rewrite!("ground-unfold"; "(Ground ⊤)" => "⊤"),
        //rewrite!("ground-unfold2"; "⊤" => "(Ground ⊤)"),

       // rewrite!("add-inst"; "(Ground (App (Op not) ?x)))" => "(Ground (App (Op not) (Ground ?x))"),

    ];

    for (name, definition) in rules {
        let goal_vars: IndexMap<String, Rc<Term>> = collect_vars(&definition.conclusion);
        let premises_vars: IndexMap<String, Rc<Term>> = definition
            .premises
            .iter()
            .map(|x| collect_vars(x))
            .flatten()
            .collect();

        let instantion_vars = premises_vars
            .iter()
            .chain(goal_vars.iter())
            .collect::<IndexMap<&String, &Rc<Term>>>();

        // Goal instation rule
        db.push(
            Rewrite::new(
                format!("{0}-goal-inst", name),
                Pattern::new(
                    make_mk_term(
                        &mut RecExpr::default(),
                        &definition.conclusion,
                        &definition.parameters,
                    )
                    .1
                    .clone(),
                ),
                Pattern::new(
                    make_instantion(
                        format!("{0}-rule", name),
                        &mut RecExpr::default(),
                        instantion_vars
                            .iter()
                            .map(|(name, _)| {
                                if goal_vars.contains_key(*name) {
                                    return InstationKind::Var((*name).clone());
                                }

                                return InstationKind::Any;
                            })
                            .collect(),
                    )
                    .1
                    .clone(),
                ),
            )
            .unwrap(),
        );

        // Apply Rare Rewrite Rule

        db.push(
            Rewrite::new(
                format!("{0}-rule-apply", name),
                Pattern::new(
                    make_typed_instantion(
                        format!("{0}-rule", name),
                        &mut RecExpr::default(),
                        instantion_vars
                            .iter()
                            .map(|(x, y)| {
                                (
                                    *x,
                                    *y,
                                    if goal_vars.contains_key(*x) {
                                        InhabitantKind::Ground
                                    } else {
                                        InhabitantKind::Free
                                    },
                                )
                            })
                            .collect(),
                        &definition.parameters,
                    )
                    .1
                    .clone(),
                ),
                Pattern::new(
                    make_arrow(
                        &mut RecExpr::default(),
                        definition.premises.iter().collect(),
                        &definition.conclusion,
                        &definition.parameters,
                    )
                    .1
                    .clone(),
                ),
            )
            .unwrap(),
        );
    }

    return db;
}

fn construct_premises(
    pool: &mut PrimitivePool,
    premises: &Rc<ProofNode>,
) -> Vec<Rewrite<Rare, ()>> {
    let mut memoize_vars = IndexSet::new();
    let mut context = vec![];
    for premise in premises.get_assumptions() {
        let clause = clauses_to_or(pool, premise.clause());
        if let Some(clause) = clause {
            // "x" => "Top"
            // "(Ground x)" => "(Inhabitant ? x)"
            let premises_variables = collect_vars(&clause);

            // let's capture variable from premises and assert that they are top, we have to capture its type also

            for (name, sort) in premises_variables {
                if memoize_vars.contains(&name) {
                    continue;
                }

                context.push(
                    Rewrite::new(
                        format!("{0}-any", name),
                        Pattern::new(make_any(&mut RecExpr::default()).1.clone()),
                        Pattern::new(
                            make_inhabitant(
                                &mut RecExpr::default(),
                                &name,
                                sort.clone(),
                                InhabitantKind::Free,
                            )
                            .1
                            .clone(),
                        ),
                    )
                    .unwrap(),
                );

                context.push(
                    Rewrite::new(
                        format!("{0}-type", name.clone()),
                        Pattern::new(make_static_ground(&name, &mut RecExpr::default()).1.clone())
                            .clone(),
                        Pattern::new(
                            make_inhabitant(
                                &mut RecExpr::default(),
                                &name,
                                sort,
                                InhabitantKind::Ground,
                            )
                            .1
                            .clone(),
                        ),
                    )
                    .unwrap(),
                );

                memoize_vars.insert(name);
            }

            // This rule says that steps rules are top
            let ground_term = Rewrite::new(
                format!("{0}-premise-ground", premise.id()),
                Pattern::new(
                    make_term(&mut RecExpr::default(), &clause, &IndexMap::default())
                        .1
                        .clone(),
                ),
                Pattern::new(make_top(&mut RecExpr::default()).1.clone()),
            );

            context.push(ground_term.unwrap());
        }
    }
    return context;
}

pub fn reconstruct_rule(
    pool: &mut PrimitivePool,
    conclusion: Rc<Term>,
    root: &Rc<ProofNode>,
    database: &Rules,
) {
    let mut root_expr = RecExpr::default();
    let (goal, _) = convert_to_egg_expr::<&mut RecExpr<Rare>>(&mut root_expr, &conclusion);
    root_expr.add(Rare::Mk(goal));

    let mut premises: Vec<Rewrite<Rare, ()>> = construct_premises(pool, root);

    let mut runner: Runner<Rare, (), ()> = Runner::new(())
        .with_explanations_enabled()
        .with_expr(&root_expr);
    let egg_rules = construct_egg_rules_database(database);

    premises.extend(egg_rules);
    runner = runner.run(&premises);
    println!("{:?}", premises);
    print!("\n\n\n\n");

    // the Runner knows which e-class the expression given with `with_expr` is in
    let root = runner.roots[0];

    let extractor = Extractor::new(&runner.egraph, AstDepth);
    let (best_cost, best) = extractor.find_best(root);
    println!(
        "Simplified {} to {} explain {} with cost {}",
        root_expr,
        best,
        runner.explain_equivalence(&root_expr, &best),
        best_cost
    );
}
