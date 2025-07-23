use std::fmt::format;

use indexmap::IndexMap;

use crate::{
    ast::{
        rare_rules::{AttributeParameters, Program, RuleDefinition, TypeParameter},
        Operator, PrimitivePool, Rc, Term, TermPool,
    },
    rare::util::{collect_vars, create_set_of_disambiguation, unify_pattern},
};

enum DecisionTree {
    Leaf(Rc<Term>, Box<DecisionTree>, Box<DecisionTree>),
    Empty,
}

fn create_decision_tree(patterns: Vec<Vec<Rc<Term>>) -> DecisionTree {
    let pattern = patterns.pop();
    match pattern {
        Some(pattern) => {
            let tree: DecisionTree = create_decision_tree(patterns);
            match tree {
                DecisionTree::Leaf(target, left, right) => {
                    for term in pattern {
                        if !unify_pattern(term, target) {
                            return DecisionTree::Leaf(
                                Box::new(DecisionTree::Node(origin, target)),
                                Box::new(tree),
                            );
                        }
                    }
                }
            }
        }
        None => DecisionTree::Empty,
    }
}

fn create_matching_clauses<'a>(
    pool: &mut PrimitivePool,
    clause: &Rc<Term>,
    fixed_params: &'a mut Vec<(Rc<Term>, bool)>,
    parameters: &IndexMap<String, TypeParameter>,
) -> (Vec<Rc<Term>>, &'a mut Vec<(Rc<Term>, bool)>) {
    let mut matching_parameters = vec![];
    let Term::App(_, args) = clause.as_ref() else {
        panic!("Expected an application term, found: {:?}", clause);
    };

    for (index, arg) in args.iter().enumerate() {
        let term = pool.add(Term::Var(
            format! {"_{}", index},
            fixed_params[index].0.clone(),
        ));
        let equality = pool.add(Term::Op(Operator::Equals, vec![term, arg.clone()]));

        for var in collect_vars(arg) {
            fixed_params[index].1 = (parameters[&var.0].attribute == AttributeParameters::List)
                || fixed_params[index].1;
        }

        matching_parameters.push(equality);
    }

    (matching_parameters, fixed_params)
}

fn compile_conclusion(
    pool: &mut PrimitivePool,
    clause: &Rc<Term>,
    fixed_params: &Vec<(Rc<Term>, bool)>,
) -> Rc<Term> {
    let Term::App(head, _) = clause.as_ref() else {
        panic!("Expected an application term, found: {:?}", clause);
    };

    let app = Term::App(
        head.clone(),
        fixed_params
            .iter()
            .enumerate()
            .map(|(index, (sort, _))| pool.add(Term::Var(format! {"_{}", index}, sort.clone())))
            .collect(),
    );

    pool.add(app)
}

pub fn compile_program(pool: &mut PrimitivePool, program: &Program) -> Vec<RuleDefinition> {
    let mut rules = vec![];
    let mut keys: Vec<String> = vec![];
    let mut symbol_table = vec![];
    let mut rejected_clauses: Vec<Vec<Rc<Term>>> = vec![];

    for (level, sort) in program
        .signature
        .iter()
        .take(program.signature.len() - 1)
        .enumerate()
    {
        let level_name = format!("_{}", level);
        keys.push(level_name.clone());
        symbol_table.push((sort.clone(), false));
    }

    for pattern in program.patterns.iter() {
        let mut vars = collect_vars(&pattern.0);
        vars.append(&mut collect_vars(&pattern.1));
        let (matching_clause, _) =
            create_matching_clauses(pool, &pattern.0, &mut symbol_table, &program.parameters);
        let lhs = compile_conclusion(pool, &pattern.0, &symbol_table);

        rules.push((
            vars.into_iter()
                .map(|v| v.0)
                .chain((0..program.signature.len() - 1).map(|x| format!("_{}", x)))
                .filter(|x| x != &program.name)
                .collect::<Vec<_>>(),
            rejected_clauses.clone(),
            matching_clause.clone(),
            pool.add(Term::Op(Operator::Equals, vec![lhs, pattern.1.clone()])),
        ));

        if !rejected_clauses.contains(&matching_clause) {
            rejected_clauses.push(matching_clause);
        }
    }

    let mut compiled_rules = vec![];
    let mut parameters = symbol_table
        .iter()
        .enumerate()
        .map(|(index, (sort, is_list))| {
            (
                format!("_{}", index),
                TypeParameter {
                    term: sort.clone(),
                    attribute: if *is_list {
                        AttributeParameters::List
                    } else {
                        AttributeParameters::None
                    },
                },
            )
        })
        .collect::<IndexMap<_, _>>();

    parameters.extend(program.parameters.clone());

    for (index, rule) in rules.into_iter().enumerate() {
        let (vars, rejected_clauses, premises, conclusion) = rule;
        let desambig_set =
            create_set_of_disambiguation(premises.as_slice(), rejected_clauses.as_slice());
        if desambig_set.is_empty() {
            compiled_rules.push(RuleDefinition {
                name: format!("{}_{}", program.name.clone(), index),
                parameters: parameters.clone(),
                arguments: vars.clone(),
                premises: premises,
                conclusion: conclusion.clone(),
            });
            continue;
        }

        for mut desambig_set in desambig_set {
            desambig_set.extend(premises.clone());
            compiled_rules.push(RuleDefinition {
                name: format!("{}_{}", program.name.clone(), index),
                parameters: parameters.clone(),
                arguments: vars.clone(),
                premises: desambig_set,
                conclusion: conclusion.clone(),
            });
        }
    }

    compiled_rules
}
