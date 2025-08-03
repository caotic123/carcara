use std::{vec};

use indexmap::IndexMap;

use crate::{
    ast::{
        rare_rules::{AttributeParameters, Program, RuleDefinition, TypeParameter},
        Operator, PrimitivePool, Rc, Term, TermPool,
    },
    rare::util::{collect_vars, unify_pattern},
};

#[derive(Debug)]
enum PatternLinkedConflict {
    Leaf(Vec<Rc<Term>>, Vec<usize>, Box<PatternLinkedConflict>),
    Empty,
}

fn create_decision_tree<'a>(
    pattern: Vec<Rc<Term>>,
    clause_index: usize,
    depth: usize,
    tree: Box<PatternLinkedConflict>,
) -> Box<PatternLinkedConflict> {
    fn can_unify(left: &Vec<Rc<Term>>, right: &Vec<Rc<Term>>) -> bool {
        for l in left.iter().zip(right) {
            if !unify_pattern(l.0, l.1) {
                return false;
            }
        }
        true
    }
    if depth == 0 {
        return tree;
    }
    match *tree {
        PatternLinkedConflict::Leaf(target, left, right) => {
            if can_unify(&target, &pattern) {
                let mut left = left;
                left.push(clause_index);
                return Box::new(PatternLinkedConflict::Leaf(
                    target,
                    left,
                    create_decision_tree(pattern, clause_index, depth - 1, right),
                ));
            } else {
                return Box::new(PatternLinkedConflict::Leaf(
                    target,
                    left,
                    create_decision_tree(pattern, clause_index, depth - 1, right),
                ));
            }
        }
        PatternLinkedConflict::Empty => Box::new(PatternLinkedConflict::Leaf(
            pattern,
            vec![clause_index],
            Box::new(PatternLinkedConflict::Empty),
        )),
    }
}

fn collect_conflict_clauses(
    pool: &mut PrimitivePool,
    tree: &PatternLinkedConflict,
    fixed_params: &Vec<(Rc<Term>, bool)>,
    clause: &Vec<Rc<Term>>,
    clause_index: usize,
) -> Vec<Rc<Term>> {
    fn collect_conflicts(
        pool: &mut PrimitivePool,
        fixed_params: &Vec<(Rc<Term>, bool)>,
        left: &Vec<Rc<Term>>,
        right: &Vec<Rc<Term>>,
    ) -> Vec<Rc<Term>> {
        let mut conflicts = vec![];
        for (index, l) in left.iter().zip(right).enumerate() {
            if l.0 != l.1 && !l.0.is_var() {
                let term = pool.add(Term::Var(
                    format! {"_{}", index},
                    fixed_params[index].0.clone(),
                ));
                conflicts.push(pool.add(Term::Op(Operator::Distinct, vec![term, l.0.clone()])));
            }
        }
        conflicts
    }

    match tree {
        PatternLinkedConflict::Leaf(target, left, right) => {
            let mut conflicts =
                collect_conflict_clauses(pool, right, fixed_params, clause, clause_index);

            if left.contains(&clause_index) {
                println!("{:?} {:?}", &target, &clause);
                conflicts.extend(collect_conflicts(pool, fixed_params, &target, clause));
            }

            conflicts
        }

        PatternLinkedConflict::Empty => vec![],
    }
}

fn create_matching_clauses<'a>(
    clause: &Rc<Term>,
    fixed_params: &'a mut Vec<(Rc<Term>, bool)>,
    parameters: &IndexMap<String, TypeParameter>,
) -> (Vec<Rc<Term>>, &'a mut Vec<(Rc<Term>, bool)>) {
    let mut matching_parameters = vec![];
    let Term::App(_, args) = clause.as_ref() else {
        panic!("Expected an application term, found: {:?}", clause);
    };

    for (index, arg) in args.iter().enumerate() {
        for var in collect_vars(arg) {
            fixed_params[index].1 = (parameters[&var.0].attribute == AttributeParameters::List)
                || fixed_params[index].1;
        }

        matching_parameters.push(arg.clone());
    }

    (matching_parameters, fixed_params)
}

fn transform_to_rare_params<'a>(
    pool: &mut PrimitivePool,
    terms: Vec<Rc<Term>>,
    fixed_params: &Vec<(Rc<Term>, bool)>,
) -> Vec<Rc<Term>> {
    let mut vec = vec![];
    for (index, rhs) in terms.into_iter().enumerate() {
        let term = pool.add(Term::Var(
            format! {"_{}", index},
            fixed_params[index].0.clone(),
        ));
        let equality: Rc<Term> = pool.add(Term::Op(Operator::Equals, vec![term, rhs]));
        vec.push(equality);
    }
    vec
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
            create_matching_clauses(&pattern.0, &mut symbol_table, &program.parameters);
        let lhs = compile_conclusion(pool, &pattern.0, &symbol_table);

        rules.push((
            vars.into_iter()
                .map(|v| v.0)
                .chain((0..program.signature.len() - 1).map(|x| format!("_{}", x)))
                .filter(|x| x != &program.name)
                .collect::<Vec<_>>(),
            matching_clause.clone(),
            pool.add(Term::Op(Operator::Equals, vec![lhs, pattern.1.clone()])),
        ));

        if !rejected_clauses.contains(&matching_clause) {
            rejected_clauses.push(matching_clause);
        }
    }

    let mut set = Box::new(PatternLinkedConflict::Empty);
    for clause in rejected_clauses.into_iter().enumerate() {
        set = create_decision_tree(clause.1, clause.0, clause.0 + 1, set);
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
        let (vars, matching_clauses, conclusion) = rule;

        let conflicts =
            collect_conflict_clauses(pool, &set, &symbol_table, &matching_clauses, index);
        let mut premises = transform_to_rare_params(pool, matching_clauses, &symbol_table);
        premises.extend(conflicts);
        compiled_rules.push(RuleDefinition {
            name: format!("{}_{}", program.name.clone(), index),
            parameters: parameters
                .clone()
                .into_iter()
                .filter(|p| vars.contains(&p.0))
                .collect(),
            arguments: vars.clone(),
            premises: premises,
            conclusion: conclusion.clone(),
        });
    }

    compiled_rules
}
