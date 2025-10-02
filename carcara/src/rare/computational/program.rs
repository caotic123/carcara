use std::vec;

use indexmap::IndexMap;

use crate::{
    ast::{
        rare_rules::{AttributeParameters, Program, RuleDefinition, TypeParameter},
        Operator, PrimitivePool, Rc, Sort, Substitution, Term, TermPool,
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
            if l.0 != l.1 && (!l.0.is_var() || (l.0.is_var() && l.1.is_var())) {
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
        for var in collect_vars(arg, false) {
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

// Eunoia list in pattern matching has a akward behavior, where when a parameter is a list, whenever we mention it
// we need to create a representation such (or x xs) = [xs/(or xs)].
fn handle_eo_lists<'a>(
    pool: &mut PrimitivePool,
    terms: &Vec<Rc<Term>>,
    parameters: &IndexMap<String, TypeParameter>,
) -> Substitution {
    use std::collections::HashSet;

    // Helper: is this a list-attribute parameter var that isn't shadowed?
    fn is_list_param(
        t: &Rc<Term>,
        parameters: &IndexMap<String, TypeParameter>,
        shadowed: &HashSet<String>,
    ) -> bool {
        if let Some(name) = t.as_var() {
            if !shadowed.contains(name) {
                if let Some(p) = parameters.get(name) {
                    return p.attribute == AttributeParameters::List;
                }
            }
        }
        false
    }

    // Traverse Sorts (they can contain Terms in some cases)
    fn visit_sort(
        pool: &mut PrimitivePool,
        s: &Sort,
        parameters: &IndexMap<String, TypeParameter>,
        mapping: &mut IndexMap<Rc<Term>, Rc<Term>>,
        shadowed: &HashSet<String>,
    ) {
        match s {
            Sort::Function(ts) | Sort::Atom(_, ts) => {
                for t in ts {
                    visit(pool, t, parameters, mapping, shadowed);
                }
            }
            Sort::Array(a, b) => {
                visit(pool, a, parameters, mapping, shadowed);
                visit(pool, b, parameters, mapping, shadowed);
            }
            Sort::ParamSort(ts, inner) => {
                for t in ts {
                    visit(pool, t, parameters, mapping, shadowed);
                }
                visit(pool, inner, parameters, mapping, shadowed);
            }
            // Primitive / leaf sorts and sort variables: nothing to do
            Sort::BitVec(_)
            | Sort::Bool
            | Sort::Int
            | Sort::Real
            | Sort::String
            | Sort::RegLan
            | Sort::RareList
            | Sort::Type
            | Sort::Var(_) => {}
        }
    }

    fn visit(
        pool: &mut PrimitivePool,
        t: &Rc<Term>,
        parameters: &IndexMap<String, TypeParameter>,
        mapping: &mut IndexMap<Rc<Term>, Rc<Term>>,
        shadowed: &HashSet<String>,
    ) {
        match &**t {
            Term::Const(_) => {}

            Term::Var(_, _) => {}

            Term::Sort(s) => {
                visit_sort(pool, s, parameters, mapping, shadowed);
            }

            Term::Op(op, args) => {
                for arg in args {
                    if is_list_param(arg, parameters, shadowed) && !mapping.contains_key(arg) {
                        let unary = pool.add(Term::Op(*op, vec![arg.clone()]));
                        mapping.insert(arg.clone(), unary);
                    }
                    visit(pool, arg, parameters, mapping, shadowed);
                }
            }

            Term::App(head, args) => {
                visit(pool, head, parameters, mapping, shadowed);

                for arg in args {
                    if is_list_param(arg, parameters, shadowed) && !mapping.contains_key(arg) {
                        let unary = pool.add(Term::App(head.clone(), vec![arg.clone()]));
                        mapping.insert(arg.clone(), unary);
                    }
                    visit(pool, arg, parameters, mapping, shadowed);
                }
            }

            Term::ParamOp { op, op_args, args } => {
                // Operator parameters can be terms (e.g., qualified sorts); recurse
                for oa in op_args {
                    visit(pool, oa, parameters, mapping, shadowed);
                }

                for arg in args {
                    if is_list_param(arg, parameters, shadowed) && !mapping.contains_key(arg) {
                        let unary = pool.add(Term::ParamOp {
                            op: *op,
                            op_args: op_args.clone(),
                            args: vec![arg.clone()],
                        });
                        mapping.insert(arg.clone(), unary);
                    }
                    visit(pool, arg, parameters, mapping, shadowed);
                }
            }

            Term::Binder(_, bindings, inner) => {
                // Visit sorts of bound vars with current scope
                for (_, sort) in bindings.0.iter() {
                    visit(pool, sort, parameters, mapping, shadowed);
                }

                // Shadow bound names for the inner term
                let mut next_shadow = shadowed.clone();
                for (name, _) in bindings.0.iter() {
                    next_shadow.insert(name.clone());
                }
                visit(pool, inner, parameters, mapping, &next_shadow);
            }

            Term::Let(bindings, body) => {
                // In let, values are evaluated in the *current* scope
                for (_, val) in bindings.0.iter() {
                    visit(pool, val, parameters, mapping, shadowed);
                }

                // Bound names are shadowed in the body
                let mut next_shadow = shadowed.clone();
                for (name, _) in bindings.0.iter() {
                    next_shadow.insert(name.clone());
                }
                visit(pool, body, parameters, mapping, &next_shadow);
            }
        }
    }

    let mut mapping: IndexMap<Rc<Term>, Rc<Term>> = IndexMap::new();
    let shadowed = HashSet::new();

    for t in terms {
        visit(pool, t, parameters, &mut mapping, &shadowed);
    }

    Substitution::new(pool, mapping).unwrap()
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
        let mut vars = collect_vars(&pattern.0, false);
        vars.append(&mut collect_vars(&pattern.1, false));
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
            (lhs, pattern.1.clone()),
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
        let (vars, matching_clauses, (lhs, rhs)) = rule;

        let conflicts =
            collect_conflict_clauses(pool, &set, &symbol_table, &matching_clauses, index);

        let rhs = handle_eo_lists(pool, &matching_clauses, &program.parameters).apply(pool, &rhs);
        let conclusion = pool.add(Term::Op(Operator::Equals, vec![lhs, rhs]));

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
            is_elaborated: true,
        });
    }

    compiled_rules
}
