use std::collections::{HashMap, hash_map::DefaultHasher};
use std::hash::{Hash, Hasher};

use indexmap::{IndexMap, IndexSet};

use crate::ast::{Operator, Rc, Sort, Term, pool::TermPool};

pub fn clauses_to_or(pool: &mut dyn TermPool, clauses: &[Rc<Term>]) -> Option<Rc<Term>> {
    match clauses {
        [] => None,
        [clause] => Some(clause.clone()),
        _ => Some(pool.add(Term::Op(Operator::Or, clauses.to_vec()))),
    }
}

pub fn get_equational_terms(term: &Rc<Term>) -> Option<(Operator, &Rc<Term>, &Rc<Term>)> {
    match term.as_op() {
        Some((Operator::Equals, [lhs, rhs])) => Some((Operator::Equals, lhs, rhs)),
        Some((Operator::Distinct, [lhs, rhs])) => Some((Operator::Distinct, lhs, rhs)),
        _ => None,
    }
}

#[inline]
pub fn str_to_u64(input: &str) -> u64 {
    let mut hasher = DefaultHasher::new();
    input.hash(&mut hasher);
    hasher.finish()
}

/// Collects variables occurring in a term along with their dedicated sort nodes.
pub fn collect_vars(root: &Rc<Term>, collect_functions: bool) -> IndexMap<String, Rc<Sort>> {
    fn visit(term: &Rc<Term>, acc: &mut IndexMap<String, Rc<Sort>>, collect_functions: bool) {
        match term.as_ref() {
            Term::Const(_) => {}
            Term::Var(name, sort) => {
                if collect_functions || !matches!(sort.as_ref(), Sort::Function(_)) {
                    acc.entry(name.clone()).or_insert_with(|| sort.clone());
                }
            }
            Term::App(function, args) => {
                visit(function, acc, collect_functions);
                for arg in args {
                    visit(arg, acc, collect_functions);
                }
            }
            Term::Op(_, args) | Term::ParamOp { args, .. } => {
                for arg in args {
                    visit(arg, acc, collect_functions);
                }
                if let Term::ParamOp { op_args, .. } = term.as_ref() {
                    for arg in op_args {
                        visit(arg, acc, collect_functions);
                    }
                }
            }
            Term::Binder(_, bindings, body) => {
                for (name, sort) in bindings {
                    acc.entry(name.clone()).or_insert_with(|| sort.clone());
                }
                visit(body, acc, collect_functions);
            }
            Term::Let(bindings, body) => {
                for (_, value) in bindings {
                    visit(value, acc, collect_functions);
                }
                visit(body, acc, collect_functions);
            }
            Term::Match(term, cases) => {
                visit(term, acc, collect_functions);
                for case in cases {
                    for (name, sort) in case.bindings() {
                        acc.entry(name.clone()).or_insert_with(|| sort.clone());
                    }
                    visit(&case.body, acc, collect_functions);
                }
            }
            Term::AsOp(_, _, args) => {
                for arg in args {
                    visit(arg, acc, collect_functions);
                }
            }
        }
    }

    let mut variables = IndexMap::new();
    visit(root, &mut variables, collect_functions);
    variables
}

pub fn collect_subterms(root: &Rc<Term>) -> Vec<Rc<Term>> {
    fn visit(term: &Rc<Term>, terms: &mut IndexSet<Rc<Term>>) {
        if !terms.insert(term.clone()) {
            return;
        }
        match term.as_ref() {
            Term::Const(_) | Term::Var(..) => {}
            Term::App(function, args) => {
                visit(function, terms);
                for arg in args {
                    visit(arg, terms);
                }
            }
            Term::Op(_, args) | Term::AsOp(_, _, args) => {
                for arg in args {
                    visit(arg, terms);
                }
            }
            Term::Binder(_, _, body) => visit(body, terms),
            Term::Let(bindings, body) => {
                for (_, value) in bindings {
                    visit(value, terms);
                }
                visit(body, terms);
            }
            Term::Match(term, cases) => {
                visit(term, terms);
                for case in cases {
                    visit(&case.body, terms);
                }
            }
            Term::ParamOp { op_args, args, .. } => {
                for arg in op_args.iter().chain(args) {
                    visit(arg, terms);
                }
            }
        }
    }

    let mut terms = IndexSet::new();
    visit(root, &mut terms);
    terms.into_iter().collect()
}

/// Unifies two terms, treating variables on either side as pattern variables.
pub fn unify_pattern_bidirectional(
    pat: &Rc<Term>,
    val: &Rc<Term>,
) -> Option<(HashMap<Rc<Term>, Rc<Term>>, HashMap<Rc<Term>, Rc<Term>>)> {
    fn occurs(variable: &Rc<Term>, term: &Rc<Term>) -> bool {
        variable == term
            || match term.as_ref() {
                Term::Const(_) | Term::Var(..) => false,
                Term::App(function, args) => {
                    occurs(variable, function) || args.iter().any(|arg| occurs(variable, arg))
                }
                Term::Op(_, args) | Term::AsOp(_, _, args) => {
                    args.iter().any(|arg| occurs(variable, arg))
                }
                Term::Binder(_, _, body) => occurs(variable, body),
                Term::Let(bindings, body) => {
                    bindings.iter().any(|(_, value)| occurs(variable, value))
                        || occurs(variable, body)
                }
                Term::Match(term, cases) => {
                    occurs(variable, term)
                        || cases.iter().any(|case| occurs(variable, &case.body))
                }
                Term::ParamOp { op_args, args, .. } => op_args
                    .iter()
                    .chain(args)
                    .any(|arg| occurs(variable, arg)),
            }
    }

    fn unify(
        left: &Rc<Term>,
        right: &Rc<Term>,
        left_env: &mut HashMap<Rc<Term>, Rc<Term>>,
        right_env: &mut HashMap<Rc<Term>, Rc<Term>>,
    ) -> bool {
        if left == right {
            return true;
        }
        match (left.as_ref(), right.as_ref()) {
            (Term::Var(..), _) => {
                if let Some(bound) = left_env.get(left).cloned() {
                    return unify(&bound, right, left_env, right_env);
                }
                if occurs(left, right) {
                    return false;
                }
                left_env.insert(left.clone(), right.clone());
                true
            }
            (_, Term::Var(..)) => {
                if let Some(bound) = right_env.get(right).cloned() {
                    return unify(left, &bound, left_env, right_env);
                }
                if occurs(right, left) {
                    return false;
                }
                right_env.insert(right.clone(), left.clone());
                true
            }
            (Term::Const(a), Term::Const(b)) => a == b,
            (Term::App(a_fun, a_args), Term::App(b_fun, b_args)) if a_args.len() == b_args.len() => {
                unify(a_fun, b_fun, left_env, right_env)
                    && a_args.iter().zip(b_args).all(|(a, b)| unify(a, b, left_env, right_env))
            }
            (Term::Op(a_op, a_args), Term::Op(b_op, b_args))
                if a_op == b_op && a_args.len() == b_args.len() =>
            {
                a_args.iter().zip(b_args).all(|(a, b)| unify(a, b, left_env, right_env))
            }
            (Term::Binder(a_kind, a_bindings, a_body), Term::Binder(b_kind, b_bindings, b_body))
                if a_kind == b_kind && a_bindings == b_bindings =>
            {
                unify(a_body, b_body, left_env, right_env)
            }
            (Term::Let(a_bindings, a_body), Term::Let(b_bindings, b_body))
                if a_bindings.len() == b_bindings.len() =>
            {
                a_bindings.iter().zip(b_bindings).all(|((_, a), (_, b))| unify(a, b, left_env, right_env))
                    && unify(a_body, b_body, left_env, right_env)
            }
            (Term::Match(a_term, a_cases), Term::Match(b_term, b_cases))
                if a_cases.len() == b_cases.len() =>
            {
                unify(a_term, b_term, left_env, right_env)
                    && a_cases.iter().zip(b_cases).all(|(a, b)| {
                        a.pattern == b.pattern && unify(&a.body, &b.body, left_env, right_env)
                    })
            }
            (
                Term::ParamOp { op: a_op, op_args: a_op_args, args: a_args },
                Term::ParamOp { op: b_op, op_args: b_op_args, args: b_args },
            ) if a_op == b_op && a_op_args.len() == b_op_args.len() && a_args.len() == b_args.len() => {
                a_op_args.iter().zip(b_op_args).chain(a_args.iter().zip(b_args)).all(|(a, b)| {
                    unify(a, b, left_env, right_env)
                })
            }
            (Term::AsOp(a_op, a_sort, a_args), Term::AsOp(b_op, b_sort, b_args))
                if a_op == b_op && a_sort == b_sort && a_args.len() == b_args.len() =>
            {
                a_args.iter().zip(b_args).all(|(a, b)| unify(a, b, left_env, right_env))
            }
            _ => false,
        }
    }

    let mut left_env = HashMap::new();
    let mut right_env = HashMap::new();
    unify(pat, val, &mut left_env, &mut right_env).then_some((left_env, right_env))
}

pub fn unify_pattern(pat: &Rc<Term>, val: &Rc<Term>) -> bool {
    unify_pattern_bidirectional(pat, val).is_some()
}

pub fn hash_var_name(map: &mut HashMap<String, u64>, name: &str) -> u64 {
    let scoped_name = format!("var:{name}");
    *map.entry(scoped_name.clone())
        .or_insert_with(|| str_to_u64(&scoped_name))
}

/// Collect all equality subterms from a term (including nested equalities).
pub fn collect_equality_subterms(term: &Rc<Term>) -> Vec<Rc<Term>> {
    fn visit(term: &Rc<Term>, result: &mut Vec<Rc<Term>>) {
        match term.as_ref() {
            Term::Op(Operator::Equals, args) if args.len() == 2 => {
                result.push(term.clone());
                visit(&args[0], result);
                visit(&args[1], result);
            }
            Term::App(function, args) => {
                visit(function, result);
                for arg in args { visit(arg, result); }
            }
            Term::Op(_, args) | Term::AsOp(_, _, args) => {
                for arg in args { visit(arg, result); }
            }
            Term::Binder(_, _, body) => visit(body, result),
            Term::Let(bindings, body) => {
                for (_, value) in bindings { visit(value, result); }
                visit(body, result);
            }
            Term::Match(term, cases) => {
                visit(term, result);
                for case in cases { visit(&case.body, result); }
            }
            Term::ParamOp { op_args, args, .. } => {
                for arg in op_args.iter().chain(args) { visit(arg, result); }
            }
            Term::Const(_) | Term::Var(..) => {}
        }
    }

    let mut result = Vec::new();
    visit(term, &mut result);
    result
}
