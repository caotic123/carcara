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
                    occurs(variable, term) || cases.iter().any(|case| occurs(variable, &case.body))
                }
                Term::ParamOp { op_args, args, .. } => {
                    op_args.iter().chain(args).any(|arg| occurs(variable, arg))
                }
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
            (Term::App(a_fun, a_args), Term::App(b_fun, b_args))
                if a_args.len() == b_args.len() =>
            {
                unify(a_fun, b_fun, left_env, right_env)
                    && a_args
                        .iter()
                        .zip(b_args)
                        .all(|(a, b)| unify(a, b, left_env, right_env))
            }
            (Term::Op(a_op, a_args), Term::Op(b_op, b_args))
                if a_op == b_op && a_args.len() == b_args.len() =>
            {
                a_args
                    .iter()
                    .zip(b_args)
                    .all(|(a, b)| unify(a, b, left_env, right_env))
            }
            (
                Term::Binder(a_kind, a_bindings, a_body),
                Term::Binder(b_kind, b_bindings, b_body),
            ) if a_kind == b_kind && a_bindings == b_bindings => {
                unify(a_body, b_body, left_env, right_env)
            }
            (Term::Let(a_bindings, a_body), Term::Let(b_bindings, b_body))
                if a_bindings.len() == b_bindings.len() =>
            {
                a_bindings
                    .iter()
                    .zip(b_bindings)
                    .all(|((_, a), (_, b))| unify(a, b, left_env, right_env))
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
                Term::ParamOp {
                    op: a_op,
                    op_args: a_op_args,
                    args: a_args,
                },
                Term::ParamOp {
                    op: b_op,
                    op_args: b_op_args,
                    args: b_args,
                },
            ) if a_op == b_op
                && a_op_args.len() == b_op_args.len()
                && a_args.len() == b_args.len() =>
            {
                a_op_args
                    .iter()
                    .zip(b_op_args)
                    .chain(a_args.iter().zip(b_args))
                    .all(|(a, b)| unify(a, b, left_env, right_env))
            }
            (Term::AsOp(a_op, a_sort, a_args), Term::AsOp(b_op, b_sort, b_args))
                if a_op == b_op && a_sort == b_sort && a_args.len() == b_args.len() =>
            {
                a_args
                    .iter()
                    .zip(b_args)
                    .all(|(a, b)| unify(a, b, left_env, right_env))
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
                for arg in args {
                    visit(arg, result);
                }
            }
            Term::Op(_, args) | Term::AsOp(_, _, args) => {
                for arg in args {
                    visit(arg, result);
                }
            }
            Term::Binder(_, _, body) => visit(body, result),
            Term::Let(bindings, body) => {
                for (_, value) in bindings {
                    visit(value, result);
                }
                visit(body, result);
            }
            Term::Match(term, cases) => {
                visit(term, result);
                for case in cases {
                    visit(&case.body, result);
                }
            }
            Term::ParamOp { op_args, args, .. } => {
                for arg in op_args.iter().chain(args) {
                    visit(arg, result);
                }
            }
            Term::Const(_) | Term::Var(..) => {}
        }
    }

    let mut result = Vec::new();
    visit(term, &mut result);
    result
}

/// A hash of a term's structure, the same in every process and pool: the
/// key under which a normal form found while checking one hole is handed to
/// the child checking a later hole, which parses its own copy of the terms.
/// Variables hash by name and sort, constants by value, applications by
/// operator and children; binders and the rarer shapes hash by their
/// printed form.  `memo` is keyed by the term's pointer.
pub fn structural_hash(term: &Rc<Term>, memo: &mut HashMap<usize, u64>) -> u64 {
    let key = Rc::as_ptr(term) as *const () as usize;
    if let Some(&hash) = memo.get(&key) {
        return hash;
    }
    let mut hasher = DefaultHasher::new();
    match term.as_ref() {
        Term::Var(name, sort) => {
            0u8.hash(&mut hasher);
            name.hash(&mut hasher);
            format!("{sort}").hash(&mut hasher);
        }
        Term::Const(constant) => {
            1u8.hash(&mut hasher);
            constant.hash(&mut hasher);
        }
        Term::Op(operator, args) => {
            2u8.hash(&mut hasher);
            operator.hash(&mut hasher);
            for arg in args {
                structural_hash(arg, memo).hash(&mut hasher);
            }
        }
        Term::App(function, args) => {
            3u8.hash(&mut hasher);
            structural_hash(function, memo).hash(&mut hasher);
            for arg in args {
                structural_hash(arg, memo).hash(&mut hasher);
            }
        }
        _ => {
            4u8.hash(&mut hasher);
            format!("{term:#}").hash(&mut hasher);
        }
    }
    let hash = hasher.finish();
    memo.insert(key, hash);
    hash
}

/// The compound subterms of `root` (operator and function applications) in
/// pre-order, each once, walking through applications only: what a normal
/// form can be recorded for and substituted at.  Outer terms come first, so
/// a cap keeps the largest ones.
pub fn compound_subterms(root: &Rc<Term>, cap: usize) -> Vec<Rc<Term>> {
    fn visit(term: &Rc<Term>, terms: &mut IndexSet<Rc<Term>>, cap: usize) {
        if terms.len() >= cap {
            return;
        }
        match term.as_ref() {
            Term::App(_, args) | Term::Op(_, args) if !args.is_empty() => {
                if !terms.insert(term.clone()) {
                    return;
                }
                if let Term::App(function, _) = term.as_ref() {
                    visit(function, terms, cap);
                }
                for arg in args {
                    visit(arg, terms, cap);
                }
            }
            _ => {}
        }
    }
    let mut terms = IndexSet::new();
    visit(root, &mut terms, cap);
    terms.into_iter().collect()
}

/// `root` with every subterm whose structural hash is in `replacements`
/// replaced, outermost first, walking through applications only.
pub fn substitute_by_hash(
    pool: &mut dyn TermPool,
    root: &Rc<Term>,
    replacements: &HashMap<u64, Rc<Term>>,
    memo: &mut HashMap<usize, u64>,
    replaced: &mut usize,
) -> Rc<Term> {
    if replacements.is_empty() {
        return root.clone();
    }
    if let Some(replacement) = replacements.get(&structural_hash(root, memo)) {
        if replacement != root {
            *replaced += 1;
            return replacement.clone();
        }
    }
    match root.as_ref() {
        Term::Op(operator, args) if !args.is_empty() => {
            let new_args: Vec<Rc<Term>> = args
                .iter()
                .map(|arg| substitute_by_hash(pool, arg, replacements, memo, replaced))
                .collect();
            if new_args.iter().zip(args).all(|(new, old)| new == old) {
                root.clone()
            } else {
                pool.add(Term::Op(*operator, new_args))
            }
        }
        Term::App(function, args) => {
            let new_function = substitute_by_hash(pool, function, replacements, memo, replaced);
            let new_args: Vec<Rc<Term>> = args
                .iter()
                .map(|arg| substitute_by_hash(pool, arg, replacements, memo, replaced))
                .collect();
            if new_function == *function && new_args.iter().zip(args).all(|(new, old)| new == old)
            {
                root.clone()
            } else {
                pool.add(Term::App(new_function, new_args))
            }
        }
        _ => root.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Constant, pool::PrimitivePool};

    fn int(pool: &mut PrimitivePool, value: i32) -> Rc<Term> {
        pool.add(Term::Const(Constant::Integer(value.into())))
    }

    /// `(+ (* 2 3) (* 2 3) 1)` in `pool`.
    fn sample(pool: &mut PrimitivePool) -> (Rc<Term>, Rc<Term>) {
        let two = int(pool, 2);
        let three = int(pool, 3);
        let one = int(pool, 1);
        let product = pool.add(Term::Op(Operator::Mult, vec![two, three]));
        let sum = pool.add(Term::Op(
            Operator::Add,
            vec![product.clone(), product.clone(), one],
        ));
        (sum, product)
    }

    #[test]
    fn structural_hash_is_the_same_across_pools_and_differs_by_structure() {
        let mut first = PrimitivePool::new();
        let mut second = PrimitivePool::new();
        let (sum_a, product_a) = sample(&mut first);
        let (sum_b, product_b) = sample(&mut second);
        let mut memo = HashMap::new();
        assert_eq!(
            structural_hash(&sum_a, &mut memo),
            structural_hash(&sum_b, &mut memo)
        );
        assert_eq!(
            structural_hash(&product_a, &mut memo),
            structural_hash(&product_b, &mut memo)
        );
        assert_ne!(
            structural_hash(&sum_a, &mut memo),
            structural_hash(&product_a, &mut memo)
        );
        let six = int(&mut first, 6);
        assert_ne!(
            structural_hash(&product_a, &mut memo),
            structural_hash(&six, &mut memo)
        );
    }

    #[test]
    fn compound_subterms_are_outermost_first_and_unique() {
        let mut pool = PrimitivePool::new();
        let (sum, product) = sample(&mut pool);
        let subterms = compound_subterms(&sum, 10);
        assert_eq!(subterms, vec![sum.clone(), product.clone()]);
        assert_eq!(compound_subterms(&sum, 1), vec![sum]);
    }

    #[test]
    fn substitution_replaces_the_outermost_match_by_hash() {
        let mut pool = PrimitivePool::new();
        let (sum, product) = sample(&mut pool);
        let mut memo = HashMap::new();
        let six = int(&mut pool, 6);
        let replacements = HashMap::from([(structural_hash(&product, &mut memo), six.clone())]);
        let mut replaced = 0;
        let result = substitute_by_hash(&mut pool, &sum, &replacements, &mut memo, &mut replaced);
        assert_eq!(replaced, 2);
        let one = int(&mut pool, 1);
        let expected = pool.add(Term::Op(Operator::Add, vec![six.clone(), six, one]));
        assert_eq!(result, expected);
        // A hash without a match leaves the term as it is.
        let none = HashMap::from([(1u64, product)]);
        let mut replaced = 0;
        assert_eq!(
            substitute_by_hash(&mut pool, &sum, &none, &mut memo, &mut replaced),
            sum
        );
        assert_eq!(replaced, 0);
    }
}
