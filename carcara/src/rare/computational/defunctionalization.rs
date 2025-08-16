use indexmap::{IndexMap, IndexSet};

use crate::{
    ast::{rare_rules::*, BindingList, PrimitivePool, Rc, Sort, Substitution, Term, TermPool},
    rare::computational::program::compile_program,
};

/// Removes any positional arguments from an application term whose head matches
/// a program in `programs` and whose signature marks some parameters as higher-order.
///
/// # Arguments
/// * `pool` - Term allocator.
/// * `term` - The term to process.
/// * `programs` - Mapping from program names to their definitions.
///
/// # Returns
/// A new term with positional arguments removed (if applicable).
pub fn remove_positional_args(
    pool: &mut PrimitivePool,
    term: &Rc<Term>,
    programs: &IndexMap<String, Program>,
    positional_signature: &Vec<usize>,
) -> Rc<Term> {
    match &**term {
        Term::App(head, args) => {
            if let Term::Var(name, _) = &**head {
                if let Some(_) = programs.get(name) {
                    // Keep only non-positional arguments
                    let filtered_args: Vec<Rc<Term>> = args
                        .iter()
                        .map(|t| remove_positional_args(pool, t, programs, positional_signature))
                        .enumerate()
                        .filter(|(idx, _)| !positional_signature.contains(idx))
                        .map(|(_, arg)| arg)
                        .collect();

                    return pool.add(Term::App(head.clone(), filtered_args));
                }
            }
            // No match: return original term
            term.clone()
        }
        Term::Op(head, args) => {
            // Keep only non-positional arguments
            let args: Vec<Rc<Term>> = args
                .iter()
                .map(|t| remove_positional_args(pool, t, programs, positional_signature))
                .collect();

            return pool.add(Term::Op(*head, args));
        }
        _ => term.clone(),
    }
}

// This function goes to every subterm search if they correspond to some program and if it program depends on some constant
// If so, we remove the constant and prepare the defunctionalization
pub fn defunctionalization(
    pool: &mut PrimitivePool,
    term: &Rc<Term>,
    programs: &IndexMap<String, Program>,
    decl_consts: &IndexMap<String, DeclConst>,
) -> (IndexSet<(String, Vec<Rc<Term>>)>, Rc<Term>) {
    #[inline]
    fn is_declared_const(arg: &Rc<Term>, decls: &IndexMap<String, DeclConst>) -> bool {
        matches!(&**arg, Term::Var(name, _) if decls.contains_key(name))
    }

    fn transform(
        pool: &mut PrimitivePool,
        t: &Rc<Term>,
        rules: &IndexMap<String, Program>,
        decls: &IndexMap<String, DeclConst>,
        out_calls: &mut IndexSet<(String, Vec<Rc<Term>>)>,
    ) -> Rc<Term> {
        match &**t {
            Term::App(head, args) => {
                let mut removed: Vec<Rc<Term>> = Vec::new();
                let mut all: Vec<Rc<Term>> = Vec::with_capacity(args.len());

                for a in args {
                    let na = transform(pool, a, rules, decls, out_calls);
                    let is_decl = is_declared_const(&na, decls);
                    if is_decl {
                        removed.push(na.clone());
                    }
                    all.push(na);
                }

                if let Term::Var(name, sort) = &**head {
                    if rules.contains_key(name) {
                        if !removed.is_empty() {
                            out_calls.insert((name.to_owned(), removed.clone()));
                        }
                    }
                }

                // not a target head: keep all transformed args in original order
                pool.add(Term::App(head.clone(), all))
            }

            Term::Op(op, args) => {
                let mut all: Vec<Rc<Term>> = Vec::with_capacity(args.len());

                for a in args {
                    let na = transform(pool, a, rules, decls, out_calls);
                    all.push(na);
                }

                pool.add(Term::Op(*op, all))
            }

            Term::Let(bindings, inner) => {
                let new_bindings = BindingList(
                    bindings
                        .as_ref()
                        .iter()
                        .map(|(v, val)| (v.clone(), transform(pool, val, rules, decls, out_calls)))
                        .collect(),
                );
                let new_inner = transform(pool, inner, rules, decls, out_calls);
                pool.add(Term::Let(new_bindings, new_inner))
            }

            // We don’t touch other variants here; they get shared
            _ => t.clone(),
        }
    }

    let mut calls = IndexSet::new();
    let rewritten = transform(pool, term, programs, decl_consts, &mut calls);
    (calls, rewritten)
}

pub fn elaborate_rule(
    pool: &mut PrimitivePool,
    rule: &RuleDefinition,
    programs: &IndexMap<String, Program>,
    decl_consts: &IndexMap<String, DeclConst>,
) -> Vec<RuleDefinition> {
    let rule = rule.clone();
    let mut elaborated_rules = vec![];
    let mut instations = IndexSet::new();

    for index in 0..rule.premises.len() {
        let (instation, _) =
            defunctionalization(pool, &rule.premises[index], programs, decl_consts);
        if !instation.is_empty() {
            instations.extend(instation);
        }
    }

    let (instation, _) = defunctionalization(pool, &rule.conclusion, programs, decl_consts);

    if !instation.is_empty() {
        instations.extend(instation);
    }

    for (program_name, constants) in instations {
        let program = programs.get(&program_name).unwrap();
        let mut patterns = vec![];
        let mut func_args = vec![];
        let mut parameters = IndexMap::new();
        let mut signature = vec![];

        let mut positional_signature = vec![];
        // Select the high-order parameters
        for (index, sort) in program.signature.iter().enumerate() {
            if let Some(Sort::Function(_)) = sort.as_sort() {
                positional_signature.push(index);
                continue;
            }
            signature.push(sort.clone());
        }

        for param in program.parameters.iter() {
            if let Some(Sort::Function(_)) = param.1.term.as_sort() {
                func_args.push(pool.add(Term::Var(param.0.to_owned(), param.1.term.clone())));
                continue;
            }
            parameters.insert(param.0.to_owned(), param.1.clone());
        }

        let subs: IndexMap<Rc<Term>, Rc<Term>> =
            func_args.into_iter().zip(constants.clone()).collect();

        let mut substitution = Substitution::new(pool, subs).unwrap();
        for index in 0..program.patterns.len() {
            let lhs = remove_positional_args(
                pool,
                &program.patterns[index].0,
                programs,
                &positional_signature,
            );
            let lhs = substitution.apply(pool, &lhs);

            let rhs = remove_positional_args(
                pool,
                &program.patterns[index].1,
                programs,
                &positional_signature,
            );
            let rhs = substitution.apply(pool, &rhs);

            patterns.push((lhs, rhs));
        }

        println!(
            "{:?}",
            Program {
                name: program.name.clone(),
                parameters: parameters.clone(),
                patterns: patterns.clone(),
                signature: signature.clone(),
            }
        );

        let compiled_programs = compile_program(
            pool,
            &Program {
                name: program.name.clone(),
                parameters: parameters,
                patterns,
                signature: signature,
            },
        );

        for compiled_program in compiled_programs {
            elaborated_rules.push(compiled_program);
        }
    }

    elaborated_rules
}
