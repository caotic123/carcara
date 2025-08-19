use indexmap::{IndexMap, IndexSet};

use crate::{
    ast::{rare_rules::*, BindingList, PrimitivePool, Rc, Sort, Substitution, Term, TermPool},
    rare::computational::program::compile_program,
};

/// Removes any positional arguments from an application term whose head matches
/// a program in `programs` and whose signature marks some parameters as higher-order.
pub fn remove_positional_args(
    pool: &mut PrimitivePool,
    term: &Rc<Term>,
    programs: &IndexMap<String, Program>,
    positional_signature: &Vec<usize>,
) -> Rc<Term> {
    use std::collections::HashSet;

    // Convert indices list to a set for O(1) filters.
    let pos_set: HashSet<usize> = positional_signature.iter().copied().collect();

    fn visit_sort(
        pool: &mut PrimitivePool,
        s: &Sort,
        programs: &IndexMap<String, Program>,
        pos_set: &HashSet<usize>,
        shadowed: &HashSet<String>,
    ) -> (bool, Sort) {
        let mut changed = false;

        let mut map_terms = |v: &Vec<Rc<Term>>| -> (bool, Vec<Rc<Term>>) {
            let mut any = false;
            let mut out = Vec::with_capacity(v.len());
            for t in v {
                let nt = visit(pool, t, programs, pos_set, shadowed);
                if t != &nt {
                    any = true;
                }
                out.push(nt);
            }
            (any, out)
        };

        match s {
            Sort::Function(ts) => {
                let (c, nts) = map_terms(ts);
                changed |= c;
                if changed {
                    (true, Sort::Function(nts))
                } else {
                    (false, s.clone())
                }
            }
            Sort::Atom(name, ts) => {
                let (c, nts) = map_terms(ts);
                changed |= c;
                if changed {
                    (true, Sort::Atom(name.clone(), nts))
                } else {
                    (false, s.clone())
                }
            }
            Sort::Array(a, b) => {
                let na = visit(pool, a, programs, pos_set, shadowed);
                let nb = visit(pool, b, programs, pos_set, shadowed);
                if a != &na || b != &nb {
                    (true, Sort::Array(na, nb))
                } else {
                    (false, s.clone())
                }
            }
            Sort::ParamSort(ts, inner) => {
                let (c1, nts) = map_terms(ts);
                let ninner = visit(pool, inner, programs, pos_set, shadowed);
                let c2 = inner != &ninner;
                if c1 || c2 {
                    (true, Sort::ParamSort(nts, ninner))
                } else {
                    (false, s.clone())
                }
            }

            _ => (false, s.clone()),
        }
    }

    fn visit(
        pool: &mut PrimitivePool,
        term: &Rc<Term>,
        programs: &IndexMap<String, Program>,
        pos_set: &HashSet<usize>,
        shadowed: &HashSet<String>,
    ) -> Rc<Term> {
        match &**term {
            Term::Const(_) => term.clone(),

            Term::Var(name, sort) => {
                let nsort = visit(pool, sort, programs, pos_set, shadowed);
                if sort != &nsort {
                    pool.add(Term::Var(name.clone(), nsort))
                } else {
                    term.clone()
                }
            }

            Term::Sort(s) => {
                let (changed, ns) = visit_sort(pool, s, programs, pos_set, shadowed);
                if changed {
                    pool.add(Term::Sort(ns))
                } else {
                    term.clone()
                }
            }

            Term::Op(op, args) => {
                let mut changed = false;
                let mut nargs = Vec::with_capacity(args.len());
                for a in args {
                    let na = visit(pool, a, programs, pos_set, shadowed);
                    if a != &na {
                        changed = true;
                    }
                    nargs.push(na);
                }
                if changed {
                    pool.add(Term::Op(*op, nargs))
                } else {
                    term.clone()
                }
            }

            Term::App(head, args) => {
                let nhead = visit(pool, head, programs, pos_set, shadowed);
                let mut changed = head != &nhead;

                let mut nargs = Vec::with_capacity(args.len());
                for a in args {
                    let na = visit(pool, a, programs, pos_set, shadowed);
                    if a != &na {
                        changed = true;
                    }
                    nargs.push(na);
                }

                let should_filter = if let Term::Var(name, _) = &*nhead {
                    !shadowed.contains(name) && programs.contains_key(name) && !pos_set.is_empty()
                } else {
                    false
                };

                if should_filter {
                    let mut filtered = Vec::with_capacity(nargs.len());
                    for (i, a) in nargs.into_iter().enumerate() {
                        if !pos_set.contains(&i) {
                            filtered.push(a);
                        } else {
                            changed = true; // dropping changes the node
                        }
                    }
                    if changed {
                        pool.add(Term::App(nhead, filtered))
                    } else {
                        term.clone()
                    }
                } else if changed {
                    pool.add(Term::App(nhead, nargs))
                } else {
                    term.clone()
                }
            }

            Term::ParamOp { op, op_args, args } => {
                let mut changed = false;

                let mut nop_args = Vec::with_capacity(op_args.len());
                for oa in op_args {
                    let no = visit(pool, oa, programs, pos_set, shadowed);
                    if oa != &no {
                        changed = true;
                    }
                    nop_args.push(no);
                }

                let mut nargs = Vec::with_capacity(args.len());
                for a in args {
                    let na = visit(pool, a, programs, pos_set, shadowed);
                    if a != &na {
                        changed = true;
                    }
                    nargs.push(na);
                }

                if changed {
                    pool.add(Term::ParamOp {
                        op: *op,
                        op_args: nop_args,
                        args: nargs,
                    })
                } else {
                    term.clone()
                }
            }

            Term::Binder(b, bindings, inner) => {
                let mut changed = false;
                let mut nbindings = Vec::with_capacity(bindings.0.len());
                for (name, sort) in bindings.0.iter() {
                    let nsort = visit(pool, sort, programs, pos_set, shadowed);
                    if sort != &nsort {
                        changed = true;
                    }
                    nbindings.push((name.clone(), nsort));
                }

                let mut next_shadow = shadowed.clone();
                for (name, _) in bindings.0.iter() {
                    next_shadow.insert(name.clone());
                }

                let ninner = visit(pool, inner, programs, pos_set, &next_shadow);
                if inner != &ninner {
                    changed = true;
                }

                if changed {
                    pool.add(Term::Binder(*b, BindingList(nbindings), ninner))
                } else {
                    term.clone()
                }
            }

            Term::Let(bindings, body) => {
                let mut changed = false;
                let mut nbindings = Vec::with_capacity(bindings.0.len());
                for (name, value) in bindings.0.iter() {
                    let nvalue = visit(pool, value, programs, pos_set, shadowed);
                    if value != &nvalue {
                        changed = true;
                    }
                    nbindings.push((name.clone(), nvalue));
                }

                let mut next_shadow = shadowed.clone();
                for (name, _) in bindings.0.iter() {
                    next_shadow.insert(name.clone());
                }

                let nbody = visit(pool, body, programs, pos_set, &next_shadow);
                if body != &nbody {
                    changed = true;
                }

                if changed {
                    pool.add(Term::Let(BindingList(nbindings), nbody))
                } else {
                    term.clone()
                }
            }
        }
    }

    let shadowed = HashSet::new();
    visit(pool, term, programs, &pos_set, &shadowed)
}

// This function goes to every subterm search if they correspond to some program and if it program depends on some constant
// If so, we remove the constant and prepare the defunctionalization
// Note: This function will return the dependencies of programs even though they are did not have any high-order position
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

    fn transform_sort(
        pool: &mut PrimitivePool,
        s: &Sort,
        rules: &IndexMap<String, Program>,
        decls: &IndexMap<String, DeclConst>,
        out_calls: &mut IndexSet<(String, Vec<Rc<Term>>)>,
    ) -> Sort {
        match s {
            Sort::Function(ts) => {
                let nts = ts
                    .iter()
                    .map(|t| transform(pool, t, rules, decls, out_calls))
                    .collect();
                Sort::Function(nts)
            }
            Sort::Atom(name, ts) => {
                let nts = ts
                    .iter()
                    .map(|t| transform(pool, t, rules, decls, out_calls))
                    .collect();
                Sort::Atom(name.clone(), nts)
            }
            Sort::Array(a, b) => {
                let na = transform(pool, a, rules, decls, out_calls);
                let nb = transform(pool, b, rules, decls, out_calls);
                Sort::Array(na, nb)
            }
            Sort::ParamSort(ts, inner) => {
                let nts = ts
                    .iter()
                    .map(|t| transform(pool, t, rules, decls, out_calls))
                    .collect();
                let ninner = transform(pool, inner, rules, decls, out_calls);
                Sort::ParamSort(nts, ninner)
            }

            _ => s.clone(),
        }
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
                    if is_declared_const(&na, decls) {
                        removed.push(na.clone());
                    }
                    all.push(na);
                }

                if let Term::Var(name, _) = &**head {
                    if rules.contains_key(name) {
                        out_calls.insert((name.to_owned(), removed.clone()));
                    }
                }

                pool.add(Term::App(head.clone(), all))
            }

            Term::Op(op, args) => {
                let all: Vec<Rc<Term>> = args
                    .iter()
                    .map(|a| transform(pool, a, rules, decls, out_calls))
                    .collect();
                pool.add(Term::Op(*op, all))
            }

            Term::ParamOp { op, op_args, args } => {
                let nop_args: Vec<Rc<Term>> = op_args
                    .iter()
                    .map(|oa| transform(pool, oa, rules, decls, out_calls))
                    .collect();
                let nargs: Vec<Rc<Term>> = args
                    .iter()
                    .map(|a| transform(pool, a, rules, decls, out_calls))
                    .collect();

                pool.add(Term::ParamOp {
                    op: *op,
                    op_args: nop_args,
                    args: nargs,
                })
            }

            Term::Binder(binder, bindings, inner) => {
                let nbindings = BindingList(
                    bindings
                        .as_ref()
                        .iter()
                        .map(|(v, srt)| (v.clone(), transform(pool, srt, rules, decls, out_calls)))
                        .collect(),
                );
                let ninner = transform(pool, inner, rules, decls, out_calls);
                pool.add(Term::Binder(*binder, nbindings, ninner))
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

            Term::Var(name, sort) => {
                let nsort = transform(pool, sort, rules, decls, out_calls);
                pool.add(Term::Var(name.clone(), nsort))
            }

            Term::Sort(s) => {
                let ns = transform_sort(pool, s, rules, decls, out_calls);
                pool.add(Term::Sort(ns))
            }

            Term::Const(_) => t.clone(),
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

    if instations.is_empty() {
        // If there are no instations, we can just return the original rule
        elaborated_rules.push(rule.clone());
        return elaborated_rules;
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

        let compiled_programs = compile_program(
            pool,
            &Program {
                name: format!(
                    "{}_*{}",
                    program.name,
                    rule.name
                ),
                parameters: parameters,
                patterns,
                signature: signature,
            },
        );

        for compiled_program in compiled_programs {
            elaborated_rules.push(compiled_program);
        }

        let mut rule = rule.clone();

        for premise in rule.premises.iter_mut() {
            let new_premise =
                remove_positional_args(pool, premise, programs, &positional_signature);
            *premise = new_premise;
        }

        rule.conclusion =
            remove_positional_args(pool, &rule.conclusion, programs, &positional_signature);

        elaborated_rules.push(rule);
    }

    elaborated_rules
}
