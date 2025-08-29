use egglog::sort::FunctionSort;
use indexmap::{IndexMap, IndexSet};

use crate::{
    ast::{rare_rules::*, BindingList, PrimitivePool, Rc, Sort, Substitution, Term, TermPool},
    rare::{
        computational::{core::interpret_eunoia, program::compile_program},
        util::{collect_vars, unify_pattern_bidirectional},
    },
};

/// Removes any positional arguments from an application term whose head matches
/// a program and its name is equal to defunctionalized_function parameter
/// and whose signature marks some parameters as higher-order.
pub fn remove_positional_args(
    pool: &mut PrimitivePool,
    term: &Rc<Term>,
    defunctionalized_function: &str,
    positional_signature: &Vec<usize>,
) -> Rc<Term> {
    use std::collections::HashSet;

    // Convert indices list to a set for O(1) filters.
    let pos_set: HashSet<usize> = positional_signature.iter().copied().collect();

    fn visit_sort(
        pool: &mut PrimitivePool,
        s: &Sort,
        defunctionalized_function: &str,
        pos_set: &HashSet<usize>,
        shadowed: &HashSet<String>,
    ) -> (bool, Sort) {
        let mut changed = false;

        let mut map_terms = |v: &Vec<Rc<Term>>| -> (bool, Vec<Rc<Term>>) {
            let mut any = false;
            let mut out = Vec::with_capacity(v.len());
            for t in v {
                let nt = visit(pool, t, defunctionalized_function, pos_set, shadowed);
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
                let na = visit(pool, a, defunctionalized_function, pos_set, shadowed);
                let nb = visit(pool, b, defunctionalized_function, pos_set, shadowed);
                if a != &na || b != &nb {
                    (true, Sort::Array(na, nb))
                } else {
                    (false, s.clone())
                }
            }
            Sort::ParamSort(ts, inner) => {
                let (c1, nts) = map_terms(ts);
                let ninner = visit(pool, inner, defunctionalized_function, pos_set, shadowed);
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
        defunctionalized_function: &str,
        pos_set: &HashSet<usize>,
        shadowed: &HashSet<String>,
    ) -> Rc<Term> {
        match &**term {
            Term::Const(_) => term.clone(),

            Term::Var(name, sort) => {
                let nsort = visit(pool, sort, defunctionalized_function, pos_set, shadowed);
                if sort != &nsort {
                    pool.add(Term::Var(name.clone(), nsort))
                } else {
                    term.clone()
                }
            }

            Term::Sort(s) => {
                let (changed, ns) =
                    visit_sort(pool, s, defunctionalized_function, pos_set, shadowed);
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
                    let na = visit(pool, a, defunctionalized_function, pos_set, shadowed);
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
                let nhead = visit(pool, head, defunctionalized_function, pos_set, shadowed);
                let mut changed = head != &nhead;

                let mut nargs = Vec::with_capacity(args.len());
                for a in args {
                    let na = visit(pool, a, defunctionalized_function, pos_set, shadowed);
                    if a != &na {
                        changed = true;
                    }
                    nargs.push(na);
                }

                let should_filter = if let Term::Var(name, _) = &*nhead {
                    !shadowed.contains(name)
                        && name == &defunctionalized_function
                        && !pos_set.is_empty()
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
                    let no = visit(pool, oa, defunctionalized_function, pos_set, shadowed);
                    if oa != &no {
                        changed = true;
                    }
                    nop_args.push(no);
                }

                let mut nargs = Vec::with_capacity(args.len());
                for a in args {
                    let na = visit(pool, a, defunctionalized_function, pos_set, shadowed);
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
                    let nsort = visit(pool, sort, defunctionalized_function, pos_set, shadowed);
                    if sort != &nsort {
                        changed = true;
                    }
                    nbindings.push((name.clone(), nsort));
                }

                let mut next_shadow = shadowed.clone();
                for (name, _) in bindings.0.iter() {
                    next_shadow.insert(name.clone());
                }

                let ninner = visit(
                    pool,
                    inner,
                    defunctionalized_function,
                    pos_set,
                    &next_shadow,
                );
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
                    let nvalue = visit(pool, value, defunctionalized_function, pos_set, shadowed);
                    if value != &nvalue {
                        changed = true;
                    }
                    nbindings.push((name.clone(), nvalue));
                }

                let mut next_shadow = shadowed.clone();
                for (name, _) in bindings.0.iter() {
                    next_shadow.insert(name.clone());
                }

                let nbody = visit(pool, body, defunctionalized_function, pos_set, &next_shadow);
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
    visit(pool, term, defunctionalized_function, &pos_set, &shadowed)
}

// This function goes to every subterm search if they correspond to some program and if it program depends on some constant
pub fn search_programs(
    term: &Rc<Term>,
    programs: &IndexMap<String, Program>,
) -> IndexSet<(String, Vec<Rc<Term>>)> {
    fn visit_sort(
        s: &Sort,
        programs: &IndexMap<String, Program>,
        out: &mut IndexSet<(String, Vec<Rc<Term>>)>,
    ) {
        match s {
            Sort::Function(ts) => {
                for t in ts {
                    visit_term(t, programs, out);
                }
            }
            Sort::Atom(_, ts) => {
                for t in ts {
                    visit_term(t, programs, out);
                }
            }
            Sort::Array(a, b) => {
                visit_term(a, programs, out);
                visit_term(b, programs, out);
            }
            Sort::ParamSort(ts, inner) => {
                for t in ts {
                    visit_term(t, programs, out);
                }
                visit_term(inner, programs, out);
            }
            // Primitive sorts / BitVec width: nothing to traverse
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

    fn visit_term(
        t: &Rc<Term>,
        programs: &IndexMap<String, Program>,
        out: &mut IndexSet<(String, Vec<Rc<Term>>)>,
    ) {
        match &**t {
            Term::App(head, args) => {
                // Traverse args and collect declared consts
                for a in args {
                    visit_term(a, programs, out);
                }
                // Record program call if head is a known program and we found declared const args
                if let Term::Var(name, _) = &**head {
                    if programs.contains_key(name) {
                        out.insert((name.clone(), args.clone()));
                    }
                }
            }

            Term::Op(_, args) => {
                for a in args {
                    visit_term(a, programs, out);
                }
            }

            Term::ParamOp { op_args, args, .. } => {
                for oa in op_args {
                    visit_term(oa, programs, out);
                }
                for a in args {
                    visit_term(a, programs, out);
                }
            }

            Term::Binder(_, bindings, inner) => {
                for (_, term) in bindings.as_ref() {
                    visit_term(term, programs, out);
                }
                visit_term(inner, programs, out);
            }

            Term::Let(bindings, inner) => {
                for (_, term) in bindings.as_ref() {
                    visit_term(term, programs, out);
                }
                visit_term(inner, programs, out);
            }

            Term::Var(_, sort_term) => {
                // Sorts can appear freely: traverse the attached sort term
                visit_term(sort_term, programs, out);
            }

            Term::Sort(s) => visit_sort(s, programs, out),

            Term::Const(_) => {}
        }
    }

    let mut calls = IndexSet::new();
    visit_term(term, programs, &mut calls);
    calls
}

pub fn elaborate_rule(
    pool: &mut PrimitivePool,
    rule: &RuleDefinition,
    programs: &IndexMap<String, Program>,
    decl_consts: &IndexMap<String, DeclConst>,
) -> Vec<RuleDefinition> {
    // Gather all instantiations triggered by *this* rule, calling defunc only once per term.
    let mut instations = IndexSet::new();

    // defunctionalization over premises (single pass)
    for prem in &rule.premises {
        instations.extend(search_programs(prem, programs));
    }

    instations.extend(search_programs(&rule.conclusion, programs));

    // Base case of the saturation: no new programs to specialize; just normalize and return this rule.
    if instations.is_empty() {
        let mut normalized = rule.clone();
        for p in normalized.premises.iter_mut() {
            *p = interpret_eunoia(pool, &decl_consts, p.clone());
        }
        normalized.conclusion = interpret_eunoia(pool, &decl_consts, normalized.conclusion.clone());
        return vec![normalized];
    }

    // Otherwise, we *saturate* by:
    //  1) specializing/compiling programs for each instantiation, and recursively elaborating them;
    //  2) removing positional args (for that program's HO signature) + interpreting this rule, then recursively elaborating it;
    // Recursion bottoms out when a branch yields no instations.
    let mut out: Vec<RuleDefinition> = Vec::new();

    for (program_name, args) in instations {
        let program = match programs.get(&program_name) {
            Some(p) => p,
            None => continue, // defensively skip if missing
        };

        let mut high_order_unifications = vec![];

        // Let's see if we can eliminate high-order parameters
        for (index, arg) in args.iter().enumerate() {
            for (lhs, _) in program.patterns.iter() {
                let Term::App(_, patts) = &**lhs else {
                    unreachable!()
                };
                if let Some(unifier) = unify_pattern_bidirectional(&patts[index], arg) {
                    let (left, _) = unifier;
                    let first_unified = left.iter().find_map(|(unified_left, unified_right)| {
                        if let Term::Sort(Sort::Function(_)) = &*pool.sort(&unified_right) {
                            Some((unified_left, unified_right))
                        } else {
                            None
                        }
                    });

                    if let Some(first_unified) = first_unified {
                        high_order_unifications
                            .push((first_unified.0.clone(), first_unified.1.clone()));
                        break;
                    }
                }
            }
        }

        println!("{:?}", high_order_unifications);

        // Build positional signature (indices of higher-order params) once per program.
        // let mut positional_signature = Vec::new();
        // let mut flat_signature = Vec::new();
        // for (idx, sort) in program.signature.iter().enumerate() {
        //     if let Some(Sort::Function(_)) = sort.as_sort() {
        //         positional_signature.push(idx);
        //     } else {
        //         flat_signature.push(sort.clone());
        //     }
        // }

        // // Split params into: function-typed -> func_args (LHS of substitution), others -> parameters.
        // let mut func_args: Vec<Rc<Term>> = Vec::new();
        // let mut parameters = IndexMap::new();
        // for (name, decl) in program.parameters.iter() {
        //     if let Some(Sort::Function(_)) = decl.term.as_sort() {
        //         func_args.push(pool.add(Term::Var(name.to_owned(), decl.term.clone())));
        //     } else {
        //         parameters.insert(name.to_owned(), decl.clone());
        //     }
        // }

        // // Substitute function-typed parameters with the collected constants.
        // let subs: IndexMap<Rc<Term>, Rc<Term>> =
        //     func_args.into_iter().zip(constants.clone()).collect();
        // let mut substitution = Substitution::new(pool, subs).expect("valid substitution");

        // // Materialize specialized (lhs, rhs) patterns with positional args removed and interpreted.
        // let mut patterns: Vec<(Rc<Term>, Rc<Term>)> = Vec::with_capacity(program.patterns.len());
        // for (lhs0, rhs0) in &program.patterns {
        //     let lhs = remove_positional_args(pool, lhs0, &program_name, &positional_signature);
        //     let lhs = substitution.apply(pool, &lhs);

        //     let rhs = remove_positional_args(pool, rhs0, &program_name, &positional_signature);
        //     let rhs = substitution.apply(pool, &rhs);
        //     let rhs = interpret_eunoia(pool, &decl_consts, rhs);

        //     patterns.push((lhs, rhs));
        // }

        // // Compile the specialized program into rules and *recursively elaborate* them to saturation.
        // let compiled = compile_program(
        //     pool,
        //     &Program {
        //         name: format!("{}@{}", program.name, rule.name),
        //         parameters,
        //         patterns,
        //         signature: flat_signature,
        //     },
        // );

        // for r in compiled {
        //     out.extend(elaborate_rule(pool, &r, programs, decl_consts));
        // }

        // // Also push a version of the *current* rule with positional args removed & interpreted,
        // // then recursively elaborate *that* as well (this propagates defunc into nested spots).
        // let mut updated = rule.clone();
        // for prem in updated.premises.iter_mut() {
        //     let t = remove_positional_args(pool, prem, &program_name, &positional_signature);
        //     *prem = interpret_eunoia(pool, &decl_consts, t);
        // }
        // let c = remove_positional_args(
        //     pool,
        //     &updated.conclusion,
        //     &program_name,
        //     &positional_signature,
        // );
        // updated.conclusion = interpret_eunoia(pool, &decl_consts,  c);

        // out.extend(elaborate_rule(pool, &updated, programs, decl_consts));
    }

    out
}
