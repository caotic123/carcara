use indexmap::{IndexMap, IndexSet};

use crate::{ast::{
    BindingList, PrimitivePool, Rc, Sort, Substitution, Term, TermPool, rare_rules::{DeclAttr, DeclConst}
}, egg_expr, rare::{computational::{aci_norm, arith_poly_norm, distinct_elim, evaluation}, engine::EggFunctions, language::{EggExpr, EggStatement}}};

// Add this type alias near the top of the module:
type Matcher<'a> = dyn Fn(&Rc<Term>, &mut PrimitivePool) -> Option<Rc<Term>> + 'a;

// condition -> action sugar
#[macro_export]
macro_rules! map_case {
    // With bindings in a closure-style pattern param
    ($pat:tt = $var:tt -> |$bind:pat_param| $body:expr) => {{
        match $crate::match_term!($pat = $var) {
            Some($bind) => $body,
            None => None,
        }
    }};
    // No bindings
    ($pat:tt = $var:tt -> $body:expr) => {{
        if $crate::match_term!($pat = $var).is_some() {
            Some($body)
        } else {
            None
        }
    }};
}

#[macro_export]
macro_rules! mappers {
    ( $( $pat:tt -> |$pool:pat_param| |$bind:pat_param| $body:expr ),+ $(,)? ) => {{
        vec![
            $(
                Box::new(|t: &Rc<$crate::ast::Term>, $pool | {
                    $crate::map_case!($pat = t -> |$bind| $body)
                })
            ),+
        ]
    }};
    ( $( $pat:tt -> $body:expr ),+ $(,)? ) => {{
        vec![
            $(
                Box::new(|t: &Rc<$crate::ast::Term>| {
                    $crate::map_case!($pat = t -> $body)
                }) as Box<dyn Fn(&Rc<$crate::ast::Term>) -> Option<Rc<$crate::ast::Term>>>
            ),+
        ]
    }};
}

pub fn map_by_matchers<'a>(
    pool: &mut PrimitivePool,
    term: &Rc<Term>,
    matchers: &[Box<Matcher<'a>>],
) -> Rc<Term> {
    fn apply_rules<'a>(
        t: &Rc<Term>,
        pool: &mut PrimitivePool,
        ms: &[Box<Matcher<'a>>],
    ) -> Option<Rc<Term>> {
        for m in ms {
            if let Some(n) = m(t, pool) {
                return Some(n);
            }
        }
        None
    }

    fn map_sort<'a>(pool: &mut PrimitivePool, s: &Sort, ms: &[Box<Matcher<'a>>]) -> (bool, Sort) {
        let mut map_vec = |v: &Vec<Rc<Term>>| -> (bool, Vec<Rc<Term>>) {
            let mut changed = false;
            let mut out = Vec::with_capacity(v.len());
            for t in v {
                let nt = map_rec(pool, t, ms);
                if *t != nt {
                    changed = true;
                }
                out.push(nt);
            }
            (changed, out)
        };
        match s {
            Sort::Function(ts) => {
                let (c, nts) = map_vec(ts);
                if c {
                    (true, Sort::Function(nts))
                } else {
                    (false, s.clone())
                }
            }
            Sort::Atom(name, ts) => {
                let (c, nts) = map_vec(ts);
                if c {
                    (true, Sort::Atom(name.clone(), nts))
                } else {
                    (false, s.clone())
                }
            }
            Sort::Array(a, b) => {
                let na = map_rec(pool, a, ms);
                let nb = map_rec(pool, b, ms);
                if *a != na || *b != nb {
                    (true, Sort::Array(na, nb))
                } else {
                    (false, s.clone())
                }
            }
            Sort::ParamSort(ts, inner) => {
                let (c1, nts) = map_vec(ts);
                let ninner = map_rec(pool, inner, ms);
                if c1 || *inner != ninner {
                    (true, Sort::ParamSort(nts, ninner))
                } else {
                    (false, s.clone())
                }
            }
            Sort::BitVec(_)
            | Sort::Bool
            | Sort::Int
            | Sort::Real
            | Sort::String
            | Sort::RegLan
            | Sort::RareList
            | Sort::Type
            | Sort::Var(_) => (false, s.clone()),
        }
    }

    fn map_rec<'a>(pool: &mut PrimitivePool, t: &Rc<Term>, ms: &[Box<Matcher<'a>>]) -> Rc<Term> {
        let node = if let Some(n) = apply_rules(t, pool, ms) {
            n
        } else {
            t.clone()
        };

        match &*node {
            Term::Const(_) => node,

            Term::Var(name, sort) => {
                let nsort = map_rec(pool, sort, ms);
                if *nsort != **sort {
                    pool.add(Term::Var(name.clone(), nsort))
                } else {
                    node
                }
            }

            Term::Sort(s) => {
                let (changed, ns) = map_sort(pool, s, ms);
                if changed {
                    pool.add(Term::Sort(ns))
                } else {
                    node
                }
            }

            Term::Op(op, args) => {
                let mut changed = false;
                let mut nargs = Vec::with_capacity(args.len());
                for a in args {
                    let na = map_rec(pool, a, ms);
                    if *na != **a {
                        changed = true;
                    }
                    nargs.push(na);
                }
                if changed {
                    pool.add(Term::Op(*op, nargs))
                } else {
                    node
                }
            }

            Term::App(head, args) => {
                let nhead = map_rec(pool, head, ms);
                let mut changed = *nhead != **head;
                let mut nargs = Vec::with_capacity(args.len());
                for a in args {
                    let na = map_rec(pool, a, ms);
                    if *na != **a {
                        changed = true;
                    }
                    nargs.push(na);
                }
                if changed {
                    pool.add(Term::App(nhead, nargs))
                } else {
                    node
                }
            }

            Term::ParamOp { op, op_args, args } => {
                let mut changed = false;
                let mut nop_args = Vec::with_capacity(op_args.len());
                for oa in op_args {
                    let no = map_rec(pool, oa, ms);
                    if *no != **oa {
                        changed = true;
                    }
                    nop_args.push(no);
                }
                let mut nargs = Vec::with_capacity(args.len());
                for a in args {
                    let na = map_rec(pool, a, ms);
                    if *na != **a {
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
                    node
                }
            }

            Term::Binder(b, bindings, inner) => {
                let mut changed = false;
                let mut nbindings = Vec::with_capacity(bindings.0.len());
                for (nm, srt) in bindings.0.iter() {
                    let ns = map_rec(pool, srt, ms);
                    if *ns != **srt {
                        changed = true;
                    }
                    nbindings.push((nm.clone(), ns));
                }
                let ninner = map_rec(pool, inner, ms);
                if *ninner != **inner {
                    changed = true;
                }
                if changed {
                    pool.add(Term::Binder(*b, BindingList(nbindings), ninner))
                } else {
                    node
                }
            }

            Term::Let(bindings, body) => {
                let mut changed = false;
                let mut nbindings = Vec::with_capacity(bindings.0.len());
                for (nm, val) in bindings.0.iter() {
                    let nv = map_rec(pool, val, ms);
                    if *nv != **val {
                        changed = true;
                    }
                    nbindings.push((nm.clone(), nv));
                }
                let nbody = map_rec(pool, body, ms);
                if *nbody != **body {
                    changed = true;
                }
                if changed {
                    pool.add(Term::Let(BindingList(nbindings), nbody))
                } else {
                    node
                }
            }
        }
    }

    map_rec(pool, term, matchers)
}

pub fn interpret_eunoia(
    pool: &mut PrimitivePool,
    constants: &IndexMap<String, DeclConst>,
    term: Rc<Term>,
) -> Rc<Term> {
    let rules: Vec<Box<Matcher<'_>>> = mappers![
    // typeof
    (eo::typeof x) -> |pool| |x| Some(pool.sort(x).clone()),
    // nil
    (eo::nil f x) -> |pool| |(f, x)| {
        if let Some(constant_name) = f.as_var() {
            if let Some(c) = constants.get(constant_name)  {
                // 1) Find a RightAssocNil attribute (template for the nil terminator)
                let nil_templ = c.attrs.iter().find_map(|a| match a {
                    DeclAttr::RightAssocNil(t) => Some(t.clone()),
                    _ => None,
                })?;

                // 2) Non-parameterized => just return the ground nil
                if !c.is_parameterized {
                    return Some(nil_templ);
                }

                // 3) Extract the return-sort template of the constant `f`
                let ret_templ = match c.sort.as_ref() {
                    Term::Sort(Sort::Function(args)) => args.last().cloned(),
                    _ => None,
                }?;

                let mut param_names: IndexSet<String> = IndexSet::new();
                let mut name_to_var: IndexMap<String, Rc<Term>> = IndexMap::new();

                // type variables like (T Type)
                for p in &c.parametrized_params {
                    if let Some(name) = &p.var_name {
                        param_names.insert(name.clone());
                        let v = pool.add((name.clone(), p.base_sort.clone()).into());
                        name_to_var.insert(name.clone(), v);
                    }
                }
                // term params like (m Int), functions, etc.
                for p in &c.ty_params {
                    if let Some(name) = &p.var_name {
                        param_names.insert(name.clone());
                        let v = pool.add((name.clone(), p.base_sort.clone()).into());
                        name_to_var.insert(name.clone(), v);
                    }
                }

                // 6) Unifier that also unwraps ParamSort on BOTH sides
                fn unify_params(
                    _pool: &mut dyn TermPool,
                    templ: &Rc<Term>,
                    actual: &Rc<Term>,
                    params: &IndexSet<String>,
                    env: &mut IndexMap<String, Rc<Term>>,
                ) -> bool {
                    if let Some(v) = templ.as_var() {
                        if params.contains(v) {
                            if let Some(bound) = env.get(v) {
                                return bound == actual;
                            } else {
                                env.insert(v.to_owned(), actual.clone());
                                return true;
                            }
                        }
                    }
                    match (templ.as_ref(), actual.as_ref()) {
                        (Term::Sort(Sort::ParamSort(_, t1)), Term::Sort(Sort::ParamSort(_, t2))) => {
                            unify_params(_pool, t1, t2, params, env)
                        }
                        (Term::Sort(Sort::ParamSort(_, t1)), _) => {
                            unify_params(_pool, t1, actual, params, env)
                        }
                        (_, Term::Sort(Sort::ParamSort(_, t2))) => {
                            unify_params(_pool, templ, t2, params, env)
                        }

                        (Term::Sort(Sort::Atom(s1, a1)), Term::Sort(Sort::Atom(s2, a2))) => {
                            if s1 != s2 || a1.len() != a2.len() { return false; }
                            a1.iter().zip(a2.iter())
                              .all(|(t1, t2)| unify_params(_pool, t1, t2, params, env))
                        }
                        (Term::Sort(Sort::Function(a1)), Term::Sort(Sort::Function(a2))) => {
                            if a1.len() != a2.len() { return false; }
                            a1.iter().zip(a2.iter())
                              .all(|(t1, t2)| unify_params(_pool, t1, t2, params, env))
                        }
                        (Term::Sort(Sort::Array(x1, y1)), Term::Sort(Sort::Array(x2, y2))) => {
                            unify_params(_pool, x1, x2, params, env)
                                && unify_params(_pool, y1, y2, params, env)
                        }

                        _ => templ == actual,
                    }
                }

                let mut env: IndexMap<String, Rc<Term>> = IndexMap::new();
                if !unify_params(pool, &ret_templ, &x, &param_names, &mut env) {
                    return None;
                }

                let mut map: IndexMap<Rc<Term>, Rc<Term>> = IndexMap::new();
                for (name, val) in env {
                    if let Some(var_term) = name_to_var.get(&name) {
                        map.insert(var_term.clone(), val);
                    }
                }
                if let Ok(mut sub) = Substitution::new(pool, map) {
                    let instantiated = sub.apply(pool, &nil_templ);
                    return Some(instantiated);
                }
            }
        }
        None
    }];

    let mut term = term;
    loop {
        let rewritten = map_by_matchers(pool, &term, &rules);
        if term != rewritten {
            term = rewritten;
            continue;
        }
        break;
    }
    term
}


pub fn declare_special_eunoia_eliminations(decls: &mut Vec<EggStatement>, functions: &EggFunctions) {

    // Use centralized ACI operator definitions
    for (_, name, op_with_at, identity) in aci_norm::aci_operators() {
        if functions.names.contains_key(name) {
            decls.extend(aci_norm::aci_rules(op_with_at, identity, functions.assoc_calls.get(op_with_at)));
        }
    }

    decls.extend(arith_poly_norm::arith_poly_norm_rules());
    decls.extend(evaluation::evaluation_rules());
    if functions.names.contains_key("distinct") {
        decls.extend(distinct_elim::distinct_solver_statements());
    }
}