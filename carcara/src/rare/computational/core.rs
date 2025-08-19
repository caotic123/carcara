use crate::ast::{BindingList, PrimitivePool, Rc, Sort, Term, TermPool};
// condition -> action sugar
#[macro_export]
macro_rules! map_case {
    // With bindings in a closure-style pattern param
    ($pat:tt = $var:tt -> |$bind:pat_param| $body:expr) => {{
        match $crate::match_term!($pat = $var) {
            Some($bind) => Some($body),
            None => None,
        }
    }};
    // No bindings
    ($pat:tt = $var:tt -> $body:expr) => {{
        if $crate::match_term!($pat = $var).is_some() { Some($body) } else { None }
    }};
}

#[macro_export]
macro_rules! mappers {
    ( $( $pat:tt -> |$bind:pat_param| $body:expr ),+ $(,)? ) => {{
        vec![
            $(
                Box::new(|t: &Rc<$crate::ast::Term>| {
                    $crate::map_case!($pat = t -> |$bind| $body)
                }) as Box<dyn Fn(&Rc<$crate::ast::Term>) -> Option<Rc<$crate::ast::Term>>>
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

// --- pre-order mapper using the above rules ----------------------------------
pub fn map_by_matchers(
    pool: &mut PrimitivePool,
    term: &Rc<Term>,
    matchers: &[Box<dyn Fn(&Rc<Term>) -> Option<Rc<Term>>>],
) -> Rc<Term> {
    fn apply_rules(
        t: &Rc<Term>,
        ms: &[Box<dyn Fn(&Rc<Term>) -> Option<Rc<Term>>>],
    ) -> Option<Rc<Term>> {
        for m in ms {
            if let Some(n) = m(t) {
                return Some(n);
            }
        }
        None
    }

    fn map_sort(
        pool: &mut PrimitivePool,
        s: &Sort,
        ms: &[Box<dyn Fn(&Rc<Term>) -> Option<Rc<Term>>>],
    ) -> (bool, Sort) {
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

    fn map_rec(
        pool: &mut PrimitivePool,
        t: &Rc<Term>,
        ms: &[Box<dyn Fn(&Rc<Term>) -> Option<Rc<Term>>>],
    ) -> Rc<Term> {
        let node = if let Some(n) = apply_rules(t, ms) {
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

fn interpret_eunoia(pool: &mut PrimitivePool, term: &Rc<Term>) -> Rc<Term> {
    let rules = mappers![
        (not (not x)) -> |x| x.clone(),
      
    ];

    let rewritten = map_by_matchers(pool, &term, &rules);
    return rewritten
}
