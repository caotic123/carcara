use indexmap::IndexMap;

use crate::ast::{Operator, PrimitivePool, Rc, Term, TermPool};

pub fn clauses_to_or(pool: &mut PrimitivePool, clauses: &[Rc<Term>]) -> Option<Rc<Term>> {
    if clauses.len() == 0 {
        return None;
    }

    if clauses.len() == 1 {
        return Some(clauses[0].clone());
    }

    return Some(pool.add(Term::Op(Operator::Or, clauses.to_vec())));
}

#[inline]
// 32-bit FNV-1a hash for small strings
pub fn str_to_u32(input: &str) -> u32 {
    const OFFSET_BASIS: u32 = 0x811c_9dc5;
    const PRIME: u32 = 0x0100_0193;

    let mut hash = OFFSET_BASIS;
    for byte in input.as_bytes().as_ref() {
        hash ^= *byte as u32;
        hash = hash.wrapping_mul(PRIME);
    }
    hash
}

pub fn collect_vars(root: &Rc<Term>) -> IndexMap<String, Rc<Term>> {
    fn visit(term: &Rc<Term>, acc: &mut IndexMap<String, Rc<Term>>) {
        match &**term {
            Term::Const(_) | Term::Sort(_) => {}

            Term::Var(name, sort) => {
                // keep the first sort we see for a given identifier
                acc.entry(name.clone()).or_insert_with(|| sort.clone());
            }

            Term::App(fun, args) => {
                visit(fun, acc);
                for arg in args {
                    visit(arg, acc);
                }
            }

            Term::Op(_, args) => {
                for arg in args {
                    visit(arg, acc);
                }
            }

            Term::Binder(_, bindings, body) => {
                // Traverse each binder declaration (identifier + sort) …
                for (id, sort) in bindings {
                    acc.entry(id.clone()).or_insert_with(|| sort.clone());
                    visit(sort, acc);
                }
                // … and then its body.
                visit(body, acc);
            }

            Term::Let(bindings, body) => {
                for (id, sort) in bindings {
                    acc.entry(id.clone()).or_insert_with(|| sort.clone());
                    visit(sort, acc);
                }
                visit(body, acc);
            }

            Term::ParamOp { op_args, args, .. } => {
                for t in op_args.iter().chain(args) {
                    visit(t, acc);
                }
            }
        }
    }

    let mut map = IndexMap::<String, Rc<Term>>::new();
    visit(&root, &mut map);
    map.into_iter().collect()
}

