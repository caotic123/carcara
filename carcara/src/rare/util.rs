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