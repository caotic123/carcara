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
    const PRIME:        u32 = 0x0100_0193;

    let mut hash = OFFSET_BASIS;
    for byte in input.as_bytes().as_ref() {
        hash ^= *byte as u32;
        hash = hash.wrapping_mul(PRIME);
    }
    hash
}