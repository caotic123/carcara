use egg::*;
use indexmap::IndexMap;

use crate::ast::{rules::TypeParameter, Rc, Term};

use super::{language::*, util::str_to_u32};

pub fn make_term<'a>(
    term: &'a mut RecExpr<ENodeOrVar<Rare>>,
    ast: &Rc<Term>,
    vars: &IndexMap<String, TypeParameter>,
) -> (Id, &'a mut RecExpr<ENodeOrVar<Rare>>) {
    let (id, (term, _)) = convert_to_egg_expr((term, vars), ast);
    return (id, term);
}

pub fn make_mk_term<'a>(
    term: &'a mut RecExpr<ENodeOrVar<Rare>>,
    ast: &Rc<Term>,
    vars: &IndexMap<String, TypeParameter>,
) -> ((Id, Id), &'a mut RecExpr<ENodeOrVar<Rare>>) {
    let (id, term) = make_term(term, ast, vars);
    let mk_id = term.add(ENodeOrVar::ENode(Rare::Mk(id)));
    return ((mk_id, id), term);
}

pub fn make_top(term: &mut RecExpr<ENodeOrVar<Rare>>) -> (Id, &mut RecExpr<ENodeOrVar<Rare>>) {
    let id = term.add(ENodeOrVar::ENode(Rare::Symbol("⊤".to_string())));
    return (id, term);
}

pub fn make_any(term: &mut RecExpr<ENodeOrVar<Rare>>) -> (Id, &mut RecExpr<ENodeOrVar<Rare>>) {
    let id = term.add(ENodeOrVar::ENode(Rare::Symbol("any".to_string())));
    return (id, term);
}

pub fn make_static_ground<'a, 'b>(
    name: &'a str,
    term: &'b mut RecExpr<ENodeOrVar<Rare>>,
) ->((Id, Id), &'b mut RecExpr<ENodeOrVar<Rare>>) {
    let name = term.add(ENodeOrVar::ENode(Rare::Symbol(name.to_string())));
    let var_name = term.add(ENodeOrVar::ENode(Rare::Var(name)));
    let id = term.add(ENodeOrVar::ENode(Rare::Ground(var_name)));
    return ((id, var_name), term);
}

pub fn make_ground<'a, 'b>(
    name: &'a str,
    term: &'b mut RecExpr<ENodeOrVar<Rare>>,
) ->((Id, Id), &'b mut RecExpr<ENodeOrVar<Rare>>) {
    let code = str_to_u32(name);
    let var_name = term.add(ENodeOrVar::Var(Var::from_u32(code)));
    let id = term.add(ENodeOrVar::ENode(Rare::Ground(var_name)));
    return ((id, var_name), term);
}
pub enum InhabitantKind {
    Free,
    Ground
}

impl InhabitantKind {
    fn to_rep(self) -> String {
        match self {
            InhabitantKind::Free => "Free",
            InhabitantKind::Ground => "Ground"
        }.to_string()
    }
}

pub fn make_inhabitant<'a, 'b>(
    term: &'b mut RecExpr<ENodeOrVar<Rare>>,
    name: &'a str,
    sort: Rc<Term>,
    kind: InhabitantKind
) -> ((Id, Id, Id), &'b mut RecExpr<ENodeOrVar<Rare>>) {
    let (sort, (term, _)) = convert_to_egg_expr((term, &IndexMap::default()), &sort);
    let var_name = term.add(ENodeOrVar::ENode(Rare::Symbol(name.to_string())));
    let var_name = term.add(ENodeOrVar::ENode(Rare::Var(var_name)));
    let rep = term.add(ENodeOrVar::ENode(Rare::Symbol(kind.to_rep())));
    let inhabitant = term.add(ENodeOrVar::ENode(Rare::Inhabitant([rep, var_name, sort])));
    return ((inhabitant, var_name, sort), term);
}

pub enum InstationKind {
    Var(String),
    Any
}

pub fn make_instantion<'a, 'b>(
    rule_name: String,
    term: &'b mut RecExpr<ENodeOrVar<Rare>>,
    instantions: Vec<InstationKind>,
) -> ((Id, Vec<Id>), &'b mut RecExpr<ENodeOrVar<Rare>>)  {
    let mut ids = vec![term.add(ENodeOrVar::ENode(Rare::Symbol(rule_name)))];
    for inst in instantions {
        match inst {
            InstationKind::Var(name) => {
                let ((id, _), _) = make_ground(&name, term);
                ids.push(id)
            }
            InstationKind::Any => {
                ids.push(make_any(term).0)
            }
        }
    }

    let id= term.add(ENodeOrVar::ENode(Rare::Inst(ids.clone())));
    return ((id, ids), term)
}

pub fn make_typed_instantion<'a, 'b>(
    rule_name: String,
    term: &'b mut RecExpr<ENodeOrVar<Rare>>,
    instantions: Vec<(&String, &Rc<Term>, InhabitantKind)>,
    vars: &IndexMap<String, TypeParameter>
) -> ((Id, Vec<Id>), &'b mut RecExpr<ENodeOrVar<Rare>>)  {
    let mut ids = vec![term.add(ENodeOrVar::ENode(Rare::Symbol(rule_name)))];
    for (name, sort, kind) in instantions {
       let code = str_to_u32(name);
       let name = term.add(ENodeOrVar::Var(Var::from_u32(code)));
       let (sort, _) = make_term(term, sort, vars);
       let rep = term.add(ENodeOrVar::ENode(Rare::Symbol(kind.to_rep())));
       ids.push(term.add(ENodeOrVar::ENode(Rare::Inhabitant([rep, name, sort]))));
    }

    let id= term.add(ENodeOrVar::ENode(Rare::Inst(ids.clone())));
    return ((id, ids), term)
}

pub fn make_arrow<'a, 'b>(
    term: &'b mut RecExpr<ENodeOrVar<Rare>>,
    prepositions: Vec<&Rc<Term>>,
    goal : &Rc<Term>,
    vars: &IndexMap<String, TypeParameter>
) -> (Id, &'b mut RecExpr<ENodeOrVar<Rare>>) {
    if prepositions.len() == 0 {
        let top = make_top(term).0;
        let conclusion = make_term(term,goal, vars).0;
        let head = term.add(ENodeOrVar::ENode(Rare::Forall([top, conclusion])));
        return (head, term)
    }

    let mut prepositions = prepositions.iter();
    let conclusion = make_term(term,goal, vars).0;
    let first_proposition = make_term(term, prepositions.next().unwrap(), vars).0;
    let mut fun = term.add(ENodeOrVar::ENode(Rare::Forall([first_proposition, conclusion])));

    for param in prepositions {
        let proposition = make_term(term, param, vars).0;
        fun = term.add(ENodeOrVar::ENode(Rare::Forall([proposition, fun])));
    }

    return (fun, term);
}