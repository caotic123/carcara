use std::{cell::RefCell, ops::Index};

use indexmap::IndexMap;

use super::{Constant, Operator, Rc, Term};

pub type Holes = IndexMap<String, Rc<RefCell<Option<Rc<Term>>>>>;

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub enum RareTerm {
    Hole(Rc<RefCell<Option<Rc<Term>>>>),

    Const(Constant),

    Var(String),

    Op(Operator),

    App(Rc<RareTerm>, Vec<Rc<RareTerm>>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum AttributeParameters {
    List,
    None,
}

#[derive(Debug, Clone)]
pub struct TypeParameter {
    pub term: Rc<Term>,
    pub attribute: AttributeParameters,
}

#[derive(Debug, Clone)]
pub struct RuleDefinition {
    pub name: String,
    pub parameters: IndexMap<String, TypeParameter>,
    pub arguments: Vec<String>,
    pub premises: Vec<Rc<Term>>,
    pub conclusion: Rc<Term>,
}

pub type Rules = IndexMap<String, RuleDefinition>;

#[macro_export]
macro_rules! match_rareterm {
    // Match App with wildcard function and extract first element from args vector
    (App (*, [?$v:ident]), $term:expr) => {{
        if let RareTerm::App(_, args) = &**$term {
            if !args.is_empty() {
                Some(args[0].clone())
            } else {
                None
            }
        } else {
            None
        }
    }};

    // Match App with wildcard function and multiple captured args
    (App (*, [?$v:ident, ?$w:ident]), $term:expr) => {{
        if let RareTerm::App(_, args) = &**$term {
            if args.len() >= 2 {
                Some((args[0].clone(), args[1].clone()))
            } else {
                None
            }
        } else {
            None
        }
    }};

    // Match Hole with captured value
    (Hole(?$v:ident), $term:expr) => {{
        if let RareTerm::Hole(cell) = &**$term {
            if let Some(term) = &*cell.borrow() {
                Some(term.clone())
            } else {
                None
            }
        } else {
            None
        }
    }};

    // Match Const with captured value
    (Const(?$v:ident), $term:expr) => {{
        if let RareTerm::Const(constant) = &**$term {
            Some(constant.clone())
        } else {
            None
        }
    }};

    // Match Const with captured value
    (Const($v:tt), $term:expr) => {{
        if let RareTerm::Const(Constant::String(name)) = &*$term {
            if name == $v {
                Some(Constant::String(name.clone()))
            } else {
                None
            }
        } else {
            None
        }
    }};

    // Match Var with captured value
    (Var(?$v:ident), $term:expr) => {{
        if let RareTerm::Var(string) = &*$term {
            Some(string.clone())
        } else {
            None
        }
    }};

    // Match Const with captured value
    (Var($v:tt), $term:expr) => {{
        if let RareTerm::Var(name) = &*$term {
            if name == $v {
                Some(RareTerm::Var(name.clone()))
            } else {
                None
            }
        } else {
            None
        }
    }};

    // Match Op with captured value
    (Op(?$v:ident), $term:expr) => {{
        if let RareTerm::Op(operator) = &**$term {
            Some(operator.clone())
        } else {
            None
        }
    }}; // Add more variants as needed

    (Type(?$v:ident), $term:expr) => {{
        match &*$term {
            RareTerm::App(_, args) if args.len() == 1 => match &*args[0] {
                RareTerm::Var(name) => Some(name.clone()),
                _ => None,
            },
            _ => None,
        }
    };};
}
