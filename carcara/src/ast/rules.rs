use std::rc::Rc;

use super::{Constant, Operator};

#[derive(Debug, Clone)]
pub enum RuleArg {
    TypeArg(String, String),
    UnitArg(String, String),
    ListArg(String, String),
}

#[derive(Debug, Clone)]
pub enum RareTerm {
    Const(Constant),

    /// A variable, consisting of an identifier and a sort.
    Var(String),

    /// An application of a bulit-in operator to one or more terms.
    Op(Operator),

    /// An application of a function to one or more terms.
    App(Rc<RareTerm>, Vec<Rc<RareTerm>>),
}

#[derive(Debug, Clone)]
pub struct RuleDefinition {
    name: String,
    parameters: Vec<RuleArg>,
    conclusion: RareTerm 
}

pub type Rules = Vec<RuleDefinition>;

