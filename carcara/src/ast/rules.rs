use std::rc::Rc;

use super::{Constant, Operator};


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
pub enum AttributeParameters {
    List,
    None
}

#[derive(Debug, Clone)]
pub struct TypeParameter {
    pub term: Rc<RareTerm>,
    pub attribute: AttributeParameters
}

#[derive(Debug, Clone)]
pub struct RuleDefinition {
    pub name: String,
    pub parameters: Vec<TypeParameter>,
    pub arguments: Vec<String>,
    pub premises: Vec<Rc<RareTerm>>,
    pub conclusion: Rc<RareTerm> 
}

pub type Rules = Vec<RuleDefinition>;

