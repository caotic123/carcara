use super::{Constant, Operator, Rc, Sort};

#[derive(Debug, Clone)]
pub enum RareTerm {
    Const(Constant),

    /// A variable, consisting of an identifier and a sort.
    Var(String, Rc<RareTerm>),

    /// An application of a function to one or more terms.
    App(Rc<RareTerm>, Vec<Rc<RareTerm>>),

    /// An application of a bulit-in operator to one or more terms.
    Op(Operator, Vec<Rc<RareTerm>>),

    /// A sort.
    Sort(Sort)
}

#[derive(Debug, Clone)]
pub struct RuleDefinition {
    name: String,
    body: RareTerm 
}

pub type Rules = Vec<RuleDefinition>;

