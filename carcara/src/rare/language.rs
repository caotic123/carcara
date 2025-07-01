use std::fmt;

use rug::Integer;

#[derive(Clone)]
pub enum ConstType {
    Var,
    Bool,
    Integer,
    ConstrType(String),
    Operator,
}

#[derive(Clone)]
pub struct Constructor {
    pub(crate) constr: (String, Vec<ConstType>),
}

#[derive(Clone, PartialEq, Eq)]
pub enum EggExpr {
    App(Box<EggExpr>, Box<EggExpr>),
    Op(String),
    Var(String),
    Bool(bool),
    Num(Integer),
    String(String),
    Real(Integer),
    Mk(Box<EggExpr>),
    BitVec(Integer, Integer),
    Literal(String),
    Ground(Box<EggExpr>),
    Equal(Box<EggExpr>, Box<EggExpr>),
    Union(Box<EggExpr>, Box<EggExpr>),
    Args(Box<EggExpr>, Box<EggExpr>),
    Call(String, Box<EggExpr>),
    Empty()
}

#[derive(Clone)]
pub enum EggStatement {
    DataType(String, Vec<Constructor>),
    Relation(String, ConstType),
    Premise(String, Box<EggExpr>),
    Let(String, Box<EggExpr>),
    Rewrite(Box<EggExpr>, Box<EggExpr>, Vec<EggExpr>),
    Union(Box<EggExpr>, Box<EggExpr>),
    Rule(Vec<EggExpr>, Vec<EggExpr>),
    Check(Box<EggExpr>),
    Constructor(String, Vec<ConstType>, ConstType),
    Run(i16),
    Saturare()
}

pub type EggLanguage = Vec<EggStatement>;

impl fmt::Display for ConstType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConstType::Var => write!(f, "String"),
            ConstType::Bool => write!(f, "bool"),
            ConstType::Integer => write!(f, "i64"),
            ConstType::Operator => write!(f, "String"),
            ConstType::ConstrType(name) => write!(f, "{}", name),
        }
    }
}

impl fmt::Display for Constructor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (name, args) = &self.constr;
        write!(f, "({}", name)?;
        for arg in args {
            write!(f, " {}", arg)?;
        }
        write!(f, ")")
    }
}
