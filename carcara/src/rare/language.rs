use std::fmt;

use rug::Integer;

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub enum ConstType {
    Var,
    Bool,
    Integer,
    ConstrType(String),
    Operator,
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct Constructor {
    pub(crate) constr: (String, Vec<ConstType>),
}

#[derive(Clone, PartialEq, Hash, Debug, Eq)]
pub enum EggExpr {
    App(Box<EggExpr>, Box<EggExpr>),
    Op(String),
    Var(String),
    Bool(bool),
    Num(Integer),
    String(String),
    Const(String),
    Real(Integer),
    Mk(Box<EggExpr>),
    BitVec(Integer, Integer),
    Literal(String),
    Ground(Box<EggExpr>),
    Equal(Box<EggExpr>, Box<EggExpr>),
    Distinct(Box<EggExpr>, Box<EggExpr>),
    Union(Box<EggExpr>, Box<EggExpr>),
    Args(Box<EggExpr>, Box<EggExpr>),
    Call(String, Vec<EggExpr>),
    Empty(),
}

#[derive(Clone, Hash, PartialEq, Eq)]
pub enum EggStatement {
    Sort(String, String, Box<EggExpr>),
    DataType(String, Vec<Constructor>),
    Relation(String, ConstType),
    Premise(String, Box<EggExpr>),
    Let(String, Box<EggExpr>),
    Rewrite(Box<EggExpr>, Box<EggExpr>, Vec<EggExpr>),
    Union(Box<EggExpr>, Box<EggExpr>),
    Rule(Vec<EggExpr>, Vec<EggExpr>),
    Check(Box<EggExpr>),
    Constructor(String, Vec<ConstType>, ConstType),
    Call(Box<EggExpr>),
    Run(i16),
    Saturare(),
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

#[macro_export]
macro_rules! literal_expr {
    ($name:expr) => {
        $crate::rare::language::EggExpr::Literal(($name).to_string())
    };
}

#[macro_export]
macro_rules! mk_expr {
    ($inner:expr) => {
        $crate::rare::language::EggExpr::Mk(Box::new($inner))
    };
}

#[macro_export]
macro_rules! empty_expr {
    () => {
        $crate::rare::language::EggExpr::Empty()
    };
}

#[macro_export]
macro_rules! call_expr {
    ($op:expr) => {
        $crate::rare::language::EggExpr::Call(($op).into(), Vec::new())
    };
    ($op:expr; $($arg:expr),* $(,)?) => {
        $crate::rare::language::EggExpr::Call(($op).into(), vec![$($arg),*])
    };
}

#[macro_export]
macro_rules! assoc_expr {
    ($arg:expr) => {
        $crate::call_expr!("Assoc"; $arg)
    };
}

#[macro_export]
macro_rules! args_chain {
    ($head:expr; $tail:expr) => {
        $crate::rare::language::EggExpr::Args(Box::new($head), Box::new($tail))
    };
    ($head:expr, $($rest:expr),+; $tail:expr) => {
        $crate::rare::language::EggExpr::Args(
            Box::new($head),
            Box::new($crate::args_chain!($($rest),+; $tail)),
        )
    };
}

#[macro_export]
macro_rules! list_expr {
    ($head:expr) => {
        $crate::args_chain!($head; $crate::empty_expr!())
    };
    ($head:expr, $($tail:expr),+ $(,)?) => {
        $crate::args_chain!($head, $($tail),+; $crate::empty_expr!())
    };
}

#[macro_export]
macro_rules! available_expr {
    ($term:expr) => {
        $crate::call_expr!("Avaliable"; $term)
    };
}

#[macro_export]
macro_rules! push_rewrite {
    ($decls:expr, $lhs:expr, $rhs:expr) => {{
        $decls.push($crate::rare::language::EggStatement::Rewrite(
            Box::new($lhs),
            Box::new($rhs),
            Vec::new(),
        ));
    }};
    ($decls:expr, $lhs:expr, $rhs:expr; when $($cond:expr),+ $(,)?) => {{
        let mut conditions = Vec::new();
        $(conditions.push($cond);)+
        $decls.push($crate::rare::language::EggStatement::Rewrite(
            Box::new($lhs),
            Box::new($rhs),
            conditions,
        ));
    }};
}
