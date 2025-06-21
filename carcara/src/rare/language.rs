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
    Run(i16),
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

impl fmt::Display for EggExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EggExpr::App(func, arg) => {
                write!(f, "(App ")?;
                write!(f, "{}", func)?;
                write!(f, " {}", arg)?;
                write!(f, ")")
            }
            EggExpr::Op(name) => write!(f, "(Op \"{}\")", name),
            EggExpr::Mk(term) => write!(f, "(Mk {})", term),
            EggExpr::Var(name) => write!(f, "(Var \"{}\")", name),
            EggExpr::Bool(b) => write!(f, "(Bool {})", if *b { "true" } else { "false" }),
            EggExpr::Num(n) => write!(f, "(Num {})", n),
            EggExpr::BitVec(i, j) => write!(f, "(Bitvec {} {})", i, j),
            EggExpr::Real(i) => write!(f, "(Real {})", i),
            EggExpr::String(s) => write!(f, "(String {})", s),
            EggExpr::Literal(s) => write!(f, "{}", s),
            EggExpr::Equal(x, y) => write!(f, "(= {} {})", x, y),
            EggExpr::Ground(expr) => write!(f, "(Ground {})", expr),
            EggExpr::Union(left, rhs) => write!(f, "(union {} {})", left, rhs),
        }
    }
}

impl fmt::Display for EggStatement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EggStatement::DataType(name, ctors) => {
                write!(f, "(datatype {}", name)?;
                for ctor in ctors {
                    write!(f, " {}", ctor)?;
                }
                write!(f, ")")
            }
            EggStatement::Relation(name, type_) => write!(f, "(relation {} ({}))", name, type_),
            EggStatement::Premise(name, expr) => write!(f, "({} {})", name, expr),
            EggStatement::Rewrite(lhs, rhs, premises) => {
                write!(f, "(rewrite")?;
                write!(f, " {}", rhs)?;
                write!(f, " {}", lhs)?;
                if premises.len() != 0 {
                    write!(f, " :when ( ")?;
                    for p in premises.iter() {
                        write!(f, "{} ", p)?;
                    }
                    write!(f, ")")?;
                }
                write!(f, ")")
            }
            EggStatement::Check(expr) => write!(f, "(check {})", expr),
            EggStatement::Rule(cond, action) => {
                write!(f, "(rule ( ",)?;
                for ctor in cond {
                    write!(f, "{} ", ctor)?;
                }
                write!(f, ") (")?;
                for ctor in action {
                    write!(f, "{} ", ctor)?;
                }
                write!(f, ") )")
            }
            EggStatement::Union(expr, expr2) => write!(f, "(union {} {})", expr, expr2),
            EggStatement::Let(s, expr) => write!(f, "(let {} {})", s, expr),
            EggStatement::Run(i) => write!(f, "(run {})", i),
        }
    }
}
