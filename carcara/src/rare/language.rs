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
    Var(u64),
    Const(String),
    Bool(bool),
    Num(Integer),
    String(String),
    Real((Integer, Integer)),
    Mk(Box<EggExpr>),
    BitVec(Integer, Integer),
    Literal(String),
    Ground(Box<EggExpr>),
    Equal(Box<EggExpr>, Box<EggExpr>),
    Distinct(Box<EggExpr>, Box<EggExpr>),
    Union(Box<EggExpr>, Box<EggExpr>),
    Args(Box<EggExpr>, Box<EggExpr>),
    Call(String, Vec<EggExpr>),
    Set(Box<EggExpr>, Box<EggExpr>),
    Empty(),
}

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub enum EggStatement {
    Sort(String, String, Box<EggExpr>),
    DataType(String, Vec<Constructor>),
    Relation(String, Vec<ConstType>),
    Function {
        name: String,
        inputs: Vec<ConstType>,
        output: ConstType,
        merge: Option<EggExpr>,
    },
    Ruleset(String),
    Premise(String, Box<EggExpr>),
    Let(String, Box<EggExpr>),
    Rewrite(Box<EggExpr>, Box<EggExpr>, Vec<EggExpr>),
    Union(Box<EggExpr>, Box<EggExpr>),
    Rule {
        ruleset: Option<String>,
        body: Vec<EggExpr>,
        head: Vec<EggExpr>,
    },
    Check(Box<EggExpr>),
    Constructor(String, Vec<ConstType>, ConstType),
    Call(Box<EggExpr>),
    Run {
        ruleset: Option<String>,
        iterations: i16,
    },
    Saturate {
        ruleset: Option<String>,
    },
    Raw(String),
}

pub type EggLanguage = Vec<EggStatement>;

impl fmt::Display for ConstType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConstType::Var => write!(f, "i32"),
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
macro_rules! egg_expr {
    (@GET_OP _and) => { "@and" };
    (@GET_OP _or) => { "@or" };
    (@GET_OP _not) => { "@not" };
    (@GET_OP _xor) => { "@xor" };
    (@GET_OP _implies) => { "@=>" };
    (@GET_OP _eq) => { "@=" };
    (@GET_OP _distinct) => { "@distinct" };
    (@GET_OP _lt) => { "@<" };
    (@GET_OP _gt) => { "@>" };
    (@GET_OP _le) => { "@<=" };
    (@GET_OP _ge) => { "@>=" };
    (@GET_OP _add) => { "@+" };
    (@GET_OP _sub) => { "@-" };
    (@GET_OP _mul) => { "@*" };
    (@GET_OP _div) => { "@/" };
    (@GET_OP _intdiv) => { "@div" };
    (@GET_OP _mod) => { "@mod" };
    (@GET_OP _abs) => { "@abs" };
    (@GET_OP _div_total) => { "@/_total" };
    (@GET_OP _to_real) => { "@to_real" };
    (@GET_OP _less_or_equal_var) => { "@$less_or_equal_var" };
    (@GET_OP _is_not_num) => { "@$is_not_num" };
    (@GET_OP set_empty) => { "set-empty" };
    (@GET_OP set_insert) => { "set-insert" };
    (@GET_OP Assoc) => { "Assoc" };
    (@GET_OP Available) => { "Available" };
    (@GET_OP to_formula) => { "to_formula" };
    (@GET_OP to_formula_rel) => { "to_formula_rel" };
    (@GET_OP $op:ident) => { stringify!($op) };
    (@GET_OP $op:literal) => { $op };

    (()) => { $crate::rare::language::EggExpr::Empty() };
    (true) => { $crate::rare::language::EggExpr::Bool(true) };
    (false) => { $crate::rare::language::EggExpr::Bool(false) };
    ($lit:literal) => { $crate::rare::language::EggExpr::Literal(($lit).to_string()) };
    ({$expr:expr}) => { $expr };

    ((var $name:tt)) => { $crate::rare::language::EggExpr::Var(egg_expr!(@GET_OP $name).to_string()) };
    ((mk $inner:tt)) => { $crate::rare::language::EggExpr::Mk(Box::new(egg_expr!($inner))) };
    ((args $head:tt $tail:tt)) => { $crate::rare::language::EggExpr::Args(Box::new(egg_expr!($head)), Box::new(egg_expr!($tail))) };
    ((= $lhs:tt $rhs:tt)) => { $crate::rare::language::EggExpr::Equal(Box::new(egg_expr!($lhs)), Box::new(egg_expr!($rhs))) };
    ((== $lhs:tt $rhs:tt)) => { $crate::rare::language::EggExpr::Distinct(Box::new(egg_expr!($lhs)), Box::new(egg_expr!($rhs))) };
    ((union $lhs:tt $rhs:tt)) => { $crate::rare::language::EggExpr::Union(Box::new(egg_expr!($lhs)), Box::new(egg_expr!($rhs))) };
    ((set $lhs:tt $rhs:tt)) => { $crate::rare::language::EggExpr::Set(Box::new(egg_expr!($lhs)), Box::new(egg_expr!($rhs))) };
    ((ground $inner:tt)) => { $crate::rare::language::EggExpr::Ground(Box::new(egg_expr!($inner))) };
    ((app $func:tt $arg:tt)) => { $crate::rare::language::EggExpr::App(Box::new(egg_expr!($func)), Box::new(egg_expr!($arg))) };
    (($op:tt)) => { $crate::rare::language::EggExpr::Call(egg_expr!(@GET_OP $op).into(), Vec::new()) };
    (($op:tt $($args:tt)+)) => { $crate::rare::language::EggExpr::Call(egg_expr!(@GET_OP $op).into(), vec![$(egg_expr!($args)),+]) };
}

#[macro_export]
macro_rules! egg_args {
    ($elem:tt) => { egg_expr!((args $elem ())) };
    ($head:tt, $($rest:tt),+ $(,)?) => { $crate::rare::language::EggExpr::Args(Box::new(egg_expr!($head)), Box::new(egg_args!($($rest),+))) };
}
