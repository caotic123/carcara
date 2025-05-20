use core::panic;

use crate::{
    ast::{
        rules::{Rules, TypeParameter},
        Constant, Operator, PrimitivePool, ProofNode, Rc, Sort, Term,
    },
    rare::util::collect_vars,
};
use indexmap::{IndexMap, IndexSet};
use rug::{Integer, Rational};

use egg::*;

use super::util::str_to_u32;

define_language! {
    pub enum Rare {
        Num(Integer),
        Symbol(String),
        Bool(bool),
        Rational(Rational),
        "Op" = Op(Id),
        "Bitvec" = Bitvec([Id; 2]),
        "Sort" = Sort(Vec<Id>),
        "Var" = Var(Id),
        "App" = App(Vec<Id>),
        "~" = Eq(Vec<Id>),
        // Logic-rewritter constructors
        "Ground" = Ground(Id),
        "List" = List(Vec<Id>),
        "Func" = Func(Vec<Id>),
        "=>" = Forall([Id; 2]),
        "Inst" = Inst(Vec<Id>),
        "Inhabitant" = Inhabitant([Id; 3]),
        "Mk" = Mk(Id),
    }
}

pub trait FromTerm {
    fn from_constant(self, c: Constant) -> (Id, Self);
    fn from_sort(self, s: Sort) -> (Id, Self);
    fn from_var(self, name: String) -> (Id, Self);
    fn from_app(self, head: Id, ids: Vec<Id>) -> (Id, Self);
    fn from_op(self, head: Operator, ids: Vec<Id>) -> (Id, Self);
    fn from_equality(self, ids: Vec<Id>) -> (Id, Self);
    fn from_list(self, ids: Vec<Id>) -> (Id, Self);
    fn from_indexed_types(self, head: Id, ids: Vec<Id>) -> (Id, Self);
}

impl FromTerm for &mut RecExpr<Rare> {
    fn from_constant(self, c: Constant) -> (Id, Self) {
        (
            match c {
                Constant::Integer(i) => self.add(Rare::Num(i.clone())),
                Constant::BitVec(i, i2) => {
                    let tuple = (
                        self.add(Rare::Num(i.clone())),
                        self.add(Rare::Num(i2.clone())),
                    );
                    self.add(Rare::Bitvec(tuple.into()))
                }
                Constant::Real(r) => self.add(Rare::Rational(r.clone())),
                Constant::String(s) => self.add(Rare::Symbol(s.clone())),
            },
            self,
        )
    }
    fn from_sort(self, s: Sort) -> (Id, Self) {
        fn from_simple_type<'a>(
            expr: &'a mut RecExpr<Rare>,
            name: &str,
        ) -> (egg::Id, &'a mut egg::RecExpr<Rare>) {
            let name = expr.add(Rare::Symbol(name.to_string()));
            let id = expr.add(Rare::Sort(vec![name]));
            (id, expr)
        }
        match s {
            Sort::Var(s) => {
                let name = self.add(Rare::Symbol(s));
                let id = self.add(Rare::Sort(vec![name]));
                (id, self)
            }
            Sort::Bool => from_simple_type(self, "Bool"),
            Sort::Int => from_simple_type(self, "Int"),
            Sort::Type => from_simple_type(self, "Type"),
            Sort::String => from_simple_type(self, "str"),
            Sort::BitVec(i) => {
                let size = self.add(Rare::Num(i));
                let bitvec = self.add(Rare::Symbol("Bitvec".to_string()));
                let id = self.add(Rare::Sort(vec![bitvec, size]));
                (id, self)
            }
            _ => panic!("Not implemented yet"),
        }
    }

    fn from_var(self, name: String) -> (Id, Self) {
        let id = self.add(Rare::Symbol(name));
        (self.add(Rare::Var(id)), self)
    }

    fn from_app(self, head: Id, ids: Vec<Id>) -> (Id, Self) {
        let mut ids_ = vec![head];
        ids_.extend(ids);
        (self.add(Rare::App(ids_)), self)
    }

    fn from_op(self, head: Operator, ids: Vec<Id>) -> (Id, Self) {
        if ids.len() == 0 {
             let op = self.add(Rare::Symbol(head.to_string()));
             return (self.add(Rare::Op(op)), self)
        }

        let symbol = self.add(Rare::Symbol(head.to_string()));
        let mut ids_ = vec![self.add(Rare::Op(symbol))];

        ids_.extend(ids);
        (self.add(Rare::App(ids_)), self)
    }

    fn from_equality(self, ids: Vec<Id>) -> (Id, Self) {
        let mut ids_ = vec![];
        ids_.extend(ids);
        (self.add(Rare::Eq(ids_)), self)
    }

    fn from_list(self, ids: Vec<Id>) -> (Id, Self) {
        let mut ids_ = vec![];
        ids_.extend(ids);
        (self.add(Rare::List(ids_)), self)
    }
    fn from_indexed_types(self, head: Id, params: Vec<Id>) -> (Id, Self) {
        let mut ids_ = vec![head];
        ids_.extend(params);
        (self.add(Rare::Sort(ids_)), self)
    }
}

impl<'a, 'b> FromTerm
    for (
        &'a mut PatternAst<Rare>,
        &'b IndexMap<String, TypeParameter>,
    )
{
    #[inline]
    fn from_constant(self, c: Constant) -> (Id, Self) {
        let (ast, params) = self;
        let id = match c {
            Constant::Integer(i) => ast.add(ENodeOrVar::ENode(Rare::Num(i.clone()))),
            Constant::BitVec(i, i2) => {
                let tuple = (
                    ast.add(ENodeOrVar::ENode(Rare::Num(i.clone()))),
                    ast.add(ENodeOrVar::ENode(Rare::Num(i2.clone()))),
                );
                ast.add(ENodeOrVar::ENode(Rare::Bitvec(tuple.into())))
            }
            Constant::Real(r) => ast.add(ENodeOrVar::ENode(Rare::Rational(r.clone()))),
            Constant::String(s) => ast.add(ENodeOrVar::ENode(Rare::Symbol(s.clone()))),
        };
        (id, (ast, params))
    }

    #[inline]
    fn from_sort(self, s: Sort) -> (Id, Self) {
        let (ast, type_params) = self;

        fn from_simple_type<'a, 'b>(
            expr: (
                &'a mut PatternAst<Rare>,
                &'b IndexMap<String, TypeParameter>,
            ),
            name: &str,
        ) -> (
            egg::Id,
            (
                &'a mut PatternAst<Rare>,
                &'b IndexMap<String, TypeParameter>,
            ),
        ) {
            let (ast, type_params) = expr;

            let name = ast.add(ENodeOrVar::ENode(Rare::Symbol(name.to_string())));
            let id = ast.add(ENodeOrVar::ENode(Rare::Sort(vec![name])));
            (id, (ast, type_params))
        }
        match s {
            Sort::Var(s) => {
                // let name = ast.add(ENodeOrVar::ENode(Rare::Symbol(s)));
                let code = str_to_u32(&s);
                let id = ast.add(ENodeOrVar::Var(Var::from_u32(code)));
                (id, (ast, type_params))
            }
            Sort::Bool => from_simple_type((ast, type_params), "Bool"),
            Sort::Int => from_simple_type((ast, type_params), "Int"),
            Sort::Type => from_simple_type((ast, type_params), "Type"),
            Sort::String => from_simple_type((ast, type_params), "str"),
            Sort::BitVec(i) => {
                let size = ast.add(ENodeOrVar::ENode(Rare::Num(i)));
                let bitvec = ast.add(ENodeOrVar::ENode(Rare::Symbol("Bitvec".to_string())));
                let id = ast.add(ENodeOrVar::ENode(Rare::Sort(vec![bitvec, size])));
                (id, (ast, type_params))
            }
            x => panic!("Not a simple type {:?}", x),
        }
    }

    #[inline]
    fn from_var(self, name: String) -> (Id, Self) {
        let (ast, type_params) = self;

        if type_params.contains_key(&name) {
            let code = str_to_u32(&name);
            let id = ast.add(ENodeOrVar::Var(Var::from_u32(code)));
            return (id, (ast, type_params));
        }

        // fallback exactly as before
        let sym_id = ast.add(ENodeOrVar::ENode(Rare::Symbol(name.clone())));
        let id = ast.add(ENodeOrVar::ENode(Rare::Var(sym_id)));
        (id, (ast, type_params))
    }

    #[inline]
    fn from_app(self, head: Id, ids: Vec<Id>) -> (Id, Self) {
        let (ast, params) = self;
        let mut all = Vec::with_capacity(ids.len() + 1);
        all.push(head);
        all.extend(ids);
        let id = ast.add(ENodeOrVar::ENode(Rare::App(all)));
        (id, (ast, params))
    }

    #[inline]
    fn from_op(self, head: Operator, ids: Vec<Id>) -> (Id, Self) {
        let (ast, params) = self;
        if ids.len() == 0 {
             let op = ast.add(ENodeOrVar::ENode(Rare::Symbol(head.to_string())));
             return (ast.add(ENodeOrVar::ENode(Rare::Op(op))), (ast, params))
        }

        let sym = ast.add(ENodeOrVar::ENode(Rare::Symbol(head.to_string())));
        let mut all = Vec::with_capacity(ids.len() + 1);
        all.push(ast.add(ENodeOrVar::ENode(Rare::Op(sym))));
        all.extend(ids);
        let id = ast.add(ENodeOrVar::ENode(Rare::App(all)));
        (id, (ast, params))
    }

    #[inline]
    fn from_equality(self, ids: Vec<Id>) -> (Id, Self) {
        let (ast, params) = self;
        let mut all = Vec::with_capacity(ids.len() + 1);
        all.extend(ids);
        let id = ast.add(ENodeOrVar::ENode(Rare::Eq(all)));
        (id, (ast, params))
    }

    fn from_list(self, ids: Vec<Id>) -> (Id, Self) {
        let (ast, params) = self;
        let mut ids_ = vec![];
        ids_.extend(ids);
        (ast.add(ENodeOrVar::ENode(Rare::List(ids_))), (ast, params))
    }

    fn from_indexed_types(self, head: Id, params: Vec<Id>) -> (Id, Self) {
        let (ast, params_) = self;
        let mut ids_ = vec![head];
        ids_.extend(params);
        (ast.add(ENodeOrVar::ENode(Rare::Sort(ids_))), (ast, params_))
    }
}

pub fn convert_to_egg_expr<L: FromTerm>(expr: L, term: &Rc<Term>) -> (Id, L) {
    match &*term.clone() {
        Term::Var(name, _) => expr.from_var(name.clone()),
        Term::Const(const_) => expr.from_constant(const_.clone()),
        Term::App(func, params) => {
            let (func, expr) = convert_to_egg_expr(expr, func);
            let mut expr_ = expr;
            let mut ids = vec![];
            for param in params {
                let (rec, expr) = convert_to_egg_expr(expr_, param);
                expr_ = expr;
                ids.push(rec);
            }
            expr_.from_app(func, ids)
        }
        Term::Op(op, params) => {
            let mut ids = vec![];
            let mut expr_ = expr;
            for param in params {
                let (rec, expr) = convert_to_egg_expr(expr_, param);
                expr_ = expr;
                ids.push(rec);
            }
            match op {
                Operator::Equals => expr_.from_equality(ids),
                _ => expr_.from_op(*op, ids),
            }
        }
        Term::Sort(sort) => match sort {
            Sort::ParamSort(params, head) => {
                let mut ids = vec![];
                let mut expr_ = expr;
                let (head, expr) = convert_to_egg_expr(expr_, head);
                expr_ = expr;
                for param in params {
                    let (rec, expr) = convert_to_egg_expr(expr_, param);
                    expr_ = expr;
                    ids.push(rec);
                }

                expr_.from_indexed_types(head, ids)
            }
            _ => expr.from_sort(sort.clone()),
        },
        _ => panic!("The format of the term can not be converted"),
    }
}
