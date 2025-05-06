use core::panic;
use std::{any::Any, collections::HashMap, fmt::format};

use crate::{
    ast::{
        rules::{Rules, TypeParameter},
        Constant, Operator, PrimitivePool, ProofNode, Rc, Sort, Term,
    },
    rare::util::collect_vars,
};
use indexmap::IndexMap;
use rug::{Integer, Rational};

use egg::*;

use super::util::{clauses_to_or, str_to_u32};

#[derive(Debug, Clone, Copy)]
enum KindContext {
    Goal,
    ProofTerm,
    Processing,
}
#[derive(Debug, Default, Clone)]
struct AnalysisContext {
    proof_context: HashMap<Id, KindContext>,
    premises: Vec<Rewrite<Rare, ()>>,
}

define_language! {
    enum Rare {
        Num(Integer),
        Symbol(String),
        Bool(bool),
        Rational(Rational),
        "Op" = Op(Id),
        "Bitvec" = Bitvec([Id; 2]),
        "Sort" = Sort(Id),
        "Var" = Var(Id),
        "App" = App(Vec<Id>),
        // Logic-rewritter constructors
        "List" = List(Vec<Id>),
        "Fun" = Fun([Id; 2]),
        "Inhabitant" = Inhabitant([Id; 2]),
        "Forall" = Forall(Vec<Id>),
        "Mk" = Mk(Id),
    }
}

trait FromTerm {
    fn from_constant(self, c: Constant) -> (Id, Self);
    fn from_sort(self, s: Sort) -> (Id, Self);
    fn from_var(self, name: String) -> (Id, Self);
    fn from_app(self, head: Id, ids: Vec<Id>) -> (Id, Self);
    fn from_op(self, head: Operator, ids: Vec<Id>) -> (Id, Self);
    fn from_list(self, ids: Vec<Id>) -> (Id, Self);
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
            let id = expr.add(Rare::Sort(name));
            (id, expr)
        }
        match s {
            Sort::Var(s) => {
                let name = self.add(Rare::Symbol(s));
                let id = self.add(Rare::Sort(name));
                (id, self)
            }
            Sort::Bool => from_simple_type(self, "Bool"),
            Sort::Int => from_simple_type(self, "Int"),
            Sort::Type => from_simple_type(self, "Type"),
            Sort::String => from_simple_type(self, "str"),
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
        let symbol = self.add(Rare::Symbol(head.to_string()));
        let mut ids_ = vec![self.add(Rare::Op(symbol))];
        ids_.extend(ids);
        (self.add(Rare::App(ids_)), self)
    }

    fn from_list(self, ids: Vec<Id>) -> (Id, Self) {
        let mut ids_ = vec![];
        ids_.extend(ids);
        (self.add(Rare::List(ids_)), self)
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
            let id = ast.add(ENodeOrVar::ENode(Rare::Sort(name)));
            (id, (ast, type_params))
        }
        match s {
            Sort::Var(s) => {
                let name = ast.add(ENodeOrVar::ENode(Rare::Symbol(s)));
                let id = ast.add(ENodeOrVar::ENode(Rare::Sort(name)));
                (id, (ast, type_params))
            }
            Sort::Bool => from_simple_type((ast, type_params), "Bool"),
            Sort::Int => from_simple_type((ast, type_params), "Int"),
            Sort::Type => from_simple_type((ast, type_params), "Type"),
            Sort::String => from_simple_type((ast, type_params), "str"),
            _ => panic!("Not implemented yet"),
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
        let sym = ast.add(ENodeOrVar::ENode(Rare::Symbol(head.to_string())));
        let mut all = Vec::with_capacity(ids.len() + 1);
        all.push(ast.add(ENodeOrVar::ENode(Rare::Op(sym))));
        all.extend(ids);
        let id = ast.add(ENodeOrVar::ENode(Rare::App(all)));
        (id, (ast, params))
    }

    fn from_list(self, ids: Vec<Id>) -> (Id, Self) {
        let (ast, params) = self;
        let mut ids_ = vec![];
        ids_.extend(ids);
        (ast.add(ENodeOrVar::ENode(Rare::List(ids_))), (ast, params))
    }
}

fn convert_to_egg_expr<L: FromTerm>(expr: L, term: &Rc<Term>) -> (Id, L) {
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
            expr_.from_op(*op, ids)
        }
        Term::Sort(sort) => expr.from_sort(sort.clone()),
        _ => panic!("The format of the term can not be converted"),
    }
}

fn construct_egg_rules_database(rules: &Rules) -> (Vec<Rewrite<Rare, ()>>, Vec<RecExpr<Rare>>) {
    let mut top = RecExpr::default();
    top.add(ENodeOrVar::ENode(Rare::Symbol("⊤".to_string())));

    fn construct_param_list<'a>(
        vars: &IndexMap<String, Rc<Term>>,
        tree: &'a mut RecExpr<ENodeOrVar<Rare>>,
    ) -> (&'a mut RecExpr<ENodeOrVar<Rare>>, Vec<Id>) {
        let mut tree = tree;
        let mut ids = vec![];
        for (name, kind) in vars {
            let name = tree.add(ENodeOrVar::Var(Var::from_u32(str_to_u32(name))));
            let (kind, (new_tree, _)) = convert_to_egg_expr((tree, &IndexMap::default()), &kind);
            tree = new_tree;
            ids.push(tree.add(ENodeOrVar::ENode(Rare::Inhabitant([name, kind]))));
        }

        return (tree, ids);
    }

    fn create_function_egg_rule(
        name: &str,
        vars: &IndexMap<String, TypeParameter>,
        goal: &Rc<Term>,
        params: &[Rc<Term>],
    ) -> (Rewrite<Rare, ()>, Rewrite<Rare, ()>) {
        let mut lhs = RecExpr::default();
        let mut rhs = RecExpr::default();
        // First we look for the variables need in the goal, they are important since they define the "shape" of the rewritte rule goal
        let goal_vars = collect_vars(goal);
        let (rhs, mut goal_vars_id) = construct_param_list(&goal_vars, &mut rhs);
        // now we need to look for the variables that is need to apply the "function" rewritten rule but the var does not appear in the goal
        let premise_vars = vars
            .iter()
            .filter(|(k, _)| !goal_vars.contains_key(*k))
            .map(|(n, t)| (n.clone(), t.term.clone()));
        let (rhs, premise_vars_id) = construct_param_list(&premise_vars.collect(), rhs);

        let (id, (lhs, _)) = convert_to_egg_expr((&mut lhs, vars), goal);
        lhs.add(ENodeOrVar::ENode(Rare::Mk(id)));
        for _ in premise_vars_id {
            let any = rhs.add(ENodeOrVar::ENode(Rare::Symbol("any".to_string())));
            goal_vars_id.push(any);
        }

        rhs.add(ENodeOrVar::ENode(Rare::Forall(goal_vars_id)));
        println!("{0} = {1}", lhs, rhs);

        let forall_rule = Rewrite::new(
            format!("{0}-forall", name),
            Pattern::new(lhs.clone()),
            Pattern::new(rhs.clone()),
        );

        let mut conclusion = &mut RecExpr::default();
        let (id, (concl, _)) = convert_to_egg_expr((conclusion, vars), goal);
        conclusion = concl;
        let mut head = id;

        for param in params {
            let (id, (concl, _)) = convert_to_egg_expr((conclusion, vars), param);
            conclusion = concl;
            head = conclusion.add(ENodeOrVar::ENode(Rare::Fun([id, head])));
        }

        let conclusion_rule = Rewrite::new(
            format!("{0}-conclusion", name),
            Pattern::new(rhs.clone()),
            Pattern::new(conclusion.clone()),
        );

        return (forall_rule.unwrap(), conclusion_rule.unwrap());
    }

    let mut db = vec![
        rewrite!("func_composition"; "(Fun ?v (App (Op =) ?x ?y))" => "(Fun (Mk ?v) (App (Op =) ?x ?y))"),
        rewrite!("func_apply"; "(Fun ⊤ (App (Op =) ?x ?y))" => "⊤"),
    ];

    let mut ground_terms = vec![];

    for (name, definition) in rules {
        let params = &definition.premises;
        let mut goal = RecExpr::default();
        convert_to_egg_expr((&mut goal, &definition.parameters), &definition.conclusion);
        let (forall_rule, conclusion_rule) = create_function_egg_rule(
            &definition.name,
            &definition.parameters,
            &definition.conclusion,
            params,
        );

        db.push(forall_rule);
        db.push(conclusion_rule);
    }

    return (db, ground_terms);
}

fn construct_analysis(
    pool: &mut PrimitivePool,
    goal: Id,
    premises: &Rc<ProofNode>,
) -> AnalysisContext {
    let mut top = RecExpr::default();
    top.add(ENodeOrVar::ENode(Rare::Symbol("⊤".to_string())));

    let mut context = AnalysisContext::default();
    context.proof_context.insert(goal, KindContext::Goal);
    for premise in premises.get_assumptions() {
        let clause = clauses_to_or(pool, premise.clause());
        if let Some(clause) = clause {
            let mut egg_term = RecExpr::default();
            let (id, _) = convert_to_egg_expr((&mut egg_term, &IndexMap::default()), &clause);
            let top_rule = Rewrite::new(
                format!("{0}-ground", premise.id()),
                Pattern::new(egg_term.clone()),
                Pattern::new(top.clone()),
            );
            context.premises.push(top_rule.unwrap());
            context.proof_context.insert(id, KindContext::ProofTerm);
        }
    }
    return context;
}

pub fn reconstruct_rule(
    pool: &mut PrimitivePool,
    conclusion: Rc<Term>,
    root: &Rc<ProofNode>,
    database: &Rules,
) {
    let mut root_expr = RecExpr::default();
    let (goal, _) = convert_to_egg_expr::<&mut RecExpr<Rare>>(&mut root_expr, &conclusion);
    let analysis = construct_analysis(pool, goal, root);
    let mut premises = analysis.premises.clone();

    let mut runner: Runner<Rare, (), ()> = Runner::new(())
        .with_explanations_enabled()
        .with_expr(&root_expr);
    let (egg_rules, ground_terms) = construct_egg_rules_database(database);
    for terms in ground_terms.iter() {
        runner = runner.with_expr(&terms);
    }

    premises.extend(egg_rules);
    runner = runner.run(&premises);
    println!("{:?}", premises);

    // // the Runner knows which e-class the expression given with `with_expr` is in
    // let root = runner.roots[0];

    // let extractor = Extractor::new(&runner.egraph, AstSize);
    // let (best_cost, best) = extractor.find_best(root);
    // println!(
    //     "Simplified {} to {} explain {} with cost {}",
    //     root_expr,
    //     best,
    //     runner.explain_equivalence(&root_expr, &best),
    //     best_cost
    // );
}
