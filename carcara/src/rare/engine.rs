use std::{any::Any, collections::HashMap, fmt::format};

use crate::ast::{rules::{Rules, TypeParameter}, Constant, Operator, PrimitivePool, ProofNode, Rc, Sort, Term};
use indexmap::IndexMap;
use rug::{Integer, Rational};

use egg::*;

use super::util::clauses_to_or;

#[derive(Debug, Clone, Copy)]
enum KindContext {
    Goal,
    ProofTerm,
    Processing
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
        "List" = List(Vec<Id>),
        "Func" = Func([Id; 2]),
    }
}

trait FromTerm {
    fn from_constant(self, c : Constant) -> (Id, Self);
    fn from_sort(self, s : Sort) -> (Id, Self);
    fn from_var(self, name : String) -> (Id, Self);
    fn from_app(self, head: Id, ids: Vec<Id>) -> (Id, Self);
    fn from_op(self, head: Operator, ids: Vec<Id>) -> (Id, Self);
    fn from_list(self, ids: Vec<Id>) -> (Id, Self);
}

impl FromTerm for &mut RecExpr<Rare> {
    fn from_constant(self, c : Constant) -> (Id, Self) {
        (match c {
            Constant::Integer(i) => self.add(Rare::Num(i.clone())),
            Constant::BitVec(i, i2) => {
                let tuple = (self.add(Rare::Num(i.clone())), self.add(Rare::Num(i2.clone())));
                self.add(Rare::Bitvec(tuple.into()))
            },
            Constant::Real(r) => self.add(Rare::Rational(r.clone())),
            Constant::String(s) => self.add(Rare::Symbol(s.clone()))          
        }, self)
    }
    fn from_sort(self, _ : Sort) -> (Id, Self) {
      panic!("The format of the term can not be converted")
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

impl<'a, 'b> FromTerm for (&'a mut PatternAst<Rare>, &'b IndexMap<String, TypeParameter>) {
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
            Constant::Real(r)   => ast.add(ENodeOrVar::ENode(Rare::Rational(r.clone()))),
            Constant::String(s) => ast.add(ENodeOrVar::ENode(Rare::Symbol(s.clone()))),
        };
        (id, (ast, params))
    }

    #[inline]
    fn from_sort(self, _s: Sort) -> (Id, Self) {
        panic!("The format of the term cannot be converted")
    }

    #[inline]
    fn from_var(self, name: String) -> (Id, Self) {
        let (ast, type_params) = self;

        #[inline]
        // 32-bit FNV-1a hash for small strings
        pub fn str_to_u32(input: &str) -> u32 {
            const OFFSET_BASIS: u32 = 0x811c_9dc5;
            const PRIME:        u32 = 0x0100_0193;
        
            let mut hash = OFFSET_BASIS;
            for byte in input.as_bytes().as_ref() {
                hash ^= *byte as u32;
                hash = hash.wrapping_mul(PRIME);
            }
            hash
        }

        if type_params.contains_key(&name) {
            let code = str_to_u32(&name);
            let id   = ast.add(ENodeOrVar::Var(Var::from_u32(code)));
            return (id, (ast, type_params));
        }

        // fallback exactly as before
        let sym_id = ast.add(ENodeOrVar::ENode(Rare::Symbol(name.clone())));
        let id     = ast.add(ENodeOrVar::ENode(Rare::Var(sym_id)));
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
        },
        Term::Op(op, params) => {
            let mut ids = vec![];
            let mut expr_ = expr;
            for param in params {
                let (rec, expr) = convert_to_egg_expr(expr_, param);
                expr_ = expr;
                ids.push(rec);
            }
            expr_.from_op(*op, ids)
        },
        Term::Sort(sort) => expr.from_sort(sort.clone()),
        _ => panic!("The format of the term can not be converted"),
    }
}

fn construct_egg_rules_database(rules: &Rules) -> (Vec<Rewrite<Rare, ()>>, Vec<RecExpr<Rare>>) {
    let mut top = RecExpr::default();
    top.add(ENodeOrVar::ENode(Rare::Symbol("⊤".to_string())));

    fn create_function_egg_rule(vars: &IndexMap<String, TypeParameter>, goal : &Rc<Term>, params: &[Rc<Term>]) -> RecExpr<ENodeOrVar<Rare>>  {
        let mut func = RecExpr::default();
        let (id, _) = convert_to_egg_expr((&mut func, vars), goal);
        let mut head = id;
    
        for param in params {
            let (id, _) = convert_to_egg_expr((&mut func, vars), param);
            head = func.add(ENodeOrVar::ENode(Rare::Func([id, head])));
        }

        return func;
    }
    

    let mut db = vec![
        rewrite!("reduction1"; "(Func ⊤ ?x)" => "?x"),
        rewrite!("reduction2"; "(Func ?x ⊤)" => "⊤"),
//        rewrite!("eq_refl_top"; "(App (Op =) ?x ?x)" => "⊤"),
    ];
    let mut ground_terms = vec![];
 
    for (name, definition) in rules {
       // let mut concl_lhs = RecExpr::default();
       // let mut concl_rhs = RecExpr::default();
     //   let terms= match_term!((= lhs rhs) =  &definition.conclusion);

        // if let Some((lhs, rhs)) = terms {
        //     let (_, (lhs, _)) = convert_to_egg_expr((&mut concl_lhs, &definition.parameters), lhs);
        //     let (_, (rhs, _)) = convert_to_egg_expr((&mut concl_rhs, &definition.parameters), rhs);
        //     let rewritten_rule = Rewrite::new(name, Pattern::new(lhs.clone()), Pattern::new(rhs.clone()));
        //     db.push(rewritten_rule.unwrap());
        // }
        let params = &definition.premises;
        //if params.len() == 0 {
            let mut goal = RecExpr::default();
            convert_to_egg_expr((&mut goal, &definition.parameters), &definition.conclusion);
            let preposition = create_function_egg_rule(&definition.parameters, &definition.conclusion, params);

            let top_rule = Rewrite::new(format!("{0}-ground", name),  Pattern::new(goal), Pattern::new(preposition));
            
            db.push(top_rule.unwrap());
        // } else {
        //     ground_terms.push(create_function_egg_rule(&definition.conclusion, &definition.premises));
        // }

        // for (index, premise) in definition.premises.iter().enumerate() {
        //     let mut concl_lhs = RecExpr::default();
        //     let mut concl_rhs = RecExpr::default();
        //     let terms= match_term!((= lhs rhs) = premise);
        //     if let Some((lhs, rhs)) = terms {
        //        let (_, (lhs, _)) = convert_to_egg_expr((&mut concl_lhs, &definition.parameters), lhs);
        //        let (_, (rhs, _)) = convert_to_egg_expr((&mut concl_rhs, &definition.parameters), rhs);
        //        println!("{:?}", &definition.parameters);
        //        let rewritten_rule = Rewrite::new(format!("{0}-p{1}", name, index), Pattern::new(lhs.clone()), Pattern::new(rhs.clone()));
        //        db.push(rewritten_rule.unwrap().clone());
        //        println!("{:?}", db.last().unwrap().clone());
        //     }
        // }
    }
    return (db, ground_terms)
}

// impl<'a> Analysis<Rare> for &mut AnalysisContext {
//     type Data = Option<(Id, KindContext)>;

//     fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
//         match (to, from) {
//             (Some(to), Some(from)) => {
//                 match (to.1, from.1) {
//                     (KindContext::Goal, KindContext::ProofTerm) => {
//                         self.goals_merged.push((to.0.clone(), from.0));
//                     }
//                     (KindContext::ProofTerm, KindContext::Goal) => {
//                         self.goals_merged.push((from.0.clone(), to.0.clone()));
//                     }
//                     _ => ()
//                 }
//             },
//             _  => ()
//         }

//         DidMerge(true, true)
//     }

//     fn make(egraph: &mut EGraph<Rare, Self>, enode: &Rare) -> Self::Data {
//         let id = egraph.lookup(enode.clone())?;
//         Some((id, egraph.analysis.proof_context.get(&id).map(|x| *x).unwrap_or(KindContext::Processing)))        
//     }

// }

fn construct_analysis(pool : &mut PrimitivePool, goal: Id, premises : &Rc<ProofNode>) -> AnalysisContext {
    let mut top = RecExpr::default();
    top.add(ENodeOrVar::ENode(Rare::Symbol("⊤".to_string())));

    let mut context = AnalysisContext::default();
    context.proof_context.insert(goal, KindContext::Goal);
    for premise in premises.get_assumptions() {
        let clause = clauses_to_or(pool, premise.clause());
        if let Some(clause) = clause {
            let mut egg_term = RecExpr::default();
            let (id, _) = convert_to_egg_expr((&mut egg_term, &IndexMap::default()), &clause);
            let top_rule = Rewrite::new(format!("{0}-ground", premise.id()), Pattern::new(egg_term.clone()), Pattern::new(top.clone()));
            context.premises.push(top_rule.unwrap());
            context.proof_context.insert(id, KindContext::ProofTerm);
        }
    }
    return context
}

pub fn reconstruct_rule(pool : &mut PrimitivePool, conclusion: Rc<Term>, root: &Rc<ProofNode>, database: &Rules) {
    let mut root_expr = RecExpr::default();
    let (goal, _) = convert_to_egg_expr::<&mut RecExpr<Rare>>(&mut root_expr, &conclusion);
    let analysis = construct_analysis(pool, goal, root);
    let mut premises = analysis.premises.clone();

    let mut runner: Runner<Rare, (), ()> = Runner::new(()).with_explanations_enabled().with_expr(&root_expr);
    let (egg_rules, ground_terms) = construct_egg_rules_database(database);
    for terms in ground_terms.iter() {
        runner = runner.with_expr(&terms);
    }
    
    premises.extend(egg_rules);
    runner = runner.run(&premises);
    println!("{:?}", premises);

    // the Runner knows which e-class the expression given with `with_expr` is in
    let root = runner.roots[0];

    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (best_cost, best) = extractor.find_best(root);
    println!("Simplified {} to {} explain {} with cost {}", root_expr, best, runner.explain_equivalence(&root_expr, &best), best_cost); 

}