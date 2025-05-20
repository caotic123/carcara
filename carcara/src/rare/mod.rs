use indexmap::IndexMap;

pub mod engine;
pub mod util;
pub mod meta;
pub mod language;

use crate::{
    ast::{rules::RewriteTerm, Rc, Term, TermPool},
    build_equation, pseudo_term,
};

pub fn get_rules() -> Vec<(RewriteTerm, RewriteTerm)> {
    return vec![
        build_equation!((RareList ..x..) ~> x),
        build_equation!((Or true) ~> true),
    ];
}

#[derive(Debug, Clone)]
enum Trace<T1, T2> {
    Term(T1),
    ManyTerm(T2),
}

type TraceRef<'a> = Trace<&'a Rc<Term>, &'a Vec<Rc<Term>>>;
type TraceOwned = Trace<Rc<Term>, Vec<Rc<Term>>>;

#[inline]
fn match_meta_terms<'a, 'b>(
    term: &'a Rc<Term>,
    rule: &'b RewriteTerm,
    traces: &'b mut IndexMap<String, TraceRef<'a>>,
) -> Option<&'b mut IndexMap<String, TraceRef<'a>>>
where
    'a: 'b,
{
    match rule {
        RewriteTerm::ManyEq(op, var) => match term.as_ref() {
            Term::Op(op_, rest_) if op == op_ => {
                traces.insert(var.to_string(), Trace::ManyTerm(rest_));
                return Some(traces);
            }
            _ => None,
        },
        RewriteTerm::OperatorEq(op, rest) => match term.as_ref() {
            Term::Op(op_, rest_) if op == op_ => {
                if rest_.len() != rest.len() {
                    return None;
                }

                let mut rest = rest.iter();
                let mut traces = Some(traces);
                for param in rest_ {
                    let rule = rest.next().unwrap();
                    traces = match_meta_terms(param, rule, traces.unwrap());
                    if traces.is_none() {
                        return None;
                    }
                }
                return traces;
            }
            _ => None,
        },
        RewriteTerm::VarEqual(var) => {
            traces.insert(var.to_string(), Trace::Term(term));
            return Some(traces);
        }
    }
}

#[inline]
fn reconstruct_meta_terms<'a>(
    pool: &mut dyn TermPool,
    rule: &'a RewriteTerm,
    traces: &IndexMap<String, TraceRef<'a>>,
) -> TraceOwned {
    match rule {
        RewriteTerm::ManyEq(_, _) => unreachable!(),
        RewriteTerm::OperatorEq(op, params) => {
            let mut args = vec![];
            for param in params {
                let k = reconstruct_meta_terms(pool, param, traces);
                if let Trace::Term(term) = k {
                    args.push(term.clone());
                }
            }
            return Trace::Term(pool.add(Term::Op(op.clone(), args)));
        }
        RewriteTerm::VarEqual(var) => {
            let trace = traces.get(*var).unwrap();
            match trace {
                Trace::Term(t) => Trace::Term((*t).clone()),
                Trace::ManyTerm(t) => Trace::ManyTerm((*t).clone()),
            }
        }
    }
}

fn check_rewrites(
    pool: &mut dyn TermPool,
    term: &Rc<Term>,
    rules: &[(RewriteTerm, RewriteTerm)],
) -> Option<TraceOwned> {
    for rule in rules {
        let mut traces = IndexMap::new();
        let lhs = &rule.0;
        if let Some(traces) = match_meta_terms(term, &lhs, &mut traces) {
            return Some(reconstruct_meta_terms(pool, &rule.1, traces));
        }
    }
    return None;
}

pub fn rewrite_meta_terms(
    pool: &mut dyn TermPool,
    term: Rc<Term>,
    cache: &mut IndexMap<String, Rc<Term>>,
    rules: &[(RewriteTerm, RewriteTerm)],
) -> Rc<Term> {
    match term.as_ref() {
        Term::Var(name, _) => {
            if let Some(cached) = cache.get(name) {
                cached.clone()
            } else {
                let rewritten = term.clone();
                cache.insert(name.clone(), rewritten.clone());
                rewritten
            }
        }

        Term::Const(_) => term.clone(),
        Term::Sort(_) => term.clone(),

        Term::App(f, args) => {
            let f_prime = rewrite_meta_terms(pool, f.clone(), cache, rules);
            let new_args = args
                .iter()
                .flat_map(|arg| {
                    if let Some(trace) = check_rewrites(pool, arg, rules) {
                        match trace {
                            Trace::Term(t) => vec![t],
                            Trace::ManyTerm(subs) => subs,
                        }
                    } else {
                        vec![rewrite_meta_terms(pool, arg.clone(), cache, rules)]
                    }
                })
                .collect::<Vec<_>>();
            let new_term = pool.add(Term::App(f_prime, new_args));
            if new_term != term {
                return rewrite_meta_terms(pool, new_term, cache, rules);
            }

            return new_term;
        }

        Term::Op(op, args) => {
            if let Some(trace) = check_rewrites(pool, &term, rules) {
                match trace {
                    Trace::Term(t) => t,
                    Trace::ManyTerm(_) => {
                        let new_args = args
                            .iter()
                            .flat_map(|arg| {
                                if let Some(trace) = check_rewrites(pool, arg, rules) {
                                    match trace {
                                        Trace::Term(t) => vec![t],
                                        Trace::ManyTerm(subs) => subs,
                                    }
                                } else {
                                    vec![rewrite_meta_terms(pool, arg.clone(), cache, rules)]
                                }
                            })
                            .collect::<Vec<_>>();
                        let new_term: Rc<Term> = pool.add(Term::Op(*op, new_args));
                        if new_term != term {
                            return rewrite_meta_terms(pool, new_term, cache, rules);
                        }

                        return new_term;
                    }
                }
            } else {
                let new_args = args
                    .iter()
                    .flat_map(|arg| {
                        if let Some(trace) = check_rewrites(pool, arg, rules) {
                            match trace {
                                Trace::Term(t) => vec![t],
                                Trace::ManyTerm(subs) => subs,
                            }
                        } else {
                            vec![rewrite_meta_terms(pool, arg.clone(), cache, rules)]
                        }
                    })
                    .collect::<Vec<_>>();
                let new_term = pool.add(Term::Op(*op, new_args));
                if let Some(_) = check_rewrites(pool, &new_term, rules) {
                    return rewrite_meta_terms(pool, new_term, cache, rules);
                }

                return new_term;
            }
        }

        Term::Binder(binder, bindings, body) => {
            let new_body = rewrite_meta_terms(pool, body.clone(), cache, rules);
            pool.add(Term::Binder(*binder, bindings.clone(), new_body))
        }

        Term::Let(bindings, body) => {
            let new_body = rewrite_meta_terms(pool, body.clone(), cache, rules);
            pool.add(Term::Let(bindings.clone(), new_body))
        }

        Term::ParamOp { op, op_args, args } => {
            let new_op_args = op_args
                .iter()
                .map(|op_arg| rewrite_meta_terms(pool, op_arg.clone(), cache, rules))
                .collect::<Vec<_>>();
            let new_args = args
                .iter()
                .map(|arg| rewrite_meta_terms(pool, arg.clone(), cache, rules))
                .collect::<Vec<_>>();
            pool.add(Term::ParamOp {
                op: *op,
                op_args: new_op_args,
                args: new_args,
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ast::PrimitivePool, parser::*};

    fn run_test(definitions: &str, original: &str, rule: (RewriteTerm, RewriteTerm), result: &str) {
        let mut pool = PrimitivePool::new();
        let mut parser = Parser::new(&mut pool, Config::new(), definitions.as_bytes()).unwrap();
        parser.parse_problem().unwrap();

        let [original, result] = [original, result].map(|s| {
            parser.reset(s.as_bytes()).unwrap();
            parser.parse_term().unwrap()
        });

        let got = rewrite_meta_terms(&mut pool, original, &mut IndexMap::new(), &vec![rule]);

        assert_eq!(&result, &got);
    }

    macro_rules! run_tests {
        (
            definitions = $defs:literal,
            $($original:literal [$rule:expr] => $result:literal,)*
        ) => {{
            let definitions = $defs;
            $(run_test(definitions, $original, $rule, $result);)*
        }};
    }

    #[test]
    fn test_substitutions() {
        run_tests! {
            definitions = "
            (declare-const v Bool)
        ",
            "(not (not (not true)))" [build_equation!((Not (Not x)) ~> x)] => "(not true)",
            "(or true)" [build_equation!((Or true) ~> true)] => "true",

        }
    }
}
