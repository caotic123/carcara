use indexmap::IndexMap;
use std::collections::{VecDeque, HashMap};

use crate::{
    ast::{
        rules::{RareTerm, RuleDefinition, TypeParameter}, Constant, Operator, Rc, Term, TermPool
    },
    checker::error::CheckerError,
};

pub fn apply_arg(
    argument: String,
    parameter: TypeParameter,
    rule: &mut RuleDefinition,
    term: Rc<Term>,
    sort: Rc<Term>,
) -> Result<(), CheckerError> {
    if let Some(hole) = rule.arguments.1.get_mut(&argument) {
        hole.replace(Some(term.clone()));
    }

    if let RareTerm::App(_, args) = &*parameter.term {
        match args.as_slice() {
            [value] => match &**value {
                RareTerm::Hole(hole) => {
                    let mut hole = hole.borrow_mut();
                    if let Some(sort_against) = hole.clone() {
                        if sort_against != sort {
                            return Err(CheckerError::RareMisMatchTypes(
                                argument.clone(),
                                sort,
                                sort_against,
                            ));
                        }
                    } else {
                        hole.replace(sort.clone());
                    }
                }
                _ => (),
            },
            _ => (),
        }
    }

    return Ok(());
}


pub fn convert_rare_term_to_term(
    rare_term: Rc<RareTerm>,
    type_equations: &IndexMap<String, Rc<Term>>,
    pool: &mut dyn TermPool
) -> Rc<Term> {
    // Map to store processed terms
    let mut term_map: HashMap<Rc<RareTerm>, Rc<Term>> = HashMap::new();
    
    // Queue for processing
    let mut work_queue = VecDeque::new();
    work_queue.push_back(rare_term.clone());
    
    while let Some(current) = work_queue.pop_front() {
        // Skip if already processed
        if term_map.contains_key(&current) {
            continue;
        }
        
        match &*current {
            RareTerm::Hole(hole) => {
                // Process holes immediately
                if let Some(term) = &*hole.borrow() {
                    term_map.insert(current.clone(), term.clone());
                } else {
                    panic!("Encountered unfilled hole in RareTerm");
                }
            },
            
            RareTerm::Const(constant) => {
                // Process constants immediately
                let term = pool.add(Term::Const(constant.clone()));
                term_map.insert(current, term);
            },
            
            RareTerm::Var(name) => {
                // Process variables immediately
                let sort = type_equations.get(name).unwrap().clone();
                let term = pool.add(Term::Var(name.clone(), sort));
                term_map.insert(current, term);
            },
            
            RareTerm::Op(operator) => {
                // Process operators immediately
                let term = pool.add(Term::Op(operator.clone(), Vec::new()));
                term_map.insert(current, term);
            },
            
            RareTerm::App(func, args) => {
                // Check if all dependencies are processed
                let func_processed = term_map.contains_key(func);
                let all_args_processed = args.iter().all(|arg| term_map.contains_key(arg));
                
                if func_processed && all_args_processed {
                    // All dependencies processed, create the term
                    let converted_args= args.iter()
                        .fold(vec![], |mut pred, arg| {
                            if let Some(list) = match_term!((rarelist ...) = term_map.get(arg).unwrap().clone()) {
                                pred.push(list.to_vec());
                                return pred;
                            }

                            let terms = vec![term_map.get(arg).unwrap().clone()];
                            pred.push(terms);
                            return pred
                        })
                        .into_iter().flatten().collect::<Vec<_>>();
                    
                    let term = match &**func {
                        RareTerm::Op(op) => {
                            // Convert App(Op, args) to Op(op, args)
                            pool.add(Term::Op(op.clone(), converted_args))
                        },
                        _ => {
                            // Regular application
                            let converted_func = term_map.get(func).unwrap().clone();
                            pool.add(Term::App(converted_func, converted_args))
                        }
                    };
                    
                    term_map.insert(current, term);
                } else {
                    // Some dependencies not processed yet
                    // Add current back to queue to process later
                    work_queue.push_back(current.clone());
                    
                    // Add unprocessed dependencies to queue
                    if !func_processed {
                        work_queue.push_back(func.clone());
                    }
                    
                    for arg in args {
                        if !term_map.contains_key(arg) {
                            work_queue.push_back(arg.clone());
                        }
                    }
                }
            }
        }
    }
    
    // Return the processed root term
    term_map.get(&rare_term).unwrap().clone()
}