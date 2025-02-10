use super::CheckerError;
use super::*;
use crate::ast::*;
use crate::drup::*;
use indexmap::IndexSet;
use std::borrow::Borrow;
use std::collections::HashMap;

pub fn elaborate_drup(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, CheckerError> {
    #[derive(Debug)]
    enum ResolutionStep<'a> {
        Resolvent(
            &'a (bool, Rc<Term>),
            u64,
            u64,
            (Vec<Rc<Term>>, IndexSet<(bool, Rc<Term>)>, u64),
        ),
        UnChanged(IndexSet<(bool, Rc<Term>)>, u64),
    }

    fn resolve(
        clause1: &IndexSet<(bool, Rc<Term>)>,
        clause2: &IndexSet<(bool, Rc<Term>)>,
        pivot: (bool, Rc<Term>),
    ) -> IndexSet<(bool, Rc<Term>)> {
        let mut resolvent = IndexSet::new();
        for literal in clause1.union(clause2) {
            if literal.1 == pivot.1 {
                continue;
            }

            resolvent.insert(literal.clone());
        }

        return resolvent;
    }

    let conclusion = step.clause.to_vec();
    let conclusion = if conclusion.len() > 0 {
        build_term!(pool, (cl[conclusion]))
    } else {
        conclusion[0].clone()
    };

    let premises = step
        .premises
        .iter()
        .map(|p| {
            let clause = p.clause().to_vec();
            let clause = if clause.len() > 0 {
                build_term!(pool, (cl[clause]))
            } else {
                clause[0].clone()
            };
            (clause.clone(), hash_term(pool, clause), p.clone())
        })
        .collect::<Vec<_>>();

    let trace = check_drup(
        pool,
        conclusion,
        &premises.iter().map(|x| x.0.clone()).collect::<Vec<_>>(),
        step.args.as_slice(),
        false,
    );

    let mut context = premises
        .iter()
        .map(|x| (x.1, x.2.clone()))
        .collect::<HashMap<_, _>>();

    if let Err(err) = trace {
        return Err(CheckerError::DrupFormatError(err));
    }

    let mut ids = IdHelper::new(&step.id);
    let mut trace = trace.unwrap();
    trace.retain(|x| match x {
        DRupProofAction::Delete(_) => false,
        _ => true,
    });

    for (arg_index, rup_story) in trace.iter().enumerate() {
        match rup_story {
            DRupProofAction::RupStory(rup_clause, rup_history) => {
                let mut rup: Vec<(IndexSet<(bool, Rc<Term>)>, u64)> = rup_history
                    .iter()
                    .map(|(vec, _, key)| (vec.clone(), *key))
                    .collect();
                let pivots: Vec<_> = rup_history.iter().map(|(_, term, _)| term).collect();

                let mut resolutions = vec![];
                for i in (0..rup_history.len() - 1).rev() {
                    let pivot = pivots[i].as_ref().unwrap();

                    if rup[i + 1].0.contains(&(!pivot.0, pivot.1.clone())) {
                        let resolvent_indexset: IndexSet<(bool, Rc<Term>)> = resolve(
                            rup[i].0.borrow(),
                            rup[i + 1].0.borrow(),
                            (pivot.0, pivot.1.clone()),
                        );
                        let resolvent: Vec<Rc<Term>> = resolvent_indexset
                            .iter()
                            .map(|(polarity, term)| {
                                if *polarity {
                                    (*term).clone()
                                } else {
                                    build_term!(pool, (not { (*term).clone() }))
                                }
                            })
                            .collect();

                        let resolvent_cl_term = if resolvent.len() > 0 {
                            build_term!(pool, (cl[resolvent.to_vec()]))
                        } else {
                            resolvent[0].clone()
                        };

                        let resolvent_hash = hash_term(pool, resolvent_cl_term);
                        resolutions.push(ResolutionStep::Resolvent(
                            pivot,
                            rup[i].1,
                            rup[i + 1].1,
                            (resolvent, resolvent_indexset.clone(), resolvent_hash),
                        ));

                        rup[i] = (resolvent_indexset, resolvent_hash);
                    } else {
                        rup[i] = (rup[i + 1].0.clone(), rup[i + 1].1);
                        resolutions.push(ResolutionStep::UnChanged(rup[i + 1].0.clone(), rup[i].1));
                    }
                }

                match &resolutions[resolutions.len() - 1] {
                    ResolutionStep::Resolvent(_, _, _, (resolvent, _, _)) => {
                        if resolvent.len() > 0 {
                            return Err(CheckerError::DrupFormatError(
                                DrupFormatError::NoFinalBottomInDrup,
                            ));
                        }
                    }
                    ResolutionStep::UnChanged(resolvent, _) => {
                        if resolvent.len() > 0 {
                            return Err(CheckerError::DrupFormatError(
                                DrupFormatError::NoFinalBottomInDrup,
                            ));
                        }
                    }
                }

                resolutions.retain(|step| match step {
                    ResolutionStep::Resolvent(_, _, _, (resolvent, _, _)) => {
                        resolvent.len() > 0 || rup_clause.len() == 0
                    }
                    ResolutionStep::UnChanged(_, _) => false, // Since unchanged are trivally avaliable we can ignore them
                });

                for (i, resolution_step) in resolutions.iter().enumerate() {
                    match resolution_step {
                        ResolutionStep::Resolvent(
                            pivot,
                            c,
                            d,
                            (resolvent, resolvent_indexset, resolvent_hash),
                        ) => {
                            let mut clause = resolvent.clone();
                            let mut hash = *resolvent_hash;

                            let mut proof_step = Rc::new(ProofNode::Step(StepNode {
                                id: ids.next_id(),
                                depth: step.depth,
                                clause: clause,
                                rule: "resolution".to_owned(),
                                premises: vec![
                                    (*context.get(c).unwrap()).clone(),
                                    (*context.get(d).unwrap()).clone(),
                                ],
                                discharge: Vec::new(),
                                args: vec![pivot.1.clone(), pool.bool_constant(pivot.0)],
                                previous_step: None,
                            }));

                            let rup_clause: IndexSet<(bool, Rc<Term>)> =
                                rup_clause.iter().map(|(k, v)| (*k, (*v).clone())).collect();

                            if i == resolutions.len() - 1
                                && resolvent_indexset.is_subset(&rup_clause)
                                && resolvent_indexset != &rup_clause
                            {
                                clause = rup_clause
                                    .iter()
                                    .map(|(polarity, term)| {
                                        if *polarity {
                                            (*term).clone()
                                        } else {
                                            build_term!(pool, (not { (*term).clone() }))
                                        }
                                    })
                                    .collect();

                                let cl_clause = if clause.len() > 0 {
                                    build_term!(pool, (cl[clause.clone()]))
                                } else {
                                    clause[0].clone()
                                };
                                
                                hash = hash_term(pool, cl_clause);
                                proof_step = Rc::new(ProofNode::Step(StepNode {
                                    id: ids.next_id(),
                                    depth: step.depth,
                                    clause: clause,
                                    rule: "weakening".to_owned(),
                                    premises: vec![proof_step],
                                    discharge: Vec::new(),
                                    args: Vec::new(),
                                    previous_step: None,
                                }));
                            }

                            if i == resolutions.len() - 1 {
                                if arg_index == trace.len() - 1 {
                                    return Ok(proof_step);
                                }
                            }

                            context.insert(hash, proof_step);
                        }

                        ResolutionStep::UnChanged(_, _) => unreachable!(),
                    }
                }
            }

            DRupProofAction::Delete(_) => unreachable!(),
        }
    }

    unreachable!()
}
