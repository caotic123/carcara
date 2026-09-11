use std::{
    collections::{BTreeMap, HashSet},
    time::{Duration, Instant},
};

use egglog_proofs::{
    proof::{Justification, ProofId, ProofStore},
    CommandOutput, EGraph,
};

const RAW_RARE_PROGRAM: &str = include_str!("fixtures/raw_rare_ite_then_false.egg");
const GOAL: &str = "(= $lhs (And (Not (Var \"c\")) (Bool true)))";

#[derive(Debug, PartialEq, Eq)]
struct ReplayedRule {
    name: String,
    lhs: String,
    rhs: String,
    substitution: BTreeMap<String, String>,
}

fn run(program_tail: &str, proofs: bool) -> (Vec<CommandOutput>, Duration) {
    let mut egraph = if proofs {
        EGraph::new_with_proofs()
    } else {
        EGraph::new(1)
    };
    let program = format!("{RAW_RARE_PROGRAM}\n{program_tail}");
    let start = Instant::now();
    let output = egraph
        .parse_and_run_program(None, &program)
        .expect("raw RARE rewrite program should run");
    (output, start.elapsed())
}

fn reconstruct_rule_replay(proof_store: &ProofStore, root: ProofId) -> Vec<ReplayedRule> {
    fn visit(
        proof_store: &ProofStore,
        proof_id: ProofId,
        seen: &mut HashSet<ProofId>,
        replay: &mut Vec<ReplayedRule>,
    ) {
        if !seen.insert(proof_id) {
            return;
        }

        let proof = proof_store.get(proof_id);
        match proof.justification() {
            Justification::Rule { name, premise_proofs, substitution } => {
                for premise in premise_proofs {
                    visit(proof_store, *premise, seen, replay);
                }
                let term_dag = proof_store.term_dag();
                replay.push(ReplayedRule {
                    name: name.clone(),
                    lhs: term_dag.to_string(proof.lhs()),
                    rhs: term_dag.to_string(proof.rhs()),
                    substitution: substitution
                        .iter()
                        .map(|(variable, term)| (variable.clone(), term_dag.to_string(*term)))
                        .collect(),
                });
            }
            Justification::MergeFn { old_proof, new_proof, .. } => {
                visit(proof_store, *old_proof, seen, replay);
                visit(proof_store, *new_proof, seen, replay);
            }
            Justification::Trans(left, right) => {
                visit(proof_store, *left, seen, replay);
                visit(proof_store, *right, seen, replay);
            }
            Justification::Sym(inner) | Justification::ContainerNormalize { proof: inner } => {
                visit(proof_store, *inner, seen, replay);
            }
            Justification::Congr { proof, child_proof, .. } => {
                visit(proof_store, *proof, seen, replay);
                visit(proof_store, *child_proof, seen, replay);
            }
            Justification::Fiat | Justification::Eval => {}
        }
    }

    let mut replay = Vec::new();
    visit(proof_store, root, &mut HashSet::new(), &mut replay);
    replay
}

#[test]
fn raw_rare_rewrite_produces_replayable_certificate() {
    let normal_command = format!("(check {GOAL})");
    run(&normal_command, false);

    let proof_command = format!("(prove {GOAL})");
    let (outputs, _) = run(&proof_command, true);
    let (proof_store, proof_id) = outputs
        .iter()
        .find_map(|output| match output {
            CommandOutput::ProveExists { proof_store, proof_id } => Some((proof_store, *proof_id)),
            _ => None,
        })
        .expect("prove should return a proof certificate");

    let term_dag = proof_store.term_dag();
    let root = proof_store.get(proof_id);
    assert_eq!(
        term_dag.to_string(root.lhs()),
        "(Ite (Var \"c\") (Bool false) (Bool true))"
    );
    assert_eq!(
        term_dag.to_string(root.rhs()),
        "(And (Not (Var \"c\")) (Bool true))"
    );
    assert!(
        matches!(root.justification(), Justification::Sym(_)),
        "egglog may orient a rule equality opposite to the requested goal"
    );

    let replay = reconstruct_rule_replay(proof_store, proof_id);
    assert_eq!(replay.len(), 1, "unexpected certificate: {replay:#?}");

    let step = &replay[0];
    assert_eq!(step.name, "ite-then-false");
    assert_eq!(
        step.substitution.get("c").map(String::as_str),
        Some("(Var \"c\")")
    );
    assert_eq!(
        step.substitution.get("x").map(String::as_str),
        Some("(Bool true)")
    );

    eprintln!("egglog proof:\n{}", proof_store.proof_to_string(proof_id));
    eprintln!("reconstructed raw-rule replay:\n{replay:#?}");
}

#[test]
#[ignore = "diagnostic microbenchmark; run explicitly with --ignored --nocapture"]
fn compare_raw_rare_proof_mode_overhead() {
    const SAMPLES: usize = 10;

    fn median(mut samples: Vec<Duration>) -> Duration {
        samples.sort_unstable();
        samples[samples.len() / 2]
    }

    let normal_command = format!("(check {GOAL})");
    let proof_command = format!("(prove {GOAL})");

    // Warm both paths before collecting a small smoke-test sample. This is not
    // a stable benchmark and intentionally has no performance assertion.
    run(&normal_command, false);
    run(&normal_command, true);
    run(&proof_command, true);

    let normal = median(
        (0..SAMPLES)
            .map(|_| run(&normal_command, false).1)
            .collect(),
    );
    let proof_mode = median((0..SAMPLES).map(|_| run(&normal_command, true).1).collect());
    let certificate = median((0..SAMPLES).map(|_| run(&proof_command, true).1).collect());
    let proof_mode_ratio = proof_mode.as_secs_f64() / normal.as_secs_f64();
    let certificate_ratio = certificate.as_secs_f64() / normal.as_secs_f64();

    eprintln!(
        "raw RARE smoke timing ({SAMPLES} samples): normal={normal:?}, proof-mode={proof_mode:?} ({proof_mode_ratio:.2}x), checked-certificate={certificate:?} ({certificate_ratio:.2}x)"
    );
}
