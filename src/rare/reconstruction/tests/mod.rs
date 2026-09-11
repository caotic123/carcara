//! Tests of the post-hoc reconstruction pipeline: fixture e-graphs run
//! through the proof-producing egglog backend, production runs of the RARE
//! engine on sliced and full cvc5 proofs, checker-side recomputation, Alethe
//! elaboration, and the env-driven corpus sweep.
use std::{
    collections::{BTreeMap, HashMap, HashSet},
    path::{Path, PathBuf},
    time::{Duration, Instant},
};

use crate::{
    RunEgglogOptions, ast::ProofNode, elaborator::rare_hole::AletheElaborator, parser,
    rare::engine::run_egglog,
};
use super::*;
use egglog::EGraph as ProductionEGraph;
use egglog_proofs::{
    CommandOutput, EGraph as ProofEGraph, SerializeConfig as ProofSerializeConfig,
};

mod raw_rare_proofs;

const PROGRAM: &str = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/raw_rare_posthoc.egg"));

fn rules() -> Vec<Rewrite> {
    use Pattern::{App, Var};

    vec![
        Rewrite {
            name: "ite-then-false",
            lhs: App("Ite", vec![Var("c"), App("False", vec![]), Var("x")]),
            rhs: App("And", vec![App("Not", vec![Var("c")]), Var("x")]),
        },
        Rewrite {
            name: "and-true-right",
            lhs: App("And", vec![Var("x"), App("True", vec![])]),
            rhs: Var("x"),
        },
    ]
}

fn source() -> Term {
    Term::new(
        "Ite",
        vec![Term::leaf("Atom"), Term::leaf("False"), Term::leaf("True")],
    )
}

fn target() -> Term {
    Term::new("Not", vec![Term::leaf("Atom")])
}

fn nested_source() -> Term {
    Term::new("Not", vec![source()])
}

fn nested_target() -> Term {
    Term::new("Not", vec![target()])
}

fn run_normal() -> (ProofEGraph, Duration) {
    let mut egraph = ProofEGraph::new(1);
    let start = Instant::now();
    egraph
        .parse_and_run_program(None, PROGRAM)
        .expect("raw RARE saturation should run");
    (egraph, start.elapsed())
}

#[test]
fn reconstructs_from_provenance_free_saturated_egraph() {
    let (egraph, _) = run_normal();
    let snapshot = capture(&egraph);
    let rules = rules();
    let reconstruction = reconstruct_detailed(
        &snapshot,
        &source(),
        &target(),
        &rules,
        SearchStrategy::default(),
    );
    let certificate = reconstruction
        .certificate
        .expect("known RARE rules should connect the two terms in the saturated class");

    assert!(certificate.verify(&rules));
    assert_eq!(certificate.lhs(), &source());
    assert_eq!(certificate.rhs(), &target());
    let mut names = Vec::new();
    certificate.rule_names(&mut names);
    assert_eq!(names, ["ite-then-false", "and-true-right"]);
    assert!(reconstruction.stats.lhs_matches >= 2);
    assert!(reconstruction.stats.rule_instances >= 2);
    assert!(reconstruction.stats.relation_rows_examined > 0);

    let nested = reconstruct(
        &snapshot,
        &nested_source(),
        &nested_target(),
        &rules,
        SearchStrategy::default(),
    )
    .expect("the structural traversal should reconstruct rewriting under Not");
    assert!(nested.verify(&rules));
    assert!(nested.contains_congruence());

    // The e-graph still says source and target are equal, but without the
    // second declarative rule there is no independently checkable replay.
    assert!(snapshot.same_class(&source(), &target()));
    assert!(
        reconstruct(
            &snapshot,
            &source(),
            &target(),
            &rules[..1],
            SearchStrategy::default(),
        )
        .is_none()
    );

    eprintln!(
        "post-hoc certificate reconstructed from e-graph: stats={:?}\n{certificate:#?}",
        reconstruction.stats
    );
}

#[test]
#[ignore = "diagnostic microbenchmark; run explicitly with --ignored --nocapture"]
fn compare_posthoc_reconstruction_with_egglog_proofs() {
    const SAMPLES: usize = 100;

    fn median(mut samples: Vec<Duration>) -> Duration {
        samples.sort_unstable();
        samples[samples.len() / 2]
    }

    fn run_reconstruction(egraph: &ProofEGraph, rules: &[Rewrite]) -> Duration {
        let start = Instant::now();
        let snapshot = capture(egraph);
        let certificate = reconstruct(
            &snapshot,
            &source(),
            &target(),
            rules,
            SearchStrategy::default(),
        )
        .expect("post-hoc reconstruction should succeed");
        assert!(certificate.verify(rules));
        start.elapsed()
    }

    fn run_egglog_proofs() -> Duration {
        let mut egraph = ProofEGraph::new_with_proofs();
        let program = format!("{PROGRAM}\n(prove (= $lhs (Not (Atom))))");
        let start = Instant::now();
        let outputs = egraph
            .parse_and_run_program(None, &program)
            .expect("egglog proof production should succeed");
        assert!(
            outputs
                .iter()
                .any(|output| matches!(output, CommandOutput::ProveExists { .. }))
        );
        start.elapsed()
    }

    let rules = rules();
    let (saturated, _) = run_normal();
    run_normal();
    run_reconstruction(&saturated, &rules);
    run_egglog_proofs();

    let normal = median((0..SAMPLES).map(|_| run_normal().1).collect());
    let reconstruction = median(
        (0..SAMPLES)
            .map(|_| run_reconstruction(&saturated, &rules))
            .collect(),
    );
    let posthoc = normal + reconstruction;
    let egglog_proofs = median((0..SAMPLES).map(|_| run_egglog_proofs()).collect());

    eprintln!(
        "raw RARE reconstruction ({SAMPLES} samples): normal={normal:?}, reconstruction={reconstruction:?}, estimated-posthoc-total={posthoc:?} ({:.2}x), egglog-proofs={egglog_proofs:?} ({:.2}x)",
        posthoc.as_secs_f64() / normal.as_secs_f64(),
        egglog_proofs.as_secs_f64() / normal.as_secs_f64(),
    );
}

fn repository_path(relative: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(relative)
}

fn encoded_mk(term: Pattern) -> Pattern {
    Pattern::App("Mk", vec![term])
}

fn encoded_call(operator: &'static str, arguments: Vec<Pattern>) -> Pattern {
    let arguments = arguments
        .into_iter()
        .rev()
        .fold(Pattern::App("Empty", vec![]), |tail, argument| {
            Pattern::App("Args", vec![encoded_mk(argument), tail])
        });
    Pattern::App(operator, vec![arguments])
}

fn encoded_formula(operator: &'static str, arguments: Vec<Pattern>) -> Pattern {
    encoded_mk(encoded_call(operator, arguments))
}

fn encoded_eq_symm_rule() -> Rewrite {
    use Pattern::Var;

    Rewrite {
        name: "eq-symm",
        lhs: encoded_formula("@=", vec![Var("t1"), Var("s1")]),
        rhs: encoded_formula("@=", vec![Var("s1"), Var("t1")]),
    }
}

fn encoded_bool_double_not_elim_rule() -> Rewrite {
    use Pattern::Var;

    Rewrite {
        name: "bool-double-not-elim",
        lhs: encoded_formula("@not", vec![encoded_call("@not", vec![Var("t1")])]),
        rhs: encoded_mk(Var("t1")),
    }
}

fn encoded_bool_or_false_rule() -> Rewrite {
    use Pattern::{App, Var};

    Rewrite {
        name: "bool-or-false",
        lhs: encoded_formula("@or", vec![Var("x"), App("Bool", vec![App("false", vec![])])]),
        rhs: encoded_mk(Var("x")),
    }
}

struct QfUfRun {
    egraph: ProductionEGraph,
    generated_program: String,
    lhs: Term,
    rhs: Term,
    saturation: Duration,
    conclusion: crate::ast::Rc<crate::ast::Term>,
    rare_rules: indexmap::IndexMap<String, crate::ast::rare_rules::RuleDefinition>,
}

/// Build the proof node forest from the parsed commands and return the node
/// carrying `root_id` — the sliced proof's hole.
fn node_with_root_id(
    commands: Vec<crate::ast::ProofCommand>,
    root_id: &str,
) -> Option<crate::ast::Rc<ProofNode>> {
    let forest = crate::ast::ProofNodeForest::from_commands(commands);
    let mut found = None;
    for root in &forest.0 {
        root.traverse(|node| {
            if found.is_none() && node.id() == root_id {
                found = Some(node.clone());
            }
        });
    }
    found
}

fn run_qf_uf_case(
    problem_relative: &str,
    proof_relative: &str,
    rare_relative: &str,
    root_id: &str,
    required_rule: Option<&str>,
) -> QfUfRun {
    let problem_path = repository_path(problem_relative);
    let proof_path = repository_path(proof_relative);
    let rare_path = repository_path(rare_relative);
    let parser_config = parser::Config::default()
        .expand_lets(true)
        .allow_int_real_subtyping(true)
        .parse_hole_args(true);
    let (mut problem_text, mut proof_text, mut rare_text) =
        (String::new(), String::new(), String::new());
    let (_, proof, database, mut pool) = parser::parse_instance(
        parser::Source::file(&problem_path, &mut problem_text)
            .expect("QF_UF problem should exist"),
        parser::Source::file(&proof_path, &mut proof_text).expect("QF_UF proof should exist"),
        Some(
            parser::Source::file(&rare_path, &mut rare_text).expect("RARE database should exist"),
        ),
        parser_config,
    )
    .expect("QF_UF instance should parse");
    if let Some(required_rule) = required_rule {
        assert!(
            database.rules.contains_key(required_rule),
            "the real RARE database should contain the rule being reconstructed"
        );
    }
    let node = node_with_root_id(proof.commands, root_id)
        .expect("sliced proof should contain the requested root");
    let conclusion = node.clause()[0].clone();

    let start = Instant::now();
    let (result, generated_program) = run_egglog(
        &mut pool,
        (conclusion.clone(), &node),
        &database,
        RunEgglogOptions::default(),
    );
    let saturation = start.elapsed();
    let egraph = result.expect("production egglog should prove the QF_UF equality");
    let (lhs, rhs) = generated_goals(&generated_program);

    QfUfRun {
        egraph,
        generated_program,
        lhs,
        rhs,
        saturation,
        conclusion,
        rare_rules: database.rules.clone(),
    }
}

fn run_qf_uf_t37() -> QfUfRun {
    run_qf_uf_case(
        "tests/rare/sliced_proofs/Examples/QF_UF/2018-Goel-hwbench/\
         QF_UF_brp.5.prop1_ab_reg_max/QF_UF_brp.5.prop1_ab_reg_max.smt2",
        "tests/rare/sliced_proofs/Examples/QF_UF/2018-Goel-hwbench/\
         QF_UF_brp.5.prop1_ab_reg_max/\
         QF_UF_brp.5.prop1_ab_reg_max__from-t37.smt2.alethe",
        "tests/rare/big.rare",
        "t37",
        Some("eq-symm"),
    )
}

fn run_qf_uf_double_not_t3() -> QfUfRun {
    run_qf_uf_case(
        "tests/rare/sliced_proofs/Examples/QF_UF/20170829-Rodin/\
         smt249825283571301584/smt249825283571301584.smt2",
        "tests/rare/sliced_proofs/Examples/QF_UF/20170829-Rodin/\
         smt249825283571301584/smt249825283571301584__from-t3.smt2.alethe",
        "tests/rare/big.rare",
        "t3",
        Some("bool-double-not-elim"),
    )
}

/// The distinct-elimination solver from `rare::computational::distinct_elim`,
/// translated to a standalone egglog program over a three-element distinct.
const RAW_DISTINCT_PROGRAM: &str = r#"
(datatype Term
  (Const String)
  (Empty)
  (Args Term Term)
  (Mk Term))
(constructor @distinct (Term) Term)
(constructor @and (Term) Term)
(constructor @not (Term) Term)
(constructor @= (Term) Term)
(relation Avaliable (Term))
(function to_formula (Term Term Term) Term :no-merge)
(relation to_formula_rel (Term Term Term))
(ruleset list-ruleset)

; Header axioms from create_headers: Args associativity (both directions)
; and Mk injectivity.
(rewrite (Args (Args t1 t2) t3) (Args t1 (Args t2 t3)))
(rewrite (Args t1 (Args t2 t3)) (Args (Args t1 t2) t3))
(rule ((= (Mk x) (Mk y))) ((union x y)))

(rule ((to_formula_rel (Empty) k (Empty)))
      ((set (to_formula (Empty) k (Empty)) (Empty)))
      :ruleset list-ruleset)
(rule ((= res (Args r rs))
       (to_formula_rel res y (Empty)))
      ((to_formula_rel rs r rs))
      :ruleset list-ruleset)
(rule ((= xs (Args x rxs))
       (to_formula_rel res y xs))
      ((to_formula_rel res y rxs))
      :ruleset list-ruleset)
(rule ((to_formula_rel res y (Args x rxs))
       (= (to_formula res y rxs) f))
      ((set (to_formula res y (Args x rxs))
            (Args (Mk (@not (Args (Mk (@= (Args y (Args x (Empty))))) (Empty)))) f)))
      :ruleset list-ruleset)
(rule ((to_formula_rel (Args r res) y (Empty))
       (= (to_formula res r res) f))
      ((set (to_formula (Args r res) y (Empty)) f))
      :ruleset list-ruleset)
(rule ((Avaliable (Mk (@distinct (Args x xs))))
       (= (to_formula xs x xs) f))
      ((union (Mk (@and f)) (Mk (@distinct (Args x xs)))))
      :ruleset list-ruleset)
(rule ((Avaliable (Mk (@distinct (Args x xs)))))
      ((to_formula_rel xs x xs))
      :ruleset list-ruleset)

(let a (Mk (Const "a")))
(let b (Mk (Const "b")))
(let c (Mk (Const "c")))
(let goal_lhs (Mk (@distinct (Args a (Args b (Args c (Empty)))))))
(Avaliable goal_lhs)
; Complete the fold before the default ruleset (Args associativity) runs:
; interleaving them makes rule 4 match reassociated list splits and fail
; to_formula's assert-eq merge.
(run-schedule (repeat 30 (run list-ruleset)))
(run-schedule (repeat 10 (run)))
"#;

/// Extract the smallest term of `eclass` whose enodes avoid `banned_ops`,
/// for diagnostic rendering of class members.  Memoized per class: large
/// snapshots hold classes with many equivalent enodes, and unmemoized
/// extraction revisits them combinatorially.
fn extract_avoiding(
    snapshot: &EGraphSnapshot,
    eclass: u32,
    banned_ops: &[&str],
    visiting: &mut HashSet<u32>,
    memo: &mut HashMap<u32, Option<Term>>,
) -> Option<Term> {
    if let Some(cached) = memo.get(&eclass) {
        return cached.clone();
    }
    if !visiting.insert(eclass) {
        return None;
    }
    let mut best: Option<Term> = None;
    for &index in snapshot.class_nodes.get(eclass as usize)? {
        let node = &snapshot.nodes[index as usize];
        let op = &snapshot.ops.names[node.op as usize];
        if banned_ops.contains(&op.as_str()) {
            continue;
        }
        let Some(children) = node
            .child_classes
            .clone()
            .iter()
            .map(|&class| extract_avoiding(snapshot, class, banned_ops, visiting, memo))
            .collect::<Option<Vec<_>>>()
        else {
            continue;
        };
        let candidate = Term::new(op, children);
        if best
            .as_ref()
            .map_or(true, |current| candidate.size() < current.size())
        {
            best = Some(candidate);
        }
    }
    visiting.remove(&eclass);
    // Cache successes only: a found term is a genuine class member either
    // way, while a failure may be an artifact of the cycle guard and the
    // path taken to reach the class.
    if best.is_some() {
        memo.insert(eclass, best.clone());
    }
    best
}

#[test]
#[ignore = "diagnostic dump of the e-graph produced by the raw distinct-elimination solver"]
fn inspect_distinct_solver_egraph_minimal() {
    let mut egraph = ProductionEGraph::default();
    egraph
        .parse_and_run_program(None, RAW_DISTINCT_PROGRAM)
        .expect("raw distinct solver program should run");
    let snapshot = EGraphSnapshot::capture_production(&egraph);

    eprintln!(
        "egraph: {} enodes, {} classes",
        snapshot.nodes.len(),
        snapshot.class_nodes.len(),
    );
    let mut op_counts: BTreeMap<&str, usize> = BTreeMap::new();
    for node in &snapshot.nodes {
        *op_counts
            .entry(snapshot.ops.names[node.op as usize].as_str())
            .or_default() += 1;
    }
    eprintln!("operators in the serialized e-graph: {op_counts:#?}");

    let lhs = Term::new(
        "Mk",
        vec![Term::new(
            "@distinct",
            vec![["a", "b", "c"].iter().rev().fold(
                Term::leaf("Empty"),
                |tail, name| {
                    Term::new(
                        "Args",
                        vec![
                            Term::new("Mk", vec![Term::new("Const", vec![Term::leaf(&format!("\"{name}\""))])]),
                            tail,
                        ],
                    )
                },
            )],
        )],
    );
    let mut cache = HashMap::new();
    let Some(eclass) = snapshot.class_of(&lhs, &mut cache) else {
        panic!("the distinct goal term should be represented in the snapshot");
    };
    eprintln!("goal class {eclass} holds:");
    for &index in &snapshot.class_nodes[eclass as usize] {
        let node = &snapshot.nodes[index as usize];
        eprintln!(
            "  {}({})",
            snapshot.ops.names[node.op as usize],
            node.child_classes
                .iter()
                .map(|class| class.to_string())
                .collect::<Vec<_>>()
                .join(", "),
        );
    }

    let rhs = extract_avoiding(
        &snapshot,
        eclass,
        &["@distinct", "to_formula"],
        &mut HashSet::new(),
        &mut HashMap::new(),
    )
    .expect("the goal class should hold a term besides the distinct application");
    eprintln!("distinct term  = {}", lhs.to_egglog());
    eprintln!("expanded term  = {}", rhs.to_egglog());
    eprintln!("same_class     = {}", snapshot.same_class(&lhs, &rhs));

    let reconstruction = reconstruct_detailed(
        &snapshot,
        &lhs,
        &rhs,
        &[],
        SearchStrategy::default(),
    );
    eprintln!(
        "declarative reconstruction: found={}, stats={:?}",
        reconstruction.certificate.is_some(),
        reconstruction.stats,
    );

    // The and-term the goal encoding would produce: conjuncts directly as
    // the operator's argument list, not wrapped in an extra Args cell.
    let constant = |name: &str| Term::new("Mk", vec![Term::new("Const", vec![Term::leaf(&format!("\"{name}\""))])]);
    let not_equal = |x: &str, y: &str| {
        let equality = Term::new(
            "Mk",
            vec![Term::new(
                "@=",
                vec![Term::new(
                    "Args",
                    vec![constant(x), Term::new("Args", vec![constant(y), Term::leaf("Empty")])],
                )],
            )],
        );
        Term::new(
            "Mk",
            vec![Term::new(
                "@not",
                vec![Term::new("Args", vec![equality, Term::leaf("Empty")])],
            )],
        )
    };
    let conjuncts = [("a", "b"), ("a", "c"), ("b", "c")]
        .iter()
        .rev()
        .fold(Term::leaf("Empty"), |tail, (x, y)| {
            Term::new("Args", vec![not_equal(x, y), tail])
        });
    let wrapped_list = Term::new("Args", vec![conjuncts.clone(), Term::leaf("Empty")]);
    eprintln!(
        "same_class(f, (Args f (Empty))) = {:?}",
        snapshot.same_class(&conjuncts, &wrapped_list),
    );
    let goal_encoded_and = Term::new("Mk", vec![Term::new("@and", vec![conjuncts])]);
    eprintln!("goal-encoded and = {}", goal_encoded_and.to_egglog());
    eprintln!(
        "same_class(distinct, goal-encoded and) = {:?}",
        snapshot.same_class(&lhs, &goal_encoded_and),
    );
    eprintln!(
        "goal-encoded and represented in snapshot = {}",
        snapshot.class_of_term(&goal_encoded_and).is_some(),
    );
}

/// Certificates elaborate into Alethe steps: trusted `TRUST_THEORY_REWRITE`
/// holes named after the RARE rule or computational rewrite, the native
/// `distinct_elim` rule for distinct expansion (with the two-element seam
/// collapsed onto it), and `trans`/`cong` glue over decoded terms.
#[test]
fn elaborates_certificates_to_alethe_steps() {
    // distinct(a, b) = (not (= b a)): distinct_elim + aci collapse + eq-symm
    // under a negation.
    let snapshot = raw_solver_snapshot(
        r#"
(rewrite (Mk (@and (Args (Mk x) (Empty)))) (Mk x))
(rewrite (Mk (@= (Args (Mk t1) (Args (Mk s1) (Empty)))))
         (Mk (@= (Args (Mk s1) (Args (Mk t1) (Empty))))))
(let a (Mk (Const "a")))
(let b (Mk (Const "b")))
(let d2 (Mk (@distinct (Args a (Args b (Empty))))))
(Avaliable d2)
(run-schedule (repeat 20 (run list-ruleset) (run)))
"#,
    );
    let [a, b] = ["a", "b"].map(encoded_const);
    let source = encoded_app("@distinct", vec![a.clone(), b.clone()]);
    let target = encoded_not_equal(&b, &a);
    let rules = [encoded_eq_symm_rule()];
    let certificate =
        reconstruct(&snapshot, &source, &target, &rules, SearchStrategy::default())
            .expect("the mixed chain should reconstruct");
    let steps = AletheElaborator::elaborate(&certificate, "t1")
        .expect("the mixed certificate should elaborate to Alethe");
    eprintln!("distinct_symm elaboration:\n{}", steps.join("\n"));
    assert!(steps
        .iter()
        .any(|step| step.contains("(= (distinct a b) (not (= a b))") && step.contains(":rule distinct_elim")));
    assert!(steps
        .iter()
        .any(|step| step.contains(":rule hole") && step.contains("\"eq-symm\"")));
    assert!(steps.iter().any(|step| step.contains(":rule cong")));
    assert!(steps
        .last()
        .is_some_and(|step| step.contains("(= (distinct a b) (not (= b a))")
            && step.contains(":rule trans")));

    // not(not(distinct(a,b,c))) = pairwise and: a trusted RARE step chained
    // with the native three-element distinct_elim.
    let snapshot = raw_solver_snapshot(
        r#"
(rewrite (Mk (@not (Args (Mk (@not (Args (Mk t1) (Empty)))) (Empty)))) (Mk t1))
(let a (Mk (Const "a")))
(let b (Mk (Const "b")))
(let c (Mk (Const "c")))
(let d3 (Mk (@distinct (Args a (Args b (Args c (Empty)))))))
(let source (Mk (@not (Args (Mk (@not (Args d3 (Empty)))) (Empty)))))
(Avaliable source)
(Avaliable d3)
(run-schedule (repeat 40 (run list-ruleset) (run)))
"#,
    );
    let [a, b, c] = ["a", "b", "c"].map(encoded_const);
    let distinct = encoded_app("@distinct", vec![a.clone(), b.clone(), c.clone()]);
    let source = encoded_app("@not", vec![encoded_app("@not", vec![distinct])]);
    let target = encoded_app(
        "@and",
        vec![
            encoded_not_equal(&a, &b),
            encoded_not_equal(&a, &c),
            encoded_not_equal(&b, &c),
        ],
    );
    let rules = [encoded_bool_double_not_elim_rule()];
    let certificate =
        reconstruct(&snapshot, &source, &target, &rules, SearchStrategy::default())
            .expect("the interior chain should reconstruct");
    let steps = AletheElaborator::elaborate(&certificate, "t2")
        .expect("the interior certificate should elaborate to Alethe");
    eprintln!("interior distinct elaboration:\n{}", steps.join("\n"));
    assert!(steps
        .iter()
        .any(|step| step.contains(":rule hole") && step.contains("\"bool-double-not-elim\"")));
    assert!(steps.iter().any(|step| {
        step.contains(":rule distinct_elim")
            && step.contains("(= (distinct a b c) (and (not (= a b)) (not (= a c)) (not (= b c))")
    }));
    assert!(steps
        .last()
        .is_some_and(|step| step.contains(":rule trans")));
}

/// The `distinct_symm` fixture through the full production pipeline: the
/// Alethe step claims `(= (distinct a b) (not (= b a)))`, so the certificate
/// must chain distinct elimination, the ACI singleton collapse, and the
/// `eq-symm` rule from the RARE file applied under the negation.
#[test]
fn reconstructs_distinct_symm_mix_from_production_egraph() {
    let run = run_qf_uf_case(
        "tests/rare/computational_mix/distinct_symm.smt2",
        "tests/rare/computational_mix/distinct_symm.alethe",
        "tests/rare/computational_mix/mix.rare",
        "t1",
        Some("eq-symm"),
    );
    let snapshot = EGraphSnapshot::capture_production(&run.egraph);
    let rules = [encoded_eq_symm_rule()];
    let reconstruction = reconstruct_detailed(
        &snapshot,
        &run.lhs,
        &run.rhs,
        &rules,
        SearchStrategy::default(),
    );
    let certificate = reconstruction
        .certificate
        .expect("distinct elimination, ACI collapse, and eq-symm should chain");

    assert!(certificate.verify(&rules));
    assert_eq!(certificate.lhs(), &run.lhs);
    assert_eq!(certificate.rhs(), &run.rhs);
    let mut names = Vec::new();
    certificate.rule_names(&mut names);
    assert_eq!(names, ["eq-symm"]);
    assert!(certificate.contains_computation(Computation::DistinctElim));
    assert!(certificate.contains_computation(Computation::AciNorm));
    assert!(certificate.contains_congruence());
    eprintln!(
        "distinct_symm mix: saturation={:?}, stats={:?}",
        run.saturation, reconstruction.stats,
    );
}

/// The `or_eval` fixture through the full production pipeline: the step
/// claims `(= (or p (and true false)) p)`, so evaluation must fold the
/// conjunction inside a congruence obligation before the RARE rule
/// `bool-or-false` strips the identity.
#[test]
fn reconstructs_or_evaluation_mix_from_production_egraph() {
    let run = run_qf_uf_case(
        "tests/rare/computational_mix/or_eval.smt2",
        "tests/rare/computational_mix/or_eval.alethe",
        "tests/rare/computational_mix/mix.rare",
        "t1",
        Some("bool-or-false"),
    );
    let snapshot = EGraphSnapshot::capture_production(&run.egraph);
    let rules = [encoded_bool_or_false_rule()];
    let reconstruction = reconstruct_detailed(
        &snapshot,
        &run.lhs,
        &run.rhs,
        &rules,
        SearchStrategy::default(),
    );
    let certificate = reconstruction
        .certificate
        .expect("evaluation under congruence should chain with bool-or-false");

    assert!(certificate.verify(&rules));
    assert_eq!(certificate.lhs(), &run.lhs);
    assert_eq!(certificate.rhs(), &run.rhs);
    let mut names = Vec::new();
    certificate.rule_names(&mut names);
    assert_eq!(names, ["bool-or-false"]);
    assert!(certificate.contains_computation(Computation::Evaluation));
    eprintln!(
        "or_eval mix: saturation={:?}, stats={:?}",
        run.saturation, reconstruction.stats,
    );
}

/// Round-trip emitted steps through the real Carcara checker against the
/// original problem and RARE database.
fn check_with_carcara(problem: &Path, steps: &[String], rare: &Path) -> Result<(), String> {
    let proof_text = format!("{}\n", steps.join("\n"));
    let problem_text = std::fs::read_to_string(problem).map_err(|error| error.to_string())?;
    let rare_text = std::fs::read_to_string(rare).map_err(|error| error.to_string())?;
    crate::check(
        parser::Source::new(problem, &problem_text),
        parser::Source::new(Path::new("<emitted-steps>"), &proof_text),
        Some(parser::Source::new(rare, &rare_text)),
        parser::Config::default()
            .expand_lets(true)
            .allow_int_real_subtyping(true)
            .parse_hole_args(true),
        crate::checker::Config::default(),
        false,
    )
    .map(|_| ())
    .or_else(|error| match error {
        // The emitted steps form a slice, not a refutation.  This error is
        // only raised after every command has been checked, so reaching it
        // means all emitted steps passed.
        crate::Error::DoesNotReachEmptyClause { .. } => Ok(()),
        error => Err(error.to_string()),
    })
}

/// Elaborate a production-run certificate to Alethe and round-trip it
/// through Carcara; returns the emitted steps.
fn elaborate_and_check(
    run: &QfUfRun,
    certificate: &Certificate,
    hole: &str,
    problem_relative: &str,
    rare_relative: &str,
) -> Vec<String> {
    let names = goal_variable_names(&run.lhs, &run.rhs, &run.conclusion);
    let rare_index = rare_arguments(&run.rare_rules);
    let steps = AletheElaborator::elaborate_full(certificate, hole, names, rare_index)
        .expect("certificate should elaborate to Alethe");
    if let Err(error) = check_with_carcara(
        &repository_path(problem_relative),
        &steps,
        &repository_path(rare_relative),
    ) {
        panic!(
            "emitted proof failed the Carcara check: {error}\n{}",
            steps.join("\n")
        );
    }
    steps
}

fn encoded_real(numer: i64, denom: i64) -> Term {
    Term::new(
        "Mk",
        vec![Term::new(
            "Real",
            vec![Term::leaf(&numer.to_string()), Term::leaf(&denom.to_string())],
        )],
    )
}

fn encoded_var(id: i64, sort: &str) -> Term {
    let sort = Term::new("Sort", vec![Term::new("Const", vec![Term::leaf(&format!("\"{sort}\""))])]);
    Term::new("Mk", vec![Term::new("Var", vec![Term::leaf(&id.to_string()), sort])])
}

/// The checker-side normal form is a ring normal form: distribution,
/// commutativity, cancellation, `to_real` erasure, constant division.
#[test]
fn arith_polynomials_normalize_modulo_ring_axioms() {
    let (x, y) = (encoded_var(1, "Int"), encoded_var(2, "Int"));
    let app = |op: &str, elements: Vec<Term>| encoded_app(op, elements);

    // (x + 1)(x - 1) = x*x - 1
    let product = app("@*", vec![app("@+", vec![x.clone(), encoded_num(1)]), app("@-", vec![x.clone(), encoded_num(1)])]);
    let expanded = app("@-", vec![app("@*", vec![x.clone(), x.clone()]), encoded_num(1)]);
    assert!(poly_equal(&product, &expanded));
    // 4x + 1 = 1 + 4x, n-ary and binarized alike
    let left = app("@+", vec![app("@*", vec![encoded_num(4), x.clone()]), encoded_num(1)]);
    let right = app("@+", vec![encoded_num(1), app("@*", vec![encoded_num(4), x.clone()])]);
    assert!(poly_equal(&left, &right));
    // to_real(x) / 2 = 1/2 * x
    let halved = app("@/", vec![app("@to_real", vec![x.clone()]), encoded_num(2)]);
    assert!(poly_equal(&halved, &app("@*", vec![encoded_real(1, 2), x.clone()])));
    // x - x + y = y; x + y != x - y
    assert!(poly_equal(&app("@+", vec![app("@-", vec![x.clone(), x.clone()]), y.clone()]), &y));
    assert!(!poly_equal(&app("@+", vec![x.clone(), y.clone()]), &app("@-", vec![x.clone(), y.clone()])));
    // division by a non-constant is opaque, but still a value
    let quotient = app("@/", vec![x.clone(), y.clone()]);
    assert!(poly_equal(&app("@*", vec![encoded_num(2), quotient.clone()]), &app("@+", vec![quotient.clone(), quotient])));
}

/// Relation keys identify equivalent relations across scaling, flipping,
/// negation, and integer tightening — and, unlike the solver's own key,
/// never tighten a strict bound with a fractional constant.
#[test]
fn arith_relation_keys_are_sound_on_fractional_strict_bounds() {
    let sorts = ArithSorts::default();
    let (x, y) = (encoded_var(1, "Int"), encoded_var(2, "Int"));
    let app = |op: &str, elements: Vec<Term>| encoded_app(op, elements);
    let twice = |term: &Term| app("@*", vec![encoded_num(2), term.clone()]);

    // 2x <= 2y  is  y >= x
    assert!(rel_equal(&app("@<=", vec![twice(&x), twice(&y)]), &app("@>=", vec![y.clone(), x.clone()]), &sorts));
    // x < y  is  not (x >= y)
    assert!(rel_equal(&app("@<", vec![x.clone(), y.clone()]), &app("@not", vec![app("@>=", vec![x.clone(), y.clone()])]), &sorts));
    // over the integers, x > 1  is  x >= 2
    assert!(rel_equal(&app("@>", vec![x.clone(), encoded_num(1)]), &app("@>=", vec![x.clone(), encoded_num(2)]), &sorts));
    // ... but to_real(x) > 1/2 is x >= 1, never x >= 2
    let fractional = app("@>", vec![app("@to_real", vec![x.clone()]), encoded_real(1, 2)]);
    assert!(!rel_equal(&fractional, &app("@>=", vec![x.clone(), encoded_num(2)]), &sorts));
    // equalities are keyed up to any nonzero scaling
    assert!(rel_equal(
        &app("@=", vec![app("@+", vec![x.clone(), y.clone()]), encoded_num(0)]),
        &app("@=", vec![app("@-", vec![encoded_num(0), y.clone()]), x.clone()]),
        &sorts
    ));
    // a boolean equality is not an arithmetic one
    let (p, q) = (encoded_var(3, "Bool"), encoded_var(4, "Bool"));
    assert!(!rel_equal(&app("@=", vec![p.clone(), q.clone()]), &app("@=", vec![q, p]), &sorts));
}

/// The `poly_norm` fixture through the full production pipeline: the step
/// claims `(= (+ (* 4 f3) 1) (+ 1 (* 4 f3)))`, which no RARE rule derives.
/// The solver proves it by polynomial normal forms without merging the two
/// sides, so the certificate is one arithmetic step, elaborated as
/// Carcara's native `poly_simp` rule.
#[test]
fn reconstructs_arith_poly_norm_from_production_egraph() {
    let run = run_qf_uf_case(
        "tests/rare/computational_mix/poly_norm.smt2",
        "tests/rare/computational_mix/poly_norm.alethe",
        "tests/rare/computational_mix/mix.rare",
        "t1",
        None,
    );
    let snapshot = EGraphSnapshot::capture_production(&run.egraph);
    assert!(
        !snapshot.same_class(&run.lhs, &run.rhs),
        "polynomial goals are proved by normal forms, not by union"
    );
    let rules = rules_from_generated_program(&run.generated_program);
    let sorts = ArithSorts::from_generated_program(&run.generated_program);
    let reconstruction = reconstruct_with_sorts(
        &snapshot,
        &run.lhs,
        &run.rhs,
        &rules,
        &sorts,
        SearchStrategy::default(),
    );
    let certificate = reconstruction
        .certificate
        .expect("polynomial normalization should reconstruct across classes");
    assert_eq!(
        certificate,
        Certificate::Computational {
            kind: Computation::ArithPolyNorm,
            lhs: run.lhs.clone(),
            rhs: run.rhs.clone(),
        }
    );
    let steps = elaborate_and_check(
        &run,
        &certificate,
        "t1",
        "tests/rare/computational_mix/poly_norm.smt2",
        "tests/rare/computational_mix/mix.rare",
    );
    assert_eq!(steps.len(), 1);
    assert!(
        steps[0].contains(":rule poly_simp") && !steps[0].contains(":rule hole"),
        "{}",
        steps[0]
    );
    eprintln!("poly_norm: saturation={:?}, steps={steps:#?}", run.saturation);
}

/// The `poly_norm_rel` fixture: `(= (not (not (<= (* 2 x) (* 2 y)))) (>= y x))`
/// mixes a RARE rewrite with relation normalization.  The e-graph strips
/// the double negation first, so the solver keys the class holding the
/// `<=`; reconstruction bridges to that enode with the RARE rule and then
/// takes one `poly_simp_rel` step.
#[test]
fn reconstructs_arith_poly_norm_rel_mixed_with_double_not_from_production_egraph() {
    let run = run_qf_uf_case(
        "tests/rare/computational_mix/poly_norm_rel.smt2",
        "tests/rare/computational_mix/poly_norm_rel.alethe",
        "tests/rare/computational_mix/mix.rare",
        "t1",
        Some("bool-double-not-elim"),
    );
    let snapshot = EGraphSnapshot::capture_production(&run.egraph);
    assert!(!snapshot.same_class(&run.lhs, &run.rhs));
    let rules = rules_from_generated_program(&run.generated_program);
    let sorts = ArithSorts::from_generated_program(&run.generated_program);
    let reconstruction = reconstruct_with_sorts(
        &snapshot,
        &run.lhs,
        &run.rhs,
        &rules,
        &sorts,
        SearchStrategy::default(),
    );
    let certificate = reconstruction
        .certificate
        .expect("double negation then relation normalization should chain");
    assert_eq!(certificate.lhs(), &run.lhs);
    assert_eq!(certificate.rhs(), &run.rhs);
    assert!(certificate.contains_computation(Computation::ArithPolyNormRel));
    let mut names = Vec::new();
    certificate.rule_names(&mut names);
    assert_eq!(names.len(), 1, "one RARE step bridges the negations: {names:?}");
    let steps = elaborate_and_check(
        &run,
        &certificate,
        "t1",
        "tests/rare/computational_mix/poly_norm_rel.smt2",
        "tests/rare/computational_mix/mix.rare",
    );
    assert!(steps.iter().any(|step| step.contains("rare_rewrite") && step.contains("\"bool-double-not-elim\"")), "{steps:#?}");
    assert!(
        steps.iter().any(|step| step.contains("\"arith_poly_norm_rel\"")),
        "{steps:#?}"
    );
    eprintln!("poly_norm_rel mix: saturation={:?}, steps={steps:#?}", run.saturation);
}

/// The `real_eval` fixture: `(= (+ 1/2 1/2) 1.0)`.  The solver rewrites
/// every `Real` literal to its `BigRat` form and folds the sum there, so
/// the recomputed rational must be spelled exactly as egglog serializes
/// it for the step to land in the goal's class; the literal renormalization
/// on the right elaborates to `refl`.
#[test]
fn reconstructs_rational_evaluation_from_production_egraph() {
    let run = run_qf_uf_case(
        "tests/rare/computational_mix/real_eval.smt2",
        "tests/rare/computational_mix/real_eval.alethe",
        "tests/rare/computational_mix/mix.rare",
        "t1",
        None,
    );
    let snapshot = EGraphSnapshot::capture_production(&run.egraph);
    let rules = rules_from_generated_program(&run.generated_program);
    let reconstruction = reconstruct_detailed(
        &snapshot,
        &run.lhs,
        &run.rhs,
        &rules,
        SearchStrategy::default(),
    );
    let certificate = reconstruction
        .certificate
        .expect("rational constant folding should reconstruct");
    assert!(certificate.contains_computation(Computation::Evaluation));
    let steps = elaborate_and_check(
        &run,
        &certificate,
        "t1",
        "tests/rare/computational_mix/real_eval.smt2",
        "tests/rare/computational_mix/mix.rare",
    );
    assert!(
        steps.iter().any(|step| step.contains(":rule evaluate")),
        "{steps:#?}"
    );
    assert!(!steps.iter().any(|step| step.contains(":rule hole")), "{steps:#?}");
    eprintln!("real_eval: saturation={:?}, steps={steps:#?}", run.saturation);
}

/// Corpus sweep for OUR algorithm: for every hole slice where the egglog
/// oracle succeeds, reconstruct a certificate from the provenance-free
/// snapshot, verify it, and elaborate it to Alethe — stopping at the first
/// case where reconstruction or elaboration fails.  Oracle failures are
/// skipped: they are engine territory, not reconstruction territory.
///
/// Driven by env vars: BENCH_LIST (tsv: alethe, smt2, hole id), BENCH_RARE,
/// optional BENCH_SKIP / BENCH_LIMIT.
#[test]
#[ignore = "corpus reconstruction sweep; set BENCH_LIST and BENCH_RARE"]
fn reconstructs_benchmark_corpus() {
    // Carcara's recursive-descent parser consumes several debug-build
    // frames per nesting level, and corpus problems nest a few hundred
    // levels deep (medium11.smt2 reaches 188) — past the default
    // test-thread stack, though not the CLI's 8 MiB main thread.  The
    // sweep therefore runs on an explicitly sized thread.
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(run_benchmark_corpus)
        .expect("corpus thread should spawn")
        .join()
        .expect("corpus thread should not panic");
}

fn run_benchmark_corpus() {
    let list = std::fs::read_to_string(std::env::var("BENCH_LIST").expect("set BENCH_LIST"))
        .expect("BENCH_LIST should be readable");
    let rare_path = std::env::var("BENCH_RARE").expect("set BENCH_RARE");
    let skip: usize = std::env::var("BENCH_SKIP").ok().and_then(|s| s.parse().ok()).unwrap_or(0);
    let limit: usize = std::env::var("BENCH_LIMIT")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(usize::MAX);

    let (mut oracle_failed, mut reconstructed) = (0usize, 0usize);
    let started = Instant::now();
    for (index, line) in list.lines().enumerate().skip(skip).take(limit) {
        let mut fields = line.split('\t');
        let (Some(alethe), Some(smt2), Some(hole)) =
            (fields.next(), fields.next(), fields.next())
        else {
            continue;
        };
        // One line per case before any work, so an abort (e.g. an oracle
        // saturation exceeding the memory cap) identifies its case for the
        // restart-and-skip driver.
        eprintln!("case {index}: {alethe}");

        let parser_config = parser::Config::default()
            .expand_lets(true)
            .allow_int_real_subtyping(true)
            .parse_hole_args(true);
        let (mut problem_text, mut proof_text, mut rare_text) =
            (String::new(), String::new(), String::new());
        let (_, proof, database, mut pool) = parser::parse_instance(
            parser::Source::file(Path::new(smt2), &mut problem_text)
                .expect("problem should exist"),
            parser::Source::file(Path::new(alethe), &mut proof_text)
                .expect("slice should exist"),
            Some(
                parser::Source::file(Path::new(&rare_path), &mut rare_text)
                    .expect("RARE database should exist"),
            ),
            parser_config,
        )
        .expect("slice should parse");
        let node = node_with_root_id(proof.commands, hole).expect("slice should contain its hole");
        let conclusion = node.clause()[0].clone();

        let (result, program) = run_egglog(
            &mut pool,
            (conclusion.clone(), &node),
            &database,
            RunEgglogOptions::default(),
        );
        if result.is_err() {
            oracle_failed += 1;
            // One line per oracle failure, so a driver can attribute the
            // case to the egglog check stage rather than to reconstruction.
            eprintln!("oracle-failed case {index}");
            continue;
        }
        if let Ok(dump_dir) = std::env::var("BENCH_DUMP") {
            let stem = Path::new(alethe)
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or(alethe)
                .trim_end_matches(".smt2.alethe");
            let dump_path = Path::new(&dump_dir).join(format!("{stem}__hole-{hole}.egg"));
            std::fs::write(&dump_path, &program).expect("BENCH_DUMP directory should be writable");
        }

        let snapshot = EGraphSnapshot::capture_production(&result.unwrap());
        let (lhs, rhs) = generated_goals(&program);
        let rules = rules_from_generated_program(&program);
        let sorts = ArithSorts::from_generated_program(&program);

        let reconstruction = reconstruct_with_sorts(
            &snapshot,
            &lhs,
            &rhs,
            &rules,
            &sorts,
            SearchStrategy::default(),
        );
        let Some(certificate) = reconstruction.certificate else {
            panic!(
                "\nSTOPPED at case {index}: RECONSTRUCTION FAILED (oracle succeeded)\n\
                 slice: {alethe}\nhole: {hole}\nrules: {}\nstats: {:?}\n\
                 lhs: {}\nrhs: {}",
                rules.len(),
                reconstruction.stats,
                lhs.to_egglog(),
                rhs.to_egglog(),
            );
        };
        let names = goal_variable_names(&lhs, &rhs, &conclusion);
        let rare_index = rare_arguments(&database.rules);
        let Some(steps) =
            AletheElaborator::elaborate_full(&certificate, hole, names.clone(), rare_index)
        else {
            panic!(
                "\nSTOPPED at case {index}: ALETHE ELABORATION FAILED\n\
                 slice: {alethe}\nhole: {hole}\ncertificate: {certificate:#?}",
            );
        };

        // Round-trip: the emitted steps must pass the real Carcara checker
        // against the original problem.
        if std::env::var("BENCH_PRINT").is_ok() {
            eprintln!(
                "--- elaborated proof (case {index}, hole {hole}) ---\n{}\n",
                steps.join("\n")
            );
        }
        // BENCH_OUT: directory to write each case's elaborated proof into,
        // named after the slice file.
        if let Ok(out_dir) = std::env::var("BENCH_OUT") {
            let stem = Path::new(alethe)
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or(alethe)
                .trim_end_matches(".smt2.alethe");
            let out_path = Path::new(&out_dir).join(format!("{stem}__hole-{hole}.alethe"));
            std::fs::write(&out_path, format!("{}\n", steps.join("\n")))
                .expect("BENCH_OUT directory should be writable");
        }
        if let Err(error) = check_with_carcara(Path::new(smt2), &steps, Path::new(&rare_path)) {
            panic!(
                "\nSTOPPED at case {index}: CARCARA CHECK FAILED: {error}\n\
                 slice: {alethe}\nhole: {hole}\n--- emitted proof ---\n{}\n\
                 names: {names:?}\nencoded lhs: {}\nconclusion: {conclusion}",
                steps.join("\n"),
                lhs.to_egglog(),
            );
        }
        reconstructed += 1;
        if index % 25 == 0 {
            eprintln!(
                "[{index}] reconstructed={reconstructed} oracle_failed={oracle_failed} \
                 ({:.0}s elapsed)",
                started.elapsed().as_secs_f64(),
            );
        }
    }
    eprintln!(
        "corpus sweep done: reconstructed={reconstructed} oracle_failed={oracle_failed} \
         in {:.0}s",
        started.elapsed().as_secs_f64(),
    );
}

/// Shared prelude for raw computational-solver programs: the term datatype
/// and the (fixed) distinct-elimination solver, without the header axioms.
const RAW_SOLVER_PRELUDE: &str = r#"
(datatype Term
  (Const String)
  (Bool bool)
  (Empty)
  (Args Term Term)
  (Mk Term))
(constructor @distinct (Term) Term)
(constructor @and (Term) Term)
(constructor @or (Term) Term)
(constructor @not (Term) Term)
(constructor @= (Term) Term)
(relation Avaliable (Term))
(function to_formula (Term Term Term) Term :no-merge)
(relation to_formula_rel (Term Term Term))
(ruleset list-ruleset)

(rule ((to_formula_rel (Empty) k (Empty)))
      ((set (to_formula (Empty) k (Empty)) (Empty)))
      :ruleset list-ruleset)
(rule ((= res (Args r rs))
       (to_formula_rel res y (Empty)))
      ((to_formula_rel rs r rs))
      :ruleset list-ruleset)
(rule ((= xs (Args x rxs))
       (to_formula_rel res y xs))
      ((to_formula_rel res y rxs))
      :ruleset list-ruleset)
(rule ((to_formula_rel res y (Args x rxs))
       (= (to_formula res y rxs) f))
      ((set (to_formula res y (Args x rxs))
            (Args (Mk (@not (Args (Mk (@= (Args y (Args x (Empty))))) (Empty)))) f)))
      :ruleset list-ruleset)
(rule ((to_formula_rel (Args r res) y (Empty))
       (= (to_formula res r res) f))
      ((set (to_formula (Args r res) y (Empty)) f))
      :ruleset list-ruleset)
(rule ((Avaliable (Mk (@distinct (Args x xs))))
       (= (to_formula xs x xs) f))
      ((union (Mk (@and f)) (Mk (@distinct (Args x xs)))))
      :ruleset list-ruleset)
(rule ((Avaliable (Mk (@distinct (Args x xs)))))
      ((to_formula_rel xs x xs))
      :ruleset list-ruleset)
"#;

fn raw_solver_snapshot(tail: &str) -> EGraphSnapshot {
    let program = format!("{RAW_SOLVER_PRELUDE}\n{tail}");
    let mut egraph = ProductionEGraph::default();
    egraph
        .parse_and_run_program(None, &program)
        .expect("raw computational solver program should run");
    EGraphSnapshot::capture_production(&egraph)
}

fn encoded_const(name: &str) -> Term {
    Term::new(
        "Mk",
        vec![Term::new("Const", vec![Term::leaf(&format!("\"{name}\""))])],
    )
}

fn encoded_not_equal(x: &Term, y: &Term) -> Term {
    encoded_app(
        "@not",
        vec![encoded_app("@=", vec![x.clone(), y.clone()])],
    )
}

/// The distinct-elimination union sits in the interior of the chain: the
/// obligation's endpoints are a double negation and the expanded
/// conjunction, so neither is distinct-shaped and only a vertex-local
/// computational edge can cross the gap.
#[test]
fn reconstructs_interior_distinct_elimination_between_rewrites() {
    let snapshot = raw_solver_snapshot(
        r#"
(rewrite (Mk (@not (Args (Mk (@not (Args (Mk t1) (Empty)))) (Empty)))) (Mk t1))
(let a (Mk (Const "a")))
(let b (Mk (Const "b")))
(let c (Mk (Const "c")))
(let d3 (Mk (@distinct (Args a (Args b (Args c (Empty)))))))
(let source (Mk (@not (Args (Mk (@not (Args d3 (Empty)))) (Empty)))))
(Avaliable source)
(Avaliable d3)
(run-schedule (repeat 40 (run list-ruleset) (run)))
"#,
    );

    let [a, b, c] = ["a", "b", "c"].map(encoded_const);
    let distinct = encoded_app("@distinct", vec![a.clone(), b.clone(), c.clone()]);
    let source = encoded_app("@not", vec![encoded_app("@not", vec![distinct])]);
    let target = encoded_app(
        "@and",
        vec![
            encoded_not_equal(&a, &b),
            encoded_not_equal(&a, &c),
            encoded_not_equal(&b, &c),
        ],
    );

    let rules = [encoded_bool_double_not_elim_rule()];
    let reconstruction = reconstruct_detailed(
        &snapshot,
        &source,
        &target,
        &rules,
        SearchStrategy::default(),
    );
    let certificate = reconstruction
        .certificate
        .expect("the rewrite and the computational step should chain");
    assert!(certificate.verify(&rules));
    assert_eq!(certificate.lhs(), &source);
    assert_eq!(certificate.rhs(), &target);
    let mut names = Vec::new();
    certificate.rule_names(&mut names);
    assert_eq!(names, ["bool-double-not-elim"]);
    assert!(certificate.contains_computation(Computation::DistinctElim));
    assert!(reconstruction.stats.computational_edges >= 1);
}

/// The two-element seam: the solver unions `distinct(a, b)` with the
/// singleton `and`, and ACI singleton elimination carries it the rest of the
/// way to the Alethe shape `(not (= a b))` — two computational edges, no
/// declarative rule at all.
#[test]
fn reconstructs_two_element_distinct_via_aci_singleton() {
    let snapshot = raw_solver_snapshot(
        r#"
(rewrite (Mk (@and (Args (Mk x) (Empty)))) (Mk x))
(let a (Mk (Const "a")))
(let b (Mk (Const "b")))
(let d2 (Mk (@distinct (Args a (Args b (Empty))))))
(Avaliable d2)
(run-schedule (repeat 20 (run list-ruleset) (run)))
"#,
    );

    let [a, b] = ["a", "b"].map(encoded_const);
    let source = encoded_app("@distinct", vec![a.clone(), b.clone()]);
    let target = encoded_not_equal(&a, &b);

    let reconstruction =
        reconstruct_detailed(&snapshot, &source, &target, &[], SearchStrategy::default());
    let certificate = reconstruction
        .certificate
        .expect("distinct elimination and ACI singleton collapse should chain");
    assert!(certificate.verify(&[]));
    assert_eq!(certificate.lhs(), &source);
    assert_eq!(certificate.rhs(), &target);
    assert!(certificate.contains_computation(Computation::DistinctElim));
    assert!(certificate.contains_computation(Computation::AciNorm));
}

/// Boolean constant folding, mirroring evaluation.egglog: a single
/// computational edge certifies `(and true false) = false`.
#[test]
fn reconstructs_boolean_evaluation() {
    let snapshot = raw_solver_snapshot(
        r#"
(rewrite (Mk (@and (Args (Mk (Bool x)) (Args (Mk (Bool y)) (Empty)))))
         (Mk (Bool (and x y))))
(let e (Mk (@and (Args (Mk (Bool true)) (Args (Mk (Bool false)) (Empty))))))
(Avaliable e)
(run-schedule (repeat 5 (run)))
"#,
    );

    let source = encoded_app("@and", vec![encoded_bool(true), encoded_bool(false)]);
    let target = encoded_bool(false);

    let reconstruction =
        reconstruct_detailed(&snapshot, &source, &target, &[], SearchStrategy::default());
    let certificate = reconstruction
        .certificate
        .expect("boolean evaluation should certify the folding");
    assert!(certificate.verify(&[]));
    assert!(certificate.contains_computation(Computation::Evaluation));
}

/// Full mix on the two-element seam: distinct elimination and the ACI
/// singleton collapse cross to `(not (= a b))`, and the RARE rule `eq-symm`
/// — applied under a `not` through congruence — carries the chain to the
/// flipped `(not (= b a))`.  One certificate, all edge kinds.
#[test]
fn reconstructs_distinct_elimination_mixed_with_eq_symm() {
    let snapshot = raw_solver_snapshot(
        r#"
(rewrite (Mk (@and (Args (Mk x) (Empty)))) (Mk x))
(rewrite (Mk (@= (Args (Mk t1) (Args (Mk s1) (Empty)))))
         (Mk (@= (Args (Mk s1) (Args (Mk t1) (Empty))))))
(let a (Mk (Const "a")))
(let b (Mk (Const "b")))
(let d2 (Mk (@distinct (Args a (Args b (Empty))))))
(Avaliable d2)
(run-schedule (repeat 20 (run list-ruleset) (run)))
"#,
    );

    let [a, b] = ["a", "b"].map(encoded_const);
    let source = encoded_app("@distinct", vec![a.clone(), b.clone()]);
    let target = encoded_not_equal(&b, &a);

    let rules = [encoded_eq_symm_rule()];
    let reconstruction = reconstruct_detailed(
        &snapshot,
        &source,
        &target,
        &rules,
        SearchStrategy::default(),
    );
    let certificate = reconstruction
        .certificate
        .expect("computational steps and eq-symm should chain");
    assert!(certificate.verify(&rules));
    assert_eq!(certificate.lhs(), &source);
    assert_eq!(certificate.rhs(), &target);
    let mut names = Vec::new();
    certificate.rule_names(&mut names);
    assert_eq!(names, ["eq-symm"]);
    assert!(certificate.contains_computation(Computation::DistinctElim));
    assert!(certificate.contains_computation(Computation::AciNorm));
    assert!(certificate.contains_congruence());
}

/// Evaluation buried inside a congruence child obligation, chained with a
/// RARE rule: `(or p (and true false))` needs the inner conjunction folded
/// to `false` before `bool-or-false` can strip it.
#[test]
fn reconstructs_evaluation_inside_congruence_with_rare_rule() {
    let snapshot = raw_solver_snapshot(
        r#"
(rewrite (Mk (@and (Args (Mk (Bool x)) (Args (Mk (Bool y)) (Empty)))))
         (Mk (Bool (and x y))))
(rewrite (Mk (@or (Args (Mk x) (Args (Mk (Bool false)) (Empty))))) (Mk x))
(let p (Mk (Const "p")))
(let tf (Mk (@and (Args (Mk (Bool true)) (Args (Mk (Bool false)) (Empty))))))
(let source (Mk (@or (Args p (Args tf (Empty))))))
(Avaliable source)
(run-schedule (repeat 10 (run)))
"#,
    );

    let p = encoded_const("p");
    let inner = encoded_app("@and", vec![encoded_bool(true), encoded_bool(false)]);
    let source = encoded_app("@or", vec![p.clone(), inner]);
    let target = p;

    let rules = [encoded_bool_or_false_rule()];
    let reconstruction = reconstruct_detailed(
        &snapshot,
        &source,
        &target,
        &rules,
        SearchStrategy::default(),
    );
    let certificate = reconstruction
        .certificate
        .expect("evaluation under congruence should chain with bool-or-false");
    assert!(certificate.verify(&rules));
    assert_eq!(certificate.lhs(), &source);
    assert_eq!(certificate.rhs(), &target);
    let mut names = Vec::new();
    certificate.rule_names(&mut names);
    assert_eq!(names, ["bool-or-false"]);
    assert!(certificate.contains_computation(Computation::Evaluation));
    assert!(certificate.contains_congruence());
}

#[test]
#[ignore = "diagnostic dump of the e-graph contents for a distinct_elim obligation"]
fn inspect_distinct_elim_egraph() {
    let run = run_qf_uf_case(
        "tests/rare/distinct_elim/QF_UF_resistance.1.prop2_ab_cti_max.smt2",
        "tests/rare/distinct_elim/QF_UF_resistance.1.prop2_ab_cti_max__from-t600.smt2.alethe",
        "tests/rare/big.rare",
        "t600",
        None,
    );
    let snapshot = EGraphSnapshot::capture_production(&run.egraph);
    eprintln!("goal lhs = {}", run.lhs.to_egglog());
    eprintln!("goal rhs = {}", run.rhs.to_egglog());
    eprintln!(
        "egraph: {} enodes, {} classes, saturation={:?}",
        snapshot.nodes.len(),
        snapshot.class_nodes.len(),
        run.saturation,
    );
    eprintln!("same_class(lhs, rhs) = {}", snapshot.same_class(&run.lhs, &run.rhs));

    let mut op_counts: BTreeMap<&str, usize> = BTreeMap::new();
    for node in &snapshot.nodes {
        *op_counts
            .entry(snapshot.ops.names[node.op as usize].as_str())
            .or_default() += 1;
    }
    eprintln!("operators in the serialized e-graph: {op_counts:#?}");

    let mut cache = HashMap::new();
    for (label, goal) in [("lhs", &run.lhs), ("rhs", &run.rhs)] {
        let Some(eclass) = snapshot.class_of(goal, &mut cache) else {
            eprintln!("goal {label} is not represented in the snapshot");
            continue;
        };
        eprintln!("goal {label} class {eclass} holds:");
        for &index in &snapshot.class_nodes[eclass as usize] {
            let node = &snapshot.nodes[index as usize];
            eprintln!(
                "  {}({})",
                snapshot.ops.names[node.op as usize],
                node.child_classes
                    .iter()
                    .map(|class| class.to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
            );
        }
    }

    let reconstruction = reconstruct_detailed(
        &snapshot,
        &run.lhs,
        &run.rhs,
        &[],
        SearchStrategy::default(),
    );
    eprintln!(
        "declarative reconstruction without rules: found={}, stats={:?}",
        reconstruction.certificate.is_some(),
        reconstruction.stats,
    );

    // Intermediate-state contamination check: a `to_formula` row is
    // serialized into the class of its output list, and being small it wins
    // naive minimal-size extraction; the internal-op guard must pick the
    // real term instead.
    let mut contaminated = 0;
    let mut example = None;
    let mut naive_memo = HashMap::new();
    let mut guarded_memo = HashMap::new();
    for (eclass, nodes) in snapshot.class_nodes.iter().enumerate() {
        let holds_row = nodes.iter().any(|&index| {
            snapshot.ops.names[snapshot.nodes[index as usize].op as usize] == "to_formula"
        });
        if !holds_row {
            continue;
        }
        let eclass = eclass as u32;
        let naive = extract_avoiding(&snapshot, eclass, &[], &mut HashSet::new(), &mut naive_memo);
        let guarded = extract_avoiding(
            &snapshot,
            eclass,
            &INTERNAL_OPS,
            &mut HashSet::new(),
            &mut guarded_memo,
        );
        if naive != guarded {
            contaminated += 1;
            example.get_or_insert((eclass, naive, guarded));
        }
    }
    eprintln!("classes where a to_formula row wins naive minimal-size extraction: {contaminated}");
    if let Some((eclass, naive, guarded)) = example {
        eprintln!(
            "example class {eclass}:\n  naive extraction   = {}\n  guarded extraction = {}",
            naive.map_or("<none>".to_owned(), |term| term.to_egglog()),
            guarded.map_or("<none>".to_owned(), |term| {
                let rendered = term.to_egglog();
                if rendered.len() > 200 {
                    format!("{}… ({} chars)", &rendered[..200], rendered.len())
                } else {
                    rendered
                }
            }),
        );
    }
}

#[test]
fn reconstructs_real_qf_uf_t37_from_production_egraph() {
    let run = run_qf_uf_t37();
    let snapshot = EGraphSnapshot::capture_production(&run.egraph);
    let rules = [encoded_eq_symm_rule()];
    let reconstruction = reconstruct_detailed(
        &snapshot,
        &run.lhs,
        &run.rhs,
        &rules,
        SearchStrategy::default(),
    );
    let certificate = reconstruction
        .certificate
        .expect("eq-symm should reconstruct the real QF_UF t37 equality");

    assert!(certificate.verify(&rules));
    assert_eq!(certificate.lhs(), &run.lhs);
    assert_eq!(certificate.rhs(), &run.rhs);
    let mut names = Vec::new();
    certificate.rule_names(&mut names);
    assert_eq!(names, ["eq-symm"]);
    assert!(reconstruction.stats.lhs_matches >= 1);
    assert!(reconstruction.stats.rule_instances >= 1);
    assert!(snapshot.same_class(&run.lhs, &run.rhs));
    assert!(
        reconstruct(
            &snapshot,
            &run.lhs,
            &run.rhs,
            &[],
            SearchStrategy::default(),
        )
        .is_none()
    );

    eprintln!(
        "QF_UF t37: generated={} bytes, egraph={} enodes, saturation={:?}, stats={:?}, certificate={certificate:#?}",
        run.generated_program.len(),
        snapshot.nodes.len(),
        run.saturation,
        reconstruction.stats,
    );
}

#[test]
fn reconstructs_real_qf_uf_double_not_from_production_egraph() {
    let run = run_qf_uf_double_not_t3();
    let snapshot = EGraphSnapshot::capture_production(&run.egraph);
    let rules = [encoded_bool_double_not_elim_rule()];
    let reconstruction = reconstruct_detailed(
        &snapshot,
        &run.lhs,
        &run.rhs,
        &rules,
        SearchStrategy::default(),
    );
    let certificate = reconstruction
        .certificate
        .expect("the final e-graph should yield the bool-double-not-elim instance");

    assert!(certificate.verify(&rules));
    assert_eq!(certificate.lhs(), &run.lhs);
    assert_eq!(certificate.rhs(), &run.rhs);
    let mut names = Vec::new();
    certificate.rule_names(&mut names);
    assert_eq!(names, ["bool-double-not-elim"]);
    assert!(reconstruction.stats.lhs_matches >= 1);
    assert!(reconstruction.stats.rule_instances >= 1);
    assert!(snapshot.same_class(&run.lhs, &run.rhs));
    assert!(
        reconstruct(
            &snapshot,
            &run.lhs,
            &run.rhs,
            &[],
            SearchStrategy::default(),
        )
        .is_none()
    );

    eprintln!(
        "QF_UF t3 double-not: generated={} bytes, egraph={} enodes, saturation={:?}, stats={:?}, certificate={certificate:#?}",
        run.generated_program.len(),
        snapshot.nodes.len(),
        run.saturation,
        reconstruction.stats,
    );
}

#[test]
#[ignore = "diagnostic benchmark over the full QF_UF rule database"]
fn benchmark_real_qf_uf_raw_rules_posthoc_reconstruction() {
    const CHECK_SAMPLES: usize = 11;
    const SAMPLES: usize = 100;

    fn median(mut samples: Vec<Duration>) -> Duration {
        samples.sort_unstable();
        samples[samples.len() / 2]
    }

    fn benchmark_case(
        label: &str,
        run_case: fn() -> QfUfRun,
        rule: Rewrite,
    ) -> (Duration, Duration) {
        // Warm the code and allocator paths, then keep one real saturated
        // e-graph for all post-check reconstruction samples.
        run_case();
        let run = run_case();
        let mut saturation_samples = vec![run.saturation];
        saturation_samples.extend((1..CHECK_SAMPLES).map(|_| run_case().saturation));
        let saturation = median(saturation_samples);
        let rules = [rule];
        let snapshot = EGraphSnapshot::capture_production(&run.egraph);
        let serialization = median(
            (0..SAMPLES)
                .map(|_| {
                    let start = Instant::now();
                    let snapshot = EGraphSnapshot::capture_production(&run.egraph);
                    assert!(!snapshot.nodes.is_empty());
                    start.elapsed()
                })
                .collect(),
        );
        let diagnostic = reconstruct_detailed(
            &snapshot,
            &run.lhs,
            &run.rhs,
            &rules,
            SearchStrategy::default(),
        );
        assert!(diagnostic.certificate.unwrap().verify(&rules));
        let search_and_verification = median(
            (0..SAMPLES)
                .map(|_| {
                    let start = Instant::now();
                    let reconstruction = reconstruct_detailed(
                        &snapshot,
                        &run.lhs,
                        &run.rhs,
                        &rules,
                        SearchStrategy::default(),
                    );
                    assert!(reconstruction.certificate.unwrap().verify(&rules));
                    start.elapsed()
                })
                .collect(),
        );
        let reconstruction = serialization + search_and_verification;
        let total = saturation + reconstruction;

        eprintln!(
            "{label} ({CHECK_SAMPLES} check samples, {SAMPLES} reconstruction samples): generated={} bytes, egraph={} enodes, normal-check={saturation:?}, serialization+indexing={serialization:?}, egraph-matching+proof-search+verification={search_and_verification:?}, posthoc={reconstruction:?}, estimated-total={total:?} ({:.4}x normal), stats={:?}",
            run.generated_program.len(),
            snapshot.nodes.len(),
            total.as_secs_f64() / saturation.as_secs_f64(),
            diagnostic.stats,
        );
        (saturation, reconstruction)
    }

    benchmark_case("QF_UF t37 eq-symm", run_qf_uf_t37, encoded_eq_symm_rule());
    benchmark_case(
        "QF_UF t3 bool-double-not-elim",
        run_qf_uf_double_not_t3,
        encoded_bool_double_not_elim_rule(),
    );
}

fn raw_qf_uf_program(lhs: &Term, rhs: &Term) -> String {
    format!(
        r#"
(datatype Term
  (Const String)
  (Var i64 Term)
  (Sort Term)
  (Empty)
  (Args Term Term)
  (Mk Term))
(constructor @= (Term) Term)
(rewrite
  (Mk (@= (Args (Mk t1) (Args (Mk s1) (Empty)))))
  (Mk (@= (Args (Mk s1) (Args (Mk t1) (Empty)))))
  :name "eq-symm")
(let $lhs {})
(let $rhs {})
(run 1)
"#,
        lhs.to_egglog(),
        rhs.to_egglog(),
    )
}

fn raw_qf_uf_double_not_program(lhs: &Term, rhs: &Term) -> String {
    format!(
        r#"
(datatype Term
  (Const String)
  (Var i64 Term)
  (Sort Term)
  (Empty)
  (Args Term Term)
  (Mk Term))
(constructor @not (Term) Term)
(rewrite
  (Mk (@not (Args (Mk (@not (Args (Mk t1) (Empty)))) (Empty))))
  (Mk t1)
  :name "bool-double-not-elim")
(let $lhs {})
(let $rhs {})
(run 1)
"#,
        lhs.to_egglog(),
        rhs.to_egglog(),
    )
}

#[test]
#[ignore = "diagnostic comparison using only raw QF_UF rewrite rules"]
fn compare_real_qf_uf_raw_rules_posthoc_with_egglog_proofs() {
    const SAMPLES: usize = 100;

    fn median(mut samples: Vec<Duration>) -> Duration {
        samples.sort_unstable();
        samples[samples.len() / 2]
    }

    fn run_normal(program: &str) -> (ProofEGraph, Duration) {
        let mut egraph = ProofEGraph::new(1);
        let start = Instant::now();
        egraph
            .parse_and_run_program(None, program)
            .expect("raw QF_UF program should saturate");
        (egraph, start.elapsed())
    }

    fn run_proofs(program: &str) -> Duration {
        let mut egraph = ProofEGraph::new_with_proofs();
        let program = format!("{program}\n(prove (= $lhs $rhs))");
        let start = Instant::now();
        let outputs = egraph
            .parse_and_run_program(None, &program)
            .expect("raw QF_UF program should produce an egglog proof");
        assert!(
            outputs
                .iter()
                .any(|output| matches!(output, CommandOutput::ProveExists { .. }))
        );
        start.elapsed()
    }

    fn benchmark_case(label: &str, program: &str, lhs: &Term, rhs: &Term, rules: &[Rewrite]) {
        let (saturated, _) = run_normal(program);
        run_normal(program);
        run_proofs(program);
        let snapshot = capture(&saturated);
        let diagnostic =
            reconstruct_detailed(&snapshot, lhs, rhs, rules, SearchStrategy::default());
        assert!(diagnostic.certificate.unwrap().verify(rules));

        let normal = median((0..SAMPLES).map(|_| run_normal(program).1).collect());
        let reconstruction = median(
            (0..SAMPLES)
                .map(|_| {
                    let start = Instant::now();
                    let snapshot = capture(&saturated);
                    let reconstruction =
                        reconstruct_detailed(&snapshot, lhs, rhs, rules, SearchStrategy::default());
                    assert!(reconstruction.certificate.unwrap().verify(rules));
                    start.elapsed()
                })
                .collect(),
        );
        let posthoc = normal + reconstruction;
        let proofs = median((0..SAMPLES).map(|_| run_proofs(program)).collect());

        eprintln!(
            "{label} ({SAMPLES} samples): normal={normal:?}, reconstruction={reconstruction:?}, posthoc={posthoc:?} ({:.2}x normal), egglog-proofs={proofs:?} ({:.2}x normal, {:.2}x posthoc), stats={:?}",
            posthoc.as_secs_f64() / normal.as_secs_f64(),
            proofs.as_secs_f64() / normal.as_secs_f64(),
            proofs.as_secs_f64() / posthoc.as_secs_f64(),
            diagnostic.stats,
        );
    }

    let eq_symm = run_qf_uf_t37();
    let eq_symm_program = raw_qf_uf_program(&eq_symm.lhs, &eq_symm.rhs);
    benchmark_case(
        "raw QF_UF eq-symm",
        &eq_symm_program,
        &eq_symm.lhs,
        &eq_symm.rhs,
        &[encoded_eq_symm_rule()],
    );

    let double_not = run_qf_uf_double_not_t3();
    let double_not_program = raw_qf_uf_double_not_program(&double_not.lhs, &double_not.rhs);
    benchmark_case(
        "raw QF_UF bool-double-not-elim",
        &double_not_program,
        &double_not.lhs,
        &double_not.rhs,
        &[encoded_bool_double_not_elim_rule()],
    );
}


/// Snapshot of a proof-producing (egglog 3.0) e-graph; the library only
/// captures the production engine's, since `egglog_proofs` is a
/// dev-dependency.
fn capture(egraph: &ProofEGraph) -> EGraphSnapshot {
    let serialized = egraph.serialize(ProofSerializeConfig::default());
    assert!(
        serialized.is_complete(),
        "reconstruction requires a complete e-graph snapshot: {}",
        serialized.omitted_description()
    );
    EGraphSnapshot::from_raw_nodes(
        serialized
            .egraph
            .nodes
            .values()
            .map(|node| {
                (
                    node.op.clone(),
                    node.children
                        .iter()
                        .map(|child| serialized.egraph.nodes[child].eclass.to_string())
                        .collect(),
                    node.eclass.to_string(),
                )
            })
            .collect(),
    )
}

/// End to end through the library entry point: `check_and_elaborate` with
/// the RARE hole elaboration replaces every `TRUST_THEORY_REWRITE` hole of
/// a cvc5 proof by a checked subproof, and the elaborated proof then passes
/// the checker with no hole checking at all.
#[test]
fn elaborates_cvc5_theory_rewrite_holes_end_to_end() {
    use crate::elaborator::{self, ElaborationPass};

    let problem_path = Path::new("tests/rare/elaborate/RF-12.smt2");
    let proof_path = Path::new("tests/rare/elaborate/RF-12.smt2.alethe");
    let rare_path = Path::new("tests/rare/big.rare");
    let parser_config = parser::Config::default()
        .expand_lets(true)
        .allow_int_real_subtyping(true)
        .parse_hole_args(true);

    let (mut problem_text, mut proof_text, mut rare_text) =
        (String::new(), String::new(), String::new());
    let (status, problem, elaborated, mut pool) = crate::check_and_elaborate(
        parser::Source::file(problem_path, &mut problem_text).expect("problem should exist"),
        parser::Source::file(proof_path, &mut proof_text).expect("proof should exist"),
        Some(parser::Source::file(rare_path, &mut rare_text).expect("RARE database should exist")),
        parser_config,
        crate::checker::Config::new(),
        elaborator::Config::new().elaborate_hole_rewrites(true),
        vec![ElaborationPass::Hole],
        false,
    )
    .expect("the cvc5 proof should check and elaborate");
    assert_eq!(
        status,
        crate::Status::Holey,
        "before elaboration the proof carries trust holes"
    );

    let mut printed = Vec::new();
    crate::ast::printer::write_proof_to_dest(
        &mut pool,
        &problem.prelude,
        &elaborated,
        &mut printed,
        false,
    )
    .expect("the elaborated proof should print");
    let printed = String::from_utf8(printed).expect("printed proof should be UTF-8");
    assert!(!printed.contains("TRUST_THEORY_REWRITE"), "{printed}");
    assert!(!printed.contains(":rule hole"), "{printed}");

    // Re-check the elaborated proof from its text, with no hole checking.
    let (mut problem_text, mut rare_text) = (String::new(), String::new());
    let rechecked = crate::check(
        parser::Source::file(problem_path, &mut problem_text).expect("problem should exist"),
        parser::Source::new(Path::new("<elaborated RF-12>"), &printed),
        Some(parser::Source::file(rare_path, &mut rare_text).expect("RARE database should exist")),
        parser_config,
        crate::checker::Config::new(),
        false,
    )
    .expect("the elaborated proof should parse and check");
    assert_eq!(rechecked, crate::Status::Valid, "{printed}");
    eprintln!("elaborated RF-12:\n{printed}");
}
