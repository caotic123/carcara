use carcara::{
    parser,
    translation::{
        ProofPrinter,
        eunoia::{
            printer::{EunoiaPrinter, SExpFormatter},
            rare,
        },
    },
};
use std::{fs, path::PathBuf, process::Command};

const SHARED: &str = r#"
(declare-rare-rule shared ((xs Bool :list)) :args (xs)
  :conclusion (= (=> (and xs) (or xs)) (or (not (and xs)) (or xs))))
"#;

fn compile(problem: &str, rules: &str, proof: &str) -> Result<String, rare::RareTranslationError> {
    let (_, proof, rules, _) = parser::parse_instance(
        problem.into(),
        proof.into(),
        Some(rules.into()),
        parser::Config::new(),
    )
    .unwrap();
    rare::validate_proof(&rules, &proof)?;
    let compiled = rare::compile(&rules)?;
    let mut output = Vec::new();
    EunoiaPrinter::new(SExpFormatter::new(&mut output))
        .write_proof(&compiled.declarations)
        .unwrap();
    Ok(String::from_utf8(output).unwrap())
}

#[test]
fn generated_rules_preserve_shared_sequence_and_operator_contexts() {
    let output = compile(
        "",
        SHARED,
        "(step s (cl true) :rule rare_rewrite :args (\"shared\" rare-list))",
    )
    .unwrap();
    assert!(output.contains("(xs eo::List :list)"));
    assert!(output.contains("$normalize_eo_list Bool eo::List eo::List::cons xs"));
    assert!(output.contains("$normalize_eo_list Bool Bool and"));
    assert!(output.contains("$normalize_eo_list Bool Bool or"));
    assert!(output.contains(":conclusion "));
    assert!(!output.contains(":conclusion-explicit"));
    assert!(!output.contains("rare_rules.eo"));
}

#[test]
fn missing_definitions_and_list_scalar_mismatches_are_errors() {
    let missing = compile(
        "",
        "",
        "(step s (cl true) :rule rare_rewrite :args (\"absent\"))",
    )
    .unwrap_err();
    assert!(missing.to_string().contains("--rare-file"));
    let shape = compile(
        "(declare-const p Bool)",
        SHARED,
        "(step s (cl true) :rule rare_rewrite :args (\"shared\" p))",
    )
    .unwrap_err();
    assert!(shape.to_string().contains("list/scalar"));
}

#[test]
fn all_rules_are_emitted_in_database_order_independently_of_the_proof() {
    let database = format!(
        r#"{SHARED}
      (declare-rare-rule double-neg ((x Bool)) :args (x)
        :conclusion (= (not (not x)) x))"#
    );
    let without_steps = compile("", &database, "").unwrap();
    let using_second_rule = compile(
        "(declare-const p Bool)",
        &database,
        "(step s (cl true) :rule rare_rewrite :args (\"double-neg\" p))",
    )
    .unwrap();
    assert_eq!(without_steps, using_second_rule);
    assert_eq!(without_steps.matches("(declare-rule").count(), 2);
    assert!(
        without_steps.find("@rare.rule.0").unwrap() < without_steps.find("@rare.rule.1").unwrap()
    );
    assert!(without_steps.contains("(not (not x))"));
}

#[test]
fn unsupported_list_context_is_rejected_even_when_unused() {
    let unsupported = r#"
      (declare-rare-rule chain ((xs Bool :list) (x Bool)) :args (xs x)
        :conclusion (= (=> xs x) x))"#;
    let error = compile(
        "",
        &format!("{SHARED}\n{unsupported}"),
        "(step s (cl true) :rule rare_rewrite :args (\"shared\" rare-list))",
    )
    .unwrap_err();
    assert_eq!(error.rule, "chain");
    assert!(
        error
            .to_string()
            .contains("outside a supported variadic application")
    );
}

#[test]
#[ignore = "requires Ethos and ALETHE_EUNOIA_SIGNATURE; see docs/src/checking/rare.md"]
fn generated_rules_check_in_ethos() {
    let signature = PathBuf::from(
        std::env::var_os("ALETHE_EUNOIA_SIGNATURE")
            .expect("set ALETHE_EUNOIA_SIGNATURE to the AletheInEunoia/signature directory"),
    );
    let ethos = std::env::var_os("ETHOS").unwrap_or_else(|| "ethos".into());
    let dir = std::env::temp_dir().join(format!("carcara-rare-eunoia-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let bools = "(declare-const p Bool) (declare-const q Bool) (declare-const r Bool)";
    let or_id = r#"(declare-rare-rule or-id ((xs Bool :list)) :args (xs)
        :conclusion (= (or xs false) (or xs)))"#;
    let distrib = r#"(declare-rare-rule distrib ((a Bool) (b Bool) (xs Bool :list) (z Bool))
        :args (a b xs z) :conclusion
        (= (=> (or a b xs) z) (and (=> a z) (=> (or b xs) z))))"#;
    let premise = r#"(declare-rare-rule premise ((xs Bool :list))
        :premises ((= (and xs) true)) :args (xs) :conclusion (= (and xs) true))"#;
    let distinct = r#"(declare-rare-rule distinct-false
        ((T Type) (t T) (xs T :list) (ys T :list) (zs T :list)) :args (t xs ys zs)
        :conclusion (= (distinct xs t ys t zs) false))"#;
    let uf = "(declare-sort U 0) (declare-const a U) (declare-const b U) (declare-const c U) (declare-const d U)";
    let add = r#"(declare-rare-rule add-id ((xs Int :list) (x Int)) :args (xs x)
        :conclusion (= (+ xs x) (+ xs x)))"#;
    let fragments = r#"(declare-rare-rule fragments
        ((xs Bool :list) (x Bool) (ys Bool :list)) :args (xs x ys)
        :conclusion (= (or xs x ys) (or xs x ys)))"#;
    let unused = r#"(declare-rare-rule unused ((xs Int :list) (x Bool))
        :args (xs x) :conclusion (= x x))"#;
    let cases = [
        (
            "shared-empty",
            bools,
            SHARED,
            "",
            "shared",
            "rare-list",
            "(= (=> true false) (or (not true) false))",
            true,
        ),
        (
            "shared-single",
            bools,
            SHARED,
            "",
            "shared",
            "(rare-list p)",
            "(= (=> p p) (or (not p) p))",
            true,
        ),
        (
            "shared-many",
            bools,
            SHARED,
            "",
            "shared",
            "(rare-list p q)",
            "(= (=> (and p q) (or p q)) (or (not (and p q)) (or p q)))",
            true,
        ),
        (
            "shared-nested",
            bools,
            SHARED,
            "",
            "shared",
            "(rare-list (or p q) r)",
            "(= (=> (and (or p q) r) (or (or p q) r)) (or (not (and (or p q) r)) (or (or p q) r)))",
            true,
        ),
        (
            "false-is-an-element",
            bools,
            SHARED,
            "",
            "shared",
            "(rare-list false)",
            "(= (=> false false) (or (not false) false))",
            true,
        ),
        (
            "true-is-an-element",
            bools,
            SHARED,
            "",
            "shared",
            "(rare-list true)",
            "(= (=> true true) (or (not true) true))",
            true,
        ),
        (
            "reject-wrong-empty",
            bools,
            SHARED,
            "",
            "shared",
            "rare-list",
            "(= (=> false false) (or (not false) false))",
            false,
        ),
        (
            "reject-wrong-order",
            bools,
            SHARED,
            "",
            "shared",
            "(rare-list p q)",
            "(= (=> (and q p) (or q p)) (or (not (and q p)) (or q p)))",
            false,
        ),
        (
            "or-id-empty",
            bools,
            or_id,
            "",
            "or-id",
            "rare-list",
            "(= false false)",
            true,
        ),
        (
            "or-id-single",
            bools,
            or_id,
            "",
            "or-id",
            "(rare-list p)",
            "(= (or p false) p)",
            true,
        ),
        (
            "distrib-empty",
            bools,
            distrib,
            "",
            "distrib",
            "p q rare-list r",
            "(= (=> (or p q) r) (and (=> p r) (=> q r)))",
            true,
        ),
        (
            "distrib-single",
            bools,
            distrib,
            "",
            "distrib",
            "p q (rare-list p) r",
            "(= (=> (or p q p) r) (and (=> p r) (=> (or q p) r)))",
            true,
        ),
        (
            "premise-empty",
            bools,
            premise,
            "(assume h (= true true))",
            "premise",
            "rare-list",
            "(= true true)",
            true,
        ),
        (
            "premise-single",
            bools,
            premise,
            "(assume h (= p true))",
            "premise",
            "(rare-list p)",
            "(= p true)",
            true,
        ),
        (
            "reject-wrong-premise",
            bools,
            premise,
            "(assume h (= p false))",
            "premise",
            "(rare-list p)",
            "(= p true)",
            false,
        ),
        (
            "distinct-empty",
            uf,
            distinct,
            "",
            "distinct-false",
            "a rare-list rare-list rare-list",
            "(= (distinct a a) false)",
            true,
        ),
        (
            "distinct-mixed",
            uf,
            distinct,
            "",
            "distinct-false",
            "a (rare-list b c) rare-list (rare-list d)",
            "(= (distinct b c a a d) false)",
            true,
        ),
        (
            "distinct-bool",
            bools,
            distinct,
            "",
            "distinct-false",
            "p (rare-list q) (rare-list false) rare-list",
            "(= (distinct q p false p) false)",
            true,
        ),
        (
            "reject-distinct-types",
            uf,
            distinct,
            "",
            "distinct-false",
            "a (rare-list true) rare-list rare-list",
            "(= (distinct a a) false)",
            false,
        ),
        (
            "add-empty",
            "(declare-const x Int)",
            add,
            "",
            "add-id",
            "rare-list x",
            "(= x x)",
            true,
        ),
        (
            "add-many",
            "(declare-const x Int) (declare-const y Int)",
            add,
            "",
            "add-id",
            "(rare-list x y) x",
            "(= (+ x y x) (+ x y x))",
            true,
        ),
        (
            "fragments-empty",
            bools,
            fragments,
            "",
            "fragments",
            "rare-list p rare-list",
            "(= p p)",
            true,
        ),
        (
            "fragments-duplicates-and-nil-operand",
            bools,
            fragments,
            "",
            "fragments",
            "(rare-list q p) p (rare-list false)",
            "(= (or q p p false) (or q p p false))",
            true,
        ),
        (
            "unused-list",
            bools,
            unused,
            "",
            "unused",
            "(rare-list 1 2) p",
            "(= p p)",
            true,
        ),
        (
            "reject-unused-list-types",
            bools,
            unused,
            "",
            "unused",
            "(rare-list true) p",
            "(= p p)",
            false,
        ),
    ];
    for (name, declarations, rules, assumptions, rule, args, conclusion, accepted) in cases {
        let problem_path = dir.join(format!("{name}.smt2"));
        let proof_path = dir.join(format!("{name}.alethe"));
        let rules_path = dir.join(format!("{name}.rare"));
        let output_path = dir.join(format!("{name}.eo"));
        fs::write(
            &problem_path,
            format!("(set-logic ALL)\n{declarations}\n(check-sat)\n"),
        )
        .unwrap();
        let premises = if assumptions.is_empty() {
            ""
        } else {
            ":premises (h)"
        };
        fs::write(&proof_path, format!("{assumptions}\n(step s (cl {conclusion}) :rule rare_rewrite {premises} :args (\"{rule}\" {args}))\n")).unwrap();
        fs::write(&rules_path, rules).unwrap();
        let translated = Command::new(env!("CARGO_BIN_EXE_carcara"))
            .args(["translate", "eunoia", "--eunoia-mech"])
            .arg(&signature)
            .arg("--rare-file")
            .arg(&rules_path)
            .arg(&proof_path)
            .arg(&problem_path)
            .output()
            .unwrap();
        assert!(
            translated.status.success(),
            "{name}: translator: {}",
            String::from_utf8_lossy(&translated.stderr)
        );
        fs::write(&output_path, &translated.stdout).unwrap();
        let checked = Command::new(&ethos)
            .arg(&output_path)
            .output()
            .expect("could not run Ethos");
        assert_eq!(
            checked.status.success(),
            accepted,
            "{name}: Ethos: {}\n{}\nGenerated file: {}",
            String::from_utf8_lossy(&checked.stdout),
            String::from_utf8_lossy(&checked.stderr),
            output_path.display()
        );
        eprintln!(
            "{name}: {}",
            if accepted {
                "accepted"
            } else {
                "rejected as expected"
            }
        );
    }
}
