use std::{fs, path::PathBuf, process::Command};

#[test]
#[ignore = "requires Ethos and ALETHE_EUNOIA_SIGNATURE"]
fn translated_and_neg_checks_computed_conclusion_in_ethos() {
    let signature = PathBuf::from(
        std::env::var_os("ALETHE_EUNOIA_SIGNATURE")
            .expect("set ALETHE_EUNOIA_SIGNATURE to the AletheInEunoia/signature directory"),
    );
    let ethos = std::env::var_os("ETHOS").unwrap_or_else(|| "ethos".into());
    let dir = std::env::temp_dir().join(format!("carcara-and-neg-eunoia-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let problem = dir.join("input.smt2");
    fs::write(
        &problem,
        "(set-logic QF_UF)\n\
         (declare-const p Bool)\n\
         (declare-const q Bool)\n\
         (declare-const r Bool)\n\
         (declare-const s Bool)\n\
         (check-sat)\n",
    )
    .unwrap();
    let cases = [
        ("binary", "(and p q) (not p) (not q)", true),
        ("ternary", "(and p q r) (not p) (not q) (not r)", true),
        (
            "four",
            "(and p q r s) (not p) (not q) (not r) (not s)",
            true,
        ),
        ("unary", "(and p) (not p)", true),
        ("explicit-true", "(and p true) (not p) (not true)", true),
        ("explicit-false", "(and p false) (not p) (not false)", true),
        ("duplicates", "(and p p q) (not p) (not p) (not q)", true),
        ("nested", "(and p (and q r)) (not p) (not (and q r))", true),
        (
            "negated-operand",
            "(and (not p) q) (not (not p)) (not q)",
            true,
        ),
        ("wrong-head", "(or p q) (not p) (not q)", false),
        ("atom-head", "p (not p)", false),
        ("empty-clause", "", false),
        ("wrong-sign", "(and p q) p (not q)", false),
        ("missing", "(and p q r) (not p) (not q)", false),
        ("extra", "(and p q) (not p) (not q) (not r)", false),
        ("reordered", "(and p q r) (not p) (not r) (not q)", false),
        ("changed", "(and p q r) (not p) (not q) (not s)", false),
        ("drop-duplicate", "(and p p q) (not p) (not q)", false),
        ("drop-explicit-true", "(and p true) (not p)", false),
        (
            "negate-terminator",
            "(and p q) (not p) (not q) (not true)",
            false,
        ),
        (
            "flatten-nested",
            "(and p (and q r)) (not p) (not q) (not r)",
            false,
        ),
    ];
    for (name, clause, accepted) in cases {
        let input = dir.join(format!("{name}.alethe"));
        let output = dir.join(format!("{name}.eo"));
        // Source Alethe steps have no arguments. The translator supplies the
        // conjunction required by the computed Eunoia rule.
        fs::write(&input, format!("(step s (cl {clause}) :rule and_neg)\n")).unwrap();
        let translated = Command::new(env!("CARGO_BIN_EXE_carcara"))
            .args(["translate", "eunoia", "--eunoia-mech"])
            .arg(&signature)
            .arg(&input)
            .arg(&problem)
            .output()
            .unwrap();
        assert!(
            translated.status.success(),
            "{name}: translator: {}",
            String::from_utf8_lossy(&translated.stderr)
        );
        fs::write(&output, translated.stdout).unwrap();
        let checked = Command::new(&ethos).arg(&output).output().unwrap();
        let diagnostic = String::from_utf8_lossy(&checked.stderr);
        assert_eq!(
            checked.status.success(),
            accepted,
            "{name}: Ethos: {}\n{diagnostic}\nGenerated file: {}",
            String::from_utf8_lossy(&checked.stdout),
            output.display()
        );
        if accepted {
            assert_eq!(String::from_utf8_lossy(&checked.stdout).trim(), "correct");
        } else {
            assert!(
                !diagnostic.contains("Could not find proof rule"),
                "{diagnostic}"
            );
            if name == "empty-clause" {
                // With no first literal, the rule's required argument is absent.
                assert!(diagnostic.contains("Non-bool conclusion"), "{diagnostic}");
            } else {
                assert!(diagnostic.contains("and_neg"), "{diagnostic}");
            }
        }
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
