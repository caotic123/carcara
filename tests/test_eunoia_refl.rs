use std::{fs, path::PathBuf, process::Command};

#[test]
#[ignore = "requires Ethos and ALETHE_EUNOIA_SIGNATURE"]
fn translated_refl_checks_in_ethos() {
    let signature = PathBuf::from(
        std::env::var_os("ALETHE_EUNOIA_SIGNATURE")
            .expect("set ALETHE_EUNOIA_SIGNATURE to the AletheInEunoia/signature directory"),
    );
    let ethos = std::env::var_os("ETHOS").unwrap_or_else(|| "ethos".into());
    let dir = std::env::temp_dir().join(format!("carcara-refl-eunoia-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let problem = dir.join("input.smt2");
    fs::write(
        &problem,
        "(set-logic ALL)\n\
         (declare-sort U 0)\n\
         (declare-const a U)\n\
         (declare-const p Bool)\n\
         (declare-const q Bool)\n\
         (check-sat)\n",
    )
    .unwrap();
    let cases = [
        (
            "boolean",
            "(step s (cl (= (not p) (not p))) :rule refl)",
            true,
            "",
        ),
        (
            "uninterpreted-sort",
            "(step s (cl (= a a)) :rule refl)",
            true,
            "",
        ),
        (
            "reject-unequal-terms",
            "(step s (cl (= p q)) :rule refl)",
            false,
            "",
        ),
        (
            "substitution-context",
            "(anchor :step s :args ((y Bool) (:= (x Bool) y)))
             (step s.refl (cl (= x y)) :rule refl)
             (step s (cl (= (forall ((x Bool)) x) (forall ((y Bool)) y))) :rule bind)
             (step after (cl (= p p)) :rule refl)",
            true,
            "(declare-const String Type)\n(declare-consts <string> String)\n",
        ),
        (
            "reject-wrong-substitution",
            "(anchor :step s :args ((y Bool) (:= (x Bool) y)))
             (step s.refl (cl (= x (not y))) :rule refl)
             (step s (cl (= (forall ((x Bool)) x) (forall ((y Bool)) (not y)))) :rule bind)",
            false,
            "(declare-const String Type)\n(declare-consts <string> String)\n",
        ),
    ];
    for (name, proof, accepted, prelude) in cases {
        let input = dir.join(format!("{name}.alethe"));
        let output = dir.join(format!("{name}.eo"));
        fs::write(&input, proof).unwrap();
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
        // Scoped cases use eo::var, which needs string literal typing. Supply
        // that declaration in the fixture until the default signature has it.
        let mut eunoia = prelude.as_bytes().to_vec();
        eunoia.extend_from_slice(&translated.stdout);
        fs::write(&output, eunoia).unwrap();
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
                diagnostic.contains("rule refl failed to check"),
                "{diagnostic}"
            );
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
