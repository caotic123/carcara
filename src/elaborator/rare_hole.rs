//! Elaboration of `TRUST_THEORY_REWRITE` holes through the RARE
//! post-hoc reconstruction pipeline.
use std::collections::HashMap;
use crate::rare::reconstruction::*;

/// Elaborates a certificate into Alethe proof steps.  Per-kind policy:
/// RARE rules, evaluation, and ACI normalization become cvc5-style
/// `TRUST_THEORY_REWRITE` holes carrying the rewrite's string name;
/// distinct elimination decomposes into Alethe's native, fully checked
/// `distinct_elim` rule; `refl`/`symm`/`trans`/`cong` glue the chain.
/// Congruence steps over the encoding spine (`Mk`, application, `Args`
/// cells) collapse into a single decoded `cong` step.
pub struct AletheElaborator {
    pub prefix: String,
    pub steps: Vec<String>,
    pub names: HashMap<String, String>,
    /// RARE rule name -> argument order, for emitting checkable
    /// `rare_rewrite` steps instead of trusted holes.
    pub rare: HashMap<String, Vec<String>>,
}

impl AletheElaborator {
    pub fn elaborate(certificate: &Certificate, prefix: &str) -> Option<Vec<String>> {
        Self::elaborate_with_names(certificate, prefix, HashMap::new())
    }

    pub fn elaborate_with_names(
        certificate: &Certificate,
        prefix: &str,
        names: HashMap<String, String>,
    ) -> Option<Vec<String>> {
        Self::elaborate_full(certificate, prefix, names, HashMap::new())
    }

    pub fn elaborate_full(
        certificate: &Certificate,
        prefix: &str,
        names: HashMap<String, String>,
        rare: HashMap<String, Vec<String>>,
    ) -> Option<Vec<String>> {
        let mut elaborator =
            Self { prefix: prefix.to_owned(), steps: Vec::new(), names, rare };
        elaborator.step_for(certificate)?;
        Some(elaborator.steps)
    }

    pub fn emit(&mut self, lhs: &Term, rhs: &Term, rule: &str, tail: &str) -> Option<String> {
        let id = format!("{}.{}", self.prefix, self.steps.len() + 1);
        self.steps.push(format!(
            "(step {id} (cl (= {} {})) :rule {rule}{tail})",
            decode_any(lhs, &self.names)?,
            decode_any(rhs, &self.names)?,
        ));
        Some(id)
    }

    pub fn trusted(&mut self, lhs: &Term, rhs: &Term, name: &str) -> Option<String> {
        let tail = format!(" :args (\"TRUST_THEORY_REWRITE\" \"{name}\")");
        self.emit(lhs, rhs, "hole", &tail)
    }

    /// The step id proving `(= lhs rhs)` for this certificate node.
    pub fn step_for(&mut self, certificate: &Certificate) -> Option<String> {
        match certificate {
            Certificate::Refl { term } => self.emit(term, term, "refl", ""),
            Certificate::Rule { name, lhs, rhs, substitution } => {
                // A rewrite the engine compiled from the RARE database
                // carries its name, so the step becomes a checkable
                // rare_rewrite with the rule's argument instantiation;
                // engine-internal rewrites keep the trusted form.
                if let Some(arguments) = self.rare.get(name).cloned() {
                    let decoded: Option<Vec<String>> = arguments
                        .iter()
                        .map(|parameter| {
                            substitution
                                .get(parameter)
                                .and_then(|term| decode_any(term, &self.names))
                        })
                        .collect();
                    if let Some(decoded) = decoded {
                        let tail = format!(" :args (\"{name}\" {})", decoded.join(" "));
                        return self.emit(lhs, rhs, "rare_rewrite", &tail);
                    }
                }
                self.trusted(lhs, rhs, name)
            }
            Certificate::Computational { kind, lhs, rhs } => match kind {
                // A literal renormalization (`Real` to `RatConst`) decodes to
                // the same text on both sides: nothing to trust.
                _ if decode_any(lhs, &self.names) == decode_any(rhs, &self.names) => {
                    self.emit(lhs, rhs, "refl", "")
                }
                Computation::DistinctElim => self.emit(lhs, rhs, "distinct_elim", ""),
                // Each computational kind maps to the native Carcara rule
                // that re-decides it, so the elaborated step carries no
                // trust: `evaluate` constant-folds, `aci_simp` normalizes
                // and/or, `poly_simp` compares polynomial normal forms.
                Computation::Evaluation => self.emit(lhs, rhs, "evaluate", ""),
                Computation::AciNorm => self.emit(lhs, rhs, "aci_simp", ""),
                Computation::ArithPolyNorm => self.emit(lhs, rhs, "poly_simp", ""),
                // The relation form stays a tagged hole: Carcara's native
                // `poly_simp_rel` needs a scaled-difference premise and the
                // same relation operator on both sides, which these
                // certificates (negated, mixed-operator, integer-tightened
                // relations) do not generally provide.
                Computation::ArithPolyNormRel => self.trusted(lhs, rhs, "arith_poly_norm_rel"),
            },
            Certificate::Symm { lhs, rhs, proof } => {
                let premise = self.step_for(proof)?;
                let tail = format!(" :premises ({premise})");
                self.emit(lhs, rhs, "symm", &tail)
            }
            Certificate::Trans { lhs, rhs, first, second, .. } => {
                // The solver's two-element seam (`distinct` to singleton
                // `and` to the negation) is exactly Alethe's two-element
                // `distinct_elim` shape, so the pair collapses into the
                // native rule.
                if let (
                    Certificate::Computational { kind: Computation::DistinctElim, lhs: d, .. },
                    Certificate::Computational { kind: Computation::AciNorm, .. },
                ) = (first.as_ref(), second.as_ref())
                {
                    if matches!(encoded_application(d), Some(("@distinct", elements)) if elements.len() == 2)
                    {
                        return self.emit(lhs, rhs, "distinct_elim", "");
                    }
                }
                // A leg whose sides decode identically (a literal
                // renormalization) adds nothing: the other leg already
                // states the whole equality.
                let identity = |certificate: &Certificate, names: &HashMap<String, String>| {
                    decode_any(certificate.lhs(), names) == decode_any(certificate.rhs(), names)
                };
                if identity(first, &self.names) {
                    return self.step_for(second);
                }
                if identity(second, &self.names) {
                    return self.step_for(first);
                }
                let first = self.step_for(first)?;
                let second = self.step_for(second)?;
                let tail = format!(" :premises ({first} {second})");
                self.emit(lhs, rhs, "trans", &tail)
            }
            Certificate::Congruence { lhs, rhs, child, .. } => {
                // The `Mk` wrapper is invisible in Alethe: a congruence
                // through it alone states exactly the child's equality.
                if lhs.op == "Mk" && !matches!(child.as_ref(), Certificate::Congruence { .. }) {
                    return self.step_for(child);
                }
                let mut arguments = Vec::new();
                spine_arguments(certificate, &mut arguments)?;
                let premises = arguments
                    .iter()
                    .map(|argument| self.step_for(argument))
                    .collect::<Option<Vec<_>>>()?;
                let tail = format!(" :premises ({})", premises.join(" "));
                self.emit(lhs, rhs, "cong", &tail)
            }
        }
    }
}

/// Descend an encoded congruence spine (`Mk` wrapper, application node,
/// `Args` cells, and the transitivity chains congruence builds when several
/// arguments differ), collecting the certificates of the differing
/// arguments in argument order — one `cong` premise each.
pub fn spine_arguments<'c>(certificate: &'c Certificate, out: &mut Vec<&'c Certificate>) -> Option<()> {
    match certificate {
        Certificate::Refl { .. } => Some(()),
        Certificate::Congruence { lhs, child_index, child, .. } => {
            match (lhs.op.as_str(), child_index) {
                // Wrapper and application layers pass straight through.
                ("Mk", 0) => spine_arguments(child, out),
                (operator, 0) if operator.starts_with('@') => spine_arguments(child, out),
                // An Args cell: index 0 is a differing element itself, index 1
                // continues along the list spine.
                ("Args", 0) => {
                    out.push(child);
                    Some(())
                }
                ("Args", 1) => spine_arguments(child, out),
                _ => None,
            }
        }
        Certificate::Trans { first, second, .. } => {
            spine_arguments(first, out)?;
            spine_arguments(second, out)
        }
        _ => None,
    }
}

use std::path::Path;

use crate::{
    Status,
    ast::{
        Constant, ProofCommand, ProofNode, StepNode,
        pool::{PrimitivePool, TermPool},
        rare_rules::Rules,
    },
    checker,
    elaborator::{Elaborator, error::ElaborationError},
    external, parser,
    rare::engine::run_egglog,
};

/// Whether `step` is a cvc5 `TRUST_THEORY_REWRITE` hole.
pub fn is_theory_rewrite_hole(step: &StepNode) -> bool {
    step.rule == "hole"
        && matches!(
            step.args.first().map(|arg| arg.as_ref()),
            Some(crate::ast::Term::Const(Constant::String(tag))) if tag == "TRUST_THEORY_REWRITE"
        )
}

/// Elaborates a `TRUST_THEORY_REWRITE` hole through the post-hoc pipeline:
/// the egglog engine proves the rewrite, a certificate is reconstructed from
/// its saturated e-graph, the certificate's Alethe steps are checked against
/// the RARE database, and the checked proof replaces the hole as a subproof
/// — the same insertion an external solver's proof goes through.
pub fn elaborate(
    elaborator: &mut Elaborator,
    node: &crate::ast::Rc<ProofNode>,
    step: &StepNode,
) -> Result<crate::ast::Rc<ProofNode>, ElaborationError> {
    let fail = |stage: &str, detail: String| {
        ElaborationError::RareReconstruction(format!("{stage}: {detail}"))
    };
    let rules = elaborator
        .rare_rules
        .ok_or_else(|| fail("setup", "no RARE database was given".to_owned()))?;
    let [conclusion] = step.clause.as_slice() else {
        return Err(fail(
            "setup",
            format!("expected a single-literal clause, found {} literals", step.clause.len()),
        ));
    };

    let (result, program) = run_egglog(
        elaborator.pool,
        (conclusion.clone(), node),
        rules,
        elaborator.config.hole_rewrite_options,
    );
    let egraph = result.map_err(|error| fail("egglog check", error))?;
    let snapshot = EGraphSnapshot::capture_production(&egraph);
    let (lhs, rhs) = generated_goals(&program);
    let rewrites = rules_from_generated_program(&program);
    let sorts = ArithSorts::from_generated_program(&program);
    let reconstruction = reconstruct_with_sorts(
        &snapshot,
        &lhs,
        &rhs,
        &rewrites,
        &sorts,
        SearchStrategy::default(),
    );
    let certificate = reconstruction.certificate.ok_or_else(|| {
        fail(
            "reconstruction",
            format!("no certificate found; stats: {:?}", reconstruction.stats),
        )
    })?;
    let names = goal_variable_names(&lhs, &rhs, conclusion);
    let index = rare_arguments(&rules.rules);
    let steps = AletheElaborator::elaborate_full(&certificate, &step.id, names, index)
        .ok_or_else(|| {
            fail(
                "alethe elaboration",
                "a certificate term failed to decode".to_owned(),
            )
        })?;

    // `insert_solver_proof` expects a refutation of the negated conclusion,
    // so the equality proof is closed by resolving its last step against
    // that assumption.
    let negated = elaborator.pool.add(crate::ast::Term::Op(
        crate::ast::Operator::Not,
        vec![conclusion.clone()],
    ));
    let problem =
        external::get_problem_string(elaborator.pool, &elaborator.problem.prelude, [&negated]);
    let assumption = format!("{}.h", step.id);
    let last = format!("{}.{}", step.id, steps.len());
    let proof = format!(
        "(assume {assumption} {negated})\n{}\n(step {}.{} (cl) :rule resolution :premises ({last} {assumption}))\n",
        steps.join("\n"),
        step.id,
        steps.len() + 1,
    );
    // A holey inner proof (an `arith_poly_norm_rel` hole) is still accepted:
    // the trusted content strictly decreased.
    let (commands, _status) = parse_and_check(elaborator.pool, &problem, &proof, rules)
        .map_err(|error| fail("checking the reconstructed steps", error.to_string()))?;
    Ok(external::insert_solver_proof(
        elaborator.pool,
        commands,
        &step.clause,
        &step.id,
        step.depth,
    ))
}

/// Parses the reconstructed proof against the problem's prelude and checks it
/// with the RARE database, so its `rare_rewrite` steps resolve.
fn parse_and_check(
    pool: &mut PrimitivePool,
    problem: &str,
    proof: &str,
    rules: &Rules,
) -> Result<(Vec<ProofCommand>, Status), crate::Error> {
    let config = parser::Config::new()
        .expand_lets(true)
        .allow_int_real_subtyping(true)
        .parse_hole_args(true);
    let problem = parser::Source::new(Path::new("<problem for reconstructed rewrite>"), problem);
    let proof = parser::Source::new(Path::new("<reconstructed rewrite proof>"), proof);
    let (problem, proof, _) = parser::parse_instance_with_pool(problem, proof, None, config, pool)?;
    let status = checker::ProofChecker::new(pool, rules, checker::Config::new())
        .check(&problem, &proof)?;
    Ok((proof.commands, status))
}
