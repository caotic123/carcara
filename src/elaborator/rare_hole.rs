//! Elaboration of `TRUST_THEORY_REWRITE` holes through the RARE
//! post-hoc reconstruction pipeline.
use crate::rare::reconstruction::*;
use rug::{Integer, Rational};
use std::collections::HashMap;

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
    /// Which uninterpreted atoms are integer-valued, for the integer
    /// tightening that relates a negated `>=` to a `<=`.
    pub sorts: ArithSorts,
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
        Self::elaborate_in(certificate, prefix, names, rare, ArithSorts::default())
    }

    pub fn elaborate_in(
        certificate: &Certificate,
        prefix: &str,
        names: HashMap<String, String>,
        rare: HashMap<String, Vec<String>>,
        sorts: ArithSorts,
    ) -> Option<Vec<String>> {
        let mut elaborator = Self {
            prefix: prefix.to_owned(),
            steps: Vec::new(),
            names,
            rare,
            sorts,
        };
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

    /// An encoded integer literal.
    fn numeral(value: &Integer) -> Term {
        Term::new(
            "Mk",
            vec![Term::new("Num", vec![Term::leaf(&value.to_string())])],
        )
    }

    /// Emits a `rare_rewrite` step for `name` instantiated at `arguments`,
    /// or `None` when the database does not carry the rule with that arity.
    fn rare_step(
        &mut self,
        lhs: &Term,
        rhs: &Term,
        name: &str,
        arguments: &[&Term],
    ) -> Option<String> {
        let parameters = self.rare.get(name)?;
        if parameters.len() != arguments.len() {
            return None;
        }
        let decoded = arguments
            .iter()
            .map(|argument| decode_any(argument, &self.names))
            .collect::<Option<Vec<_>>>()?;
        let tail = format!(" :args (\"{name}\" {})", decoded.join(" "));
        self.emit(lhs, rhs, "rare_rewrite", &tail)
    }

    /// Rewrites one side of the goal into an equivalent `>=` relation,
    /// emitting the steps that justify the rewrite.  Returns the `>=` term
    /// together with the id of a step proving `(= side geq)`, or `None` for
    /// a shape with no route.
    fn to_geq(&mut self, side: &Term) -> Option<(Term, Option<String>)> {
        let (operator, arguments) = encoded_application(side)?;
        match (operator, arguments.as_slice()) {
            ("@>=", [_, _]) => Some((side.clone(), None)),
            // (<= a b) = (>= b a)
            ("@<=", [a, b]) => {
                let geq = encoded_app("@>=", vec![b.clone(), a.clone()]);
                let id = self.rare_step(side, &geq, "arith-elim-leq", &[a, b])?;
                Some((geq, Some(id)))
            }
            ("@not", [inner]) => {
                let (inner_operator, inner_arguments) = encoded_application(inner)?;
                let [a, b] = inner_arguments.as_slice() else {
                    return None;
                };
                if inner_operator != "@>=" {
                    return None;
                }
                // (not (>= a b)) is (< a b); over the integers that tightens
                // to (>= b (+ a 1)).  The tightening is only sound when the
                // difference really is integer-valued.
                let difference = poly_of(a)?.sub(&poly_of(b)?);
                if !difference.is_int_valued(&self.sorts, true) {
                    return None;
                }
                let less = encoded_app("@<", vec![a.clone(), b.clone()]);
                // arith-elim-lt: (= (< a b) (not (>= a b)))
                let forward = self.rare_step(&less, side, "arith-elim-lt", &[a, b])?;
                let backward =
                    self.emit(side, &less, "symm", &format!(" :premises ({forward})"))?;
                let bumped = encoded_app("@+", vec![a.clone(), Self::numeral(&Integer::from(1))]);
                let geq = encoded_app("@>=", vec![b.clone(), bumped]);
                // arith-elim-int-lt: (= (< a b) (>= b (+ a 1)))
                let tightened = self.rare_step(&less, &geq, "arith-elim-int-lt", &[a, b])?;
                let id = self.emit(
                    side,
                    &geq,
                    "trans",
                    &format!(" :premises ({backward} {tightened})"),
                )?;
                Some((geq, Some(id)))
            }
            _ => None,
        }
    }

    /// The integer coefficients `(c1, c2)` with `c1 * d1 = c2 * d2`, if the
    /// two differences really are proportional.  `allow_flip` admits a
    /// sign-reversing pair, which `poly_simp_rel` permits only for `=`.
    fn scaling(d1: &Poly, d2: &Poly, allow_flip: bool) -> Option<(Integer, Integer)> {
        let (p1, p2) = (d1.pivot()?, d2.pivot()?);
        if p1 == 0 || p2 == 0 {
            return None;
        }
        let mut candidates = vec![(p2.clone(), p1.clone())];
        if allow_flip {
            candidates.push((Rational::from(-p2.clone()), p1.clone()));
        }
        for (c1, c2) in candidates {
            if d1.scale(&c1) != d2.scale(&c2) {
                continue;
            }
            // Clear denominators so the premise carries integer literals.
            let scale = Integer::from(c1.denom().lcm_ref(c2.denom()));
            let (n1, n2) = (
                Rational::from(&c1 * Rational::from(scale.clone())),
                Rational::from(&c2 * Rational::from(scale)),
            );
            if !n1.is_integer() || !n2.is_integer() {
                continue;
            }
            return Some((n1.numer().clone(), n2.numer().clone()));
        }
        None
    }

    /// `(step p (cl (= (* c1 (- x1 x2)) (* c2 (- y1 y2)))) :rule poly_simp)`
    /// followed by the `poly_simp_rel` step it licenses.
    fn poly_simp_rel_pair(
        &mut self,
        lhs: &Term,
        rhs: &Term,
        x1: &Term,
        x2: &Term,
        y1: &Term,
        y2: &Term,
        allow_flip: bool,
    ) -> Option<String> {
        let d1 = poly_of(x1)?.sub(&poly_of(x2)?);
        let d2 = poly_of(y1)?.sub(&poly_of(y2)?);
        let (c1, c2) = Self::scaling(&d1, &d2, allow_flip)?;
        let scaled = |c: &Integer, a: &Term, b: &Term| {
            encoded_app(
                "@*",
                vec![
                    Self::numeral(c),
                    encoded_app("@-", vec![a.clone(), b.clone()]),
                ],
            )
        };
        let premise = self.emit(&scaled(&c1, x1, x2), &scaled(&c2, y1, y2), "poly_simp", "")?;
        self.emit(
            lhs,
            rhs,
            "poly_simp_rel",
            &format!(" :premises ({premise})"),
        )
    }

    /// Justifies an `arith_poly_norm_rel` obligation with `poly_simp_rel`.
    /// Equalities go straight through; every other relation is routed to a
    /// `>=` form on both sides first, and the routing steps are glued back on
    /// with `trans`/`symm`.
    fn poly_simp_rel_chain(&mut self, lhs: &Term, rhs: &Term) -> Option<String> {
        if let (Some(("@=", left)), Some(("@=", right))) =
            (encoded_application(lhs), encoded_application(rhs))
        {
            if let ([x1, x2], [y1, y2]) = (left.as_slice(), right.as_slice()) {
                return self.poly_simp_rel_pair(lhs, rhs, x1, x2, y1, y2, true);
            }
        }

        let mark = self.steps.len();
        let chain = (|| {
            let (left_geq, left_bridge) = self.to_geq(lhs)?;
            let (right_geq, right_bridge) = self.to_geq(rhs)?;
            let (_, left_arguments) = encoded_application(&left_geq)?;
            let (_, right_arguments) = encoded_application(&right_geq)?;
            let ([x1, x2], [y1, y2]) = (left_arguments.as_slice(), right_arguments.as_slice())
            else {
                return None;
            };
            let mut current =
                self.poly_simp_rel_pair(&left_geq, &right_geq, x1, x2, y1, y2, false)?;
            let mut source = left_geq.clone();
            // Prepend `lhs = left_geq`.
            if let Some(bridge) = left_bridge {
                current = self.emit(
                    lhs,
                    &right_geq,
                    "trans",
                    &format!(" :premises ({bridge} {current})"),
                )?;
                source = lhs.clone();
            }
            // Append `right_geq = rhs`, which is the reverse of the bridge.
            if let Some(bridge) = right_bridge {
                let reversed =
                    self.emit(&right_geq, rhs, "symm", &format!(" :premises ({bridge})"))?;
                current = self.emit(
                    &source,
                    rhs,
                    "trans",
                    &format!(" :premises ({current} {reversed})"),
                )?;
            }
            Some(current)
        })();
        if chain.is_none() {
            // A partial chain must not be left behind for the trusted
            // fallback to be appended to.
            self.steps.truncate(mark);
        }
        chain
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
                // `poly_simp_rel` states one relation as another under a
                // scaled-difference premise, but only between the same
                // operator.  Both sides are therefore first routed to a `>=`
                // form through the RARE arithmetic-elimination rules, which
                // is where the negated and integer-tightened shapes are
                // discharged.  A relation the routing does not cover keeps
                // the trusted form.
                Computation::ArithPolyNormRel => self
                    .poly_simp_rel_chain(lhs, rhs)
                    .or_else(|| self.trusted(lhs, rhs, "arith_poly_norm_rel")),
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
                    Certificate::Computational {
                        kind: Computation::DistinctElim,
                        lhs: d,
                        ..
                    },
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
pub fn spine_arguments<'c>(
    certificate: &'c Certificate,
    out: &mut Vec<&'c Certificate>,
) -> Option<()> {
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

use std::{path::Path, time::Instant};

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

/// Largest e-graph, in tuples, that is worth serializing for reconstruction.
/// Applied only when a budget is in force; an untimed run captures whatever it
/// built, as before.
pub const MAX_SNAPSHOT_TUPLES: usize = 4_000_000;

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
/// The Alethe steps justifying one `TRUST_THEORY_REWRITE` hole.
///
/// Split out from [`elaborate`] because it is the whole cost of a hole and
/// touches nothing shared: it reads the proof node, drives egglog on a pool of
/// its own, and returns text.  That makes it safe to run for many holes at
/// once, with the results parsed back into the proof's own pool afterwards.
pub fn reconstruct_steps(
    pool: &mut dyn TermPool,
    node: &crate::ast::Rc<ProofNode>,
    step: &StepNode,
    rules: &Rules,
    options: crate::checker::RunEgglogOptions,
) -> Result<Vec<String>, String> {
    let stage = |stage: &str, detail: String| format!("{stage}: {detail}");
    let [conclusion] = step.clause.as_slice() else {
        return Err(stage(
            "setup",
            format!(
                "expected a single-literal clause, found {} literals",
                step.clause.len()
            ),
        ));
    };

    // One budget covers the whole hole: the egglog check and the search that
    // follows it are two phases of the same per-hole work, so bounding only
    // the first leaves the second free to run away.
    let deadline = options
        .timeout
        .and_then(|timeout| Instant::now().checked_add(timeout));
    let (result, program) = run_egglog(pool, (conclusion.clone(), node), rules, options);
    let egraph = result.map_err(|error| stage("egglog check", error))?;
    // Serializing the saturated e-graph is proportional to its size and cannot
    // be interrupted once begun, so a budget already spent stops the hole here
    // rather than paying for a snapshot that has no time left to be searched.
    if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
        return Err(stage(
            "egglog check",
            "budget exhausted before the e-graph could be captured".to_owned(),
        ));
    }
    // The copy's cost is proportional to the e-graph, and one saturation
    // iteration can add millions of tuples at once, so the deadline alone does
    // not bound it: an e-graph too large to copy is rejected outright.
    let tuples = egraph.num_tuples();
    if deadline.is_some() && tuples > MAX_SNAPSHOT_TUPLES {
        return Err(stage(
            "egglog check",
            format!("e-graph too large to capture: {tuples} tuples"),
        ));
    }
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
        SearchStrategy::default().with_deadline(deadline),
    );
    let certificate = reconstruction.certificate.ok_or_else(|| {
        stage(
            "reconstruction",
            format!("no certificate found; stats: {:?}", reconstruction.stats),
        )
    })?;
    let names = goal_variable_names(&lhs, &rhs, conclusion);
    let index = rare_arguments(&rules.rules);
    AletheElaborator::elaborate_in(&certificate, &step.id, names, index, sorts).ok_or_else(|| {
        stage(
            "alethe elaboration",
            "a certificate term failed to decode".to_owned(),
        )
    })
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
    let rules = elaborator.rare_rules.ok_or_else(|| {
        ElaborationError::RareReconstruction("setup: no RARE database was given".to_owned())
    })?;
    let options = elaborator.config.hole_rewrite_options;
    let steps = reconstruct_steps(elaborator.pool, node, step, rules, options)
        .map_err(ElaborationError::RareReconstruction)?;
    insert_steps(elaborator, step, steps)
}

/// Checks the reconstructed steps against the problem and splices them in.
/// Always runs on the proof's own pool: the steps arrive as text precisely so
/// that the terms they mention are interned once, here.
pub fn insert_steps(
    elaborator: &mut Elaborator,
    step: &StepNode,
    steps: Vec<String>,
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
            format!(
                "expected a single-literal clause, found {} literals",
                step.clause.len()
            ),
        ));
    };

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
    // A holey inner proof (a relation hole the routing could not discharge)
    // is still accepted: the trusted content strictly decreased.
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
    let status =
        checker::ProofChecker::new(pool, rules, checker::Config::new()).check(&problem, &proof)?;
    Ok((proof.commands, status))
}
