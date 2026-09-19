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
    #[allow(dead_code)]
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
                if let Some(parameters) = self.rare.get(name).cloned() {
                    let decoded: Option<Vec<String>> = parameters
                        .iter()
                        .map(|parameter| match substitution.get(parameter) {
                            // A `:list` parameter binds a sequence of
                            // arguments: a whole chain of them, or none at
                            // all when the rule's empty-list variant is what
                            // matched.  `rare-list` is the term for such a
                            // sequence, which the checker splices back into
                            // the operator when it recomputes the rule.
                            Some(term) => decode_any(term, &self.names)
                                .or_else(|| decode_sequence(term, &self.names)),
                            None => Some("(rare-list)".to_owned()),
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
                // A complementary pair short-circuits the connective, which
                // is what `and_simplify`/`or_simplify` decide.
                Computation::AciComplement => {
                    // The side may have lost its `Mk` wrapper to a congruence
                    // above it, so the connective is read off either form.
                    let connective = |side: &Term| {
                        let inner = if side.op == "Mk" {
                            side.children.first()?
                        } else {
                            side
                        };
                        match inner.op.as_str() {
                            "@and" => Some("and_simplify"),
                            "@or" => Some("or_simplify"),
                            _ => None,
                        }
                    };
                    let rule = connective(lhs).or_else(|| connective(rhs))?;
                    self.emit(lhs, rhs, rule, "")
                }
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

use std::{
    fmt::Write as _,
    io::Write as _,
    os::unix::process::ExitStatusExt,
    path::Path,
    process::{Command, Stdio},
    time::{Duration, Instant},
};

use crate::{
    Status,
    ast::{
        Constant, ProblemPrelude, ProofCommand, ProofNode, ProofNodeForest, Rc, StepNode,
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

/// The tags cvc5 prints on a `ProofRule::TRUST_THEORY_REWRITE` hole: the
/// rule's own name up to April 2026, and `"untranslated rewrite"` since
/// cvc5 #12639 renamed the printed form (same rule, same code path).
pub const THEORY_REWRITE_TAGS: [&str; 2] = ["TRUST_THEORY_REWRITE", "untranslated rewrite"];

/// Whether `step` is a cvc5 theory-rewrite hole.
pub fn is_theory_rewrite_hole(step: &StepNode) -> bool {
    step.rule == "hole"
        && matches!(
            step.args.first().map(|arg| arg.as_ref()),
            Some(crate::ast::Term::Const(Constant::String(tag)))
                if THEORY_REWRITE_TAGS.contains(&tag.as_str())
        )
}

/// Elaborates a `TRUST_THEORY_REWRITE` hole through the post-hoc pipeline:
/// the egglog engine proves the rewrite, a certificate is reconstructed from
/// its saturated e-graph, the certificate's Alethe steps are checked against
/// the RARE database, and the checked proof replaces the hole as a subproof
/// — the same insertion an external solver's proof goes through.
/// Every `TRUST_THEORY_REWRITE` hole in the forest, in encounter order.
pub fn theory_rewrite_holes(proof: &ProofNodeForest) -> Vec<(Rc<ProofNode>, StepNode)> {
    let mut holes = Vec::new();
    let mut seen: std::collections::HashSet<Rc<ProofNode>> = std::collections::HashSet::new();
    let mut todo: Vec<Rc<ProofNode>> = proof.0.iter().cloned().collect();
    while let Some(node) = todo.pop() {
        if !seen.insert(node.clone()) {
            continue;
        }
        match node.as_ref() {
            ProofNode::Step(s) => {
                if is_theory_rewrite_hole(s) {
                    holes.push((node.clone(), s.clone()));
                }
                todo.extend(s.premises.iter().cloned());
                todo.extend(s.discharge.iter().cloned());
                todo.extend(s.previous_step.iter().cloned());
            }
            ProofNode::Subproof(s) => {
                todo.push(s.last_step.clone());
                todo.extend(s.extra_steps.iter().cloned());
                todo.extend(s.outbound_premises.iter().cloned());
            }
            ProofNode::Assume { .. } => {}
        }
    }
    holes
}

/// The line separating the problem from the hole in a child process's input.
pub const HOLE_INPUT_BOUNDARY: &str = ";; --- hole ---";

/// What a child process needs to reconstruct one hole: the problem prelude,
/// then the hole's depth-0 assumptions as top-level `assume`s and the hole
/// itself citing them as premises.  That is exactly what `run_egglog` reads
/// off the in-process node, which collects the depth-0 assumptions beneath it,
/// so the child works from the same inputs the in-process worker would.
/// The problem's text for a hole's terms: the prelude and `assertions`, plus
/// a constant declaration for every variable in `terms` the problem never
/// declares.  A hole inside a subproof may mention variables the enclosing
/// anchors bind (`:args ((x Int) ...)`), and the hole's text must stand on
/// its own.
fn hole_problem_string<'a>(
    pool: &mut PrimitivePool,
    prelude: &ProblemPrelude,
    terms: impl IntoIterator<Item = &'a crate::ast::Rc<crate::ast::Term>>,
    assertions: impl IntoIterator<Item = &'a crate::ast::Rc<crate::ast::Term>>,
) -> String {
    let mut declared: std::collections::HashSet<String> = prelude
        .function_declarations
        .iter()
        .map(|(name, _)| name.clone())
        .collect();
    let mut declarations = String::new();
    for term in terms {
        let free_vars = TermPool::free_vars(pool, term).into_owned();
        for var in free_vars {
            if let crate::ast::Term::Var(name, sort) = var.as_ref() {
                if declared.insert(name.clone()) {
                    let _ = writeln!(declarations, "(declare-const {var} {sort})");
                }
            }
        }
    }
    // The same shape as `external::get_problem_string`, with the extra
    // declarations before the assertions that may use them.
    let mut text = String::new();
    let _ = writeln!(text, "(set-option :produce-proofs true)");
    let _ = write!(text, "{prelude}{declarations}");
    let mut asserts = Vec::new();
    if crate::ast::printer::write_asserts(pool, prelude, &mut asserts, assertions, false).is_ok() {
        text.push_str(&String::from_utf8_lossy(&asserts));
    }
    let _ = writeln!(text, "(check-sat)\n(get-proof)\n(exit)");
    text
}

/// The rule of the steps carrying a normal form to a child: `(step nfK (cl
/// (= t t)) :rule nf-hint :args (H))` says that the subterm of structural
/// hash `H` may be replaced by `t` in the hole's goal.
pub const NF_HINT_RULE: &str = "nf-hint";

pub fn hole_input(
    pool: &mut PrimitivePool,
    prelude: &ProblemPrelude,
    node: &Rc<ProofNode>,
    step: &StepNode,
    extra_premises: &[crate::ast::Rc<crate::ast::Term>],
    hints: &[(u64, String)],
) -> Option<String> {
    let [conclusion] = step.clause.as_slice() else {
        return None;
    };
    // The hole's own assumptions, then the equalities the caller adds (earlier
    // holes already proved whose sides occur in this goal): the child takes
    // every assumption as a union, so those give it the subterm rewrites.
    let assumptions: Vec<crate::ast::Rc<crate::ast::Term>> = node
        .get_assumptions()
        .iter()
        .filter_map(|assumption| match assumption.as_ref() {
            ProofNode::Assume { term, .. } => Some(term.clone()),
            _ => None,
        })
        .chain(extra_premises.iter().cloned())
        .collect();
    let mut text = hole_problem_string(
        pool,
        prelude,
        assumptions.iter().chain(std::iter::once(conclusion)),
        [],
    );
    text.push_str(HOLE_INPUT_BOUNDARY);
    text.push('\n');
    let mut ids = Vec::new();
    for (index, term) in assumptions.iter().enumerate() {
        let id = format!("h{index}");
        // `{:#}` prints without term sharing, so the text stands on its own.
        writeln!(text, "(assume {id} {term:#})").ok()?;
        ids.push(id);
    }
    let premises = if ids.is_empty() {
        String::new()
    } else {
        format!(" :premises ({})", ids.join(" "))
    };
    for (index, (hash, normal_form)) in hints.iter().enumerate() {
        writeln!(
            text,
            "(step nf{index} (cl (= {normal_form} {normal_form})) :rule {NF_HINT_RULE} :args ({hash}))"
        )
        .ok()?;
    }
    writeln!(
        text,
        "(step {} (cl {conclusion:#}) :rule hole{premises} :args (\"TRUST_THEORY_REWRITE\"))",
        step.id
    )
    .ok()?;
    Some(text)
}

/// The input of a batch of holes for the child process: the problem text
/// with every hole's assumptions and conclusion declared, the boundary, then
/// each hole's assumptions and its `hole` step.
pub fn holes_input(
    pool: &mut PrimitivePool,
    prelude: &ProblemPrelude,
    holes: &[(&Rc<ProofNode>, &StepNode)],
) -> Option<String> {
    let mut per_hole = Vec::with_capacity(holes.len());
    for (node, step) in holes {
        let [conclusion] = step.clause.as_slice() else {
            return None;
        };
        let assumptions: Vec<crate::ast::Rc<crate::ast::Term>> = node
            .get_assumptions()
            .iter()
            .filter_map(|assumption| match assumption.as_ref() {
                ProofNode::Assume { term, .. } => Some(term.clone()),
                _ => None,
            })
            .collect();
        per_hole.push((step.id.clone(), assumptions, conclusion.clone()));
    }
    let terms: Vec<&crate::ast::Rc<crate::ast::Term>> = per_hole
        .iter()
        .flat_map(|(_, assumptions, conclusion)| {
            assumptions.iter().chain(std::iter::once(conclusion))
        })
        .collect();
    let mut text = hole_problem_string(pool, prelude, terms, []);
    text.push_str(HOLE_INPUT_BOUNDARY);
    text.push('\n');
    for (hole_index, (id, assumptions, conclusion)) in per_hole.iter().enumerate() {
        let mut ids = Vec::new();
        for (index, term) in assumptions.iter().enumerate() {
            let assume_id = format!("h{hole_index}_{index}");
            writeln!(text, "(assume {assume_id} {term:#})").ok()?;
            ids.push(assume_id);
        }
        let premises = if ids.is_empty() {
            String::new()
        } else {
            format!(" :premises ({})", ids.join(" "))
        };
        writeln!(
            text,
            "(step {id} (cl {conclusion:#}) :rule hole{premises} :args (\"TRUST_THEORY_REWRITE\"))"
        )
        .ok()?;
    }
    Some(text)
}

/// The child's half of [`check_batch_in_child`]: parse the input produced by
/// [`holes_input`] and check every hole in it in one e-graph, returning each
/// hole's id with its verdict.
pub fn check_batch_from_input(
    input: &str,
    rules: parser::Source<'_>,
    options: crate::checker::RunEgglogOptions,
    sequential: bool,
    report: &mut dyn FnMut(&str, &Result<(), String>),
) -> Result<Vec<(String, Result<(), String>)>, String> {
    let boundary = format!("{HOLE_INPUT_BOUNDARY}\n");
    let (problem, proof) = input
        .split_once(&boundary)
        .ok_or_else(|| "hole input has no boundary line".to_owned())?;
    let config = parser::Config::new()
        .expand_lets(true)
        .allow_int_real_subtyping(true)
        .parse_hole_args(true);
    let (_, proof, database, mut pool) = parser::parse_instance(
        parser::Source::new(Path::new("<hole problem>"), problem),
        parser::Source::new(Path::new("<hole>"), proof),
        Some(rules),
        config,
    )
    .map_err(|error| format!("parsing the hole input: {error}"))?;
    let forest = ProofNodeForest::from_commands(proof.commands);
    let holes = theory_rewrite_holes(&forest);
    if holes.is_empty() {
        return Err("hole input contains no TRUST_THEORY_REWRITE hole".to_owned());
    }
    let refs: Vec<(&Rc<ProofNode>, &StepNode)> =
        holes.iter().map(|(node, step)| (node, step)).collect();
    if sequential {
        // One prepared rule database, one e-graph per hole: each verdict is
        // reported as it is reached, so a kill loses only the rest.
        let context = crate::rare::engine::RareCtx::new(&database);
        let mut verdicts = Vec::with_capacity(refs.len());
        // The per-hole budget in `options` is only cooperative, and egglog
        // cannot be interrupted inside an iteration; alone, a hole is killed
        // with its child.  Here a watchdog does the same: past the budget it
        // reports the hole as killed, in the line format the parent parses,
        // and exits, so the parent retries only the holes after it.
        let current: std::sync::Arc<std::sync::Mutex<Option<(String, Instant)>>> =
            std::sync::Arc::new(std::sync::Mutex::new(None));
        if let Some(timeout) = options.timeout {
            let current = std::sync::Arc::clone(&current);
            let grace = Duration::from_millis(500);
            std::thread::spawn(move || loop {
                std::thread::sleep(Duration::from_millis(50));
                let guard = current.lock().unwrap();
                if let Some((id, started)) = guard.as_ref() {
                    let elapsed = started.elapsed();
                    if elapsed > timeout + grace {
                        let mut out = std::io::stdout().lock();
                        let _ = writeln!(
                            out,
                            "hole {id} failed: killed after {:.1}s during egglog: hard budget exhausted",
                            elapsed.as_secs_f64()
                        );
                        let _ = out.flush();
                        std::process::exit(3);
                    }
                }
            });
        }
        for (node, step) in &refs {
            // Announced before the check so that a parent whose child dies
            // without a verdict knows which hole took it down.
            {
                let mut out = std::io::stdout().lock();
                let _ = writeln!(out, "hole {} started", step.id);
                let _ = out.flush();
            }
            *current.lock().unwrap() = Some((step.id.clone(), Instant::now()));
            let verdict = match step.clause.as_slice() {
                [conclusion] => {
                    let assumptions = node.get_assumptions();
                    let premise_clauses: Vec<&[crate::ast::Rc<crate::ast::Term>]> =
                        assumptions.iter().map(|premise| premise.clause()).collect();
                    let (result, _) = crate::rare::engine::check_hole_rewrite_with_context(
                        &mut pool,
                        &step.id,
                        conclusion.clone(),
                        &premise_clauses,
                        &context,
                        options,
                    );
                    result
                        .map(|_| ())
                        .map_err(|error| format!("egglog check: {error}"))
                }
                clause => Err(format!(
                    "setup: expected a single-literal clause, found {} literals",
                    clause.len()
                )),
            };
            *current.lock().unwrap() = None;
            report(&step.id, &verdict);
            verdicts.push((step.id.clone(), verdict));
        }
        return Ok(verdicts);
    }
    let verdicts = check_holes_batched(&mut pool, &refs, &database, options);
    let verdicts: Vec<(String, Result<(), String>)> = refs
        .iter()
        .zip(verdicts)
        .map(|((_, step), verdict)| (step.id.clone(), verdict))
        .collect();
    for (id, verdict) in &verdicts {
        report(id, verdict);
    }
    Ok(verdicts)
}

/// Checks several holes in one e-graph, in this process.  See
/// [`crate::rare::engine::check_hole_rewrites_batched`].
pub fn check_holes_batched(
    pool: &mut dyn TermPool,
    holes: &[(&Rc<ProofNode>, &StepNode)],
    rules: &Rules,
    options: crate::checker::RunEgglogOptions,
) -> Vec<Result<(), String>> {
    let mut goals = Vec::with_capacity(holes.len());
    for (node, step) in holes {
        let [conclusion] = step.clause.as_slice() else {
            // Keep the positions aligned: an ill-formed hole gets a goal that
            // fails translation with a clear message.
            goals.push(crate::rare::engine::BatchGoal {
                label: step.id.clone(),
                conclusion: step.clause.first().cloned().unwrap_or_else(|| {
                    pool.add(crate::ast::Term::Op(crate::ast::Operator::False, vec![]))
                }),
                premise_clauses: Vec::new(),
            });
            continue;
        };
        let premise_clauses = node
            .get_assumptions()
            .iter()
            .map(|premise| premise.clause().to_vec())
            .collect();
        goals.push(crate::rare::engine::BatchGoal {
            label: step.id.clone(),
            conclusion: conclusion.clone(),
            premise_clauses,
        });
    }
    let context = crate::rare::engine::RareCtx::new(rules);
    crate::rare::engine::check_hole_rewrites_batched(pool, &goals, &context, options)
        .into_iter()
        .map(|verdict| verdict.map_err(|error| format!("egglog check: {error}")))
        .collect()
}

/// The child's half of [`reconstruct_in_child`]: parse the input produced by
/// [`hole_input`], find the hole, reconstruct it.
pub fn reconstruct_from_input(
    input: &str,
    rules: parser::Source<'_>,
    options: crate::checker::RunEgglogOptions,
    check_only: bool,
    export_normal_forms: bool,
    phase: &mut dyn FnMut(&str, Duration),
) -> Result<Vec<String>, String> {
    let boundary = format!("{HOLE_INPUT_BOUNDARY}\n");
    let (problem, proof) = input
        .split_once(&boundary)
        .ok_or_else(|| "hole input has no boundary line".to_owned())?;
    let config = parser::Config::new()
        .expand_lets(true)
        .allow_int_real_subtyping(true)
        .parse_hole_args(true);
    let (_, proof, database, mut pool) = parser::parse_instance(
        parser::Source::new(Path::new("<hole problem>"), problem),
        parser::Source::new(Path::new("<hole>"), proof),
        Some(rules),
        config,
    )
    .map_err(|error| format!("parsing the hole input: {error}"))?;
    let forest = ProofNodeForest::from_commands(proof.commands);
    let (node, step) = theory_rewrite_holes(&forest)
        .into_iter()
        .next()
        .ok_or_else(|| "hole input contains no TRUST_THEORY_REWRITE hole".to_owned())?;
    if check_only {
        // The normal forms the parent handed over replace the goal's
        // subterms before translation, so the engine never sees the
        // original subterm and does not normalize it again.
        let hints = normal_form_hints(&forest);
        let [conclusion] = step.clause.as_slice() else {
            return Err(format!(
                "setup: expected a single-literal clause, found {} literals",
                step.clause.len()
            ));
        };
        let mut memo = HashMap::new();
        let mut replaced = 0;
        let goal = crate::rare::util::substitute_by_hash(
            &mut pool,
            conclusion,
            &hints,
            &mut memo,
            &mut replaced,
        );
        if replaced > 0 {
            eprintln!("substituted {replaced} normal forms into the goal");
        }
        return check_hole_exporting(
            &mut pool,
            &node,
            &goal,
            &database,
            options,
            export_normal_forms,
            phase,
        );
    }
    reconstruct_steps_timed(&mut pool, &node, &step, &database, options, phase)
}

/// The normal forms a parent handed to this child, from the `nf-hint` steps
/// of the input: structural hash of the subterm to replace -> its normal form.
fn normal_form_hints(forest: &ProofNodeForest) -> HashMap<u64, crate::ast::Rc<crate::ast::Term>> {
    let mut hints = HashMap::new();
    for root in &forest.0 {
        let ProofNode::Step(step) = root.as_ref() else {
            continue;
        };
        if step.rule != NF_HINT_RULE {
            continue;
        }
        let (Some(hash), Some(clause)) = (step.args.first(), step.clause.first()) else {
            continue;
        };
        let (Some(crate::ast::Term::Const(Constant::Integer(hash))), Some((_, lhs, _))) = (
            Some(hash.as_ref()),
            crate::rare::util::get_equational_terms(clause),
        ) else {
            continue;
        };
        if let Some(hash) = hash.to_u64() {
            hints.insert(hash, lhs.clone());
        }
    }
    hints
}

/// The most subterms of a goal whose normal forms a child exports.
pub const NF_EXPORT_CAP: usize = 256;

/// [`check_hole`] on `goal` (the hole's conclusion, possibly with normal
/// forms substituted in), which after a successful check also reports the
/// normal forms the e-graph found for the goal's compound subterms when
/// `export` is set: one `nf <hash> <term>` line per subterm whose class
/// holds a smaller term, `<hash>` being the subterm's structural hash.
fn check_hole_exporting(
    pool: &mut PrimitivePool,
    node: &crate::ast::Rc<ProofNode>,
    goal: &crate::ast::Rc<crate::ast::Term>,
    rules: &Rules,
    options: crate::checker::RunEgglogOptions,
    export: bool,
    phase: &mut dyn FnMut(&str, Duration),
) -> Result<Vec<String>, String> {
    let deadline = options
        .timeout
        .and_then(|timeout| Instant::now().checked_add(timeout));
    let clock = Instant::now();
    let (result, program) = run_egglog(pool, (goal.clone(), node), rules, options);
    phase("egglog", clock.elapsed());
    let egraph = result.map_err(|error| format!("egglog check: {error}"))?;
    if !export {
        return Ok(Vec::new());
    }
    // The snapshot is skipped when it would not fit the budget or the graph
    // is too large to copy: the verdict stands, the later holes just get
    // nothing from this one.
    if deadline.is_some_and(|deadline| Instant::now() >= deadline)
        || egraph.num_tuples() > MAX_SNAPSHOT_TUPLES
    {
        return Ok(Vec::new());
    }
    let clock = Instant::now();
    let snapshot = EGraphSnapshot::from_raw_nodes(EGraphSnapshot::serialize_production(&egraph));
    phase("serialize", clock.elapsed());
    let clock = Instant::now();
    let lines = export_normal_forms(goal, &snapshot, &program);
    phase("export", clock.elapsed());
    Ok(lines)
}

/// The `nf` lines for `goal`: its compound subterms are aligned with the
/// encoded goal the engine built (the same tree, one `Mk` node per term),
/// each is classified in the snapshot, and the smallest decodable term of
/// its class is reported when it is strictly smaller than the subterm.
fn export_normal_forms(
    goal: &crate::ast::Rc<crate::ast::Term>,
    snapshot: &EGraphSnapshot,
    program: &str,
) -> Vec<String> {
    let (lhs, rhs) = generated_goals(program);
    let names = goal_variable_names(&lhs, &rhs, goal);
    let Some((goal_lhs, goal_rhs)) = crate::rare::util::get_equational_terms(goal)
        .map(|(_, lhs, rhs)| (lhs.clone(), rhs.clone()))
    else {
        return Vec::new();
    };
    let mut aligned: Vec<(crate::ast::Rc<crate::ast::Term>, Term)> = Vec::new();
    align_encoded(&goal_lhs, &lhs, &mut aligned);
    align_encoded(&goal_rhs, &rhs, &mut aligned);
    let mut seen: std::collections::HashSet<usize> = std::collections::HashSet::new();
    let mut classes = HashMap::new();
    let mut representatives: HashMap<u32, Option<Term>> = HashMap::new();
    let mut memo = HashMap::new();
    let mut lines = Vec::new();
    for (subterm, encoded) in aligned {
        if lines.len() >= NF_EXPORT_CAP {
            break;
        }
        if !seen.insert(crate::ast::Rc::as_ptr(&subterm) as *const () as usize) {
            continue;
        }
        let Some(class) = snapshot.class_of(&encoded, &mut classes) else {
            continue;
        };
        let Some(representative) =
            smallest_in_class(snapshot, class, &mut representatives, &mut Vec::new())
        else {
            continue;
        };
        if representative.size() >= encoded.size() || !all_variables_named(&representative, &names)
        {
            continue;
        }
        let Some(text) = decode_any(&representative, &names) else {
            continue;
        };
        lines.push(format!(
            "nf {} {text}",
            crate::rare::util::structural_hash(&subterm, &mut memo)
        ));
    }
    lines
}

/// Pairs each compound subterm of `term` with its encoding, walking both
/// trees in step: an operator application is `(Mk (@op (Args ...)))` with
/// one list element per argument, a function application a curried `App`
/// chain.  A subtree whose shapes disagree is left out.
fn align_encoded(
    term: &crate::ast::Rc<crate::ast::Term>,
    encoded: &Term,
    out: &mut Vec<(crate::ast::Rc<crate::ast::Term>, Term)>,
) {
    let ("Mk", [inner]) = (encoded.op.as_str(), encoded.children.as_slice()) else {
        return;
    };
    match term.as_ref() {
        crate::ast::Term::Op(_, args) if !args.is_empty() => {
            let (operator, [list]) = (inner.op.as_str(), inner.children.as_slice()) else {
                return;
            };
            if !operator.starts_with('@') {
                return;
            }
            let Some(elements) = list_elements(list) else {
                return;
            };
            if elements.len() != args.len() {
                return;
            }
            out.push((term.clone(), encoded.clone()));
            for (arg, element) in args.iter().zip(&elements) {
                align_encoded(arg, element, out);
            }
        }
        crate::ast::Term::App(function, args) => {
            let mut arguments = Vec::new();
            let mut current = inner;
            while let ("App", [next, argument]) = (current.op.as_str(), current.children.as_slice())
            {
                arguments.push(argument);
                current = next;
            }
            arguments.reverse();
            if arguments.len() != args.len() {
                return;
            }
            out.push((term.clone(), encoded.clone()));
            align_encoded(function, current, out);
            for (arg, argument) in args.iter().zip(arguments) {
                align_encoded(arg, argument, out);
            }
        }
        _ => {}
    }
}

/// Whether every variable of an encoded term has a name in `names`, i.e.
/// comes from the goal; a term over a premise's variables cannot be printed.
fn all_variables_named(term: &Term, names: &HashMap<String, String>) -> bool {
    if term.op == "Var" {
        return term
            .children
            .first()
            .is_some_and(|id| names.contains_key(&id.op));
    }
    term.children
        .iter()
        .all(|child| all_variables_named(child, names))
}

/// The smallest term of a class, built from the class's enodes over the
/// smallest terms of their children (solver-internal rows skipped), or
/// `None` for a class reachable only through internal rows or a cycle.
fn smallest_in_class(
    snapshot: &EGraphSnapshot,
    class: u32,
    memo: &mut HashMap<u32, Option<Term>>,
    visiting: &mut Vec<u32>,
) -> Option<Term> {
    if let Some(known) = memo.get(&class) {
        return known.clone();
    }
    if visiting.contains(&class) {
        return None;
    }
    visiting.push(class);
    let mut best: Option<Term> = None;
    if let Some(indices) = snapshot.class_nodes.get(class as usize) {
        for &index in indices {
            let node = &snapshot.nodes[index as usize];
            let op = snapshot.ops.names[node.op as usize].as_str();
            if INTERNAL_OPS.contains(&op) {
                continue;
            }
            let Some(children) = node
                .child_classes
                .iter()
                .map(|&child| smallest_in_class(snapshot, child, memo, visiting))
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            let candidate = Term::new(op, children);
            if best
                .as_ref()
                .is_none_or(|current| (candidate.size(), &candidate) < (current.size(), current))
            {
                best = Some(candidate);
            }
        }
    }
    visiting.pop();
    memo.insert(class, best.clone());
    best
}

/// Reconstructs a hole in a child process that is killed outright when the
/// budget expires.  This is the only hard per-hole bound: the in-process
/// budget can stop egglog only between iterations, and one iteration may run
/// for minutes.  The child is this same binary's hidden `reconstruct-hole`
/// subcommand, fed [`hole_input`] on stdin and read back as Alethe text; an
/// optional address-space limit is applied to it through `ulimit`, so a hole
/// that blows up in memory dies alone instead of taking the parent with it.
pub fn reconstruct_in_child(
    pool: &mut PrimitivePool,
    prelude: &ProblemPrelude,
    node: &Rc<ProofNode>,
    step: &StepNode,
    rare_file: &Path,
    options: crate::checker::RunEgglogOptions,
    memory_limit_mb: Option<usize>,
    check_only: bool,
    deadline: Option<Instant>,
    extra_premises: &[crate::ast::Rc<crate::ast::Term>],
    hints: &[(u64, String)],
    export_normal_forms: bool,
) -> Result<Vec<String>, String> {
    let input = hole_input(pool, prelude, node, step, extra_premises, hints)
        .ok_or_else(|| "expected a single-literal clause".to_owned())?;
    run_hole_worker(
        &step.id,
        input,
        rare_file,
        options,
        None,
        memory_limit_mb,
        check_only,
        if export_normal_forms {
            WorkerMode::SingleExporting
        } else {
            WorkerMode::Single
        },
        deadline,
    )
    .map_err(|(reason, _)| reason)
}

/// Checks a batch of holes in one child process (`reconstruct-hole
/// --check-only --batch`), which saturates them in one e-graph and reports
/// one verdict per hole.  `Ok` maps each hole's id to its verdict; `Err` is
/// the batch as a whole failing (killed at its budget or the proof's, out of
/// memory, or a worker error), in which case the caller may retry the holes
/// one by one.  `options.timeout` is the batch's own budget.
#[allow(clippy::too_many_arguments)]
pub fn check_batch_in_child(
    pool: &mut PrimitivePool,
    prelude: &ProblemPrelude,
    holes: &[(&Rc<ProofNode>, &StepNode)],
    rare_file: &Path,
    options: crate::checker::RunEgglogOptions,
    kill_after: Option<Duration>,
    memory_limit_mb: Option<usize>,
    sequential: bool,
    deadline: Option<Instant>,
) -> Result<HashMap<String, Result<(), String>>, (String, HashMap<String, Result<(), String>>)> {
    let input = holes_input(pool, prelude, holes)
        .ok_or_else(|| ("expected single-literal clauses".to_owned(), HashMap::new()))?;
    let label = format!("batch of {} holes", holes.len());
    // Verdict lines, plus the hole the child had started when it died: that
    // one is charged with the death rather than retried, since alone it
    // would die the same way.
    let parse = |lines: Vec<String>, death: Option<&str>| {
        let mut verdicts = HashMap::new();
        let mut started: Option<String> = None;
        for line in lines {
            let Some(rest) = line.strip_prefix("hole ") else {
                continue;
            };
            let Some((id, verdict)) = rest.split_once(' ') else {
                continue;
            };
            if verdict == "started" {
                started = Some(id.to_owned());
                continue;
            }
            let verdict = match verdict.strip_prefix("failed: ") {
                Some(reason) => Err(reason.to_owned()),
                None => Ok(()),
            };
            verdicts.insert(id.to_owned(), verdict);
        }
        if let (Some(id), Some(reason)) = (started, death) {
            verdicts
                .entry(id)
                .or_insert_with(|| Err(reason.to_owned()));
        }
        verdicts
    };
    match run_hole_worker(
        &label,
        input,
        rare_file,
        options,
        kill_after,
        memory_limit_mb,
        true,
        if sequential { WorkerMode::BatchSequential } else { WorkerMode::Batch },
        deadline,
    ) {
        Ok(lines) => Ok(parse(lines, None)),
        // A killed child may have reported some verdicts before dying.
        Err((reason, lines)) => {
            let partial = parse(lines, Some(&reason));
            Err((reason, partial))
        }
    }
}

/// What the child checks: one hole, a batch in one e-graph, or a batch one
/// hole at a time over a shared rule database.
#[derive(Clone, Copy, PartialEq, Eq)]
enum WorkerMode {
    Single,
    /// One hole, checked, with the normal forms of its goal's subterms
    /// reported afterwards.
    SingleExporting,
    Batch,
    BatchSequential,
}

/// Runs this binary's `reconstruct-hole` subcommand on `input`, killed at
/// the earlier of `options.timeout` and `deadline`, and returns its stdout
/// lines; on failure, the reason together with whatever stdout lines the
/// child produced before it died.
#[allow(clippy::too_many_arguments)]
fn run_hole_worker(
    label: &str,
    input: String,
    rare_file: &Path,
    options: crate::checker::RunEgglogOptions,
    kill_after: Option<Duration>,
    memory_limit_mb: Option<usize>,
    check_only: bool,
    mode: WorkerMode,
    deadline: Option<Instant>,
) -> Result<Vec<String>, (String, Vec<String>)> {
    let batch = !matches!(mode, WorkerMode::Single | WorkerMode::SingleExporting);
    run_hole_worker_inner(
        label,
        input,
        rare_file,
        options,
        kill_after,
        memory_limit_mb,
        check_only,
        batch,
        mode == WorkerMode::BatchSequential,
        mode == WorkerMode::SingleExporting,
        deadline,
    )
}

/// `kill_after` is the child's hard budget when it differs from the
/// cooperative one in `options` (a sequential batch: the per-hole budget
/// inside, the batch's outside).
#[allow(clippy::too_many_arguments)]
fn run_hole_worker_inner(
    label: &str,
    input: String,
    rare_file: &Path,
    options: crate::checker::RunEgglogOptions,
    kill_after: Option<Duration>,
    memory_limit_mb: Option<usize>,
    check_only: bool,
    batch: bool,
    sequential: bool,
    export_normal_forms: bool,
    deadline: Option<Instant>,
) -> Result<Vec<String>, (String, Vec<String>)> {
    let fail = |reason: String| (reason, Vec::new());
    let exe = std::env::current_exe()
        .map_err(|error| fail(format!("locating carcara: {error}")))?;
    // At debug level the child logs too and its whole stderr is reported, so
    // a reconstruction can be followed.
    let debug = log::log_enabled!(log::Level::Debug);
    let mut arguments: Vec<std::ffi::OsString> = Vec::new();
    if debug {
        arguments.push("--log".into());
        arguments.push("debug".into());
    }
    arguments.extend::<[std::ffi::OsString; 3]>([
        "reconstruct-hole".into(),
        "--rare-file".into(),
        rare_file.into(),
    ]);
    if let Some(timeout) = options.timeout {
        arguments.push("--rare-check-timeout".into());
        arguments.push(timeout.as_millis().to_string().into());
    }
    if options.continuous_saturation {
        arguments.push("--continuous-saturation".into());
    }
    if options.seed_from_goal {
        arguments.push("--seed-from-goal".into());
    }
    if options.sort_guards {
        arguments.push("--sort-guards".into());
    }
    if options.growth_cap_arith > 0 {
        arguments.push("--growth-cap-arith".into());
        arguments.push(options.growth_cap_arith.to_string().into());
    }
    if options.growth_cap_plain > 0 {
        arguments.push("--growth-cap-plain".into());
        arguments.push(options.growth_cap_plain.to_string().into());
    }
    if options.memory_soft_cap_mb > 0 {
        arguments.push("--memory-soft-cap".into());
        arguments.push(options.memory_soft_cap_mb.to_string().into());
    }
    if check_only {
        arguments.push("--check-only".into());
    }
    if batch {
        arguments.push("--batch".into());
    }
    if sequential {
        arguments.push("--batch-sequential".into());
    }
    if export_normal_forms {
        arguments.push("--export-normal-forms".into());
    }
    let mut command = match memory_limit_mb {
        // `exec` keeps the child's pid on carcara itself, so killing the pid
        // kills the worker and not a shell wrapped around it.
        Some(megabytes) => {
            let mut command = Command::new("sh");
            command
                .arg("-c")
                .arg("ulimit -v \"$0\" && exec \"$@\"")
                .arg((megabytes * 1024).to_string())
                .arg(&exe)
                .args(&arguments);
            command
        }
        None => {
            let mut command = Command::new(&exe);
            command.args(&arguments);
            command
        }
    };
    let started = Instant::now();
    // The child dies at the earlier of its own budget and the proof's.
    let own_deadline = kill_after
        .or(options.timeout)
        .and_then(|timeout| started.checked_add(timeout));
    let kill_at = match (own_deadline, deadline) {
        (Some(own), Some(all)) => Some(own.min(all)),
        (own, all) => own.or(all),
    };
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| fail(format!("spawning the hole worker: {error}")))?;
    // A child that dies early closes the pipe; the write then fails with
    // EPIPE (Rust ignores SIGPIPE), which the exit status below explains.
    if let Some(mut stdin) = child.stdin.take() {
        let _ = stdin.write_all(input.as_bytes());
    }
    // Both pipes are drained concurrently: the steps can run to megabytes, and
    // a child blocked on a full pipe would look exactly like a stuck one.
    let drain = |mut pipe: Option<_>| {
        std::thread::spawn(move || {
            let mut buffer = Vec::new();
            if let Some(pipe) = pipe.as_mut() {
                let _ = std::io::Read::read_to_end(pipe, &mut buffer);
            }
            buffer
        })
    };
    let stdout = child
        .stdout
        .take()
        .map(|p| Box::new(p) as Box<dyn std::io::Read + Send>);
    let stderr = child
        .stderr
        .take()
        .map(|p| Box::new(p) as Box<dyn std::io::Read + Send>);
    let stdout = drain(stdout);
    let stderr = drain(stderr);
    let status = loop {
        if let Some(status) = child
            .try_wait()
            .map_err(|error| fail(format!("waiting for the hole worker: {error}")))?
        {
            break Some(status);
        }
        if kill_at.is_some_and(|kill_at| Instant::now() >= kill_at) {
            let _ = child.kill();
            let _ = child.wait();
            break None;
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    let stdout = stdout.join().unwrap_or_default();
    let stderr = stderr.join().unwrap_or_default();
    if debug {
        log::debug!("hole worker stderr:\n{}", String::from_utf8_lossy(&stderr));
    }
    // The child reports "phase <name>=<seconds>" as each phase completes, so
    // the phases seen say how far it got.
    let phases: Vec<(String, String)> = String::from_utf8_lossy(&stderr)
        .lines()
        .filter_map(|line| line.strip_prefix("phase ")?.split_once('='))
        .map(|(name, secs)| (name.to_owned(), secs.to_owned()))
        .collect();
    let phase_in_progress = || {
        PHASES
            .iter()
            .find(|name| !phases.iter().any(|(seen, _)| seen == *name))
            .copied()
            .unwrap_or("emit")
    };
    if !phases.is_empty() && !check_only {
        log::info!(
            "hole {}: phases {}",
            label,
            phases
                .iter()
                .map(|(name, secs)| format!("{name}={secs}"))
                .collect::<Vec<_>>()
                .join(" ")
        );
    }
    let lines = || -> Vec<String> {
        String::from_utf8_lossy(&stdout)
            .lines()
            .filter(|line| !line.trim().is_empty())
            .map(str::to_owned)
            .collect()
    };
    let tail = || {
        // The reason is the last thing the child said that was not egglog's
        // routine "Query took a long time" chatter, which would otherwise
        // crowd the real error out of a three-line tail.
        let text = String::from_utf8_lossy(&stderr);
        let lines: Vec<&str> = text
            .lines()
            .filter(|l| {
                let l = l.trim_start();
                !l.is_empty() && !l.starts_with("warn:") && !l.starts_with("phase ")
            })
            .collect();
        lines[lines.len().saturating_sub(3)..].join(" | ")
    };
    match status {
        None => {
            let by_proof = deadline.is_some_and(|all| own_deadline.is_none_or(|own| all < own));
            // The phases already completed say how the budget was spent
            // before the kill, e.g. "(after egglog=0.2)".
            let completed = phases
                .iter()
                .map(|(name, secs)| format!("{name}={secs}"))
                .collect::<Vec<_>>()
                .join(" ");
            Err((format!(
                "killed after {:.1}s during {}{}: {}",
                started.elapsed().as_secs_f64(),
                if check_only {
                    "egglog"
                } else {
                    phase_in_progress()
                },
                if completed.is_empty() {
                    String::new()
                } else {
                    format!(" (after {completed})")
                },
                if by_proof {
                    "the proof's hole budget ran out"
                } else {
                    "hard budget exhausted"
                }
            ), lines()))
        }
        Some(status) if status.success() => Ok(lines()),
        Some(status) => match status.signal() {
            Some(signal) => Err((
                format!("worker killed by signal {signal}: {}", tail()),
                lines(),
            )),
            None => Err((
                format!(
                    "worker exited with status {}: {}",
                    status.code().unwrap_or(-1),
                    tail()
                ),
                lines(),
            )),
        },
    }
}

/// The egglog phase alone: whether the engine proves the hole's equality
/// within the budget.  This is the checking half of the evaluation, run under
/// the same workers and limits as reconstruction so the two are comparable.
pub fn check_hole(
    pool: &mut dyn TermPool,
    node: &crate::ast::Rc<ProofNode>,
    step: &StepNode,
    rules: &Rules,
    options: crate::checker::RunEgglogOptions,
) -> Result<(), String> {
    let [conclusion] = step.clause.as_slice() else {
        return Err(format!(
            "setup: expected a single-literal clause, found {} literals",
            step.clause.len()
        ));
    };
    let (result, _) = run_egglog(pool, (conclusion.clone(), node), rules, options);
    result
        .map(|_| ())
        .map_err(|error| format!("egglog check: {error}"))
}

/// [`check_hole`] over an already prepared rule database, so that a run of
/// holes pays for the database once.
pub fn check_hole_with_context(
    pool: &mut dyn TermPool,
    node: &crate::ast::Rc<ProofNode>,
    step: &StepNode,
    context: &crate::rare::engine::RareCtx<'_>,
    options: crate::checker::RunEgglogOptions,
) -> Result<(), String> {
    let [conclusion] = step.clause.as_slice() else {
        return Err(format!(
            "setup: expected a single-literal clause, found {} literals",
            step.clause.len()
        ));
    };
    let assumptions = node.get_assumptions();
    let premise_clauses: Vec<&[crate::ast::Rc<crate::ast::Term>]> =
        assumptions.iter().map(|premise| premise.clause()).collect();
    let (result, _) = crate::rare::engine::check_hole_rewrite_with_context(
        pool,
        &step.id,
        conclusion.clone(),
        &premise_clauses,
        context,
        options,
    );
    result
        .map(|_| ())
        .map_err(|error| format!("egglog check: {error}"))
}

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
    reconstruct_steps_timed(pool, node, step, rules, options, &mut |_, _| {})
}

/// The phases of one hole's reconstruction, in order.  A worker reports each
/// as it completes, so a hole cut short can be attributed to the phase it was
/// in.
pub const PHASES: [&str; 5] = ["egglog", "serialize", "index", "search", "emit"];

/// [`reconstruct_steps`], calling `phase` with each phase's name and duration
/// as it completes.
pub fn reconstruct_steps_timed(
    pool: &mut dyn TermPool,
    node: &crate::ast::Rc<ProofNode>,
    step: &StepNode,
    rules: &Rules,
    options: crate::checker::RunEgglogOptions,
    phase: &mut dyn FnMut(&str, Duration),
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
    let clock = Instant::now();
    let (result, program) = run_egglog(pool, (conclusion.clone(), node), rules, options);
    phase("egglog", clock.elapsed());
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
    // The snapshot's two halves are timed apart: egglog's serialization of
    // the e-graph, then the indexing of what it produced.
    let clock = Instant::now();
    let raw = EGraphSnapshot::serialize_production(&egraph);
    phase("serialize", clock.elapsed());
    let clock = Instant::now();
    let snapshot = EGraphSnapshot::from_raw_nodes(raw);
    phase("index", clock.elapsed());
    let clock = Instant::now();
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
    phase("search", clock.elapsed());
    let certificate = reconstruction.certificate.ok_or_else(|| {
        stage(
            "reconstruction",
            format!("no certificate found; stats: {:?}", reconstruction.stats),
        )
    })?;
    let clock = Instant::now();
    let names = goal_variable_names(&lhs, &rhs, conclusion);
    let index = rare_arguments(&rules.rules);
    let steps = AletheElaborator::elaborate_in(&certificate, &step.id, names, index, sorts)
        .ok_or_else(|| {
            stage(
                "alethe elaboration",
                "a certificate term failed to decode".to_owned(),
            )
        });
    phase("emit", clock.elapsed());
    steps
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
    let problem = hole_problem_string(
        elaborator.pool,
        &elaborator.problem.prelude,
        [conclusion],
        [&negated],
    );
    let assumption = format!("{}.h", step.id);
    let last = format!("{}.{}", step.id, steps.len());
    let proof = format!(
        "(assume {assumption} {negated})\n{}\n(step {}.{} (cl) :rule resolution :premises ({last} {assumption}))\n",
        steps.join("\n"),
        step.id,
        steps.len() + 1,
    );
    log::debug!("hole {}: reconstructed steps:\n{proof}", step.id);
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

/// The `rare-list` term of an encoded argument chain: what a `:list`
/// parameter binding several arguments is written as.
fn decode_sequence(term: &Term, names: &HashMap<String, String>) -> Option<String> {
    let elements = list_elements(term)?;
    let decoded = elements
        .iter()
        .map(|element| decode_any(element, names))
        .collect::<Option<Vec<_>>>()?;
    Some(format!("(rare-list {})", decoded.join(" ")))
}
