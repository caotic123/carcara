//! An elaborator for Alethe proofs

pub mod error;
pub mod fold;
mod hoist;
pub mod prenorm;
mod hole;
mod local;
mod prune;
mod polyeq;
pub mod rare_hole;
mod reordering;
mod sat_refutation;
mod uncrowding;

use crate::{
    Error, RunEgglogOptions,
    ast::{
        ContextStack, Polyeq, Problem, ProofNode, ProofNodeForest, Rc, StepNode, SubproofNode,
        Term, build_term, match_term,
        pool::{PrimitivePool, TermPool},
        rare_rules::Rules,
    },
    external::{ExternalTool, SatTools},
};
use carcara_macros::GenerateSetters;
use error::{ElaborationError, ElaborationErrorAtStep};
use indexmap::IndexSet;
use polyeq::PolyeqElaborator;
use std::{
    collections::{HashMap, HashSet},
    path::Path,
    path::PathBuf,
    time::{Duration, Instant},
};

/// Configuration options for [`Elaborator`].
#[derive(Debug, Default, Clone, GenerateSetters)]
pub struct Config {
    /// If `Some`, enables the elaboration of `lia_generic` steps using an external solver.
    ///
    /// This involves calling the solver to solve the linear integer arithmetic problem, checking
    /// the proof, and inserting it in the place of the `lia_generic` step.
    lia_solver: Option<ExternalTool>,

    /// Enables an optimization that reorders premises when uncrowding resolution steps, in order to
    /// further minimize the number of `contraction` steps added.
    uncrowd_rotation: bool,

    /// If `Some`, enables the elaboration of `all_simplify` and `rare_rewrite` steps using an
    /// external solver, inserting the solver's proof in the place of those steps.
    hole_solver: Option<ExternalTool>,

    /// The external tools used to elaborate `sat_refutation` steps.
    sat_ref_tools: Option<SatTools>,

    /// Enables the elaboration of `hole` steps marked as `TRUST_THEORY_REWRITE` through the
    /// RARE post-hoc reconstruction pipeline: the egglog engine proves the rewrite, a
    /// certificate is reconstructed from its saturated e-graph, and the certificate's checked
    /// Alethe steps replace the hole. Needs the RARE database, given with
    /// [`Elaborator::with_rare_rules`].
    elaborate_hole_rewrites: bool,

    /// How many holes to reconstruct at once.  One keeps the original
    /// single-threaded pass.
    hole_threads: usize,

    /// Reconstruct each hole in a child process that is killed when the
    /// egglog budget expires — the only hard per-hole bound.  A hole whose
    /// child fails is kept as it was rather than failing the elaboration.
    hole_isolate: bool,

    /// Address-space limit, in megabytes, for each hole's child process.
    hole_memory_limit_mb: Option<usize>,

    /// The RARE file's path, which a child process needs to load the rules.
    hole_rare_file: Option<PathBuf>,

    /// Wall-clock deadline for the proof's holes, set by the caller from
    /// whatever budget it counts (the CLI counts from its start, parsing and
    /// checking included).  Holes not started when it passes are kept as
    /// they were and isolated children still running are killed, so the
    /// proof is always finished with whatever was justified in time rather
    /// than lost to an outer timeout.
    hole_deadline: Option<Instant>,

    /// Only ask egglog whether each hole's equality holds, reconstructing and
    /// splicing nothing: the checking half of the evaluation, under the same
    /// workers and limits as elaboration so the two compare.
    hole_check_only: bool,

    /// With `hole_check_only`, check holes in batches of this many (0 or 1:
    /// one at a time): a batch is saturated in one e-graph, and one that
    /// fails as a whole is retried hole by hole.  Only holes under the same
    /// assumptions share a batch.
    hole_batch: usize,

    /// The budget of one batch; `None` means four times the per-hole budget
    /// (the per-hole budget times the batch size when sequential).
    hole_batch_timeout: Option<Duration>,

    /// A batch's child checks its holes one at a time over one prepared
    /// rule database, each in its own e-graph, instead of all in one.
    hole_batch_sequential: bool,

    /// Group holes into batches by the subterms they share rather than by
    /// proof order: a hole joins the open batch it overlaps most, and a
    /// batch closes at `hole_batch` holes or at `hole_batch_term_cap`
    /// distinct subterms.
    hole_batch_overlap: bool,

    /// With `hole_batch_overlap`, the most distinct compound subterms a
    /// batch may hold (0: no cap).
    hole_batch_term_cap: usize,

    /// Options for the egglog runs behind `elaborate_hole_rewrites`.
    hole_rewrite_options: RunEgglogOptions,

    /// The rules the checker was told to accept as holes, which the hoist pass treats as such.
    allowed_rules: HashSet<String>,

    /// In the checking pass, give each hole the equalities of the holes already proved whose
    /// sides occur in its goal, as premises: the e-graph then starts with those subterm rewrites.
    /// Only equalities proved under a subset of the hole's assumptions are reused.
    hole_reuse_proved: bool,

    /// In the checking pass, hand each hole the normal forms of the subterms of its goal that the
    /// holes already proved found (the smallest equal term in their e-graphs), so that the child
    /// substitutes them into the goal before translation instead of normalizing them again; holes
    /// are scheduled after the holes that normalize their subterms.  Only normal forms found under
    /// a subset of the hole's assumptions are used.
    hole_reuse_subst: bool,

    /// In the checking pass, normalize both sides of every hole with Carcara's own normal forms
    /// (polynomials, linear relations, constant evaluation, `and`/`or` flattening) before egglog:
    /// a hole whose sides coincide is proved outright, the others are checked as the equality of
    /// their normal forms.
    hole_prenormalize: bool,

    /// In the fold pass, the most steps a derivation folded into one hole may have, counted as a
    /// tree (a shared step counts once per use); 0 for no limit.  A larger derivation keeps its
    /// top `cong`/`trans` steps and folds the derivations below them, so the limit sets the
    /// granularity of the holes: 1 makes every rewrite step its own hole.
    fold_limit: usize,
}

impl Config {
    /// Constructs a new `Config`, with default settings.
    pub fn new() -> Self {
        Self::default()
    }
}

/// An elaboration pass, to be applied to a proof.
#[derive(Debug, Clone, Copy)]
pub enum ElaborationPass {
    /// Folds every derivation of `*_simplify`, `ac_simp`, ... steps assembled by `cong`, `trans`,
    /// `refl` and `symm` into one `TRUST_THEORY_REWRITE` hole concluding its equality, so that a
    /// veriT proof's rewrites go through the same hole checking and elaboration as cvc5's.
    Fold,
    /// Lifts every repeated closed derivation, holes included, to the top level and re-points
    /// its other uses at it, so that a `TRUST_THEORY_REWRITE` equality cvc5 printed once per
    /// subproof becomes one hole.
    Hoist,
    /// Removes every command that the derivation of the empty clause does not use.
    Prune,
    /// Elaborates away all uses of polyequality in the proof.
    Polyeq,
    /// Fills holes in the proof using an external solver.
    Hole,
    /// Performs small local elaborations.
    ///
    /// Currently, this affects the rules:
    /// - `eq_transitive`
    /// - `trans`
    /// - `resolution`
    /// - `cong`
    /// - `eq_congruent`
    /// - `eq_congruent_pred`
    /// - `bounded_farkas`
    /// - `eq_mp`
    Local,
    /// Uncrowds `resolution` steps, removing the implicit removal of duplicates by adding
    /// `contraction` steps.
    Uncrowd,
    /// Removes `reordering` steps from the proof, recomputing the conclusions of order-sensitive
    /// steps when necessary.
    Reordering,
    /// Elaborates `sat_refutation` steps using an external SAT solver.
    SatRefutation,
}

/// Groups holes into batches, as lists of indices into `holes`.  Only holes
/// under the same assumptions share a batch, so a batch has one premise
/// context.  In proof order, a batch is the next `batch_size` such holes.
/// By overlap, each hole joins the open batch of its context that shares
/// the most compound subterms with it (none: a new batch), and a batch
/// closes at `batch_size` holes or when adding a hole would exceed
/// `term_cap` distinct compound subterms (0: no cap).  Terms are pooled,
/// so pointer identity is structural identity.
fn group_holes_into_batches(
    holes: &[(Rc<ProofNode>, StepNode)],
    batch_size: usize,
    by_overlap: bool,
    term_cap: usize,
) -> Vec<Vec<usize>> {
    use std::collections::HashSet;
    /// Open batches kept per context; the oldest is closed past this.
    const OPEN_PER_CONTEXT: usize = 16;

    let context_of = |node: &Rc<ProofNode>| {
        let mut key: Vec<usize> = node
            .get_assumptions()
            .iter()
            .map(|assumption| Rc::as_ptr(assumption) as *const () as usize)
            .collect();
        key.sort_unstable();
        key
    };
    let mut batches: Vec<Vec<usize>> = Vec::new();

    if !by_overlap {
        let mut open: HashMap<Vec<usize>, Vec<usize>> = HashMap::new();
        for (index, (node, _)) in holes.iter().enumerate() {
            let batch = open.entry(context_of(node)).or_default();
            batch.push(index);
            if batch.len() >= batch_size {
                batches.push(std::mem::take(batch));
            }
        }
        batches.extend(open.into_values().filter(|batch| !batch.is_empty()));
        return batches;
    }

    let subterms_of = |step: &StepNode| -> HashSet<usize> {
        step.clause
            .iter()
            .flat_map(crate::rare::util::collect_subterms)
            .filter(|term| !matches!(term.as_ref(), Term::Var(..) | Term::Const(_)))
            .map(|term| Rc::as_ptr(&term) as *const () as usize)
            .collect()
    };
    struct Open {
        members: Vec<usize>,
        terms: HashSet<usize>,
    }
    let mut open: HashMap<Vec<usize>, Vec<Open>> = HashMap::new();
    let (mut sum_terms, mut sum_holes) = (0usize, 0usize);
    let mut close = |batch: Open, batches: &mut Vec<Vec<usize>>| {
        sum_terms += batch.terms.len();
        sum_holes += batch.members.len();
        batches.push(batch.members);
    };
    for (index, (node, step)) in holes.iter().enumerate() {
        let terms = subterms_of(step);
        let candidates = open.entry(context_of(node)).or_default();
        let best = candidates
            .iter()
            .enumerate()
            .filter(|(_, batch)| {
                batch.members.len() < batch_size
                    && (term_cap == 0 || batch.terms.union(&terms).count() <= term_cap)
            })
            .map(|(i, batch)| (batch.terms.intersection(&terms).count(), i))
            .filter(|(shared, _)| *shared > 0)
            .max_by_key(|(shared, i)| (*shared, std::cmp::Reverse(*i)));
        match best {
            Some((_, i)) => {
                let batch = &mut candidates[i];
                batch.members.push(index);
                batch.terms.extend(terms);
                if batch.members.len() >= batch_size
                    || (term_cap > 0 && batch.terms.len() >= term_cap)
                {
                    let batch = candidates.remove(i);
                    close(batch, &mut batches);
                }
            }
            None => {
                if candidates.len() >= OPEN_PER_CONTEXT {
                    let oldest = candidates.remove(0);
                    close(oldest, &mut batches);
                }
                candidates.push(Open { members: vec![index], terms });
            }
        }
    }
    for candidates in open.into_values() {
        for batch in candidates {
            if !batch.members.is_empty() {
                close(batch, &mut batches);
            }
        }
    }
    let single: usize = holes
        .iter()
        .map(|(_, step)| subterms_of(step).len())
        .sum();
    log::info!(
        "batches by overlap: {} batches for {} holes, {} distinct compound subterms in the batches against {} summed over the holes (sharing {:.2}), mean {:.1} per batch",
        batches.len(),
        sum_holes,
        sum_terms,
        single,
        if single > 0 { sum_terms as f64 / single as f64 } else { 1.0 },
        if batches.is_empty() { 0.0 } else { sum_terms as f64 / batches.len() as f64 }
    );
    batches
}

/// A proof elaborator for Alethe.
pub struct Elaborator<'e> {
    pool: &'e mut PrimitivePool,
    problem: &'e Problem,
    config: Config,
    rare_rules: Option<&'e Rules>,
}

impl<'e> Elaborator<'e> {
    /// Constructs a new [`Elaborator`] with the given `pool`, `problem`, and `config`.
    pub fn new(pool: &'e mut PrimitivePool, problem: &'e Problem, config: Config) -> Self {
        Self {
            pool,
            problem,
            config,
            rare_rules: None,
        }
    }

    /// Gives the elaborator the RARE database that the `TRUST_THEORY_REWRITE` hole elaboration
    /// runs the egglog engine with and checks the reconstructed steps against.
    pub fn with_rare_rules(mut self, rules: &'e Rules) -> Self {
        self.rare_rules = Some(rules);
        self
    }

    /// Elaborates a proof, applying the default pipeline of passes.
    pub fn elaborate_with_default_pipeline(
        &mut self,
        proof: ProofNodeForest,
        proof_filename: &Path,
    ) -> Result<ProofNodeForest, Error> {
        use ElaborationPass::*;
        let pipeline = vec![Polyeq, Hole, Local, Uncrowd, Reordering];
        self.elaborate(proof, proof_filename, pipeline)
    }

    /// Elaborates a proof, applying the given `pipeline` of passes, in order.
    pub fn elaborate(
        &mut self,
        proof: ProofNodeForest,
        proof_filename: &Path,
        pipeline: Vec<ElaborationPass>,
    ) -> Result<ProofNodeForest, Error> {
        Ok(self
            .elaborate_with_stats(proof, proof_filename, pipeline)?
            .0)
    }

    /// Elaborates a proof, applying the given `pipeline` of passes in order, and returns the
    /// elaborated proof together with the time spent on each pass.
    pub fn elaborate_with_stats(
        &mut self,
        proof: ProofNodeForest,
        proof_filename: &Path,
        pipeline: Vec<ElaborationPass>,
    ) -> Result<(ProofNodeForest, Vec<Duration>), Error> {
        let mut durations = Vec::new();
        let mut current = proof;
        for pass in pipeline {
            let time = Instant::now();
            let result = match pass {
                ElaborationPass::Fold => {
                    Ok(fold::fold(self.pool, current, self.config.fold_limit))
                }
                ElaborationPass::Hoist => {
                    Ok(hoist::hoist(self.pool, current, &self.config.allowed_rules, true))
                }
                ElaborationPass::Prune => Ok(prune::prune(current)),
                ElaborationPass::Polyeq => self.elaborate_polyeq(current),
                ElaborationPass::Hole => self.elaborate_hole(current),
                ElaborationPass::Local => self.elaborate_local(current),
                ElaborationPass::Uncrowd => current.mutate(|_, node, _| match node.as_ref() {
                    ProofNode::Step(s)
                        if (s.rule == "resolution" || s.rule == "th_resolution")
                            && !s.args.is_empty() =>
                    {
                        uncrowding::uncrowd_resolution(self.pool, s, self.config.uncrowd_rotation)
                            .map_err(|e| e.at(s))
                    }
                    _ => Ok(node.clone()),
                }),
                ElaborationPass::Reordering => reordering::remove_reorderings(current),
                ElaborationPass::SatRefutation => {
                    if self.config.sat_ref_tools.is_some() {
                        current.mutate(|_, node, _| match node.as_ref() {
                            ProofNode::Step(s) if (s.rule == "sat_refutation") => {
                                // TODO: proper error handling
                                Ok(sat_refutation::sat_refutation(self, s)
                                    .unwrap_or_else(|| node.clone()))
                            }
                            _ => Ok(node.clone()),
                        })
                    } else {
                        Ok(current)
                    }
                }
            };
            current = result.map_err(|e| e.at(proof_filename, pass))?;
            durations.push(time.elapsed());
        }
        Ok((current, durations))
    }

    fn elaborate_polyeq(
        &mut self,
        proof: ProofNodeForest,
    ) -> Result<ProofNodeForest, ElaborationErrorAtStep> {
        fn get_elaboration_function(rule: &str) -> Option<ElaborationFunc> {
            Some(match rule {
                "refl" => polyeq::reflexivity::refl,
                "forall_inst" => polyeq::quantifiers::forall_inst,
                "subproof" => polyeq::subproof::subproof,
                "ite_intro" => polyeq::tautology::ite_intro,
                "bfun_elim" => polyeq::clausification::bfun_elim,
                _ => return None,
            })
        }

        proof.mutate(|context, node, _| match node.as_ref() {
            ProofNode::Assume { id, depth, term }
                if context.is_empty() && !self.problem.premises.contains(term) =>
            {
                Ok(self.elaborate_assume(id, *depth, term))
            }
            ProofNode::Step(s) => {
                if let Some(func) = get_elaboration_function(&s.rule) {
                    func(self.pool, context, s).map_err(|e| e.at(s))
                } else {
                    Ok(node.clone())
                }
            }
            _ => Ok(node.clone()),
        })
    }

    /// Reconstructs every hole on a pool of workers, returning what each one
    /// produced.  Workers share nothing but the immutable proof and rule
    /// database: each drives egglog on a term pool of its own — or, with
    /// `hole_isolate`, in a child process it can kill — and hands back text,
    /// so the proof's own pool is touched only by the caller.
    fn reconstruct_holes_in_parallel(
        &mut self,
        proof: &ProofNodeForest,
    ) -> HashMap<String, (Result<Vec<String>, String>, Duration)> {
        let mut holes = rare_hole::theory_rewrite_holes(proof);
        if holes.is_empty() {
            return HashMap::new();
        }
        let Some(rules) = self.rare_rules else {
            return HashMap::new();
        };
        // Carcara's own normal forms first: a hole whose sides normalize to
        // the same term needs no egglog, the others are checked as the
        // equality of the normal forms.
        let mut prenormalized: HashMap<String, (Result<Vec<String>, String>, Duration)> =
            HashMap::new();
        // In the elaboration pass the certificate of a closed hole replaces it.
        let mut normalizer = prenorm::Normalizer::new();
        if self.config.hole_prenormalize {
            let started = Instant::now();
            let mut rewritten = 0;
            for (_, step) in holes.iter_mut() {
                let Some(conclusion) = step.clause.first().cloned() else {
                    continue;
                };
                let Some((crate::ast::Operator::Equals, lhs, rhs)) =
                    crate::rare::util::get_equational_terms(&conclusion)
                else {
                    continue;
                };
                let (lhs, rhs) = (lhs.clone(), rhs.clone());
                let left = normalizer.normalize(self.pool, &lhs);
                let right = normalizer.normalize(self.pool, &rhs);
                if left == right {
                    log::debug!("hole {}: closed by normalization to {:#}", step.id, left);
                    let steps = if self.config.hole_check_only {
                        Vec::new()
                    } else {
                        normalizer
                            .certificate(self.pool, &step.id, &lhs, &rhs)
                            .unwrap_or_default()
                    };
                    prenormalized.insert(step.id.clone(), (Ok(steps), Duration::ZERO));
                } else if self.config.hole_check_only && (left != lhs || right != rhs) {
                    // Only the checking pass hands egglog the normalized goal.
                    // In the elaboration pass the certificate search works on
                    // the e-graph of the goal it was given, and a normalized
                    // goal is a different term from the ones the rules were
                    // compiled around, so egglog proves more of them and the
                    // reconstruction replays less; the original goal is kept,
                    // and the normalizer contributes the holes it closes
                    // outright.  (Trying the normalized goal first and the
                    // original on a reconstruction failure would get both, at
                    // one extra child run per lost hole.)
                    step.clause = vec![
                        self.pool
                            .add(Term::Op(crate::ast::Operator::Equals, vec![left, right])),
                    ];
                    rewritten += 1;
                }
            }
            let total = holes.len();
            holes.retain(|(_, step)| !prenormalized.contains_key(&step.id));
            log::info!(
                "hole prenorm: {} of {} holes closed by normalization, {} goals rewritten, in {:.3}s",
                prenormalized.len(),
                total,
                rewritten,
                started.elapsed().as_secs_f64()
            );
            if holes.is_empty() {
                return prenormalized;
            }
        }
        let options = self.config.hole_rewrite_options;
        let isolate = self.config.hole_isolate;
        let check_only = self.config.hole_check_only;
        let deadline = self.config.hole_deadline;
        let memory_limit = self.config.hole_memory_limit_mb;
        let rare_file = self.config.hole_rare_file.clone();
        let prelude = &self.problem.prelude;
        let workers = self.config.hole_threads.min(holes.len()).max(1);
        let next = std::sync::atomic::AtomicUsize::new(0);
        let results = std::sync::Mutex::new(HashMap::new());

        // cvc5 prints the same theory-rewrite equality as a separate hole
        // step at every use: on the sample proofs 40–75% of the holes of an
        // arithmetic proof are duplicates.  A verdict depends only on the
        // goal and its assumptions (terms are pooled, so pointer identity is
        // structural identity), so the checking pass runs one hole per
        // distinct goal and copies its verdict to the others.
        let mut worklist: Vec<usize> = Vec::with_capacity(holes.len());
        let mut duplicates: Vec<(usize, usize)> = Vec::new();
        if check_only {
            let mut first: HashMap<(usize, Vec<usize>), usize> = HashMap::new();
            for (index, (node, step)) in holes.iter().enumerate() {
                let conclusion = step
                    .clause
                    .first()
                    .map(|term| Rc::as_ptr(term) as *const () as usize)
                    .unwrap_or(0);
                let mut context: Vec<usize> = node
                    .get_assumptions()
                    .iter()
                    .map(|assumption| Rc::as_ptr(assumption) as *const () as usize)
                    .collect();
                context.sort_unstable();
                match first.entry((conclusion, context)) {
                    std::collections::hash_map::Entry::Occupied(entry) => {
                        duplicates.push((index, *entry.get()));
                    }
                    std::collections::hash_map::Entry::Vacant(entry) => {
                        entry.insert(index);
                        worklist.push(index);
                    }
                }
            }
            if !duplicates.is_empty() {
                log::info!(
                    "hole memo: {} of {} holes repeat an earlier goal; {} distinct goals to check",
                    duplicates.len(),
                    holes.len(),
                    worklist.len()
                );
            }
        } else {
            worklist.extend(0..holes.len());
        }
        let mut worklist = worklist;

        // Substitution-based reuse: the holes that normalize a subterm run
        // before the holes sharing it.  Every hole's compound subterms are
        // hashed structurally; the owner of a subterm is the smallest hole
        // holding it (the cheapest one that normalizes it), and a hole
        // depends on the owners of its subterms.  The worklist is ordered
        // by goal size, and a worker takes the first hole whose owners are
        // all done, falling back to the first hole left when none is ready
        // within a window, so workers never idle.
        let subst = check_only && self.config.hole_reuse_subst;
        let mut hole_hashes: Vec<Vec<u64>> = vec![Vec::new(); holes.len()];
        let mut dependencies: Vec<Vec<usize>> = vec![Vec::new(); holes.len()];
        // Per hole: whether a later hole depends on it, so its normal forms
        // are worth the snapshot that exporting them costs.
        let mut exports: Vec<bool> = vec![false; holes.len()];
        if subst {
            let mut memo = HashMap::new();
            let mut sizes: Vec<usize> = vec![0; holes.len()];
            for &index in &worklist {
                if let Some(conclusion) = holes[index].1.clause.first() {
                    sizes[index] = term_node_count(conclusion);
                    hole_hashes[index] =
                        crate::rare::util::compound_subterms(conclusion, rare_hole::NF_EXPORT_CAP)
                            .iter()
                            .map(|term| crate::rare::util::structural_hash(term, &mut memo))
                            .collect();
                }
            }
            let mut by_size = worklist.clone();
            by_size.sort_by_key(|&index| (sizes[index], index));
            let mut owner: HashMap<u64, usize> = HashMap::new();
            for &index in &by_size {
                for &hash in &hole_hashes[index] {
                    owner.entry(hash).or_insert(index);
                }
            }
            let mut with_dependencies = 0;
            for &index in &by_size {
                let mut deps: Vec<usize> = hole_hashes[index]
                    .iter()
                    .filter_map(|hash| owner.get(hash).copied())
                    .filter(|&owner| owner != index)
                    .collect();
                deps.sort_unstable();
                deps.dedup();
                if !deps.is_empty() {
                    with_dependencies += 1;
                }
                for &dep in &deps {
                    exports[dep] = true;
                }
                dependencies[index] = deps;
            }
            // The owners go first, smallest first; the other holes keep the
            // proof's order, which spreads the large ones over the pass.
            let owners: Vec<usize> = by_size.iter().copied().filter(|&i| exports[i]).collect();
            let others: Vec<usize> = worklist.iter().copied().filter(|&i| !exports[i]).collect();
            worklist = owners.iter().chain(&others).copied().collect();
            log::info!(
                "hole schedule: {} holes normalize a subterm of a later hole and go first; {} wait for them",
                owners.len(),
                with_dependencies
            );
        }
        let worklist = worklist;
        let hole_hashes = hole_hashes;
        let dependencies = dependencies;
        let exports = exports;
        // Per hole index: finished (whatever the verdict).
        let done: Vec<std::sync::atomic::AtomicBool> = (0..holes.len())
            .map(|_| std::sync::atomic::AtomicBool::new(false))
            .collect();
        struct Schedule {
            taken: Vec<bool>,
            cursor: usize,
        }
        let schedule = std::sync::Mutex::new(Schedule {
            taken: vec![false; worklist.len()],
            cursor: 0,
        });
        const SCHEDULE_WINDOW: usize = 512;
        let pick = || -> Option<usize> {
            if !subst {
                let position = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                return worklist.get(position).copied();
            }
            let mut schedule = schedule.lock().unwrap();
            while schedule.cursor < worklist.len() && schedule.taken[schedule.cursor] {
                schedule.cursor += 1;
            }
            let start = schedule.cursor;
            if start >= worklist.len() {
                return None;
            }
            let end = (start + SCHEDULE_WINDOW).min(worklist.len());
            let ready = (start..end).find(|&position| {
                !schedule.taken[position]
                    && dependencies[worklist[position]]
                        .iter()
                        .all(|&dep| done[dep].load(std::sync::atomic::Ordering::Acquire))
            });
            let position = ready.unwrap_or(start);
            schedule.taken[position] = true;
            Some(worklist[position])
        };
        // The normal forms found so far, by the structural hash of the
        // subterm: (assumptions they were found under, normal form text).
        type NormalForms = HashMap<u64, Vec<(Vec<usize>, String)>>;
        let normal_forms: std::sync::Mutex<NormalForms> = std::sync::Mutex::new(HashMap::new());
        let exported_count = std::sync::atomic::AtomicUsize::new(0);
        let substituted_count = std::sync::atomic::AtomicUsize::new(0);
        const HINT_LIMIT: usize = 64;

        // The equalities proved so far, by the pointer of each side: an
        // equality is reused for a later hole whose goal contains that side,
        // when it was proved under a subset of that hole's assumptions.
        type Proved = HashMap<usize, Vec<(Vec<usize>, Rc<Term>)>>;
        let proved: std::sync::Mutex<Proved> = std::sync::Mutex::new(HashMap::new());
        let reuse = check_only && self.config.hole_reuse_proved;
        let reused_count = std::sync::atomic::AtomicUsize::new(0);
        let context_of = |node: &Rc<ProofNode>| -> Vec<usize> {
            let mut key: Vec<usize> = node
                .get_assumptions()
                .iter()
                .map(|assumption| Rc::as_ptr(assumption) as *const () as usize)
                .collect();
            key.sort_unstable();
            key
        };
        let ptr = |term: &Rc<Term>| Rc::as_ptr(term) as *const () as usize;
        let sides = |step: &StepNode| -> Option<(Rc<Term>, Rc<Term>)> {
            match step.clause.first().map(|c| c.as_ref()) {
                Some(Term::Op(crate::ast::Operator::Equals, args)) if args.len() == 2 => {
                    Some((args[0].clone(), args[1].clone()))
                }
                _ => None,
            }
        };

        if check_only && self.config.hole_batch > 1 {
            self.check_holes_in_batches(&holes, &results);
            let mut results = results.into_inner().unwrap();
            results.extend(prenormalized.clone());
            for (_, step) in &holes {
                results.entry(step.id.clone()).or_insert_with(|| {
                    (
                        Err("skipped: the proof's hole budget ran out".to_owned()),
                        Duration::ZERO,
                    )
                });
            }
            return results;
        }

        std::thread::scope(|scope| {
            for _ in 0..workers {
                scope.spawn(|| {
                    let mut pool = crate::ast::pool::PrimitivePool::new();
                    loop {
                        // Past the proof's budget no further hole is started;
                        // the ones never started are recorded as skipped below.
                        if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
                            return;
                        }
                        let Some(index) = pick() else {
                            return;
                        };
                        let (node, step) = &holes[index];
                        let started = Instant::now();
                        // The normal forms known for this goal's subterms,
                        // outermost first, found under a compatible context.
                        let hints: Vec<(u64, String)> = if subst {
                            let context = context_of(node);
                            let table = normal_forms.lock().unwrap();
                            let mut hints = Vec::new();
                            for hash in &hole_hashes[index] {
                                let Some(entries) = table.get(hash) else {
                                    continue;
                                };
                                if let Some((_, text)) = entries.iter().find(|(found_under, _)| {
                                    found_under
                                        .iter()
                                        .all(|a| context.binary_search(a).is_ok())
                                }) {
                                    hints.push((*hash, text.clone()));
                                    if hints.len() >= HINT_LIMIT {
                                        break;
                                    }
                                }
                            }
                            hints
                        } else {
                            Vec::new()
                        };
                        if !hints.is_empty() {
                            substituted_count
                                .fetch_add(hints.len(), std::sync::atomic::Ordering::Relaxed);
                        }
                        // Earlier proved equalities whose sides occur in this
                        // goal, under a compatible context.
                        let extra: Vec<Rc<Term>> = if reuse {
                            const REUSE_LIMIT: usize = 64;
                            let context = context_of(node);
                            let own = step.clause.first().map(ptr).unwrap_or(0);
                            let table = proved.lock().unwrap();
                            let mut seen = HashSet::new();
                            let mut extra = Vec::new();
                            'outer: for term in step.clause.iter() {
                                for subterm in crate::rare::util::collect_subterms(term) {
                                    let Some(entries) = table.get(&ptr(&subterm)) else {
                                        continue;
                                    };
                                    for (proved_context, equality) in entries {
                                        if ptr(equality) == own
                                            || !seen.insert(ptr(equality))
                                            || !proved_context
                                                .iter()
                                                .all(|a| context.binary_search(a).is_ok())
                                        {
                                            continue;
                                        }
                                        extra.push(equality.clone());
                                        if extra.len() >= REUSE_LIMIT {
                                            break 'outer;
                                        }
                                    }
                                }
                            }
                            extra
                        } else {
                            Vec::new()
                        };
                        if !extra.is_empty() {
                            reused_count.fetch_add(extra.len(), std::sync::atomic::Ordering::Relaxed);
                        }
                        let result = if isolate {
                            match rare_file.as_deref() {
                                Some(path) => rare_hole::reconstruct_in_child(
                                    &mut pool,
                                    prelude,
                                    node,
                                    step,
                                    path,
                                    options,
                                    memory_limit,
                                    check_only,
                                    deadline,
                                    &extra,
                                    &hints,
                                    subst && exports[index],
                                ),
                                None => {
                                    Err("isolating holes needs the RARE file's path".to_owned())
                                }
                            }
                        } else if check_only {
                            rare_hole::check_hole(&mut pool, node, step, rules, options)
                                .map(|()| Vec::new())
                        } else {
                            rare_hole::reconstruct_steps(&mut pool, node, step, rules, options)
                        };
                        if reuse && result.is_ok() {
                            if let (Some((lhs, rhs)), Some(conclusion)) =
                                (sides(step), step.clause.first())
                            {
                                let context = context_of(node);
                                let mut table = proved.lock().unwrap();
                                for side in [lhs, rhs] {
                                    table
                                        .entry(ptr(&side))
                                        .or_default()
                                        .push((context.clone(), conclusion.clone()));
                                }
                            }
                        }
                        // The child's `nf <hash> <term>` lines are the normal
                        // forms it found; they are text until a later child
                        // parses them, so no pool is shared between workers.
                        let result = if subst {
                            result.map(|lines| {
                                let mut found = 0;
                                let context = context_of(node);
                                let mut table = normal_forms.lock().unwrap();
                                for line in &lines {
                                    let Some(rest) = line.strip_prefix("nf ") else {
                                        continue;
                                    };
                                    let Some((hash, text)) = rest.split_once(' ') else {
                                        continue;
                                    };
                                    let Ok(hash) = hash.parse::<u64>() else {
                                        continue;
                                    };
                                    table
                                        .entry(hash)
                                        .or_default()
                                        .push((context.clone(), text.to_owned()));
                                    found += 1;
                                }
                                exported_count.fetch_add(found, std::sync::atomic::Ordering::Relaxed);
                                Vec::new()
                            })
                        } else {
                            result
                        };
                        results
                            .lock()
                            .unwrap()
                            .insert(step.id.clone(), (result, started.elapsed()));
                        done[index].store(true, std::sync::atomic::Ordering::Release);
                    }
                });
            }
        });
        let mut results = results.into_inner().unwrap();
        if subst {
            log::info!(
                "hole subst: {} normal forms exported, {} substitutions handed to later holes",
                exported_count.load(std::sync::atomic::Ordering::Relaxed),
                substituted_count.load(std::sync::atomic::Ordering::Relaxed)
            );
        }
        if reuse {
            log::info!(
                "hole reuse: {} proved equalities handed to later holes as premises",
                reused_count.load(std::sync::atomic::Ordering::Relaxed)
            );
        }
        // A duplicate takes its representative's verdict; one whose
        // representative was never started is skipped like it.
        for (index, representative) in duplicates {
            let copied = results
                .get(&holes[representative].1.id)
                .map(|(result, _)| (result.clone(), Duration::ZERO));
            if let Some(copied) = copied {
                results.insert(holes[index].1.id.clone(), copied);
            }
        }
        for (_, step) in &holes {
            results.entry(step.id.clone()).or_insert_with(|| {
                (
                    Err("skipped: the proof's hole budget ran out".to_owned()),
                    Duration::ZERO,
                )
            });
        }
        results.extend(prenormalized);
        results
    }

    /// See [`group_holes_into_batches`].
    #[cfg(test)]
    pub(crate) fn batches_for_test(
        holes: &[(Rc<ProofNode>, StepNode)],
        batch_size: usize,
        by_overlap: bool,
        term_cap: usize,
    ) -> Vec<Vec<usize>> {
        group_holes_into_batches(holes, batch_size, by_overlap, term_cap)
    }

    /// The batched checking pass: holes are grouped, in proof order, into
    /// batches of `hole_batch` that share their assumptions, and each batch
    /// is saturated in one e-graph (one child with `hole_isolate`).  A batch
    /// that fails as a whole is retried hole by hole, so batching can only
    /// lose time, never verdicts.  Records one result per hole in `results`,
    /// with the batch's time split evenly over its holes.
    fn check_holes_in_batches(
        &self,
        holes: &[(Rc<ProofNode>, StepNode)],
        results: &std::sync::Mutex<HashMap<String, (Result<Vec<String>, String>, Duration)>>,
    ) {
        let Some(rules) = self.rare_rules else {
            return;
        };
        let options = self.config.hole_rewrite_options;
        let isolate = self.config.hole_isolate;
        let deadline = self.config.hole_deadline;
        let memory_limit = self.config.hole_memory_limit_mb;
        let rare_file = self.config.hole_rare_file.clone();
        let prelude = &self.problem.prelude;
        let batch_size = self.config.hole_batch;
        let sequential = self.config.hole_batch_sequential;
        // The child's cooperative budget: for a shared e-graph the whole
        // batch's, for sequential checking each hole's own.  The kill of the
        // child is at the batch budget below.
        let child_options = if sequential {
            options
        } else {
            RunEgglogOptions {
                timeout: self
                    .config
                    .hole_batch_timeout
                    .or_else(|| options.timeout.map(|timeout| timeout * 4)),
                ..options
            }
        };
        let batch_kill_after = |holes: usize| {
            if sequential {
                self.config
                    .hole_batch_timeout
                    .or_else(|| options.timeout.map(|timeout| timeout * holes as u32))
            } else {
                child_options.timeout
            }
        };

        let batches = group_holes_into_batches(
            holes,
            batch_size,
            self.config.hole_batch_overlap,
            self.config.hole_batch_term_cap,
        );
        let workers = self.config.hole_threads.min(batches.len()).max(1);
        let next = std::sync::atomic::AtomicUsize::new(0);

        std::thread::scope(|scope| {
            for _ in 0..workers {
                scope.spawn(|| {
                    let mut pool = crate::ast::pool::PrimitivePool::new();
                    loop {
                        if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
                            return;
                        }
                        let index = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        let Some(batch) = batches.get(index) else {
                            return;
                        };
                        let members: Vec<(&Rc<ProofNode>, &StepNode)> = batch
                            .iter()
                            .map(|&i| (&holes[i].0, &holes[i].1))
                            .collect();
                        let started = Instant::now();
                        type Verdicts = HashMap<String, Result<(), String>>;
                        let outcome: Result<Verdicts, (String, Verdicts)> = if isolate {
                            match rare_file.as_deref() {
                                Some(path) => rare_hole::check_batch_in_child(
                                    &mut pool,
                                    prelude,
                                    &members,
                                    path,
                                    child_options,
                                    batch_kill_after(members.len()),
                                    memory_limit,
                                    sequential,
                                    deadline,
                                ),
                                None => Err((
                                    "isolating holes needs the RARE file's path".to_owned(),
                                    HashMap::new(),
                                )),
                            }
                        } else if sequential {
                            let context = crate::rare::engine::RareCtx::new(rules);
                            Ok(members
                                .iter()
                                .map(|(node, step)| {
                                    let verdict = rare_hole::check_hole_with_context(
                                        &mut pool, node, step, &context, options,
                                    );
                                    (step.id.clone(), verdict)
                                })
                                .collect())
                        } else {
                            let verdicts = rare_hole::check_holes_batched(
                                &mut pool,
                                &members,
                                rules,
                                child_options,
                            );
                            Ok(members
                                .iter()
                                .zip(verdicts)
                                .map(|((_, step), verdict)| (step.id.clone(), verdict))
                                .collect())
                        };
                        let elapsed = started.elapsed();
                        let (verdicts, failure) = match outcome {
                            Ok(verdicts) => (verdicts, None),
                            Err((reason, partial)) => (partial, Some(reason)),
                        };
                        let proved = verdicts.values().filter(|v| v.is_ok()).count();
                        // The batch's time is split over the holes it gave a
                        // verdict to; a retried hole gets its own time below.
                        let share = elapsed / verdicts.len().max(1) as u32;
                        {
                            let mut results = results.lock().unwrap();
                            for (id, verdict) in &verdicts {
                                results.insert(
                                    id.clone(),
                                    (verdict.clone().map(|()| Vec::new()), share),
                                );
                            }
                        }
                        let Some(reason) = failure else {
                            log::info!(
                                "batch {index}: {} holes, proved {proved}, {:.3}s",
                                members.len(),
                                elapsed.as_secs_f64()
                            );
                            continue;
                        };
                        let missing: Vec<&(&Rc<ProofNode>, &StepNode)> = members
                            .iter()
                            .filter(|(_, step)| !verdicts.contains_key(&step.id))
                            .collect();
                        log::warn!(
                            "batch {index}: {} holes failed after {:.3}s with {} verdicts ({reason}); retrying the {} without one",
                            members.len(),
                            elapsed.as_secs_f64(),
                            verdicts.len(),
                            missing.len()
                        );
                        {
                            let members = missing;
                                for (node, step) in members {
                                    if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
                                        return;
                                    }
                                    let started = Instant::now();
                                    let result = if isolate {
                                        match rare_file.as_deref() {
                                            Some(path) => rare_hole::reconstruct_in_child(
                                                &mut pool,
                                                prelude,
                                                node,
                                                step,
                                                path,
                                                options,
                                                memory_limit,
                                                true,
                                                deadline,
                                                &[],
                                                &[],
                                                false,
                                            ),
                                            None => Err(
                                                "isolating holes needs the RARE file's path"
                                                    .to_owned(),
                                            ),
                                        }
                                    } else {
                                        rare_hole::check_hole(&mut pool, node, step, rules, options)
                                            .map(|()| Vec::new())
                                    };
                                    results
                                        .lock()
                                        .unwrap()
                                        .insert(step.id.clone(), (result, started.elapsed()));
                                }
                            }
                        }
                });
            }
        });
    }

    fn elaborate_hole(
        &mut self,
        proof: ProofNodeForest,
    ) -> Result<ProofNodeForest, ElaborationErrorAtStep> {
        // Skip `mutate` in the common case where none of the options was given
        let rare_holes = self.config.elaborate_hole_rewrites && self.rare_rules.is_some();
        if self.config.hole_solver.is_none() && self.config.lia_solver.is_none() && !rare_holes {
            return Ok(proof);
        }

        // Reconstructing a hole is the whole cost and shares nothing, so the
        // holes are done together up front and `mutate` below only splices the
        // finished text in.
        let prepass = rare_holes
            && (self.config.hole_threads > 1
                || self.config.hole_isolate
                || self.config.hole_check_only
                || self.config.hole_deadline.is_some());
        let prepass_started = Instant::now();
        let mut reconstructed = if prepass {
            self.reconstruct_holes_in_parallel(&proof)
        } else {
            HashMap::new()
        };
        let prepass_time = prepass_started.elapsed();
        // A prepass result is final for its hole in every mode but the plain
        // multi-threaded one: nothing is retried in-process, since that would
        // re-run exactly the work the budget or the child gave up on.  In the
        // plain mode a hole missing from the map falls through to the
        // sequential path, which reports the error at the right step.
        let final_results = self.config.hole_isolate
            || self.config.hole_check_only
            || self.config.hole_deadline.is_some();
        let check_only = self.config.hole_check_only;
        let (mut total, mut done, mut kept, mut skipped) = (0usize, 0usize, 0usize, 0usize);

        let result = proof.mutate(|_, node, _| match node.as_ref() {
            ProofNode::Step(s) if rare_holes && rare_hole::is_theory_rewrite_hole(s) => {
                total += 1;
                match reconstructed.remove(&s.id) {
                    // Checking only: egglog's verdict is recorded and the hole
                    // stays as it was.
                    Some((Ok(_), elapsed)) if check_only => {
                        done += 1;
                        log::info!("hole {}: proved in {:.3}s", s.id, elapsed.as_secs_f64());
                        Ok(node.clone())
                    }
                    // Final results make the pass best-effort for the whole
                    // hole: a child that fails, and a reconstruction the
                    // checker then rejects, both leave the hole as it was, so
                    // one bad hole cannot cost the rest of the proof.
                    Some((Ok(steps), elapsed)) if final_results => {
                        let checking = Instant::now();
                        match rare_hole::insert_steps(self, s, steps) {
                            Ok(inserted) => {
                                done += 1;
                                log::info!(
                                    "hole {}: justified in {:.3}s (check {:.3}s)",
                                    s.id,
                                    elapsed.as_secs_f64(),
                                    checking.elapsed().as_secs_f64()
                                );
                                Ok(inserted)
                            }
                            Err(error) => {
                                kept += 1;
                                log::warn!("hole {}: kept as trusted: {error}", s.id);
                                Ok(node.clone())
                            }
                        }
                    }
                    Some((Ok(steps), _)) => {
                        rare_hole::insert_steps(self, s, steps).map_err(|e| e.at(s))
                    }
                    Some((Err(reason), _)) if final_results => {
                        if reason.starts_with("skipped") {
                            skipped += 1;
                            log::info!("hole {}: {reason}", s.id);
                        } else {
                            kept += 1;
                            log::warn!("hole {}: kept as trusted: {reason}", s.id);
                        }
                        Ok(node.clone())
                    }
                    Some((Err(_), _)) | None => {
                        rare_hole::elaborate(self, node, s).map_err(|e| e.at(s))
                    }
                }
            }
            ProofNode::Step(s)
                if self.config.hole_solver.is_some()
                    && (s.rule == "all_simplify" || s.rule == "rare_rewrite") =>
            {
                hole::hole(self, s).map_err(|e| e.at(s))
            }
            ProofNode::Step(s) if self.config.lia_solver.is_some() && s.rule == "lia_generic" => {
                hole::lia_generic(self, s).map_err(|e| e.at(s))
            }
            _ => Ok(node.clone()),
        });
        if prepass {
            log::info!(
                "hole summary: total={total} {}={done} kept={kept} skipped={skipped} time={:.3}s",
                if check_only { "proved" } else { "justified" },
                prepass_time.as_secs_f64()
            );
        }
        result
    }

    fn elaborate_local(
        &mut self,
        proof: ProofNodeForest,
    ) -> Result<ProofNodeForest, ElaborationErrorAtStep> {
        fn get_elaboration_function(rule: &str) -> Option<ElaborationFunc> {
            Some(match rule {
                "eq_transitive" => local::transitivity::eq_transitive,
                "trans" => local::transitivity::trans,
                "resolution" | "th_resolution" => local::resolution::resolution,
                "cong" => local::congruence::cong,
                "eq_congruent" => local::congruence::eq_congruent,
                "eq_congruent_pred" => local::congruence::eq_congruent_pred,
                "bounded_farkas" => local::farkas::bounded_farkas,
                "eq_mp" => local::eq_mp::eq_mp,
                _ => return None,
            })
        }

        proof.mutate(|context, node, _| {
            match node.as_ref() {
                ProofNode::Step(s) => {
                    if let Some(func) = get_elaboration_function(&s.rule) {
                        return func(self.pool, context, s).map_err(|e| e.at(s));
                    }
                }
                ProofNode::Subproof(_) => unreachable!(),
                ProofNode::Assume { .. } => (),
            }
            Ok(node.clone())
        })
    }

    fn elaborate_assume(&mut self, id: &str, depth: usize, term: &Rc<Term>) -> Rc<ProofNode> {
        let mut found = None;
        for p in &self.problem.premises {
            if Polyeq::new()
                .mod_reordering(true)
                .mod_nary(true)
                .eq(term, p)
            {
                found = Some(p.clone());
                break;
            }
        }
        let premise = found.expect("trying to elaborate assume, but it is invalid!");

        let new_assume = Rc::new(ProofNode::Assume {
            id: id.to_owned(),
            depth,
            term: premise.clone(),
        });

        let mut ids = IdHelper::new(id);
        let equality_step = PolyeqElaborator::new(&mut ids, depth, false).elaborate(
            self.pool,
            premise.clone(),
            term.clone(),
        );

        let equiv1_step = Rc::new(ProofNode::Step(StepNode {
            id: ids.next_id(),
            depth,
            clause: vec![
                build_term!(self.pool, (not {premise.clone()})),
                term.clone(),
            ],
            rule: "equiv1".to_owned(),
            premises: vec![equality_step],
            ..Default::default()
        }));

        Rc::new(ProofNode::Step(StepNode {
            id: ids.next_id(),
            depth,
            clause: vec![term.clone()],
            rule: "resolution".to_owned(),
            premises: vec![new_assume, equiv1_step],
            args: vec![premise, self.pool.bool_true()],
            ..Default::default()
        }))
    }
}

fn add_refl_step(
    pool: &mut dyn TermPool,
    a: Rc<Term>,
    b: Rc<Term>,
    id: String,
    depth: usize,
) -> Rc<ProofNode> {
    Rc::new(ProofNode::Step(StepNode {
        id,
        depth,
        clause: vec![build_term!(pool, (= {a} {b}))],
        rule: "refl".to_owned(),
        premises: Vec::new(),
        args: Vec::new(),
        discharge: Vec::new(),
        previous_step: None,
    }))
}

fn add_symm_step(pool: &mut PrimitivePool, node: &Rc<ProofNode>, id: String) -> Rc<ProofNode> {
    assert_eq!(node.clause().len(), 1);
    let (a, b) = match_term!((= a b) = node.clause()[0]).unwrap();
    let clause = vec![build_term!(pool, (= {b.clone()} {a.clone()}))];
    Rc::new(ProofNode::Step(StepNode {
        id,
        depth: node.depth(),
        clause,
        rule: "symm".into(),
        premises: vec![node.clone()],
        args: Vec::new(),
        discharge: Vec::new(),
        previous_step: None,
    }))
}

fn add_trans_step(
    pool: &mut PrimitivePool,
    nodes: impl IntoIterator<Item = Rc<ProofNode>>,
    id: String,
) -> Rc<ProofNode> {
    let premises: Vec<_> = nodes.into_iter().collect();
    let depth = premises.first().unwrap().depth();
    let (a, _) =
        match_term!((= a b) = premises.first().unwrap().clause().first().unwrap()).unwrap();
    let (_, b) = match_term!((= a b) = premises.last().unwrap().clause().first().unwrap()).unwrap();
    Rc::new(ProofNode::Step(StepNode {
        id,
        depth,
        clause: vec![build_term!(pool, (= {a.clone()} {b.clone()}))],
        rule: "trans".to_owned(),
        premises,
        ..StepNode::default()
    }))
}

type ElaborationFunc =
    fn(&mut PrimitivePool, &mut ContextStack, &StepNode) -> Result<Rc<ProofNode>, ElaborationError>;

/// A proof that can be mutated by applying a function to each of its nodes.
///
/// The function is applied to the nodes in a bottom-up order, so that the premises of a step are
/// always processed before the step itself. Shared nodes are only processed once.
pub trait Mutate: Sized {
    /// Applies `mutate_func` to every node of the proof, returning the new proof.
    ///
    /// `mutate_func` receives the current context, the node, and whether the node's premises were
    /// modified, and returns the new node.
    fn mutate<F, E>(self, mutate_func: F) -> Result<Self, E>
    where
        F: FnMut(&mut ContextStack, &Rc<ProofNode>, bool) -> Result<Rc<ProofNode>, E>;
}

impl Mutate for ProofNodeForest {
    fn mutate<F, E>(self, mut mutate_func: F) -> Result<Self, E>
    where
        F: FnMut(&mut ContextStack, &Rc<ProofNode>, bool) -> Result<Rc<ProofNode>, E>,
    {
        let mut cache = HashMap::new();
        self.0
            .into_iter()
            .map(|node| mutate_impl(&node, &mut cache, &mut mutate_func))
            .collect::<Result<Vec<_>, E>>()
            .map(ProofNodeForest)
    }
}

impl Mutate for Rc<ProofNode> {
    fn mutate<F, E>(self, mutate_func: F) -> Result<Self, E>
    where
        F: FnMut(&mut ContextStack, &Rc<ProofNode>, bool) -> Result<Rc<ProofNode>, E>,
    {
        let mut cache = HashMap::new();
        mutate_impl(&self, &mut cache, mutate_func)
    }
}

fn mutate_impl<F, E>(
    root: &Rc<ProofNode>,
    cache: &mut HashMap<Rc<ProofNode>, Rc<ProofNode>>,
    mut mutate_func: F,
) -> Result<Rc<ProofNode>, E>
where
    F: FnMut(&mut ContextStack, &Rc<ProofNode>, bool) -> Result<Rc<ProofNode>, E>,
{
    let mut did_outbound: HashSet<&Rc<ProofNode>> = HashSet::new();
    let mut todo = vec![(root, false)];

    let mut outbound_premises_stack = vec![IndexSet::new()];
    let mut context = ContextStack::new();

    while let Some((node, is_done)) = todo.pop() {
        if cache.contains_key(node) {
            continue;
        }

        let mutated = match node.as_ref() {
            ProofNode::Assume { .. } => mutate_func(&mut context, node, false)?,
            ProofNode::Step(s) if !is_done => {
                todo.push((node, true));

                let all_premises = s
                    .premises
                    .iter()
                    .chain(&s.discharge)
                    .chain(&s.previous_step)
                    .rev();
                todo.extend(
                    all_premises.filter_map(|p| (!cache.contains_key(p)).then_some((p, false))),
                );

                continue;
            }
            ProofNode::Step(s) => {
                let premises: Vec<_> = s.premises.iter().map(|p| cache[p].clone()).collect();
                let discharge: Vec<_> = s.discharge.iter().map(|p| cache[p].clone()).collect();
                let previous_step = s.previous_step.as_ref().map(|p| cache[p].clone());
                let changed = s
                    .premises
                    .iter()
                    .chain(s.discharge.iter())
                    .chain(s.previous_step.iter())
                    .any(|p| *p != cache[p]);

                let new_node = Rc::new(ProofNode::Step(StepNode {
                    premises,
                    discharge,
                    previous_step,
                    ..s.clone()
                }));
                mutate_func(&mut context, &new_node, changed)?
            }
            ProofNode::Subproof(s) if !is_done => {
                assert!(
                    node.depth() == outbound_premises_stack.len() - 1,
                    "all outbound premises should have already been dealt with!"
                );

                if !did_outbound.contains(node) {
                    did_outbound.insert(node);
                    todo.push((node, false));
                    todo.extend(s.outbound_premises.iter().map(|premise| (premise, false)));
                    continue;
                }

                todo.push((node, true));
                todo.push((&s.last_step, false));
                todo.extend(s.extra_steps.iter().rev().map(|node| (node, false)));
                outbound_premises_stack.push(IndexSet::new());
                context.push(&s.args);
                continue;
            }
            ProofNode::Subproof(s) => {
                context.pop();
                let outbound_premises =
                    outbound_premises_stack.pop().unwrap().into_iter().collect();
                let extra_steps = s
                    .extra_steps
                    .iter()
                    .map(|node| cache[node].clone())
                    .collect();
                Rc::new(ProofNode::Subproof(SubproofNode {
                    last_step: cache[&s.last_step].clone(),
                    args: s.args.clone(),
                    outbound_premises,
                    extra_steps,
                }))
            }
        };
        outbound_premises_stack
            .last_mut()
            .unwrap()
            .extend(mutated.get_outbound_premises());
        cache.insert(node.clone(), mutated);
    }
    assert!(outbound_premises_stack.len() == 1 && outbound_premises_stack[0].is_empty());
    Ok(cache[root].clone())
}

/// A helper for generating unique step IDs from a root ID, by appending numeric suffixes to it.
pub struct IdHelper {
    root: String,
    stack: Vec<usize>,
}

impl IdHelper {
    /// Constructs a new [`IdHelper`] for the given root ID.
    pub fn new(root: &str) -> Self {
        Self {
            root: root.to_owned(),
            stack: vec![0],
        }
    }

    /// Returns the next generated ID, and advances the internal counter.
    pub fn next_id(&mut self) -> String {
        use std::fmt::Write;

        let mut current = self.root.clone();
        for i in &self.stack {
            write!(&mut current, ".t{}", i + 1).unwrap();
        }
        *self.stack.last_mut().unwrap() += 1;
        current
    }

    /// Starts a new nesting level.
    ///
    /// That is, if the current ID is `t5.t3`, `push` will use that as the root for the next ids,
    /// such that the following ID will be `t5.t3.t1`. This is reverted by [`IdHelper::pop`].
    pub fn push(&mut self) {
        self.stack.push(0);
    }

    /// Ends the current nesting level.
    pub fn pop(&mut self) {
        assert!(self.stack.len() >= 2, "can't pop last frame from the stack");
        self.stack.pop();
    }
}


/// The number of nodes of a term, walking through applications only.
fn term_node_count(term: &Rc<Term>) -> usize {
    match term.as_ref() {
        Term::Op(_, args) => 1 + args.iter().map(term_node_count).sum::<usize>(),
        Term::App(function, args) => {
            1 + term_node_count(function) + args.iter().map(term_node_count).sum::<usize>()
        }
        _ => 1,
    }
}
