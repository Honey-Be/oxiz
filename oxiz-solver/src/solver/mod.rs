//! Main CDCL(T) SMT Solver module

pub(super) mod check_array;
pub(super) mod check_bv;
pub(super) mod check_dt;
pub(super) mod check_fp;
pub(super) mod check_nlsat;
pub(super) mod check_string;
pub(super) mod config;
pub(super) mod encode;
pub(super) mod fd_propagator;
pub(super) mod model_builder;
pub(super) mod theory_manager;
pub(super) mod trail;
pub(super) mod types;

pub use types::{
    FpConstraintData, Model, NamedAssertion, OutputMode, Proof, ProofStep, SatLevel, SolverConfig,
    SolverResult, Statistics, TheoryMode, UnsatCore,
};

use crate::clean_mbqi::{EufCongruence, OxizHost, OxizSig, SolverModel};
#[allow(unused_imports)]
use crate::prelude::*;
use oxiz_mbqi::{Config as CleanConfig, Engine as CleanEngine, Verdict as CleanVerdict};
use crate::simplify::Simplifier;
use oxiz_core::ast::{TermId, TermKind, TermManager};
#[cfg(test)]
use oxiz_sat::RestartStrategy;
use oxiz_sat::{
    Solver as SatSolver, SolverConfig as SatConfig, SolverResult as SatResult, Var,
};
use oxiz_theories::Theory;
use oxiz_theories::arithmetic::ArithSolver;
use oxiz_theories::bv::BvSolver;
use oxiz_theories::euf::EufSolver;

use theory_manager::{TheoryManager, TheoryParts};
use trail::{ContextState, TrailOp};
use types::{Constraint, ParsedArithConstraint, Polarity};

/// Replace every quantifier node reachable through the boolean spine of `t` with
/// a FRESH Bool proposition — memoized per quantifier `TermId` in `map`, so the
/// same quantifier maps to the SAME proposition across every call. Ground/theory
/// atoms (and anything that is not a boolean connective) are returned verbatim —
/// a quantifier is `Bool`-sorted, so it can only sit under a boolean connective.
///
/// Used by [`Solver::fresh_ground_resolve`] (#347): abstracting a quantifier `Q`
/// to a free Bool `p_Q` shared between the original assertions and the guarded
/// instances `Q ⇒ φ` preserves each instance's guard in the single-shot
/// verifier, so a guarded `Q ⇒ ⊥` collapses to `¬p_Q` (sound `Sat`) instead of
/// asserting `⊥` unconditionally (the old spurious `unsat`). Sound because a free
/// Bool over-approximates the quantifier's truth value (`abstract-unsat ⇒
/// real-unsat`).
fn abstract_quants(
    manager: &mut TermManager,
    t: TermId,
    map: &mut FxHashMap<TermId, TermId>,
) -> TermId {
    let Some(kind) = manager.get(t).map(|x| x.kind.clone()) else {
        return t;
    };
    match kind {
        TermKind::Forall { .. } | TermKind::Exists { .. } => {
            if let Some(&v) = map.get(&t) {
                return v;
            }
            let bool_sort = manager.sorts.bool_sort;
            // `!` cannot start an SMT-LIB simple symbol, so this never collides
            // with a user-declared constant.
            let name = format!("!mbqi-qabs!{}", map.len());
            let v = manager.mk_var(&name, bool_sort);
            map.insert(t, v);
            v
        }
        TermKind::Not(a) => {
            let a2 = abstract_quants(manager, a, map);
            manager.mk_not(a2)
        }
        TermKind::And(args) => {
            let v: Vec<TermId> = args.iter().map(|&a| abstract_quants(manager, a, map)).collect();
            manager.mk_and(v)
        }
        TermKind::Or(args) => {
            let v: Vec<TermId> = args.iter().map(|&a| abstract_quants(manager, a, map)).collect();
            manager.mk_or(v)
        }
        TermKind::Implies(a, b) => {
            let a2 = abstract_quants(manager, a, map);
            let b2 = abstract_quants(manager, b, map);
            manager.mk_implies(a2, b2)
        }
        TermKind::Xor(a, b) => {
            let a2 = abstract_quants(manager, a, map);
            let b2 = abstract_quants(manager, b, map);
            manager.mk_xor(a2, b2)
        }
        TermKind::Ite(c, a, b) => {
            let c2 = abstract_quants(manager, c, map);
            let a2 = abstract_quants(manager, a, map);
            let b2 = abstract_quants(manager, b, map);
            manager.mk_ite(c2, a2, b2)
        }
        TermKind::Eq(a, b) => {
            // A `Bool`-sorted `=` (iff) may carry a quantifier → recurse. An
            // arith/UF `=` has no quantifier operand, so both recursions are the
            // identity and this rebuilds the same hash-consed term.
            let a2 = abstract_quants(manager, a, map);
            let b2 = abstract_quants(manager, b, map);
            manager.mk_eq(a2, b2)
        }
        _ => t,
    }
}

/// Default wall-clock budget (milliseconds) for the MBQI quantifier-
/// instantiation loop when no explicit `timeout_ms` is configured.  A pure
/// non-termination guard: quantifier reasoning over an infinite domain is
/// semi-decidable, so without it a genuinely-SAT `forall`-with-trigger axiom
/// can spin forever.  On expiry the loop returns the sound `Unknown`.
#[cfg(feature = "std")]
const MBQI_NONTERMINATION_GUARD_MS: u64 = 3_000;

/// Main CDCL(T) SMT Solver
#[derive(Debug)]
pub struct Solver {
    /// Configuration
    pub(super) config: SolverConfig,
    /// SAT solver core
    pub(super) sat: SatSolver,
    /// EUF theory solver
    pub(super) euf: EufSolver,
    /// Arithmetic theory solver
    pub(super) arith: ArithSolver,
    /// Bitvector theory solver
    pub(super) bv: BvSolver,
    /// NLSAT solver for nonlinear arithmetic (QF_NIA/QF_NRA)
    #[cfg(feature = "std")]
    pub(super) nlsat: Option<oxiz_theories::nlsat::NlsatTheory>,
    /// Whether the formula contains quantifiers
    pub(super) has_quantifiers: bool,
    /// Term to SAT variable mapping
    pub(super) term_to_var: FxHashMap<TermId, Var>,
    /// SAT variable to term mapping
    pub(super) var_to_term: Vec<TermId>,
    /// SAT variable to theory constraint mapping
    pub(super) var_to_constraint: FxHashMap<Var, Constraint>,
    /// SAT variable to parsed arithmetic constraint mapping
    pub(super) var_to_parsed_arith: FxHashMap<Var, ParsedArithConstraint>,
    /// Current logic
    pub(super) logic: Option<String>,
    /// Assertions
    pub(super) assertions: Vec<TermId>,
    /// Named assertions for unsat core tracking
    pub(super) named_assertions: Vec<NamedAssertion>,
    /// Assumption literals for unsat core tracking (maps assertion index to assumption var)
    /// Reserved for future use with assumption-based unsat core extraction
    #[allow(dead_code)]
    pub(super) assumption_vars: FxHashMap<u32, Var>,
    /// Model (if sat)
    pub(super) model: Option<Model>,
    /// Unsat core (if unsat)
    pub(super) unsat_core: Option<UnsatCore>,
    /// Context stack for push/pop
    pub(super) context_stack: Vec<ContextState>,
    /// Trail of operations for efficient undo
    pub(super) trail: Vec<TrailOp>,
    /// Tracking which literals have been processed by theories
    pub(super) theory_processed_up_to: usize,
    /// Whether to produce unsat cores
    pub(super) produce_unsat_cores: bool,
    /// Track if we've asserted False (for immediate unsat)
    pub(super) has_false_assertion: bool,
    /// Polarity tracking for optimization
    pub(super) polarities: FxHashMap<TermId, Polarity>,
    /// Whether polarity-aware encoding is enabled
    pub(super) polarity_aware: bool,
    /// Whether theory-aware branching is enabled
    pub(super) theory_aware_branching: bool,
    /// Proof of unsatisfiability (if proof generation is enabled)
    pub(super) proof: Option<Proof>,
    /// Formula simplifier
    pub(super) simplifier: Simplifier,
    /// Solver statistics
    pub(super) statistics: Statistics,
    /// Bitvector terms (for model extraction)
    pub(super) bv_terms: FxHashSet<TermId>,
    /// Whether we've seen arithmetic BV operations (division/remainder)
    /// Used to decide when to run eager BV checking
    pub(super) has_bv_arith_ops: bool,
    /// Arithmetic terms (Int/Real variables for model extraction)
    pub(super) arith_terms: FxHashSet<TermId>,
    /// Datatype constructor constraints: variable -> constructor name
    /// Used to detect mutual exclusivity conflicts (var = C1 AND var = C2 where C1 != C2)
    pub(super) dt_var_constructors: FxHashMap<TermId, oxiz_core::interner::Spur>,
    /// Datatype-sorted subterms whose ground constructor-cover axiom
    /// `(or (= t (C₁ sels(t))) …)` has been encoded into the SAT core
    /// (see `add_dt_cover_axioms`). Entries are trail-undone on `pop()` —
    /// the cover CLAUSE dies with the SAT level, so a re-assert of the same
    /// term in a later scope must re-emit it.
    pub(super) dt_cover_done: FxHashSet<TermId>,
    /// Monotone counter naming the fresh constants of the ground term-ite
    /// elimination (`eliminate_term_ites`). Never decremented — a popped
    /// definition must never have its name reused by a later scope.
    pub(super) term_ite_counter: usize,
    /// Cache for parsed arithmetic constraints, keyed by the comparison term id.
    /// `ParsedArithConstraint` is purely structural (depends only on the term graph),
    /// so it is safe to reuse across CDCL backtracks.
    pub(super) arith_parse_cache: FxHashMap<TermId, Option<ParsedArithConstraint>>,
    /// Set of compound term ids whose theory-variable sub-graph has been fully
    /// traversed by `track_theory_vars`.  Avoids redundant O(depth) re-walks
    /// when the same sub-expression appears in multiple parent constraints.
    pub(super) tracked_compound_terms: FxHashSet<TermId>,
    /// Cache for FP constraint checking results.
    pub(super) fp_constraint_cache: FxHashMap<TermId, FpConstraintData>,
}

impl Default for Solver {
    fn default() -> Self {
        Self::new()
    }
}

impl Solver {
    /// Create a new solver
    #[must_use]
    pub fn new() -> Self {
        Self::with_config(SolverConfig::default())
    }

    /// Create a new solver with configuration
    #[must_use]
    pub fn with_config(config: SolverConfig) -> Self {
        let proof_enabled = config.proof;

        // Build SAT solver configuration from our config
        let sat_config = SatConfig {
            restart_strategy: config.restart_strategy,
            enable_inprocessing: config.enable_inprocessing,
            inprocessing_interval: config.inprocessing_interval,
            ..SatConfig::default()
        };

        // Note: The following features are controlled by the SAT solver's preprocessor
        // and clause management systems. We pass the configuration but the actual
        // implementation is in oxiz-sat:
        // - Clause minimization (via RecursiveMinimizer)
        // - Clause subsumption (via SubsumptionChecker)
        // - Variable elimination (via Preprocessor::variable_elimination)
        // - Blocked clause elimination (via Preprocessor::blocked_clause_elimination)
        // - Symmetry breaking (via SymmetryBreaker)

        Self {
            config,
            sat: SatSolver::with_config(sat_config),
            euf: EufSolver::new(),
            arith: ArithSolver::lra(),
            bv: BvSolver::new(),
            #[cfg(feature = "std")]
            nlsat: None,
            has_quantifiers: false,
            term_to_var: FxHashMap::default(),
            var_to_term: Vec::new(),
            var_to_constraint: FxHashMap::default(),
            var_to_parsed_arith: FxHashMap::default(),
            logic: None,
            assertions: Vec::new(),
            named_assertions: Vec::new(),
            assumption_vars: FxHashMap::default(),
            model: None,
            unsat_core: None,
            context_stack: Vec::new(),
            trail: Vec::new(),
            theory_processed_up_to: 0,
            produce_unsat_cores: false,
            has_false_assertion: false,
            polarities: FxHashMap::default(),
            polarity_aware: true, // Enable polarity-aware encoding by default
            theory_aware_branching: true, // Enable theory-aware branching by default
            proof: if proof_enabled {
                Some(Proof::new())
            } else {
                None
            },
            simplifier: Simplifier::new(),
            statistics: Statistics::new(),
            bv_terms: FxHashSet::default(),
            has_bv_arith_ops: false,
            arith_terms: FxHashSet::default(),
            dt_var_constructors: FxHashMap::default(),
            dt_cover_done: FxHashSet::default(),
            term_ite_counter: 0,
            arith_parse_cache: FxHashMap::default(),
            tracked_compound_terms: FxHashSet::default(),
            fp_constraint_cache: FxHashMap::default(),
        }
    }

    /// Get the proof (if proof generation is enabled and the result is unsat)
    #[must_use]
    pub fn get_proof(&self) -> Option<&Proof> {
        self.proof.as_ref()
    }

    /// Get the solver statistics
    #[must_use]
    pub fn get_statistics(&self) -> &Statistics {
        &self.statistics
    }

    /// Reset the solver statistics
    pub fn reset_statistics(&mut self) {
        self.statistics.reset();
    }

    /// Enable or disable theory-aware branching
    pub fn set_theory_aware_branching(&mut self, enabled: bool) {
        self.theory_aware_branching = enabled;
    }

    /// Check if theory-aware branching is enabled
    #[must_use]
    pub fn theory_aware_branching(&self) -> bool {
        self.theory_aware_branching
    }

    /// Enable or disable unsat core production
    pub fn set_produce_unsat_cores(&mut self, produce: bool) {
        self.produce_unsat_cores = produce;
    }

    /// Snapshot the current model as the oracle the clean engine consults for
    /// CDQI / relevance-gating. Holds a CLONE of the `term → value`
    /// assignments (so it does not alias the manager the host borrows mutably)
    /// plus the interned `true`/`false` ids. Conservative everywhere — a wrong
    /// answer can only cost completeness, never soundness.
    fn build_clean_model(&self, manager: &TermManager) -> SolverModel {
        let assign = self
            .model
            .as_ref()
            .map(|m| m.assignments().clone())
            .unwrap_or_default();
        let model = SolverModel::new(assign, manager.mk_true(), manager.mk_false());
        // Attach the global model-completion facts only when there are
        // quantifiers (the M3 recognizers in `eval_forall` need them; for a
        // quantifier-free problem they would never fire). Cheap: one linear
        // walk of the asserted formula.
        if self.has_quantifiers {
            model.with_completion_facts(manager, &self.assertions)
        } else {
            model
        }
    }

    /// Confirm a clean-engine `unsat` with a SINGLE-SHOT ground solve.
    ///
    /// OxiZ's INCREMENTAL CDCL(T) can report a spurious `unsat` after the clean
    /// engine adds instance lemmas across MBQI rounds (the same clause set
    /// solved fresh is sound). The engine's instances are sound GROUND
    /// consequences of the asserted quantifiers, so we re-solve
    /// `{non-quantifier assertions} ∪ {ground instances}` in a FRESH solver
    /// that instantiates nothing (clean off, no quantifiers asserted): a
    /// confirmed `unsat` is real (it follows from sound consequences); anything
    /// else means the incremental `unsat` was spurious, and the sound verdict
    /// is `Unknown` (never a fabricated `unsat`).
    ///
    /// SCOPE: this only catches an INCREMENTAL/single-shot DIVERGENCE — it
    /// trusts the single-shot ground solve. If OxiZ's *ground* EUF/arith solver
    /// is itself unsound on a particular instance set (a separate, deeper bug
    /// the clean engine can also expose), this verification confirms the
    /// spurious `unsat`. A fully sound clean engine requires a sound host
    /// ground core; closing the remaining ground-solver soundness gaps is a
    /// follow-up.
    fn verify_clean_unsat(
        &mut self,
        instances: &[TermId],
        manager: &mut TermManager,
    ) -> SolverResult {
        match self.fresh_ground_resolve(instances, manager) {
            SolverResult::Unsat => {
                self.build_unsat_core();
                SolverResult::Unsat
            }
            // Not confirmed by a sound ground solve ⇒ the incremental `unsat`
            // was spurious; report the sound `Unknown`.
            _ => SolverResult::Unknown,
        }
    }

    /// Confirm a clean-engine `Saturated` (→ `sat`) with the same SINGLE-SHOT
    /// ground re-solve — the DUAL of [`Self::verify_clean_unsat`].
    ///
    /// The incremental CDCL(T) can also MISS a conflict GLOBAL across the
    /// emitted instances (e.g. pigeonhole), so a bounded quantifier's
    /// `Saturated` does not by itself justify `Sat`. A bounded quantifier is
    /// FULLY captured by its emitted instances (a `∀`'s box conjunction / a
    /// `∃`'s box disjunction), so re-solving `{ground assertions ∪ instances}`
    /// in a FRESH solver gives the true verdict: a fresh `unsat` is a real
    /// `unsat` (the instances are sound ground consequences); a fresh `sat` is a
    /// genuine model (sound `Sat`); anything else is the sound `Unknown`.
    fn verify_clean_saturated(
        &mut self,
        instances: &[TermId],
        manager: &mut TermManager,
    ) -> SolverResult {
        match self.fresh_ground_resolve(instances, manager) {
            SolverResult::Unsat => {
                self.build_unsat_core();
                SolverResult::Unsat
            }
            SolverResult::Sat => {
                self.unsat_core = None;
                SolverResult::Sat
            }
            SolverResult::Unknown => SolverResult::Unknown,
        }
    }

    /// Re-solve `{non-quantifier assertions ∪ ground instances}` in a FRESH,
    /// single-shot solver that instantiates nothing. Shared by both clean-engine
    /// verifications.
    ///
    /// CRUCIAL: the fresh solver must carry the LOGIC. `logic` is a `Solver`
    /// field, NOT part of `SolverConfig`, so `with_config(self.config.clone())`
    /// would leave it `None` — and a logic-less solve does not enable the right
    /// theory wiring (it misses the EUF↔LIA combination that refutes
    /// pigeonhole), so an unsat re-solve would spuriously come back `sat`/
    /// `unknown`. `set_logic` both records the logic and runs its theory setup.
    fn fresh_ground_resolve(
        &self,
        instances: &[TermId],
        manager: &mut TermManager,
    ) -> SolverResult {
        let mut config = self.config.clone();
        config.clean_mbqi = false;
        let mut verifier = Solver::with_config(config);
        verifier.set_logic(self.logic.as_deref().unwrap_or("ALL"));
        // #347 — abstract every quantifier node (top-level OR nested in the
        // boolean spine) to a FRESH Bool proposition, the SAME proposition per
        // quantifier `TermId` shared across the re-asserted original assertions
        // AND the guarded instances. This preserves each instance's guard:
        //   - the original `(=> g Q)` ⤳ `(=> g p_Q)`,
        //   - the guarded instance `(=> Q φ)` ⤳ `(=> p_Q φ)`,
        // so a `(=> p_Q ⊥)` collapses to `¬p_Q` and `(or ¬g p_Q)` yields `¬g`
        // → the sound `Sat` (the old code dropped the guard — asserting the
        // instance body `φ` unconditionally AND skipping the quantifiers — so a
        // guarded `Q ⇒ ⊥` became an unconditional `⊥` → spurious unsat).
        // The abstraction is an OVER-approximation (a free Bool admits ≥ the
        // quantifier's models), so `abstract-unsat ⇒ real-unsat`: a top-level
        // forall is asserted (`p_Q` true) and a genuine cross-instance conflict
        // (pigeonhole) still resolves `Unsat`. (For quantifiers under boolean
        // shapes the abstraction does not descend, the raw quantifier survives
        // and the verifier reports the sound `Unknown`.)
        let mut qabs: FxHashMap<TermId, TermId> = FxHashMap::default();
        let assertions = self.assertions.clone();
        for a in assertions {
            let aa = abstract_quants(manager, a, &mut qabs);
            verifier.assert(aa, manager);
        }
        for &inst in instances {
            let ia = abstract_quants(manager, inst, &mut qabs);
            verifier.assert(ia, manager);
        }
        verifier.check(manager)
    }

    /// Move this solver's persistent theory state — the EUF/arith/BV solvers,
    /// the statistics, the read-only atom maps — together with the real
    /// `TermManager` into an OWNING [`TheoryManager`] for the span of one solve.
    ///
    /// §4 redesign (Phase 2): the theory manager used to BORROW all of this; it
    /// now owns it (no lifetime ⇒ it fits the `'static` lock-step hooks driver).
    /// The maps are read-only during a solve so the relocation is a set of O(1)
    /// `mem::take`s (a throwaway `TermManager::default()` is parked in `*manager`
    /// for the duration). [`restore_theory_manager`] is the exact inverse, run
    /// immediately after the solve, so observable behaviour is identical to the
    /// old borrowing manager — and the per-iteration take/restore reproduces the
    /// old "recreate the theory manager each MBQI round" semantics (the scratch
    /// state is reinitialised every round; only euf/arith/bv persist).
    fn take_theory_manager(&mut self, manager: &mut TermManager) -> TheoryManager {
        let parts = TheoryParts {
            manager: core::mem::take(manager),
            euf: core::mem::take(&mut self.euf),
            arith: core::mem::take(&mut self.arith),
            bv: core::mem::take(&mut self.bv),
            bv_terms: core::mem::take(&mut self.bv_terms),
            var_to_constraint: core::mem::take(&mut self.var_to_constraint),
            var_to_parsed_arith: core::mem::take(&mut self.var_to_parsed_arith),
            term_to_var: core::mem::take(&mut self.term_to_var),
            var_to_term: core::mem::take(&mut self.var_to_term),
            statistics: core::mem::take(&mut self.statistics),
        };
        TheoryManager::new(
            parts,
            self.config.theory_mode,
            self.config.max_conflicts,
            self.config.max_decisions,
            self.has_bv_arith_ops,
            // Stale-bound suppression stays ON for BOTH drivers. 369a3a8
            // retired it on the hooks path claiming a lock-step frame makes a
            // stale bound unrepresentable — but verus-fork's trigger-F family
            // (a `height_lt`/arith interaction) still leaves a retracted atom
            // asserting a simplex bound on the hooks path, so the claim has a
            // hole. The guard is sound regardless of driver (it suppresses only
            // a conflict with <2 distinct atom terms — provably no real reason),
            // so always-on restores soundness without risking a spurious sat.
            true,
        )
    }

    /// Reinstall the persistent theory state (and the real `TermManager`) after
    /// a solve, dropping the per-solve scratch. Inverse of
    /// [`take_theory_manager`].
    fn restore_theory_manager(&mut self, manager: &mut TermManager, tm: TheoryManager) {
        let parts = tm.into_parts();
        *manager = parts.manager;
        self.euf = parts.euf;
        self.arith = parts.arith;
        self.bv = parts.bv;
        self.bv_terms = parts.bv_terms;
        self.var_to_constraint = parts.var_to_constraint;
        self.var_to_parsed_arith = parts.var_to_parsed_arith;
        self.term_to_var = parts.term_to_var;
        self.var_to_term = parts.var_to_term;
        self.statistics = parts.statistics;
    }

    /// Get a SAT variable for a term, then check satisfiability — the
    /// **z3-compatible** 3-valued verdict. This collapses the internal
    /// [`SatLevel`] lattice at this single boundary; use [`check_level`] to read
    /// the un-collapsed 5-level verdict (the "full" output mode).
    ///
    /// [`check_level`]: Solver::check_level
    pub fn check(&mut self, manager: &mut TermManager) -> SolverResult {
        self.check_level(manager).collapse()
    }

    /// Check satisfiability, returning the full internal [`SatLevel`] verdict
    /// WITHOUT collapsing to 3 values. Every engine keeps its confirmed/
    /// unconfirmed grade all the way to this one boundary, so the lattice is
    /// reduced to `sat`/`unsat`/`unknown` only by the caller — [`check`] in
    /// z3-compatible mode, or not at all in "full" output mode.
    ///
    /// [`check`]: Solver::check
    pub fn check_level(&mut self, manager: &mut TermManager) -> SatLevel {
        // Check for trivial unsat (false assertion)
        if self.has_false_assertion {
            self.build_unsat_core_trivial_false();
            return SatLevel::DefiniteUnsat;
        }

        if self.assertions.is_empty() {
            return SatLevel::DefiniteSat;
        }

        // Check string constraints for early conflict detection
        if self.check_string_constraints(manager) {
            return SatLevel::DefiniteUnsat;
        }

        // Check floating-point constraints for early conflict detection
        if self.check_fp_constraints(manager) {
            return SatLevel::DefiniteUnsat;
        }

        // Check datatype constraints for early conflict detection
        if self.check_dt_constraints(manager) {
            return SatLevel::DefiniteUnsat;
        }

        // Check array constraints for early conflict detection
        if self.check_array_constraints(manager) {
            return SatLevel::DefiniteUnsat;
        }

        // Check bitvector constraints for early conflict detection
        if self.check_bv_constraints(manager) {
            return SatLevel::DefiniteUnsat;
        }

        // Trichotomy / total-order: a single term pinned to mutually-infeasible
        // literal bounds (`t > c ∧ t < c`, disjoint intervals, conflicting
        // equalities) is UNSAT regardless of what the term denotes — sound even
        // for an opaque NONLINEAR product whose bounds the CDCL(T) relaxation
        // would otherwise miss (e.g. `x*y > 0 ∧ x*y < 0`).
        if self.check_term_bound_infeasible(manager) {
            return SatLevel::DefiniteUnsat;
        }

        // For NIA/NRA logics: dispatch all assertions to the full polynomial
        // solver first (NiaSolver or NlsatSolver). This gives a definitive
        // SAT/UNSAT for most benchmark problems without the CDCL(T) loop.
        let nl_dispatch = self.dispatch_nl_solver(manager);
        if let Some(nl_result) = nl_dispatch {
            match nl_result {
                // The nonlinear dispatch only returns Sat/Unsat when CONFIRMED
                // (G-SAT model / cross-checked covering / Layer-0), so these are
                // Definite poles.
                SolverResult::Sat => return SatLevel::DefiniteSat,
                SolverResult::Unsat => return SatLevel::DefiniteUnsat,
                SolverResult::Unknown => {}
            }
        }

        // Part B of the confirmed/unconfirmed verdict discipline (the `SatLevel`
        // lattice). The sound nonlinear oracle above did NOT return a `Definite*`
        // verdict, yet the formula carries a genuine nonlinear term (`(* x y)`,
        // `x²`, …). The CDCL(T)/MBQI loop below treats such a term as an OPAQUE
        // variable, so any `sat` it reaches is unconfirmed — it never checked the
        // nonlinear semantics (e.g. `(= (* x y) 6) ∧ (= (* x y) 7)` is fine to the
        // opaque view). Mark it so the final `sat` is graded `PossiblySat` and
        // collapses to the sound `unknown`. A CDCL(T) `unsat` stays sound (it is a
        // conflict-clause refutation, monotone over the opaque abstraction), so
        // only the `sat` side is downgraded. Keyed on the PRESENCE of a native
        // nonlinear term (`term_is_nonlinear`), NOT on the logic string: a problem
        // submitted under `ALL`, under no `(set-logic)`, or under a mislabeled
        // logic (e.g. the AD1 lu-smt delegation, which replays `QF_NIA` obligations
        // under `ALL` semantics) is STILL nonlinear and must be downgraded — the
        // old `logic.contains("NIA"|"NRA")` gate let exactly those bypass the net
        // and report a spurious `sat` for `(= (* x x) 3)` / `(x−y)² < 0`. The verus
        // `Mul`/`RMul`-wrapper path is UNAFFECTED: its products are uninterpreted
        // `Apply`s and the only native `(* …)` lives inside `Forall` bridge axioms,
        // both of which `term_is_nonlinear` returns `false` on (its `_ => false`
        // arm does not recurse through `Apply`/`Forall`).
        let _ = &nl_dispatch; // (the definite verdicts already returned above)
        let nonlinear_opaque_sat = self
            .assertions
            .iter()
            .any(|&a| oxiz_theories::nlsat::term_is_nonlinear(a, manager));

        // Check nonlinear arithmetic constraints for early conflict detection
        // (static pattern matching, complementary to the dispatch above).
        if self.check_nonlinear_constraints(manager) {
            return SatLevel::DefiniteUnsat;
        }

        // Check resource limits before starting
        if self.config.max_conflicts > 0 && self.statistics.conflicts >= self.config.max_conflicts {
            return SatLevel::Unknown;
        }
        if self.config.max_decisions > 0 && self.statistics.decisions >= self.config.max_decisions {
            return SatLevel::Unknown;
        }

        // MBQI loop for quantified formulas.
        //
        // §4 redesign (Phase 2): the owning `TheoryManager` is constructed fresh
        // at the top of EACH iteration via `take_theory_manager` (moving the
        // persistent euf/arith/bv state + the real `TermManager` in) and torn
        // down via `restore_theory_manager` right after the solve. This replaces
        // the old "construct once before the loop, recreate at the loop tail"
        // dance — same effect (scratch reinitialised per round, theory state
        // persists), but the manager no longer needs to outlive a `&mut` borrow
        // of `self`/`manager` across the MBQI instantiation work.
        let max_mbqi_iterations = 100;
        let mut mbqi_iteration = 0;

        // Wall-clock backstop for the MBQI loop.  Quantifier instantiation over
        // an infinite domain is only semi-decidable: a `forall`-with-`:pattern`
        // axiom whose model is genuinely SAT (e.g. `y>0 ∧ ¬(Add(x,y)>0)` with
        // `Add(a,b)=a+b`) can make the counterexample/enumeration path generate
        // fresh ground terms without converging, so the iteration cap alone does
        // not bound wall-clock.  Honour the configured `timeout_ms` if set, else
        // apply a default non-termination guard.  On expiry the verdict is the
        // SOUND `Unknown` (never a guessed sat/unsat).  Quantifier-free problems
        // run the body once and never reach this.
        #[cfg(feature = "std")]
        let mbqi_deadline: Option<std::time::Instant> = {
            let ms = if self.config.timeout_ms > 0 {
                self.config.timeout_ms
            } else {
                MBQI_NONTERMINATION_GUARD_MS
            };
            Some(std::time::Instant::now() + std::time::Duration::from_millis(ms))
        };

        // The clean-room quantifier engine (`oxiz-mbqi`), built lazily on the
        // first SAT-with-quantifiers round and PERSISTED across MBQI iterations
        // so its ground-term index, `seen` dedup, and frontier watermarks
        // accumulate (the whole point of the lifetime-free `Engine<OxizSig>`:
        // it outlives any single `&mut TermManager` borrow). Only used when
        // `config.clean_mbqi` is set; when it is off the solver runs ground-only
        // (no quantifier instantiation) — the mode the internal unsat verifier
        // uses (`verify_clean_unsat`). The old in-tree `mbqi/` engine is gone.
        let mut clean_engine: Option<CleanEngine<OxizSig>> = None;
        // The GROUND bodies of the clean engine's instances (each a sound
        // consequence of the asserted quantifiers). Used to VERIFY an
        // incremental `unsat` with a single-shot ground solve — OxiZ's
        // incremental CDCL(T) can report a spurious `unsat` after lemmas are
        // added across MBQI rounds, whereas the same clause set solved fresh is
        // sound. See `verify_clean_unsat`.
        let mut clean_instances: Vec<TermId> = Vec::new();

        // Propagate the wall-clock deadline INTO the ground SAT solver so a single
        // non-terminating ground solve (e.g. a dense-real f-tower instance set)
        // bails to `Unknown` rather than overshooting the cap — the MBQI
        // between-round check alone cannot interrupt a hung `solve_*` call.
        #[cfg(feature = "std")]
        self.sat.set_deadline(mbqi_deadline);
        loop {
            #[cfg(feature = "std")]
            if self.has_quantifiers && mbqi_deadline.is_some_and(|d| std::time::Instant::now() >= d)
            {
                return SatLevel::Unknown;
            }
            // Move the persistent theory state + the real term manager into an
            // owning theory manager for this solve, then move it all back out
            // (the MBQI body below mutates `self.euf`/`manager` directly).
            let mut theory_manager = self.take_theory_manager(manager);
            let sat_result = if self.config.use_hooks_driver {
                // §4 redesign path: lock-step `TheoryHooks` driver. It CONSUMES the
                // owning theory manager and hands it back (the trail stores it
                // type-erased for the solve), so we rebind.
                let (result, tm) = self.sat.solve_with_hooks(theory_manager);
                theory_manager = tm;
                result
            } else {
                // Legacy path: advisory `TheoryCallback`.
                self.sat.solve_with_theory(&mut theory_manager)
            };
            // Soundness gate: read whether the authorising theory battery confirmed
            // its `Sat` or only fell back to it from an `Unknown`/`Err` (an
            // incomplete theory — e.g. LIA branch-and-bound that proved the
            // LP-feasible vertex has no integer point). A non-trivial, unconfirmed
            // `Sat` MUST be reported as `Unknown`, never as a model. Capture it
            // before `restore_theory_manager` consumes the owning manager.
            let last_unconfirmed = theory_manager.last_check_unconfirmed();
            self.restore_theory_manager(manager, theory_manager);
            match sat_result {
                SatResult::Unsat => {
                    // The clean engine never *concludes* `unsat` — that is the
                    // host ground core's job, and is sound only for a sound
                    // core. OxiZ's INCREMENTAL re-solve (after lemmas are added
                    // across rounds) can be unsound here, so when the clean
                    // engine has contributed lemmas, confirm the `unsat` with a
                    // single-shot ground solve before trusting it.
                    if self.config.clean_mbqi && !clean_instances.is_empty() {
                        // Combine two verdicts about the same formula via the lattice
                        // `meet`: the incremental solve's UNCONFIRMED `unsat` claim
                        // (`PossiblyUnsat`) and the single-shot ground re-solve's
                        // CONFIRMED verdict. meet adjudicates exactly right — confirm
                        // (`⊓ DefiniteUnsat = DefiniteUnsat`), can't-confirm
                        // (`⊓ Unknown = PossiblyUnsat`, collapses to sound `unknown`),
                        // and even a re-solve that finds a MODEL
                        // (`⊓ DefiniteSat = DefiniteSat`) refutes the stale claim.
                        let reverify =
                            SatLevel::from_definite(self.verify_clean_unsat(&clean_instances, manager));
                        return SatLevel::PossiblyUnsat.meet(reverify);
                    }
                    self.build_unsat_core();
                    return SatLevel::DefiniteUnsat;
                }
                SatResult::Unknown => {
                    return SatLevel::Unknown;
                }
                SatResult::Sat => {
                    // If no quantifiers, we're done
                    if !self.has_quantifiers {
                        // Grade the `Sat` on the `SatLevel` lattice: it is a
                        // CONFIRMED model (`DefiniteSat` → `sat`) ONLY when the
                        // authorising theory battery verified it (`!last_unconfirmed`)
                        // AND no opaque nonlinear term was left unchecked
                        // (`!nonlinear_opaque_sat`); otherwise it is an unconfirmed
                        // `PossiblySat`, which collapses to the sound `unknown`.
                        let level = if last_unconfirmed || nonlinear_opaque_sat {
                            SatLevel::PossiblySat
                        } else {
                            SatLevel::DefiniteSat
                        };
                        if level == SatLevel::DefiniteSat {
                            self.build_model(manager);
                            self.unsat_core = None;
                        }
                        return level;
                    }

                    // Build partial model for MBQI
                    self.build_model(manager);

                    // ===== Clean-room model-based instantiation phase =====
                    // Sound by construction: the engine only emits guarded
                    // ground instances drawn from the real ground-term index, so
                    // a spurious `unsat` (e-match self/sibling capture,
                    // fabricated `u!N` witnesses, dropped fuel guards) is
                    // structurally impossible. A trigger-free axiom it cannot
                    // model-verify yields the sound `Unknown`, never a guess.
                    if self.config.clean_mbqi {
                        // #404 phase-2 probe (env-gated): the wall shows a lemma
                        // asserted in round N with the ground core still SAT in
                        // round N+1 — dump each clean instance's SAT-model truth
                        // plus its immediate structure to see which link of
                        // `Q ⇒ (guard ⇒ concl)` failed to bite.
                        if std::env::var_os("OXIZ_MBQI_DBG").is_some()
                            && !clean_instances.is_empty()
                        {
                            let sat_model = self.sat.model();
                            let tv = |t: TermId| -> &'static str {
                                match self.term_to_var.get(&t) {
                                    Some(v) => match sat_model.get(v.index()).copied() {
                                        Some(b) if b.is_true() => "T",
                                        Some(b) if b.is_false() => "F",
                                        _ => "?",
                                    },
                                    None => "novar",
                                }
                            };
                            for &l in &clean_instances {
                                eprintln!("[mbqi-dbg] model: lemma {l:?}={}", tv(l));
                                let Some(TermKind::Implies(q, phi)) =
                                    manager.get(l).map(|t| t.kind.clone())
                                else {
                                    continue;
                                };
                                eprintln!(
                                    "[mbqi-dbg]   q {q:?}={} phi {phi:?}={}",
                                    tv(q),
                                    tv(phi)
                                );
                                if let Some(TermKind::Implies(g, c)) =
                                    manager.get(phi).map(|t| t.kind.clone())
                                {
                                    eprintln!(
                                        "[mbqi-dbg]   guard {g:?}={} concl {c:?}={}",
                                        tv(g),
                                        tv(c)
                                    );
                                    if let Some(TermKind::And(args)) =
                                        manager.get(g).map(|t| t.kind.clone())
                                    {
                                        for a in args {
                                            // a is typically Not(eq): print the
                                            // inner ATOM too (the Not node itself
                                            // never gets a var — its literal is
                                            // the negated atom var).
                                            let inner = match manager.get(a).map(|t| t.kind.clone())
                                            {
                                                Some(TermKind::Not(i)) => Some(i),
                                                _ => None,
                                            };
                                            match inner {
                                                Some(i) => eprintln!(
                                                    "[mbqi-dbg]     guard-conj {a:?}={} (inner atom {i:?}={})",
                                                    tv(a),
                                                    tv(i)
                                                ),
                                                None => eprintln!(
                                                    "[mbqi-dbg]     guard-conj {a:?}={}",
                                                    tv(a)
                                                ),
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        // Build + assert the formula once; persist across rounds.
                        if clean_engine.is_none() {
                            let mut eng = CleanEngine::new(CleanConfig {
                                // CCFV (P2): opt-in congruence-aware e-matching.
                                ccfv_ematch: self.config.ccfv_ematch,
                                // CCFV (P4): opt-in model-completion verdict-flip.
                                ccfv_model_compl: self.config.ccfv_model_compl,
                                // Fuel-aware cost scheduler (P2): env-gated for the
                                // corpus A/B until it is validated 0-regression. Off
                                // (default) ⇒ the fire-all round is byte-identical.
                                cost_schedule: std::env::var_os("OXIZ_COST_SCHEDULE")
                                    .is_some(),
                                awr_age_ratio: std::env::var("OXIZ_AWR_AGE_RATIO")
                                    .ok()
                                    .and_then(|s| s.parse().ok())
                                    .unwrap_or(0),
                                awr_weight_ratio: std::env::var("OXIZ_AWR_WEIGHT_RATIO")
                                    .ok()
                                    .and_then(|s| s.parse().ok())
                                    .unwrap_or(1),
                                ..CleanConfig::default()
                            });
                            {
                                let host = OxizHost::new(manager);
                                for &a in &self.assertions {
                                    eng.assert(&host, a);
                                }
                            }
                            clean_engine = Some(eng);
                        }
                        // One instantiation round against the current model.
                        let verdict = {
                            let model = self.build_clean_model(manager);
                            // Declared integer constants the top-level equalities
                            // pin (`(= n 5)`), so the host can resolve a symbolic
                            // guard bound `(< i n)` to a finite domain.
                            let mut int_consts = FxHashMap::default();
                            crate::clean_mbqi::collect_int_consts(
                                manager,
                                &self.assertions,
                                &mut int_consts,
                            );
                            let eng = clean_engine.as_mut().expect("just built above");
                            let mut host = OxizHost::with_int_consts(manager, int_consts);
                            // CCFV (P2): single-pattern e-matching runs modulo the
                            // live post-solve EUF congruence (`self.euf`, restored by
                            // `restore_theory_manager` above) when `ccfv_ematch` is
                            // on. With the flag off the engine ignores the oracle, so
                            // the default path is byte-identical to `round_with`.
                            //
                            // CCFV (P4): when the model-completion flip is armed the
                            // oracle ALSO carries the by-sort ground-term index the
                            // brute-force conflict search enumerates witnesses over
                            // (`build_ground_by_sort`, computed once per round). The
                            // index is empty on the default (flip-off) path, so the
                            // matching/CDQI queries pay nothing.
                            let cong = if self.config.ccfv_model_compl {
                                let gbs = crate::clean_mbqi::build_ground_by_sort(
                                    &self.euf,
                                    host.tm_ref(),
                                );
                                EufCongruence::with_ground_index(&self.euf, gbs)
                            } else {
                                EufCongruence::new(&self.euf)
                            };
                            eng.round_with_cong(&mut host, &model, &cong)
                        };
                        match verdict {
                            CleanVerdict::NewLemmas(lemmas) => {
                                // Assert each guarded instance `Q ⇒ φ[x̄↦t̄]` and
                                // re-solve on the next loop iteration (fall
                                // through to the tail below).
                                //
                                // The lemma is added as the DIRECT guarded clause
                                // `[¬Q, φ]`, NOT as a unit on the `Implies` node's
                                // Tseitin proxy. This is the standard SMT
                                // instantiation-lemma form: when the quantifier
                                // literal `Q` is asserted/derived true the instance
                                // `φ` is forced (so a real conflict surfaces);
                                // when `Q` is false the clause is vacuous (sound
                                // for guarded / disjunctive quantifiers, where the
                                // unconditional `φ` would be unsound).
                                for l in lemmas {
                                    match manager.get(l).map(|t| t.kind.clone()) {
                                        Some(TermKind::Implies(q, phi)) => {
                                            // Defensive substitution guard: the host
                                            // `substitute` is total over FO/UF/LIA
                                            // but not (yet) over BV/string/nested
                                            // quantifiers, so an instance could
                                            // retain one of THIS quantifier's BOUND
                                            // variables (incomplete substitution).
                                            // Adding such a clause would be unsound
                                            // (the stray bound var is implicitly
                                            // closed); DROP it — costs only
                                            // completeness.
                                            //
                                            // Crucially the test is "retains a BOUND
                                            // variable", NOT "has any free var":
                                            // OxiZ models declared constants as `Var`
                                            // terms too, so a perfectly ground
                                            // instance like `Add(x,y)=x+y` over
                                            // declared constants `x,y` has non-empty
                                            // `free_vars`. The old `is_empty()` check
                                            // over-rejected it, dropping the lemma
                                            // that entails the conflict → a spurious
                                            // `Saturated`/`sat` (regression:
                                            // `patterned_quantifier_still_instantiates_at_real_ground_terms`).
                                            // Compare (name, sort) — not the name
                                            // alone. OxiZ models declared constants
                                            // as `Var(name)` too, so a GROUND
                                            // constant that merely shares a bound
                                            // var's name (verus AIR: the axiom binds
                                            // `x!: Poly` while the query declares a
                                            // global `x!: Int`) matched a name-only
                                            // check and the legitimate instance was
                                            // dropped → the fuel-chain never closed
                                            // → spurious unknown that was ORDER-
                                            // sensitive (only when the axiom was
                                            // asserted before the colliding decl
                                            // did the witness contain the const).
                                            // #397 part C.
                                            let bound_vars: smallvec::SmallVec<
                                                [(oxiz_core::interner::Spur, oxiz_core::SortId); 2],
                                            > = match manager.get(q).map(|t| &t.kind) {
                                                Some(
                                                    TermKind::Forall { vars, .. }
                                                    | TermKind::Exists { vars, .. },
                                                ) => vars.iter().map(|(n, s)| (*n, *s)).collect(),
                                                _ => Default::default(),
                                            };
                                            let retains_bound =
                                                manager.free_vars(phi).into_iter().any(|v| {
                                                    matches!(
                                                        manager.get(v).map(|t| (&t.kind, t.sort)),
                                                        Some((TermKind::Var(n), srt))
                                                            if bound_vars.contains(&(*n, srt))
                                                    )
                                                });
                                            if retains_bound {
                                                if std::env::var_os("OXIZ_MBQI_DBG").is_some() {
                                                    eprintln!(
                                                        "[mbqi-dbg] host: lemma DROPPED (retains a bound var)"
                                                    );
                                                }
                                                continue;
                                            }
                                            // Record the GUARDED lemma `Q ⇒ φ`
                                            // (NOT the bare body `φ`) for the
                                            // single-shot verification. #347: `φ`
                                            // is a consequence ONLY when `Q` holds;
                                            // recording the bare `φ` let
                                            // `fresh_ground_resolve` assert a
                                            // guarded `Q ⇒ ⊥`'s body `⊥`
                                            // unconditionally → spurious unsat on
                                            // `(=> g (∀x. false-body))`. The
                                            // verifier re-abstracts each `Q` to a
                                            // shared Bool proposition, so the guard
                                            // is preserved (`Q ⇒ ⊥` ⤳ `¬Q`).
                                            clean_instances.push(l);
                                            // Reuse the quantifier's EXISTING literal — do NOT
                                            // `encode(q)`, which re-runs the `Forall` arm and
                                            // re-registers the quantifier with mbqi/ematch on
                                            // every instance (state pollution).
                                            let qlit_reused = self.term_to_var.contains_key(&q);
                                            let qlit = match self.term_to_var.get(&q) {
                                                Some(&v) => oxiz_sat::Lit::pos(v),
                                                None => self.encode(q, manager),
                                            };
                                            if std::env::var_os("OXIZ_MBQI_DBG").is_some() {
                                                let p = oxiz_core::smtlib::Printer::new(manager);
                                                let g = match manager.get(phi).map(|t| t.kind.clone())
                                                {
                                                    Some(TermKind::Implies(g, _)) => Some(g),
                                                    _ => None,
                                                };
                                                eprintln!(
                                                    "[mbqi-dbg] host: lemma asserted — qlit {} (q={:?}), phi={:?} pol={:?} guard-pol={:?} aware={} = {}",
                                                    if qlit_reused { "REUSED" } else { "FRESH" },
                                                    q,
                                                    phi,
                                                    self.polarities.get(&phi),
                                                    g.and_then(|g| self.polarities.get(&g)),
                                                    self.polarity_aware,
                                                    p.print_term(phi),
                                                );
                                            }
                                            if manager
                                                .get(phi)
                                                .is_some_and(|t| matches!(t.kind, TermKind::False))
                                            {
                                                // `Q ⇒ false` ≡ `¬Q`.
                                                let _ = self.sat.add_clause([qlit.negate()]);
                                            } else {
                                                // #397 — an instance body is ground
                                                // by construction, so any `ite` the
                                                // quantifier body carried is now a
                                                // ground term-ite: lower it here
                                                // (this path bypasses `assert`).
                                                let phi = self.eliminate_term_ites(phi, manager);
                                                let philit = self.encode(phi, manager);
                                                let _ =
                                                    self.sat.add_clause([qlit.negate(), philit]);
                                            }
                                        }
                                        // The engine always guards with `Implies`;
                                        // a bare lemma is only a defensive fallback.
                                        _ => {
                                            // #397 — same ground term-ite lowering as
                                            // the guarded arm.
                                            let l = self.eliminate_term_ites(l, manager);
                                            let lit = self.encode(l, manager);
                                            let _ = self.sat.add_clause([lit]);
                                        }
                                    }
                                }
                            }
                            CleanVerdict::Saturated => {
                                // Every quantifier satisfied by the (incremental)
                                // model. But the incremental CDCL(T) can MISS a
                                // conflict GLOBAL across instances accumulated over
                                // rounds (pigeonhole: a bounded ∀ whose box
                                // conjunction is jointly unsat). When instances were
                                // emitted (bounded quantifiers), confirm the model
                                // with a single-shot ground re-solve before trusting
                                // `sat`; with none (pure model-completion) the
                                // `Saturated` is already sound.
                                if self.config.clean_mbqi && !clean_instances.is_empty() {
                                    // Same lattice `meet` as the unsat path: the
                                    // incremental's UNCONFIRMED `sat` claim
                                    // (`PossiblySat`) met with the single-shot ground
                                    // re-solve's CONFIRMED verdict — confirm
                                    // (`⊓ DefiniteSat`), a global conflict the
                                    // incremental missed (`⊓ DefiniteUnsat`), or
                                    // can't-confirm (`⊓ Unknown = PossiblySat`).
                                    let reverify = SatLevel::from_definite(
                                        self.verify_clean_saturated(&clean_instances, manager),
                                    );
                                    return SatLevel::PossiblySat.meet(reverify);
                                }
                                // Same `SatLevel` grade as the quantifier-free path:
                                // an incomplete theory battery or an opaque nonlinear
                                // term ⇒ `PossiblySat` (collapses to `unknown`).
                                let level = if last_unconfirmed || nonlinear_opaque_sat {
                                    SatLevel::PossiblySat
                                } else {
                                    SatLevel::DefiniteSat
                                };
                                if level == SatLevel::DefiniteSat {
                                    self.unsat_core = None;
                                }
                                return level;
                            }
                            CleanVerdict::Inconclusive | CleanVerdict::BudgetExhausted => {
                                // A trigger-free axiom could not be verified, or
                                // the budget was hit: the SOUND verdict is
                                // `Unknown` (never a fabricated `unsat`/`sat`).
                                return SatLevel::Unknown;
                            }
                        }
                    }

                    mbqi_iteration += 1;
                    if mbqi_iteration >= max_mbqi_iterations {
                        return SatLevel::Unknown;
                    }

                    // The theory manager is rebuilt at the top of the next loop
                    // iteration via `take_theory_manager` (which moves the
                    // persistent euf/arith/bv state back in). Theory state is NOT
                    // reset here: resetting EUF/Arith/BV would cause spurious
                    // conflicts when accumulated MBQI lemmas interact with state
                    // that was cleared — it accumulates correctly across rounds.
                }
            }
        }
    }

    /// Check satisfiability under assumptions
    /// Assumptions are temporary constraints that don't modify the assertion stack
    pub fn check_with_assumptions(
        &mut self,
        assumptions: &[TermId],
        manager: &mut TermManager,
    ) -> SolverResult {
        // Save current state
        self.push();

        // Assert all assumptions
        for &assumption in assumptions {
            self.assert(assumption, manager);
        }

        // Check satisfiability
        let result = self.check(manager);

        // Restore state
        self.pop();

        result
    }

    /// Check satisfiability (pure SAT, no theory integration)
    /// Useful for benchmarking or when theories are not needed
    pub fn check_sat_only(&mut self, manager: &mut TermManager) -> SolverResult {
        if self.assertions.is_empty() {
            return SolverResult::Sat;
        }

        match self.sat.solve() {
            SatResult::Sat => {
                self.build_model(manager);
                SolverResult::Sat
            }
            SatResult::Unsat => SolverResult::Unsat,
            SatResult::Unknown => SolverResult::Unknown,
        }
    }

    /// Build the model after SAT solving, which can be used to efficiently extract minimal unsat cores
    pub fn enable_assumption_based_cores(&mut self) {
        self.produce_unsat_cores = true;
        // Assumption variables would be created during assertion
        // to enable fine-grained core extraction
    }

    /// Minimize an unsat core using greedy deletion
    /// This creates a minimal (but not necessarily minimum) unsatisfiable subset
    pub fn minimize_unsat_core(&mut self, manager: &mut TermManager) -> Option<UnsatCore> {
        if !self.produce_unsat_cores {
            return None;
        }

        // Get the current unsat core
        let core = self.unsat_core.as_ref()?;
        if core.is_empty() {
            return Some(core.clone());
        }

        // Extract the assertions in the core
        let mut core_assertions: Vec<_> = core
            .indices
            .iter()
            .map(|&idx| {
                let assertion = self.assertions[idx as usize];
                let name = self
                    .named_assertions
                    .iter()
                    .find(|na| na.index == idx)
                    .and_then(|na| na.name.clone());
                (idx, assertion, name)
            })
            .collect();

        // Try to remove each assertion one by one
        let mut i = 0;
        while i < core_assertions.len() {
            // Create a temporary solver with all assertions except the i-th one
            let mut temp_solver = Solver::new();
            temp_solver.set_logic(self.logic.as_deref().unwrap_or("ALL"));

            // Add all assertions except the i-th one
            for (j, &(_, assertion, _)) in core_assertions.iter().enumerate() {
                if i != j {
                    temp_solver.assert(assertion, manager);
                }
            }

            // Check if still unsat
            if temp_solver.check(manager) == SolverResult::Unsat {
                // Still unsat without this assertion - remove it
                core_assertions.remove(i);
                // Don't increment i, check the next element which is now at position i
            } else {
                // This assertion is needed
                i += 1;
            }
        }

        // Build the minimized core
        let mut minimized = UnsatCore::new();
        for (idx, _, name) in core_assertions {
            minimized.indices.push(idx);
            if let Some(n) = name {
                minimized.names.push(n);
            }
        }

        Some(minimized)
    }

    /// Get the model (if sat)
    #[must_use]
    pub fn model(&self) -> Option<&Model> {
        self.model.as_ref()
    }

    /// Congruence-closed function-application entries from the EUF solver for
    /// the given function symbol id (crate-internal use only).
    ///
    /// Each entry's argument and result classes have already been canonicalized
    /// through the union-find, so callers building a `FuncInterp` get congruence
    /// applied for free (e.g. `f(a)` and `f(b)` collapse when `a = b`).  The
    /// `func_id` is the EUF function symbol id, which for an `Apply` term is the
    /// underlying value of the function-name `Spur` (`spur.into_inner().get()`).
    #[must_use]
    pub(crate) fn euf_function_entries(
        &self,
        func_id: u32,
    ) -> Vec<oxiz_theories::euf::FuncAppEntry> {
        self.euf.function_application_entries(func_id)
    }

    /// Check satisfiability with resource limits.
    pub fn check_with_limits(
        &mut self,
        manager: &mut TermManager,
        limits: &crate::resource_limits::ResourceLimits,
    ) -> core::result::Result<SolverResult, crate::resource_limits::ResourceExhausted> {
        use crate::resource_limits::ResourceMonitor;
        let mut monitor = ResourceMonitor::new(limits.clone());
        if let Some(reason) = monitor.check() {
            return Err(reason);
        }
        let orig_max_conflicts = self.config.max_conflicts;
        let orig_max_decisions = self.config.max_decisions;
        if let Some(max_c) = limits.max_conflicts {
            if self.config.max_conflicts == 0 || max_c < self.config.max_conflicts {
                self.config.max_conflicts = max_c;
            }
        }
        if let Some(max_d) = limits.max_decisions {
            if self.config.max_decisions == 0 || max_d < self.config.max_decisions {
                self.config.max_decisions = max_d;
            }
        }
        let result = self.check(manager);
        self.config.max_conflicts = orig_max_conflicts;
        self.config.max_decisions = orig_max_decisions;
        monitor.conflicts = self.statistics.conflicts;
        monitor.decisions = self.statistics.decisions;
        monitor.restarts = self.statistics.restarts;
        monitor.theory_checks =
            self.statistics.theory_propagations + self.statistics.theory_conflicts;
        if result == SolverResult::Unknown {
            if let Some(reason) = monitor.check() {
                return Err(reason);
            }
        }
        Ok(result)
    }
    /// Set a wall-clock timeout.
    pub fn set_timeout(&mut self, timeout: core::time::Duration) {
        self.config.timeout_ms = timeout.as_millis() as u64;
    }
    /// Set the maximum number of SAT conflicts.
    pub fn set_conflict_limit(&mut self, max_conflicts: u64) {
        self.config.max_conflicts = max_conflicts;
    }
    /// Set the maximum number of SAT decisions.
    pub fn set_decision_limit(&mut self, max_decisions: u64) {
        self.config.max_decisions = max_decisions;
    }

    /// Assert multiple terms at once
    /// This is more efficient than calling assert() multiple times
    pub fn assert_many(&mut self, terms: &[TermId], manager: &mut TermManager) {
        for &term in terms {
            self.assert(term, manager);
        }
    }

    /// Get the number of assertions in the solver
    #[must_use]
    pub fn num_assertions(&self) -> usize {
        self.assertions.len()
    }

    /// Get the number of variables in the SAT solver
    #[must_use]
    pub fn num_variables(&self) -> usize {
        self.term_to_var.len()
    }

    /// Check if the solver has any assertions
    #[must_use]
    pub fn has_assertions(&self) -> bool {
        !self.assertions.is_empty()
    }

    /// Get the current context level (push/pop depth)
    #[must_use]
    pub fn context_level(&self) -> usize {
        self.context_stack.len()
    }

    /// Push a context level
    pub fn push(&mut self) {
        self.context_stack.push(ContextState {
            num_assertions: self.assertions.len(),
            num_vars: self.var_to_term.len(),
            has_false_assertion: self.has_false_assertion,
            trail_position: self.trail.len(),
        });
        self.sat.push();
        self.euf.push();
        self.arith.push();
        #[cfg(feature = "std")]
        if let Some(nlsat) = &mut self.nlsat {
            nlsat.push();
        }
    }

    /// Pop a context level using trail-based undo
    pub fn pop(&mut self) {
        if let Some(state) = self.context_stack.pop() {
            // Undo all operations in the trail since the push
            while self.trail.len() > state.trail_position {
                if let Some(op) = self.trail.pop() {
                    match op {
                        TrailOp::AssertionAdded { index } => {
                            if self.assertions.len() > index {
                                self.assertions.truncate(index);
                            }
                        }
                        TrailOp::VarCreated { var: _, term } => {
                            // Remove the term-to-var mapping
                            self.term_to_var.remove(&term);
                        }
                        TrailOp::ConstraintAdded { var } => {
                            // Remove the constraint
                            self.var_to_constraint.remove(&var);
                        }
                        TrailOp::FalseAssertionSet => {
                            // Reset the flag
                            self.has_false_assertion = false;
                        }
                        TrailOp::NamedAssertionAdded { index } => {
                            // Remove the named assertion
                            if self.named_assertions.len() > index {
                                self.named_assertions.truncate(index);
                            }
                        }
                        TrailOp::BvTermAdded { term } => {
                            // Remove the bitvector term
                            self.bv_terms.remove(&term);
                        }
                        TrailOp::ArithTermAdded { term } => {
                            // Remove the arithmetic term
                            self.arith_terms.remove(&term);
                        }
                        TrailOp::DtCoverAdded { term } => {
                            // The cover CLAUSE died with the SAT-level pop; drop
                            // the marker so a later scope re-emits it.
                            self.dt_cover_done.remove(&term);
                        }
                    }
                }
            }

            // Use state to restore other fields
            self.assertions.truncate(state.num_assertions);
            self.var_to_term.truncate(state.num_vars);
            self.has_false_assertion = state.has_false_assertion;

            self.sat.pop();
            self.euf.pop();
            self.arith.pop();
            #[cfg(feature = "std")]
            if let Some(nlsat) = &mut self.nlsat {
                nlsat.pop();
            }
        }
    }

    /// Reset the solver
    pub fn reset(&mut self) {
        self.sat.reset();
        self.euf.reset();
        self.arith.reset();
        self.bv.reset();
        self.term_to_var.clear();
        self.var_to_term.clear();
        self.var_to_constraint.clear();
        self.var_to_parsed_arith.clear();
        self.assertions.clear();
        self.named_assertions.clear();
        self.model = None;
        self.unsat_core = None;
        self.context_stack.clear();
        self.trail.clear();
        self.logic = None;
        self.theory_processed_up_to = 0;
        self.has_false_assertion = false;
        self.bv_terms.clear();
        self.arith_terms.clear();
        self.dt_var_constructors.clear();
        self.dt_cover_done.clear();
        self.arith_parse_cache.clear();
        self.tracked_compound_terms.clear();
    }

    /// Get the configuration
    #[must_use]
    pub fn config(&self) -> &SolverConfig {
        &self.config
    }

    /// Set configuration
    pub fn set_config(&mut self, config: SolverConfig) {
        self.config = config;
    }

    /// Get solver statistics
    #[must_use]
    pub fn stats(&self) -> &oxiz_sat::SolverStats {
        self.sat.stats()
    }
}

#[cfg(test)]
mod tests;
