//! Types and data structures for the SMT solver

#[allow(unused_imports)]
use crate::prelude::*;
use oxiz_theories::ArithRat;
use oxiz_core::ast::{RoundingMode, TermId, TermKind, TermManager};
use oxiz_sat::{Lit, RestartStrategy, Var};
use smallvec::SmallVec;

/// Proof step for resolution-based proofs
#[derive(Debug, Clone)]
pub enum ProofStep {
    /// Input clause (from the original formula)
    Input {
        /// Clause index
        index: u32,
        /// The clause (as a disjunction of literals)
        clause: Vec<Lit>,
    },
    /// Resolution step
    Resolution {
        /// Index of this proof step
        index: u32,
        /// Left parent clause index
        left: u32,
        /// Right parent clause index
        right: u32,
        /// Pivot variable (the variable resolved on)
        pivot: Var,
        /// Resulting clause
        clause: Vec<Lit>,
    },
    /// Theory lemma (from a theory solver)
    TheoryLemma {
        /// Index of this proof step
        index: u32,
        /// The theory that produced this lemma
        theory: String,
        /// The lemma clause
        clause: Vec<Lit>,
        /// Explanation terms
        explanation: Vec<TermId>,
    },
}

/// A proof of unsatisfiability
#[derive(Debug, Clone)]
pub struct Proof {
    /// Sequence of proof steps leading to the empty clause
    steps: Vec<ProofStep>,
    /// Index of the final empty clause (proving unsat)
    empty_clause_index: Option<u32>,
}

impl Proof {
    /// Create a new empty proof
    #[must_use]
    pub fn new() -> Self {
        Self {
            steps: Vec::new(),
            empty_clause_index: None,
        }
    }

    /// Add a proof step
    pub fn add_step(&mut self, step: ProofStep) {
        self.steps.push(step);
    }

    /// Set the index of the empty clause (final step proving unsat)
    pub fn set_empty_clause(&mut self, index: u32) {
        self.empty_clause_index = Some(index);
    }

    /// Check if the proof is complete (has an empty clause)
    #[must_use]
    pub fn is_complete(&self) -> bool {
        self.empty_clause_index.is_some()
    }

    /// Get the number of proof steps
    #[must_use]
    pub fn len(&self) -> usize {
        self.steps.len()
    }

    /// Check if the proof is empty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }

    /// Iterate over all proof steps
    pub fn steps(&self) -> impl Iterator<Item = &ProofStep> {
        self.steps.iter()
    }

    /// Format the proof as a string (for debugging or output)
    #[must_use]
    pub fn format(&self) -> String {
        let mut result = String::from("(proof\n");
        for step in &self.steps {
            match step {
                ProofStep::Input { index, clause } => {
                    result.push_str(&format!("  (input {} {:?})\n", index, clause));
                }
                ProofStep::Resolution {
                    index,
                    left,
                    right,
                    pivot,
                    clause,
                } => {
                    result.push_str(&format!(
                        "  (resolution {} {} {} {:?} {:?})\n",
                        index, left, right, pivot, clause
                    ));
                }
                ProofStep::TheoryLemma {
                    index,
                    theory,
                    clause,
                    ..
                } => {
                    result.push_str(&format!(
                        "  (theory-lemma {} {} {:?})\n",
                        index, theory, clause
                    ));
                }
            }
        }
        if let Some(idx) = self.empty_clause_index {
            result.push_str(&format!("  (empty-clause {})\n", idx));
        }
        result.push_str(")\n");
        result
    }
}

impl Default for Proof {
    fn default() -> Self {
        Self::new()
    }
}

/// Represents a theory constraint associated with a boolean variable
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub(crate) enum Constraint {
    /// Equality constraint: lhs = rhs
    Eq(TermId, TermId),
    /// Disequality constraint: lhs != rhs (negation of equality)
    Diseq(TermId, TermId),
    /// Less-than constraint: lhs < rhs
    Lt(TermId, TermId),
    /// Less-than-or-equal constraint: lhs <= rhs
    Le(TermId, TermId),
    /// Greater-than constraint: lhs > rhs
    Gt(TermId, TermId),
    /// Greater-than-or-equal constraint: lhs >= rhs
    Ge(TermId, TermId),
    /// Boolean-valued uninterpreted function application.
    /// When the SAT solver assigns this variable true/false, we must inform
    /// the EUF solver so that congruence closure can detect conflicts
    /// (e.g., `t(m) = true` and `t(co) = false` but `m = co`).
    BoolApp(TermId),
    /// #433: a Bool-sorted term used as a UF ARGUMENT, watched so its truth
    /// value reaches EUF. `k(p)` vs `k(q)` with `p` and `q` both assigned true
    /// is a congruence (`p` and `q` share the canonical true node), but nothing
    /// told EUF the values — [`Constraint::BoolApp`] completes only Bool-valued
    /// application RESULTS, and a plain Bool variable or an `and`/`or`/`not`
    /// compound in argument position had no completion at all, so
    /// `p, q, k(p) != k(q)` reported `sat`.
    ///
    /// `negated` handles the argument whose encoded literal is NEGATIVE
    /// (`k((not p))` encodes the arg to `¬p`, whose variable is `p`'s): the
    /// watched variable's assignment is then the term's value FLIPPED. On
    /// assignment, EUF merges the term's node with the canonical true/false
    /// node for `assignment XOR negated`.
    BoolValue {
        /// The Bool-sorted argument term whose node gets the value merge.
        term: TermId,
        /// `true` iff the watched variable holds the term's NEGATION.
        negated: bool,
    },
}

/// Type of arithmetic constraint
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ArithConstraintType {
    /// Less than (<)
    Lt,
    /// Less than or equal (<=)
    Le,
    /// Greater than (>)
    Gt,
    /// Greater than or equal (>=)
    Ge,
}

/// Parsed arithmetic constraint with extracted linear expression
/// Represents: sum of (term, coefficient) <= constant OR < constant (if strict)
#[derive(Debug, Clone)]
pub(crate) struct ParsedArithConstraint {
    /// Linear terms: (variable_term, coefficient).
    ///
    /// Coefficients/constant are [`oxiz_theories::ArithRat`] (= `Ratio<i128>`),
    /// the LRA/LIA core's widened rational — the value `extract_arith_constraint`
    /// already accumulates flows straight into `ArithSolver` with no narrowing.
    pub(crate) terms: SmallVec<[(TermId, ArithRat); 4]>,
    /// Constant bound (RHS)
    pub(crate) constant: ArithRat,
    /// Type of constraint
    pub(crate) constraint_type: ArithConstraintType,
    /// The original term (for conflict explanation)
    pub(crate) reason_term: TermId,
}

/// Polarity of a term in the formula
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Polarity {
    /// Term appears only positively
    Positive,
    /// Term appears only negatively
    Negative,
    /// Term appears in both polarities
    Both,
}

/// Result of SMT solving — the 3-valued SMT-LIB verdict (the `(check-sat)`
/// output format). This is the PUBLIC type the CLI/bindings consume; the solver
/// computes a finer-grained [`SatLevel`] internally and collapses it here.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolverResult {
    /// Satisfiable
    Sat,
    /// Unsatisfiable
    Unsat,
    /// Unknown (timeout, incomplete, etc.)
    Unknown,
}

/// The solver's INTERNAL 5-level verdict — a confidence lattice that sharply
/// separates a CONFIRMED verdict from a merely heuristic one:
///
/// ```text
///   DefiniteUnsat  — a sound refutation (conflict clause / G-UNSAT covering)
///   PossiblyUnsat  — an UNconfirmed unsat (a tier that was not re-verified,
///                    e.g. nl2's multivariate CDCAC covering)
///   Unknown        — no information
///   PossiblySat    — an UNconfirmed sat (a model the theories could not verify,
///                    e.g. a CDCL(T) assignment over an opaque nonlinear term, or
///                    an LP-feasible vertex with no integer-feasibility proof)
///   DefiniteSat    — a CONFIRMED model (theory-verified / G-SAT)
/// ```
///
/// Only the two `Definite*` poles may surface as `sat`/`unsat`; every `Possibly*`
/// and `Unknown` collapses to the sound `unknown` at the SMT boundary
/// ([`SatLevel::collapse`]). This makes a false `sat`/`unsat` structurally
/// impossible from an unconfirmed source — the soundness discipline that the
/// per-site `last_check_unconfirmed` / `sat_is_trustworthy` flags expressed
/// ad-hoc is now one first-class type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SatLevel {
    /// A confirmed, theory-/G-SAT-verified model exists.
    DefiniteSat,
    /// Heuristically satisfiable but NOT confirmed — must not be reported `sat`.
    PossiblySat,
    /// No information.
    Unknown,
    /// Heuristically unsatisfiable but NOT confirmed — must not be reported `unsat`.
    PossiblyUnsat,
    /// A confirmed refutation (conflict clause / re-verified covering).
    DefiniteUnsat,
}

impl SatLevel {
    /// Collapse to the 3-valued SMT verdict: only a `Definite*` pole is trusted;
    /// every unconfirmed level becomes the sound `Unknown`.
    #[must_use]
    pub fn collapse(self) -> SolverResult {
        match self {
            SatLevel::DefiniteSat => SolverResult::Sat,
            SatLevel::DefiniteUnsat => SolverResult::Unsat,
            SatLevel::PossiblySat | SatLevel::Unknown | SatLevel::PossiblyUnsat => {
                SolverResult::Unknown
            }
        }
    }

    /// Lift a CONFIRMED 3-valued result into the lattice (`Sat`→`DefiniteSat`,
    /// `Unsat`→`DefiniteUnsat`, `Unknown`→`Unknown`). Use only when the source is
    /// genuinely confirmed; an unconfirmed result must be built as `Possibly*`.
    #[must_use]
    pub fn from_definite(r: SolverResult) -> Self {
        match r {
            SolverResult::Sat => SatLevel::DefiniteSat,
            SolverResult::Unsat => SatLevel::DefiniteUnsat,
            SolverResult::Unknown => SatLevel::Unknown,
        }
    }

    /// Whether this is a confirmed pole — the only levels [`collapse`] turns into
    /// a definite `sat`/`unsat`.
    ///
    /// [`collapse`]: SatLevel::collapse
    #[must_use]
    pub fn is_definite(self) -> bool {
        matches!(self, SatLevel::DefiniteSat | SatLevel::DefiniteUnsat)
    }

    /// The **full-mode** output token — the un-collapsed 5-level verdict, emitted
    /// verbatim when the output mode is `Full` (the internal lattice is NOT
    /// reduced to the 3-valued `sat`/`unsat`/`unknown`). `Unknown` shares the
    /// `unknown` token with the collapsed form (they denote the same thing).
    #[must_use]
    pub fn as_full_str(self) -> &'static str {
        match self {
            SatLevel::DefiniteSat => "definite-sat",
            SatLevel::PossiblySat => "possibly-sat",
            SatLevel::Unknown => "unknown",
            SatLevel::PossiblyUnsat => "possibly-unsat",
            SatLevel::DefiniteUnsat => "definite-unsat",
        }
    }

    /// Combine two verdicts about the **same** formula into the most informative
    /// SOUND verdict — the precision-meet of the confidence lattice (the AFT
    /// `(under,over)`-style reconciliation the four ad-hoc `*_is_trustworthy`
    /// gates expressed by hand).
    ///
    /// * `Unknown` is the identity: no information defers to the other engine.
    /// * Same side ⇒ the higher-confidence level wins. A confirmed pole is ground
    ///   truth — an actual model (`DefiniteSat`) or a refutation (`DefiniteUnsat`)
    ///   — so it dominates an unconfirmed guess, *consistent with* [`collapse`]
    ///   trusting only `Definite*`. Hence it also dominates the OPPOSITE
    ///   unconfirmed guess (the `Possibly*` was heuristic and simply wrong).
    /// * Two OPPOSING unconfirmed guesses (`PossiblySat` ⊓ `PossiblyUnsat`) — or
    ///   two contradicting confirmed poles, which would be a solver bug — yield
    ///   the sound `Unknown`. `meet` never *upgrades*: two `Possibly*` can never
    ///   manufacture a `Definite*`.
    ///
    /// [`collapse`]: SatLevel::collapse
    #[must_use]
    pub fn meet(self, other: SatLevel) -> SatLevel {
        use SatLevel::{DefiniteSat, DefiniteUnsat, PossiblySat, PossiblyUnsat, Unknown};
        match (self, other) {
            (Unknown, x) | (x, Unknown) => x,
            (a, b) if a == b => a,
            // confirmed pole dominates ANY unconfirmed guess (same or opposite side)
            (DefiniteSat, PossiblySat | PossiblyUnsat)
            | (PossiblySat | PossiblyUnsat, DefiniteSat) => DefiniteSat,
            (DefiniteUnsat, PossiblySat | PossiblyUnsat)
            | (PossiblySat | PossiblyUnsat, DefiniteUnsat) => DefiniteUnsat,
            // opposing unconfirmed guesses ⇒ genuine uncertainty
            (PossiblySat, PossiblyUnsat) | (PossiblyUnsat, PossiblySat) => Unknown,
            // two contradicting confirmed poles would mean the solver is unsound
            // somewhere — never trust either; the sound fallback is `Unknown`.
            (DefiniteSat, DefiniteUnsat) | (DefiniteUnsat, DefiniteSat) => Unknown,
            _ => unreachable!("all same-level pairs handled by the `a == b` arm"),
        }
    }
}

impl From<SatLevel> for SolverResult {
    fn from(s: SatLevel) -> Self {
        s.collapse()
    }
}

/// How a `(check-sat)` verdict is rendered at the final output boundary.
///
/// The solver always computes the full 5-level [`SatLevel`] internally and keeps
/// it un-collapsed up to this one boundary; the mode decides whether to reduce it
/// to the 3-valued SMT-LIB form.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum OutputMode {
    /// **z3-compatible** (default): collapse the lattice to `sat`/`unsat`/
    /// `unknown` (standard SMT-LIB output) via [`SatLevel::collapse`].
    #[default]
    Z3Compatible,
    /// **Full**: emit the un-collapsed 5-level verdict verbatim
    /// (`definite-sat` / `possibly-sat` / `unknown` / `possibly-unsat` /
    /// `definite-unsat`) via [`SatLevel::as_full_str`] — no reduction to 3-valued
    /// logic.
    Full,
}

/// Theory checking mode
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TheoryMode {
    /// Eager theory checking (check on every assignment)
    Eager,
    /// Lazy theory checking (check only on complete assignments)
    Lazy,
}

/// Solver configuration
#[derive(Debug, Clone)]
pub struct SolverConfig {
    /// Timeout in milliseconds (0 = no timeout)
    pub timeout_ms: u64,
    /// Enable parallel solving
    pub parallel: bool,
    /// Number of threads for parallel solving
    pub num_threads: usize,
    /// Enable proof generation
    pub proof: bool,
    /// Enable model generation
    pub model: bool,
    /// Theory checking mode
    pub theory_mode: TheoryMode,
    /// Enable preprocessing/simplification
    pub simplify: bool,
    /// Maximum number of conflicts before giving up (0 = unlimited)
    pub max_conflicts: u64,
    /// Maximum number of decisions before giving up (0 = unlimited)
    pub max_decisions: u64,
    /// Restart strategy for SAT solver
    pub restart_strategy: RestartStrategy,
    /// Enable clause minimization (recursive minimization of learned clauses)
    pub enable_clause_minimization: bool,
    /// Enable learned clause subsumption
    pub enable_clause_subsumption: bool,
    /// Enable variable elimination during preprocessing
    pub enable_variable_elimination: bool,
    /// Variable elimination limit (max clauses to produce)
    pub variable_elimination_limit: usize,
    /// Enable blocked clause elimination during preprocessing
    pub enable_blocked_clause_elimination: bool,
    /// Enable symmetry breaking predicates
    pub enable_symmetry_breaking: bool,
    /// Enable inprocessing (periodic preprocessing during search)
    pub enable_inprocessing: bool,
    /// Inprocessing interval (number of conflicts between inprocessing)
    pub inprocessing_interval: u64,
    /// Run the clean-room quantifier engine (`oxiz-mbqi`) model-based
    /// instantiation phase. **On by default** — it is the solver's only
    /// quantifier engine (the legacy in-tree `mbqi/` subsystem was removed,
    /// #262).
    ///
    /// The clean engine is **sound by construction** — it never fabricates a
    /// universe witness and only emits guarded ground instances drawn from the
    /// real ground-term index, so the spurious-`unsat` bug class (e-match
    /// self/sibling capture, fabricated `u!N` MBQI witnesses, dropped fuel
    /// guards) is structurally impossible. A trigger-free axiom it cannot
    /// model-verify yields the sound `Unknown` rather than a guess.
    ///
    /// Setting this `false` makes the solver run **ground-only** (it encodes
    /// quantifiers as opaque boolean proxies and never instantiates them). That
    /// is the mode the internal single-shot unsat verifier uses
    /// (`verify_clean_unsat`); end users should leave it on. See `clean_mbqi.rs`
    /// and the `oxiz-mbqi` crate.
    pub clean_mbqi: bool,
    /// §4 redesign (Phase 2): drive the CDCL(T) loop through the lock-step
    /// `TheoryHooks` contract (`SatSolver::solve_with_hooks`) instead of the
    /// advisory `TheoryCallback` (`solve_with_theory`). Both run the SAME real
    /// EUF/arith/BV theory state (`TheoryManager` implements both traits); the
    /// hooks path additionally enforces the §4.1 `|frames| == level+1`
    /// invariant by construction (per-literal `unassign_hook` + per-level
    /// `pop_frame` make a desynced theory frame unrepresentable). **ON by
    /// default** (Phase 2 step 5): validated verdict-for-verdict against the
    /// legacy path (full suite + z3 differential, both drivers, zero spurious
    /// UNSAT). The legacy `TheoryCallback` path is retained as an opt-out
    /// (`false`) cross-check fallback. Because lock-step makes a stale theory
    /// frame unrepresentable, the hooks path also skips the `arith`
    /// stale-bound suppression guards (kept active for the legacy fallback).
    pub use_hooks_driver: bool,
    /// CCFV (Phase P2): run the clean-MBQI engine's trigger e-matching **modulo
    /// congruence** via `ccfv::match_trigger` (backed by the live EUF through
    /// `EufCongruence`). CCFV is the engine's sole matcher; this flag selects the
    /// congruence-aware oracle vs. the syntactic-equivalent `NoCong`.
    /// **ON by default.** The default-flip gates passed:
    /// the z3-parity corpus is byte-identical to syntactic matching (166/168
    /// agree, 0 spurious) and the full-prelude consult shows no measurable
    /// overhead (most congruence classes are singletons). The flip is also a
    /// *soundness* fix: the syntactic matcher misses triggers that fire only
    /// modulo congruence (e.g. `(P (f x))` against ground `(P c)` where
    /// `c = (f a)`), so model-completion could certify a congruence-blind model
    /// as `sat` on a nested-congruence shape that z3 calls `unsat` (regression
    /// test `nested_congruence_trigger_is_sound` in
    /// `tests/uf_sort_and_quant_soundness.rs`). CCFV matching is a superset of
    /// syntactic — it only adds matches holding modulo the congruence — and every
    /// match still passes the unchanged `instantiate`/`emit` firewall, so it can
    /// only add sound instances. See `clean_mbqi.rs` and the design
    /// `external/oxiz/docs/design/CCFV_UNIFIED_INSTANTIATION.md` §P2.
    pub ccfv_ematch: bool,
    /// **CCFV model-completion verdict-flip (P4, design §3 `Mode::ModelCompl`).**
    /// When set, a trigger-free universal the structural recognizers leave
    /// unverified is given a final CCFV `¬ψ` conflict search over the total view
    /// `E_TOT`; *no* conflict ⇒ a `Sat` contribution (the completeness half of
    /// CCFV). **OFF by default** and SOUNDNESS-CRITICAL: a missed conflict is a
    /// spurious `sat` (the cardinal sin), so it stays gated until the disequality
    /// search is complete, verus-pre-verified, and corpus-0-spurious-gated (design
    /// §6). With the flag clear the backstop is never consulted, so the verdict
    /// path is byte-identical. Toggled by `(set-option :oxiz.ccfv-model-compl true)`.
    pub ccfv_model_compl: bool,
    /// **E1 additive-patterns mode (#425).** After a clean-MBQI pass that
    /// would conclude `Saturated`/`Inconclusive`, augment each parsed-trigger
    /// universal with INFERRED trigger groups (a union — the author's groups
    /// are kept) and re-pass, at most once per quantifier. Rescues
    /// under-triggered axioms (dead `:pattern` symbols, ill-arity patterns)
    /// that z3's auto-config would still instantiate. Augmented quantifiers
    /// lose the trigger-semantics saturation exemption (they are
    /// model-verified like inferred-trigger ones), so the mode only ever adds
    /// sound instances or moves a verdict in the sound direction. **OFF by
    /// default** pending the corpus A/B; also armed by the
    /// `OXIZ_MBQI_ADDITIVE` env var (read where the engine config is built,
    /// the `OXIZ_MBQI_GUARD_MS` convention) or
    /// `(set-option :oxiz.mbqi-additive-patterns true)`.
    pub mbqi_additive_patterns: bool,
    /// **Work-bounded round emission.** Maximum number of ground instances the
    /// MBQI round loop may accumulate for one `check-sat` before it stops
    /// emitting. `0` disables the bound (the historical deadline-only loop).
    ///
    /// ## Why a WORK bound and not only a wall bound
    ///
    /// The round loop is otherwise bounded only by `OXIZ_MBQI_GUARD_MS` (plus a
    /// 100-round cap that never binds — measured 2 to 7 rounds per episode), so
    /// the verdict is a function of MACHINE SPEED: a faster engine emits more
    /// instances inside the same window, and a contended machine emits fewer.
    /// Both directions are measured, not hypothetical:
    ///
    /// * making backtracking cheaper ([`crate`]-external
    ///   `BacktrackMode::Trail`, push+pop containment 46% → ~0%) DROWNED five
    ///   fuel-recursion corpus rows, because the freed throughput was
    ///   reinvested into more instantiation per window rather than into
    ///   finishing earlier — which is why that mode is still opt-in;
    /// * the corpus sweep protocol requires an IDLE machine for the same reason
    ///   in reverse; contention silently moves verdicts.
    ///
    /// A work bound removes both. It also makes budget exhaustion AFFORDABLE to
    /// recover from: exhaustion arrives with wall clock left over, so the
    /// accumulated instances (sound ground consequences) can be handed to the
    /// same single-shot confirm the `SaturatedUnverified` path uses, trusting
    /// only its `unsat` half. Deadline expiry cannot do that — there is by
    /// definition no time left.
    ///
    /// Calibrated from a 209-row instance census: verified rows peak far below
    /// the runaways (hundreds to ~1.1k versus 2.0k, 4.1k, 6.9k and three rows
    /// above 72k). Env `OXIZ_MBQI_INSTANCE_BUDGET` overrides at construction
    /// (the `OXIZ_MBQI_GUARD_MS` convention); `0` restores the historical loop
    /// exactly.
    pub mbqi_instance_budget: usize,
    /// **#434 — carry the canonical integer/BV constant index across the
    /// per-round `TheoryManager`. DEFAULT `false`, and the default is a
    /// deliberate choice to keep a KNOWN completeness bug rather than ship an
    /// unsoundness.**
    ///
    /// `TheoryManager::interned_int_constants` is a derived index over the
    /// PERSISTENT `euf`, but it is rebuilt empty on every `TheoryManager`
    /// construction — once per iteration of `check_level`'s loop. Since
    /// `intern_term_for_congruence` returns early for a term EUF already
    /// interned, a value registered in round 1 can never re-register, so from
    /// round 2 on the index is permanently empty and both of its jobs stop:
    /// `model_based_combination`'s entailed-value merge (which looks the
    /// canonical node up BY VALUE) and the pairwise constant-disequality edges.
    /// That is a real bug, and it loses conflicts — the false-`sat` direction.
    ///
    /// Turning it on measurably closes those (see
    /// `corpus-triage/434-*.smt2`), and measurably OPENS a false-`unsat`:
    /// re-enabling the merge in later rounds makes the solver refute
    /// satisfiable scripts that `z3` and `cvc5` both call `sat` — reproduced
    /// down to a script with no case split and no quantifiers, where the only
    /// ingredient is asserting a valid clause AFTER a `(check-sat)` and
    /// re-solving. The merge is recorded in the EUF proof forest with a
    /// PLACEHOLDER reason (the merged term, which has no SAT variable), so a
    /// conflict explained through that edge produces a clause the theory does
    /// not entail. Widening the clause at the two MBC conflict sites does not
    /// cover a conflict detected anywhere else, and an attempt to attach a
    /// per-edge justification did not close the repro either.
    ///
    /// The design that closes #434 without this hazard asserts ACKERMANN
    /// lemmas — `(or (not (= a_i b_i)) ... (= (f a) (f b)))`, valid in FOL with
    /// equality and therefore independent of the model, the decision level and
    /// every value map — instead of merging. Until that lands, a completeness
    /// bug in the `sat` direction is strictly preferable to a false proof.
    pub persist_const_index: bool,
}

impl Default for SolverConfig {
    fn default() -> Self {
        Self::balanced()
    }
}

impl SolverConfig {
    /// Create a configuration optimized for speed (minimal preprocessing)
    /// Best for easy problems or when quick results are needed
    #[must_use]
    pub fn fast() -> Self {
        Self {
            timeout_ms: 0,
            parallel: false,
            num_threads: 4,
            proof: false,
            model: true,
            theory_mode: TheoryMode::Eager,
            simplify: true, // Keep basic simplification
            max_conflicts: 0,
            max_decisions: 0,
            restart_strategy: RestartStrategy::Geometric, // Faster than Glucose
            enable_clause_minimization: true,             // Keep this, it's fast
            enable_clause_subsumption: false,             // Skip for speed
            enable_variable_elimination: false,           // Skip preprocessing
            variable_elimination_limit: 0,
            enable_blocked_clause_elimination: false, // Skip preprocessing
            enable_symmetry_breaking: false,
            enable_inprocessing: false, // No inprocessing for speed
            inprocessing_interval: 0,
            clean_mbqi: true,
            use_hooks_driver: true,
            ccfv_ematch: true,
            ccfv_model_compl: false,
            mbqi_additive_patterns: false,
            mbqi_instance_budget: 0,
            persist_const_index: false,
        }
    }

    /// Create a balanced configuration (default)
    /// Good balance between preprocessing and solving speed
    #[must_use]
    pub fn balanced() -> Self {
        Self {
            timeout_ms: 0,
            parallel: false,
            num_threads: 4,
            proof: false,
            model: true,
            theory_mode: TheoryMode::Eager,
            simplify: true,
            max_conflicts: 0,
            max_decisions: 0,
            restart_strategy: RestartStrategy::Glucose, // Adaptive restarts
            enable_clause_minimization: true,
            enable_clause_subsumption: true,
            enable_variable_elimination: true,
            variable_elimination_limit: 1000, // Conservative limit
            enable_blocked_clause_elimination: true,
            enable_symmetry_breaking: false, // Still expensive
            enable_inprocessing: true,
            inprocessing_interval: 10000,
            clean_mbqi: true,
            use_hooks_driver: true,
            ccfv_ematch: true,
            ccfv_model_compl: false,
            mbqi_additive_patterns: false,
            mbqi_instance_budget: 0,
            persist_const_index: false,
        }
    }

    /// Create a configuration optimized for hard problems
    /// Uses aggressive preprocessing and symmetry breaking
    #[must_use]
    pub fn thorough() -> Self {
        Self {
            timeout_ms: 0,
            parallel: false,
            num_threads: 4,
            proof: false,
            model: true,
            theory_mode: TheoryMode::Eager,
            simplify: true,
            max_conflicts: 0,
            max_decisions: 0,
            restart_strategy: RestartStrategy::Glucose,
            enable_clause_minimization: true,
            enable_clause_subsumption: true,
            enable_variable_elimination: true,
            variable_elimination_limit: 5000, // More aggressive
            enable_blocked_clause_elimination: true,
            enable_symmetry_breaking: true, // Enable for hard problems
            enable_inprocessing: true,
            inprocessing_interval: 5000, // More frequent inprocessing
            clean_mbqi: true,
            use_hooks_driver: true,
            ccfv_ematch: true,
            ccfv_model_compl: false,
            mbqi_additive_patterns: false,
            mbqi_instance_budget: 0,
            persist_const_index: false,
        }
    }

    /// Create a minimal configuration (almost all features disabled)
    /// Useful for debugging or when you want full control
    #[must_use]
    pub fn minimal() -> Self {
        Self {
            timeout_ms: 0,
            parallel: false,
            num_threads: 1,
            proof: false,
            model: true,
            theory_mode: TheoryMode::Lazy, // Lazy for minimal overhead
            simplify: false,
            max_conflicts: 0,
            max_decisions: 0,
            restart_strategy: RestartStrategy::Geometric,
            enable_clause_minimization: false,
            enable_clause_subsumption: false,
            enable_variable_elimination: false,
            variable_elimination_limit: 0,
            enable_blocked_clause_elimination: false,
            enable_symmetry_breaking: false,
            enable_inprocessing: false,
            inprocessing_interval: 0,
            clean_mbqi: true,
            use_hooks_driver: true,
            ccfv_ematch: true,
            ccfv_model_compl: false,
            mbqi_additive_patterns: false,
            mbqi_instance_budget: 0,
            persist_const_index: false,
        }
    }

    /// Enable proof generation
    #[must_use]
    pub fn with_proof(mut self) -> Self {
        self.proof = true;
        self
    }

    /// Set timeout in milliseconds
    #[must_use]
    pub fn with_timeout(mut self, timeout_ms: u64) -> Self {
        self.timeout_ms = timeout_ms;
        self
    }

    /// Set maximum number of conflicts
    #[must_use]
    pub fn with_max_conflicts(mut self, max_conflicts: u64) -> Self {
        self.max_conflicts = max_conflicts;
        self
    }

    /// Set maximum number of decisions
    #[must_use]
    pub fn with_max_decisions(mut self, max_decisions: u64) -> Self {
        self.max_decisions = max_decisions;
        self
    }

    /// Enable parallel solving
    #[must_use]
    pub fn with_parallel(mut self, num_threads: usize) -> Self {
        self.parallel = true;
        self.num_threads = num_threads;
        self
    }

    /// Set restart strategy
    #[must_use]
    pub fn with_restart_strategy(mut self, strategy: RestartStrategy) -> Self {
        self.restart_strategy = strategy;
        self
    }

    /// Set theory mode
    #[must_use]
    pub fn with_theory_mode(mut self, mode: TheoryMode) -> Self {
        self.theory_mode = mode;
        self
    }
}

/// Solver statistics
#[derive(Debug, Clone, Default)]
pub struct Statistics {
    /// Number of decisions made
    pub decisions: u64,
    /// Number of conflicts encountered
    pub conflicts: u64,
    /// Number of propagations performed
    pub propagations: u64,
    /// Number of restarts performed
    pub restarts: u64,
    /// Number of learned clauses
    pub learned_clauses: u64,
    /// Number of theory propagations
    pub theory_propagations: u64,
    /// Number of theory conflicts
    pub theory_conflicts: u64,
}

impl Statistics {
    /// Create new statistics with all counters set to zero
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Reset all statistics
    pub fn reset(&mut self) {
        *self = Self::default();
    }
}

/// A model (assignment to variables)
#[derive(Debug, Clone)]
pub struct Model {
    /// Variable assignments
    assignments: FxHashMap<TermId, TermId>,
}

impl Model {
    /// Create a new empty model
    #[must_use]
    pub fn new() -> Self {
        Self {
            assignments: FxHashMap::default(),
        }
    }

    /// Get the value of a term in the model
    #[must_use]
    pub fn get(&self, term: TermId) -> Option<TermId> {
        self.assignments.get(&term).copied()
    }

    /// Set a value in the model
    pub fn set(&mut self, term: TermId, value: TermId) {
        self.assignments.insert(term, value);
    }

    /// Minimize the model by removing redundant assignments
    /// Returns a new minimized model containing only essential assignments
    pub fn minimize(&self, essential_vars: &[TermId]) -> Model {
        let mut minimized = Model::new();

        // Only keep assignments for essential variables
        for &var in essential_vars {
            if let Some(&value) = self.assignments.get(&var) {
                minimized.set(var, value);
            }
        }

        minimized
    }

    /// Get the number of assignments in the model
    #[must_use]
    pub fn size(&self) -> usize {
        self.assignments.len()
    }

    /// Get the assignments map (for MBQI integration)
    #[must_use]
    pub fn assignments(&self) -> &FxHashMap<TermId, TermId> {
        &self.assignments
    }

    /// Evaluate a term in this model
    /// Returns the simplified/evaluated term
    pub fn eval(&self, term: TermId, manager: &mut TermManager) -> TermId {
        // First check if we have a direct assignment
        if let Some(val) = self.get(term) {
            return val;
        }

        // Otherwise, recursively evaluate based on term structure
        let Some(t) = manager.get(term).cloned() else {
            return term;
        };

        match t.kind {
            // Constants evaluate to themselves
            TermKind::True
            | TermKind::False
            | TermKind::IntConst(_)
            | TermKind::RealConst(_)
            | TermKind::BitVecConst { .. } => term,

            // Variables: look up in model or return the variable itself
            TermKind::Var(_) => self.get(term).unwrap_or(term),

            // Boolean operations
            TermKind::Not(arg) => {
                let arg_val = self.eval(arg, manager);
                if let Some(t) = manager.get(arg_val) {
                    match t.kind {
                        TermKind::True => manager.mk_false(),
                        TermKind::False => manager.mk_true(),
                        _ => manager.mk_not(arg_val),
                    }
                } else {
                    manager.mk_not(arg_val)
                }
            }

            TermKind::And(ref args) => {
                let mut eval_args = Vec::new();
                for &arg in args {
                    let val = self.eval(arg, manager);
                    if let Some(t) = manager.get(val) {
                        if matches!(t.kind, TermKind::False) {
                            return manager.mk_false();
                        }
                        if !matches!(t.kind, TermKind::True) {
                            eval_args.push(val);
                        }
                    } else {
                        eval_args.push(val);
                    }
                }
                if eval_args.is_empty() {
                    manager.mk_true()
                } else if eval_args.len() == 1 {
                    eval_args[0]
                } else {
                    manager.mk_and(eval_args)
                }
            }

            TermKind::Or(ref args) => {
                let mut eval_args = Vec::new();
                for &arg in args {
                    let val = self.eval(arg, manager);
                    if let Some(t) = manager.get(val) {
                        if matches!(t.kind, TermKind::True) {
                            return manager.mk_true();
                        }
                        if !matches!(t.kind, TermKind::False) {
                            eval_args.push(val);
                        }
                    } else {
                        eval_args.push(val);
                    }
                }
                if eval_args.is_empty() {
                    manager.mk_false()
                } else if eval_args.len() == 1 {
                    eval_args[0]
                } else {
                    manager.mk_or(eval_args)
                }
            }

            TermKind::Implies(lhs, rhs) => {
                let lhs_val = self.eval(lhs, manager);
                let rhs_val = self.eval(rhs, manager);

                if let Some(t) = manager.get(lhs_val) {
                    if matches!(t.kind, TermKind::False) {
                        return manager.mk_true();
                    }
                    if matches!(t.kind, TermKind::True) {
                        return rhs_val;
                    }
                }

                if let Some(t) = manager.get(rhs_val)
                    && matches!(t.kind, TermKind::True)
                {
                    return manager.mk_true();
                }

                manager.mk_implies(lhs_val, rhs_val)
            }

            TermKind::Ite(cond, then_br, else_br) => {
                let cond_val = self.eval(cond, manager);

                if let Some(t) = manager.get(cond_val) {
                    match t.kind {
                        TermKind::True => return self.eval(then_br, manager),
                        TermKind::False => return self.eval(else_br, manager),
                        _ => {}
                    }
                }

                let then_val = self.eval(then_br, manager);
                let else_val = self.eval(else_br, manager);
                manager.mk_ite(cond_val, then_val, else_val)
            }

            TermKind::Eq(lhs, rhs) => {
                let lhs_val = self.eval(lhs, manager);
                let rhs_val = self.eval(rhs, manager);

                if lhs_val == rhs_val {
                    return manager.mk_true();
                }

                // Simplify boolean equalities with constants:
                // x = true  => x
                // x = false => NOT x
                // true = x  => x
                // false = x => NOT x
                if let Some(lhs_term) = manager.get(lhs_val)
                    && lhs_term.sort == manager.sorts.bool_sort
                {
                    // Check if rhs is a boolean constant
                    if let Some(rhs_term) = manager.get(rhs_val) {
                        match rhs_term.kind {
                            TermKind::True => return lhs_val,
                            TermKind::False => return manager.mk_not(lhs_val),
                            _ => {}
                        }
                    }
                    // Check if lhs is a boolean constant
                    match lhs_term.kind {
                        TermKind::True => return rhs_val,
                        TermKind::False => return manager.mk_not(rhs_val),
                        _ => {}
                    }
                }

                manager.mk_eq(lhs_val, rhs_val)
            }

            // Arithmetic operations - basic constant folding
            TermKind::Neg(arg) => {
                let arg_val = self.eval(arg, manager);
                if let Some(t) = manager.get(arg_val) {
                    match &t.kind {
                        TermKind::IntConst(n) => return manager.mk_int(-n),
                        TermKind::RealConst(r) => return manager.mk_real(-r),
                        _ => {}
                    }
                }
                manager.mk_neg(arg_val)
            }

            TermKind::Add(ref args) => {
                let eval_args: Vec<_> = args.iter().map(|&a| self.eval(a, manager)).collect();
                manager.mk_add(eval_args)
            }

            TermKind::Sub(lhs, rhs) => {
                let lhs_val = self.eval(lhs, manager);
                let rhs_val = self.eval(rhs, manager);
                manager.mk_sub(lhs_val, rhs_val)
            }

            TermKind::Mul(ref args) => {
                let eval_args: Vec<_> = args.iter().map(|&a| self.eval(a, manager)).collect();
                manager.mk_mul(eval_args)
            }

            // For other operations, just return the term or look it up
            _ => self.get(term).unwrap_or(term),
        }
    }
}

impl Default for Model {
    fn default() -> Self {
        Self::new()
    }
}

impl Model {
    /// Pretty print the model in SMT-LIB2 format
    #[cfg(feature = "std")]
    pub fn pretty_print(&self, manager: &TermManager) -> String {
        if self.assignments.is_empty() {
            return "(model)".to_string();
        }

        let mut lines = vec!["(model".to_string()];
        let printer = oxiz_core::smtlib::Printer::new(manager);

        for (&var, &value) in &self.assignments {
            if let Some(term) = manager.get(var) {
                // Only print top-level variables, not internal encoding variables
                if let TermKind::Var(name) = &term.kind {
                    let sort_str = Self::format_sort(term.sort, manager);
                    let value_str = printer.print_term(value);
                    // Use Debug format for the symbol name
                    let name_str = format!("{:?}", name);
                    lines.push(format!(
                        "  (define-fun {} () {} {})",
                        name_str, sort_str, value_str
                    ));
                }
            }
        }
        lines.push(")".to_string());
        lines.join("\n")
    }

    /// Format a sort ID to its SMT-LIB2 representation
    fn format_sort(sort: oxiz_core::sort::SortId, manager: &TermManager) -> String {
        if sort == manager.sorts.bool_sort {
            "Bool".to_string()
        } else if sort == manager.sorts.int_sort {
            "Int".to_string()
        } else if sort == manager.sorts.real_sort {
            "Real".to_string()
        } else if let Some(s) = manager.sorts.get(sort) {
            if let Some(w) = s.bitvec_width() {
                format!("(_ BitVec {})", w)
            } else {
                "Unknown".to_string()
            }
        } else {
            "Unknown".to_string()
        }
    }
}

/// A named assertion for unsat core tracking
#[derive(Debug, Clone)]
pub struct NamedAssertion {
    /// The assertion term (kept for potential future use in minimization)
    #[allow(dead_code)]
    pub term: TermId,
    /// The name (if any)
    pub name: Option<String>,
    /// Index of this assertion
    pub index: u32,
}

/// An unsat core - a minimal set of assertions that are unsatisfiable
#[derive(Debug, Clone)]
pub struct UnsatCore {
    /// The names of assertions in the core
    pub names: Vec<String>,
    /// The indices of assertions in the core
    pub indices: Vec<u32>,
}

impl UnsatCore {
    /// Create a new empty unsat core
    #[must_use]
    pub fn new() -> Self {
        Self {
            names: Vec::new(),
            indices: Vec::new(),
        }
    }

    /// Check if the core is empty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.indices.is_empty()
    }

    /// Get the number of assertions in the core
    #[must_use]
    pub fn len(&self) -> usize {
        self.indices.len()
    }
}

impl Default for UnsatCore {
    fn default() -> Self {
        Self::new()
    }
}

/// Cached FP constraint data for a single assertion term.
#[derive(Debug, Clone)]
pub struct FpConstraintData {
    pub additions: Vec<(TermId, TermId, TermId, TermId, RoundingMode)>,
    pub divisions: Vec<(TermId, TermId, TermId, TermId, RoundingMode)>,
    pub multiplications: Vec<(TermId, TermId, TermId, TermId, RoundingMode)>,
    pub comparisons: Vec<(TermId, TermId, bool)>,
    pub equalities: Vec<(TermId, TermId)>,
    pub literals: FxHashMap<TermId, f64>,
    pub rounding_add_results: FxHashMap<(TermId, TermId, RoundingMode), TermId>,
    pub is_zero: FxHashSet<TermId>,
    pub is_positive: FxHashSet<TermId>,
    pub is_negative: FxHashSet<TermId>,
    pub not_nan: FxHashSet<TermId>,
    pub gt_comparisons: Vec<(TermId, TermId)>,
    pub lt_comparisons: Vec<(TermId, TermId)>,
    pub conversions: Vec<(TermId, u32, u32, TermId)>,
    pub real_to_fp_conversions: Vec<(TermId, u32, u32, TermId)>,
    pub subtractions: Vec<(TermId, TermId, TermId)>,
}

impl FpConstraintData {
    #[must_use]
    pub fn new() -> Self {
        Self {
            additions: Vec::new(),
            divisions: Vec::new(),
            multiplications: Vec::new(),
            comparisons: Vec::new(),
            equalities: Vec::new(),
            literals: FxHashMap::default(),
            rounding_add_results: FxHashMap::default(),
            is_zero: FxHashSet::default(),
            is_positive: FxHashSet::default(),
            is_negative: FxHashSet::default(),
            not_nan: FxHashSet::default(),
            gt_comparisons: Vec::new(),
            lt_comparisons: Vec::new(),
            conversions: Vec::new(),
            real_to_fp_conversions: Vec::new(),
            subtractions: Vec::new(),
        }
    }

    #[must_use]
    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.additions.is_empty()
            && self.divisions.is_empty()
            && self.multiplications.is_empty()
            && self.comparisons.is_empty()
            && self.equalities.is_empty()
    }

    pub fn merge(&mut self, other: &FpConstraintData) {
        self.additions.extend_from_slice(&other.additions);
        self.divisions.extend_from_slice(&other.divisions);
        self.multiplications
            .extend_from_slice(&other.multiplications);
        self.comparisons.extend_from_slice(&other.comparisons);
        self.equalities.extend_from_slice(&other.equalities);
        for (&k, &v) in &other.literals {
            self.literals.insert(k, v);
        }
        for (&k, &v) in &other.rounding_add_results {
            self.rounding_add_results.insert(k, v);
        }
        self.is_zero.extend(other.is_zero.iter().copied());
        self.is_positive.extend(other.is_positive.iter().copied());
        self.is_negative.extend(other.is_negative.iter().copied());
        self.not_nan.extend(other.not_nan.iter().copied());
        self.gt_comparisons.extend_from_slice(&other.gt_comparisons);
        self.lt_comparisons.extend_from_slice(&other.lt_comparisons);
        self.conversions.extend_from_slice(&other.conversions);
        self.real_to_fp_conversions
            .extend_from_slice(&other.real_to_fp_conversions);
        self.subtractions.extend_from_slice(&other.subtractions);
    }
}

impl Default for FpConstraintData {
    fn default() -> Self {
        Self::new()
    }
}

/// Lazy model evaluation cache.
#[derive(Debug)]
#[allow(dead_code)]
pub struct ModelCache {
    model: Model,
    eval_cache: FxHashMap<TermId, TermId>,
    cache_hits: u64,
    cache_misses: u64,
}

#[allow(dead_code)]
impl ModelCache {
    #[must_use]
    pub fn new(model: Model) -> Self {
        Self {
            model,
            eval_cache: FxHashMap::default(),
            cache_hits: 0,
            cache_misses: 0,
        }
    }

    #[must_use]
    pub fn model(&self) -> &Model {
        &self.model
    }

    #[must_use]
    pub fn get_direct(&self, term: TermId) -> Option<TermId> {
        self.model.get(term)
    }

    pub fn eval_lazy(&mut self, term: TermId, manager: &mut TermManager) -> TermId {
        if let Some(&cached) = self.eval_cache.get(&term) {
            self.cache_hits += 1;
            return cached;
        }
        self.cache_misses += 1;
        let result = self.model.eval(term, manager);
        self.eval_cache.insert(term, result);
        result
    }

    pub fn eval_batch(
        &mut self,
        terms: &[TermId],
        manager: &mut TermManager,
    ) -> SmallVec<[TermId; 8]> {
        terms
            .iter()
            .map(|&t| {
                if let Some(&cached) = self.eval_cache.get(&t) {
                    self.cache_hits += 1;
                    cached
                } else {
                    self.cache_misses += 1;
                    let result = self.model.eval(t, manager);
                    self.eval_cache.insert(t, result);
                    result
                }
            })
            .collect()
    }

    pub fn invalidate(&mut self) {
        self.eval_cache.clear();
    }

    pub fn invalidate_term(&mut self, term: TermId) {
        self.eval_cache.remove(&term);
    }

    #[must_use]
    pub fn cache_stats(&self) -> (u64, u64) {
        (self.cache_hits, self.cache_misses)
    }

    #[must_use]
    pub fn cache_size(&self) -> usize {
        self.eval_cache.len()
    }

    #[must_use]
    pub fn model_size(&self) -> usize {
        self.model.size()
    }

    #[must_use]
    pub fn is_cached(&self, term: TermId) -> bool {
        self.eval_cache.contains_key(&term)
    }

    #[must_use]
    pub fn into_model(self) -> Model {
        self.model
    }
}

#[cfg(test)]
mod satlevel_tests {
    use super::{SatLevel, SolverResult};
    use SatLevel::{DefiniteSat, DefiniteUnsat, PossiblySat, PossiblyUnsat, Unknown};

    #[test]
    fn collapse_only_definite_poles_surface() {
        assert_eq!(DefiniteSat.collapse(), SolverResult::Sat);
        assert_eq!(DefiniteUnsat.collapse(), SolverResult::Unsat);
        assert_eq!(PossiblySat.collapse(), SolverResult::Unknown);
        assert_eq!(PossiblyUnsat.collapse(), SolverResult::Unknown);
        assert_eq!(Unknown.collapse(), SolverResult::Unknown);
    }

    #[test]
    fn full_str_is_uncollapsed() {
        assert_eq!(DefiniteSat.as_full_str(), "definite-sat");
        assert_eq!(PossiblySat.as_full_str(), "possibly-sat");
        assert_eq!(Unknown.as_full_str(), "unknown");
        assert_eq!(PossiblyUnsat.as_full_str(), "possibly-unsat");
        assert_eq!(DefiniteUnsat.as_full_str(), "definite-unsat");
    }

    #[test]
    fn meet_unknown_is_identity() {
        for x in [DefiniteSat, PossiblySat, Unknown, PossiblyUnsat, DefiniteUnsat] {
            assert_eq!(Unknown.meet(x), x);
            assert_eq!(x.meet(Unknown), x);
        }
    }

    #[test]
    fn meet_is_commutative_and_idempotent() {
        let all = [DefiniteSat, PossiblySat, Unknown, PossiblyUnsat, DefiniteUnsat];
        for a in all {
            assert_eq!(a.meet(a), a);
            for b in all {
                assert_eq!(a.meet(b), b.meet(a), "meet not commutative for {a:?},{b:?}");
            }
        }
    }

    #[test]
    fn meet_confirmed_pole_dominates_any_guess() {
        // a confirmed model is ground truth, even against the opposite guess
        assert_eq!(DefiniteSat.meet(PossiblySat), DefiniteSat);
        assert_eq!(DefiniteSat.meet(PossiblyUnsat), DefiniteSat);
        assert_eq!(DefiniteUnsat.meet(PossiblyUnsat), DefiniteUnsat);
        assert_eq!(DefiniteUnsat.meet(PossiblySat), DefiniteUnsat);
    }

    #[test]
    fn meet_never_upgrades_two_guesses() {
        // two unconfirmed guesses can never manufacture a Definite pole
        assert_eq!(PossiblySat.meet(PossiblyUnsat), Unknown);
        assert!(!PossiblySat.meet(PossiblySat).is_definite());
        assert!(!PossiblyUnsat.meet(PossiblyUnsat).is_definite());
        assert_eq!(PossiblySat.meet(PossiblySat), PossiblySat);
        assert_eq!(PossiblyUnsat.meet(PossiblyUnsat), PossiblyUnsat);
    }
}
