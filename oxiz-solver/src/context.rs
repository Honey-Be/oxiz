//! Solver context

#[allow(unused_imports)]
use crate::prelude::*;
use crate::solver::{OutputMode, SatLevel, Solver, SolverResult};
use oxiz_core::ast::{TermId, TermKind, TermManager};
#[cfg(feature = "std")]
use oxiz_core::error::Result;
#[cfg(feature = "std")]
use oxiz_core::smtlib::{Command, ParserEnv, parse_script_with_env};
use oxiz_core::sort::{SortId, SortKind};
#[cfg(feature = "std")]
use std::path::{Path, PathBuf};

/// Raw function interpretation: a list of `(arg_strings, value_string)` entries
/// together with an `else_value` string and the function arity.
///
/// Used as the return type of [`Context::get_func_interp_raw`] to avoid pulling
/// `oxiz_core::model` types into the public API of this file.
pub type RawFuncInterp = (Vec<(Vec<String>, String)>, String, usize);

/// Whether `t` (or any subterm, including under quantifiers) contains an
/// arithmetic operator the theory layer does NOT decide — integer `div`/`mod`,
/// or one of the Int/Real conversion ops the parser keeps uninterpreted (`abs`,
/// `to_real`, `to_int`, `is_int`). Each reaches EUF/arith as a free
/// over-approximation, so a `Sat` resting on one is untrustworthy and
/// [`Context::check_sat`] downgrades it to the sound `Unknown` (see there).
/// `visited` dedups the hash-consed DAG so a shared subterm is walked once.
fn term_contains_undecided_op(
    terms: &TermManager,
    t: TermId,
    visited: &mut std::collections::HashSet<TermId>,
) -> bool {
    if !visited.insert(t) {
        return false;
    }
    let Some(term) = terms.get(t) else { return false };
    match &term.kind {
        TermKind::Div(..) | TermKind::Mod(..) => return true,
        // `((_ divisible n) x)` desugars to `(= (mod x n) 0)`, so it is caught by
        // the `Mod` arm above — only the non-desugarable conversion ops, parsed
        // as uninterpreted applications, need a name check here.
        TermKind::Apply { func, .. }
            if matches!(terms.resolve_str(*func), "abs" | "to_real" | "to_int" | "is_int") =>
        {
            return true;
        }
        _ => {}
    }
    // Recurse through the CANONICAL complete child enumeration. (The earlier
    // `clean_mbqi::subterms` walk skipped `Let`/String/FP/BV/`Dt*` kinds via its
    // `_ => Vec::new()` catch-all, so an op hidden under e.g. a `let` escaped the
    // downgrade and a `Sat` resting on it leaked — adversarially confirmed. The
    // `get_children` enumeration descends into let bindings + body and every
    // other wrapper, so the downgrade is now coverage-complete.)
    oxiz_core::ast::get_children(&term.kind)
        .into_iter()
        .any(|c| term_contains_undecided_op(terms, c, visited))
}

/// A declared constant
#[derive(Debug, Clone)]
struct DeclaredConst {
    /// The term ID for this constant
    term: TermId,
    /// The sort of this constant
    sort: SortId,
    /// The name of this constant
    name: String,
}

/// A declared function
#[derive(Debug, Clone)]
struct DeclaredFun {
    /// The function name
    name: String,
    /// Argument sorts
    arg_sorts: Vec<SortId>,
    /// Return sort
    ret_sort: SortId,
}

/// Solver context for managing the solving process
///
/// The `Context` provides a high-level API for SMT solving, similar to
/// the SMT-LIB2 standard. It manages declarations, assertions, and solver state.
///
/// # Examples
///
/// ## Basic Usage
///
/// ```
/// use oxiz_solver::Context;
///
/// let mut ctx = Context::new();
/// ctx.set_logic("QF_UF");
///
/// // Declare boolean constants
/// let p = ctx.declare_const("p", ctx.terms.sorts.bool_sort);
/// let q = ctx.declare_const("q", ctx.terms.sorts.bool_sort);
///
/// // Assert p AND q
/// let formula = ctx.terms.mk_and(vec![p, q]);
/// ctx.assert(formula);
///
/// // Check satisfiability
/// ctx.check_sat();
/// ```
///
/// ## SMT-LIB2 Script Execution
///
/// ```
/// use oxiz_solver::Context;
///
/// let mut ctx = Context::new();
///
/// let script = r#"
/// (set-logic QF_LIA)
/// (declare-const x Int)
/// (assert (>= x 0))
/// (assert (<= x 10))
/// (check-sat)
/// "#;
///
/// let _ = ctx.execute_script(script);
/// ```
#[derive(Debug)]
pub struct Context {
    /// Term manager
    pub terms: TermManager,
    /// Solver instance
    solver: Solver,
    /// Current logic
    logic: Option<String>,
    /// Assertions
    assertions: Vec<TermId>,
    /// Assertion stack for push/pop
    assertion_stack: Vec<usize>,
    /// Declared constants
    declared_consts: Vec<DeclaredConst>,
    /// Declared constants stack for push/pop
    const_stack: Vec<usize>,
    /// Mapping from constant names to indices (for efficient removal)
    const_name_to_index: crate::prelude::HashMap<String, usize>,
    /// Declared functions
    declared_funs: Vec<DeclaredFun>,
    /// Declared functions stack for push/pop
    fun_stack: Vec<usize>,
    /// Mapping from function names to indices
    fun_name_to_index: crate::prelude::HashMap<String, usize>,
    /// Last check-sat result (the collapsed 3-valued verdict).
    last_result: Option<SolverResult>,
    /// Last check-sat verdict at full 5-level resolution (un-collapsed), used to
    /// render the `Full` output mode and queryable via [`Context::last_level`].
    last_level: Option<SatLevel>,
    /// How `(check-sat)` renders its verdict (z3-compatible by default).
    output_mode: OutputMode,
    /// Persistent parser symbol tables (declared funcs / consts / sorts /
    /// defined funcs / datatype constructors), carried across `execute_script`
    /// calls so that a function's declared sort is known on every command even
    /// when a front-end feeds them one at a time (streaming stdin, embedded
    /// per-command replay).  Without this a later `(f x)` defaults to `Bool`
    /// and theory reasoning over it silently breaks.
    parser_env: ParserEnv,
    /// Options
    options: crate::prelude::HashMap<String, String>,
    /// Optional path for binary proof logging.
    ///
    /// When set, `check_sat` creates a `ProofLogger` at this path, records
    /// proof steps derived from the solver result, and flushes/closes the log
    /// before returning.
    #[cfg(feature = "std")]
    proof_log_path: Option<PathBuf>,
}

impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
}

impl Context {
    /// Create a new context
    #[must_use]
    pub fn new() -> Self {
        Self {
            terms: TermManager::new(),
            solver: Solver::new(),
            logic: None,
            assertions: Vec::new(),
            assertion_stack: Vec::new(),
            declared_consts: Vec::new(),
            const_stack: Vec::new(),
            const_name_to_index: crate::prelude::HashMap::new(),
            declared_funs: Vec::new(),
            fun_stack: Vec::new(),
            fun_name_to_index: crate::prelude::HashMap::new(),
            last_result: None,
            last_level: None,
            output_mode: OutputMode::default(),
            parser_env: ParserEnv::default(),
            options: crate::prelude::HashMap::new(),
            #[cfg(feature = "std")]
            proof_log_path: None,
        }
    }

    /// Configure a path for binary proof logging.
    ///
    /// When a path is configured, every subsequent call to `check_sat` opens a
    /// [`oxiz_proof::logging::ProofLogger`] at that path, writes a structural
    /// summary of the proof, and flushes/closes the log before returning.
    /// Pass `None` to disable proof logging.
    #[cfg(feature = "std")]
    pub fn set_proof_log_path(&mut self, path: Option<PathBuf>) {
        self.proof_log_path = path;
    }

    /// Return the currently configured proof log path, if any.
    #[cfg(feature = "std")]
    #[must_use]
    pub fn proof_log_path(&self) -> Option<&Path> {
        self.proof_log_path.as_deref()
    }

    /// Verify a binary proof log produced by a previous `check_sat` call with
    /// proof logging enabled.
    ///
    /// Delegates to [`oxiz_proof::replay::ProofReplayer::replay_from_file`].
    ///
    /// # Errors
    ///
    /// Returns `Err` only for hard I/O or binary-format failures; logical
    /// invalidity is encoded as `Ok(VerificationResult::Invalid(_))`.
    #[cfg(feature = "std")]
    pub fn verify_proof_log(
        path: &Path,
    ) -> std::result::Result<oxiz_proof::replay::VerificationResult, oxiz_proof::replay::ProofError>
    {
        oxiz_proof::replay::ProofReplayer::replay_from_file(path)
    }

    /// Declare a constant
    pub fn declare_const(&mut self, name: &str, sort: SortId) -> TermId {
        let term = self.terms.mk_var(name, sort);
        let index = self.declared_consts.len();
        self.declared_consts.push(DeclaredConst {
            term,
            sort,
            name: name.to_string(),
        });
        self.const_name_to_index.insert(name.to_string(), index);
        term
    }

    /// Declare a function
    ///
    /// Registers a function signature in the context. For nullary functions (constants),
    /// use `declare_const` instead.
    pub fn declare_fun(&mut self, name: &str, arg_sorts: Vec<SortId>, ret_sort: SortId) {
        let index = self.declared_funs.len();
        self.declared_funs.push(DeclaredFun {
            name: name.to_string(),
            arg_sorts,
            ret_sort,
        });
        self.fun_name_to_index.insert(name.to_string(), index);
    }

    /// Get function signature if it exists
    pub fn get_fun_signature(&self, name: &str) -> Option<(Vec<SortId>, SortId)> {
        self.fun_name_to_index.get(name).and_then(|&idx| {
            self.declared_funs
                .get(idx)
                .map(|f| (f.arg_sorts.clone(), f.ret_sort))
        })
    }

    /// Iterate over the names of all currently declared uninterpreted functions.
    pub fn declared_function_names(&self) -> impl Iterator<Item = &str> {
        self.declared_funs.iter().map(|d| d.name.as_str())
    }

    /// Set the logic
    pub fn set_logic(&mut self, logic: &str) {
        self.logic = Some(logic.to_string());
        self.solver.set_logic(logic);
    }

    /// Get the current logic
    #[must_use]
    pub fn logic(&self) -> Option<&str> {
        self.logic.as_deref()
    }

    /// Add an assertion
    pub fn assert(&mut self, term: TermId) {
        self.assertions.push(term);
        self.solver.assert(term, &mut self.terms);
    }

    /// Check satisfiability — the collapsed 3-valued verdict (z3-compatible). For
    /// the un-collapsed 5-level verdict use [`check_sat_level`].
    ///
    /// [`check_sat_level`]: Context::check_sat_level
    pub fn check_sat(&mut self) -> SolverResult {
        self.check_sat_level().collapse()
    }

    /// Check satisfiability, returning the full internal [`SatLevel`] WITHOUT
    /// collapsing to 3 values. The solver keeps the confirmed/unconfirmed grade
    /// to this boundary; the only reduction to `sat`/`unsat`/`unknown` is the
    /// caller's [`SatLevel::collapse`] (z3-compatible mode), or none at all
    /// (`Full` mode). Also records [`last_level`] and the collapsed
    /// [`last_result`].
    ///
    /// [`last_level`]: Context::last_level
    /// [`last_result`]: Context::last_result
    pub fn check_sat_level(&mut self) -> SatLevel {
        let mut level = self.solver.check_level(&mut self.terms);
        // SOUNDNESS — undecided-op downgrade. Integer `div`/`mod` and the Int/Real
        // conversion ops `abs`/`to_real`/`to_int`/`is_int` are NOT decided by the
        // theory layer (they reach EUF/arith as uninterpreted applications); a
        // model is free to assign them arbitrary values, so the solved formula is
        // an OVER-approximation of the real one. By the soundness asymmetry
        // (dropping/weakening a constraint preserves `unsat` but can fabricate
        // `sat`), an `Unsat` here is still sound, but a confirmed `DefiniteSat` is
        // untrustworthy — it may rest on an op value the real semantics forbid.
        // Downgrade it to the unconfirmed `PossiblySat` (which collapses to the
        // sound `unknown`, and surfaces as `possibly-sat` in full mode). (Verified:
        // `oxiz-undecided-op-verification` — abstraction monotonicity ⇒
        // relaxed-UNSAT implies concrete-UNSAT, and the converse fails, e.g.
        // `(< (abs x) 0)` is UNSAT yet its uninterpreted relaxation `r < 0` is SAT
        // — exactly the case this downgrade catches.) Deciding constant/linear
        // div/mod via the Euclidean axioms, `abs` via its `ite` definition, etc. is
        // the completeness follow-up.
        if level == SatLevel::DefiniteSat {
            let mut visited = std::collections::HashSet::new();
            if self
                .assertions
                .iter()
                .any(|&a| term_contains_undecided_op(&self.terms, a, &mut visited))
            {
                level = SatLevel::PossiblySat;
            }
        }
        self.last_level = Some(level);
        let result = level.collapse();
        self.last_result = Some(result);

        // Write a binary proof log if a path is configured (std-only).
        #[cfg(feature = "std")]
        if let Some(ref path) = self.proof_log_path.clone() {
            if let Err(e) = self.write_proof_log(path, result) {
                // Non-fatal: warn but do not abort the solve.
                #[cfg(feature = "tracing")]
                tracing::warn!("proof log write failed for {:?}: {}", path, e);
                let _ = e;
            }
        }

        level
    }

    /// The collapsed result of the most recent `(check-sat)`, if any.
    #[must_use]
    pub fn last_result(&self) -> Option<SolverResult> {
        self.last_result
    }

    /// The full un-collapsed [`SatLevel`] of the most recent `(check-sat)`, if
    /// any — the verdict the `Full` output mode renders.
    #[must_use]
    pub fn last_level(&self) -> Option<SatLevel> {
        self.last_level
    }

    /// Set how `(check-sat)` renders its verdict (the in-process control for the
    /// output mode; the CLI exposes `--output-mode` and the
    /// `:oxiz.output-mode` option).
    pub fn set_output_mode(&mut self, mode: OutputMode) {
        self.output_mode = mode;
    }

    /// The current output mode.
    #[must_use]
    pub fn output_mode(&self) -> OutputMode {
        self.output_mode
    }

    /// Render a `(check-sat)` verdict per the active output mode: the collapsed
    /// `sat`/`unsat`/`unknown` (z3-compatible) or the un-collapsed 5-level token
    /// (`Full` — `definite-sat`/`possibly-sat`/`unknown`/`possibly-unsat`/
    /// `definite-unsat`).
    fn render_verdict(&self, level: SatLevel) -> String {
        match self.output_mode {
            OutputMode::Z3Compatible => match level.collapse() {
                SolverResult::Sat => "sat",
                SolverResult::Unsat => "unsat",
                SolverResult::Unknown => "unknown",
            }
            .to_string(),
            OutputMode::Full => level.as_full_str().to_string(),
        }
    }

    /// Serialise a proof log entry for the given result.
    ///
    /// For `Unsat`, resolution proof steps are emitted when available;
    /// for `Sat` and `Unknown`, a single axiom node is written so the log is
    /// never empty and can be cleanly replayed.
    #[cfg(feature = "std")]
    fn write_proof_log(
        &self,
        path: &Path,
        result: SolverResult,
    ) -> std::result::Result<(), oxiz_proof::logging::LoggingError> {
        use oxiz_proof::logging::ProofLogger;
        use oxiz_proof::proof::{ProofNodeId, ProofStep};
        use smallvec::SmallVec;

        let mut logger = ProofLogger::create(path)?;

        match result {
            SolverResult::Unsat => {
                if let Some(proof) = self.solver.get_proof() {
                    let mut counter: u32 = 0;
                    for step in proof.steps() {
                        let entry = match step {
                            crate::solver::ProofStep::Input { index, .. } => ProofStep::Axiom {
                                conclusion: format!("input-clause-{}", index),
                            },
                            crate::solver::ProofStep::Resolution {
                                index,
                                left,
                                right,
                                pivot,
                                ..
                            } => {
                                let mut premises: SmallVec<[ProofNodeId; 4]> = SmallVec::new();
                                premises.push(ProofNodeId(*left));
                                premises.push(ProofNodeId(*right));
                                let mut args: SmallVec<[String; 2]> = SmallVec::new();
                                args.push(format!("{:?}", pivot));
                                ProofStep::Inference {
                                    rule: "resolution".to_string(),
                                    premises,
                                    conclusion: format!("resolution-{}", index),
                                    args,
                                }
                            }
                            crate::solver::ProofStep::TheoryLemma { index, theory, .. } => {
                                ProofStep::Axiom {
                                    conclusion: format!("theory-lemma-{}-{}", theory, index),
                                }
                            }
                        };
                        logger.log_step(ProofNodeId(counter), &entry)?;
                        counter += 1;
                    }
                    if counter == 0 {
                        // Proof object present but empty — emit minimal witness.
                        logger.log_step(
                            ProofNodeId(0),
                            &ProofStep::Axiom {
                                conclusion: "unsat".to_string(),
                            },
                        )?;
                    }
                } else {
                    logger.log_step(
                        ProofNodeId(0),
                        &ProofStep::Axiom {
                            conclusion: "unsat".to_string(),
                        },
                    )?;
                }
            }
            SolverResult::Sat => {
                logger.log_step(
                    ProofNodeId(0),
                    &ProofStep::Axiom {
                        conclusion: "sat".to_string(),
                    },
                )?;
            }
            SolverResult::Unknown => {
                logger.log_step(
                    ProofNodeId(0),
                    &ProofStep::Axiom {
                        conclusion: "unknown".to_string(),
                    },
                )?;
            }
        }

        logger.flush()?;
        logger.close()
    }

    /// Evaluate a `term` in the current model.
    ///
    /// Returns `None` if no model is available (i.e. the last `check_sat` did
    /// not return `Sat`).  Otherwise, calls `Model::eval` which traverses the
    /// term structure, substituting variables with their model values, and
    /// returns the simplified/concrete `TermId`.
    ///
    /// The returned `TermId` belongs to `self.terms` — the same `TermManager`
    /// owned by this `Context`.
    pub fn eval_in_model(&mut self, term: TermId) -> Option<TermId> {
        if self.last_result != Some(SolverResult::Sat) {
            return None;
        }
        let value = self.solver.model()?.eval(term, &mut self.terms);
        Some(value)
    }

    /// Get the model (if SAT)
    /// Returns a list of (name, sort, value) tuples
    pub fn get_model(&self) -> Option<Vec<(String, String, String)>> {
        if self.last_result != Some(SolverResult::Sat) {
            return None;
        }

        let mut model = Vec::new();
        let solver_model = self.solver.model()?;

        for decl in &self.declared_consts {
            let value = if let Some(val) = solver_model.get(decl.term) {
                self.format_value(val)
            } else {
                // Default value based on sort
                self.default_value(decl.sort)
            };
            let sort_name = self.format_sort_name(decl.sort);
            model.push((decl.name.clone(), sort_name, value));
        }

        Some(model)
    }

    /// Build a raw function interpretation for a declared uninterpreted function.
    ///
    /// Derives entries from the EUF congruence closure rather than from raw
    /// `Apply` terms alone.  For every application `f(a1, …, an)` interned in the
    /// E-graph, the arguments and the result are canonicalized through their
    /// equivalence-class representatives, so:
    ///
    /// - Two applications whose arguments are pairwise congruent (e.g. `f(a)` and
    ///   `f(b)` when `a = b` is implied by the assertions) collapse to a **single**
    ///   entry keyed by the shared argument class.
    /// - The reported argument and result strings are **model values** taken from
    ///   the class (resolving through the representative), not raw term ids.
    /// - When an application has no direct model value, the value of any congruent
    ///   member of its class is used.
    ///
    /// `else_value` is chosen as the most frequently occurring entry value (ties
    /// broken by first occurrence), mirroring how Z3 selects a default; if there
    /// are no entries it falls back to the return sort's default value.
    ///
    /// Returns `None` when:
    /// - the last check was not `Sat`, or
    /// - no model is available, or
    /// - `func_name` is not a declared function.
    ///
    /// The return type is `(entries, else_value_string, arity)` to avoid
    /// pulling `oxiz_core::model` types into this file.
    pub fn get_func_interp_raw(&self, func_name: &str) -> Option<RawFuncInterp> {
        if self.last_result != Some(SolverResult::Sat) {
            return None;
        }
        let solver_model = self.solver.model()?;

        // Find the declared function so we know its arity and default sort.
        let decl = self.declared_funs.iter().find(|d| d.name == func_name)?;
        let arity = decl.arg_sorts.len();
        let default_else = self.default_value(decl.ret_sort);

        // Resolve `func_name` to the EUF function-symbol id.  For an `Apply`
        // term the EUF id is the underlying value of the function-name `Spur`,
        // so we recover it from any matching application term (read-only — no
        // mutable interner access required).
        let mut func_id: Option<u32> = None;
        for idx in 0..(self.terms.len() as u32) {
            let tid = TermId(idx);
            let Some(term) = self.terms.get(tid) else {
                continue;
            };
            if let TermKind::Apply {
                func: func_spur, ..
            } = &term.kind
                && self.terms.resolve_str(*func_spur) == func_name
            {
                func_id = Some(func_spur.into_inner().get());
                break;
            }
        }

        // No application of this function exists in the E-graph: the function is
        // declared but never applied, so its interpretation is purely the default.
        let Some(func_id) = func_id else {
            return Some((Vec::new(), default_else, arity));
        };

        // Pull congruence-closed application entries from the EUF solver.  Each
        // entry already has its argument and result classes canonicalized, so
        // congruence (e.g. f(a) == f(b) when a == b) is applied for us.
        let euf_entries = self.solver.euf_function_entries(func_id);

        // Deduplicate on the canonical argument-class representative tuple so
        // congruent applications produce exactly one entry.  Because congruence
        // forces congruent applications into the same result class, the values
        // agree in a consistent model.
        let mut seen_arg_keys: crate::prelude::HashSet<smallvec::SmallVec<[u32; 4]>> =
            crate::prelude::HashSet::new();
        let mut entries: Vec<(Vec<String>, String)> = Vec::new();
        for entry in &euf_entries {
            // Resolve the result value first: skip applications whose class has
            // no concrete model value (an unconstrained application contributes
            // nothing observable beyond the else-branch).
            let Some(val_str) = self.class_value_string(&entry.result_class_terms, solver_model)
            else {
                continue;
            };

            if !seen_arg_keys.insert(entry.arg_reps.clone()) {
                continue; // already emitted this congruence class of arguments
            }

            // Resolve each argument to its canonical model value.  Falls back to
            // the default value for the corresponding argument sort when the
            // class carries no concrete value (rare: an unconstrained argument).
            let arg_strs: Vec<String> = entry
                .arg_class_terms
                .iter()
                .enumerate()
                .map(|(i, members)| {
                    self.class_value_string(members, solver_model)
                        .unwrap_or_else(|| {
                            decl.arg_sorts
                                .get(i)
                                .map_or_else(|| "?".to_string(), |&s| self.default_value(s))
                        })
                })
                .collect();
            entries.push((arg_strs, val_str));
        }

        // Pick `else_value`: the most common entry value (ties → first seen),
        // matching Z3's habit of reusing an existing value as the default.
        let else_value = Self::most_common_value(&entries).unwrap_or(default_else);

        Some((entries, else_value, arity))
    }

    /// Resolve an equivalence class (its member `TermId`s) to a formatted model
    /// value string, by finding the first member that carries either a direct
    /// model assignment or is itself a literal constant.
    ///
    /// Returns `None` when no member of the class has an observable value.
    fn class_value_string(
        &self,
        members: &[TermId],
        solver_model: &crate::solver::Model,
    ) -> Option<String> {
        for &member in members {
            // Direct model assignment (covers variables and applications whose
            // value was extracted from an equality constraint).
            if let Some(val_term) = solver_model.get(member) {
                return Some(self.format_value(val_term));
            }
            // The member may itself be a literal constant (e.g. the term `5` in
            // `f(a) = 5`), which has no separate model entry but is its own value.
            if let Some(term) = self.terms.get(member)
                && matches!(
                    term.kind,
                    TermKind::True
                        | TermKind::False
                        | TermKind::IntConst(_)
                        | TermKind::RealConst(_)
                        | TermKind::BitVecConst { .. }
                )
            {
                return Some(self.format_value(member));
            }
        }
        None
    }

    /// Choose the most frequently occurring value among the interpretation
    /// entries, breaking ties in favour of the earliest occurrence.  Returns
    /// `None` for an empty entry list.
    fn most_common_value(entries: &[(Vec<String>, String)]) -> Option<String> {
        let mut counts: crate::prelude::HashMap<&str, (usize, usize)> =
            crate::prelude::HashMap::new();
        for (order, (_, value)) in entries.iter().enumerate() {
            let slot = counts.entry(value.as_str()).or_insert((0, order));
            slot.0 += 1;
        }
        counts
            .into_iter()
            .max_by(|(_, (count_a, order_a)), (_, (count_b, order_b))| {
                // Higher count wins; on a tie the smaller insertion order wins,
                // so we reverse the order comparison.
                count_a.cmp(count_b).then_with(|| order_b.cmp(order_a))
            })
            .map(|(value, _)| value.to_string())
    }

    /// Format a sort ID to its SMT-LIB2 name
    fn format_sort_name(&self, sort: SortId) -> String {
        if sort == self.terms.sorts.bool_sort {
            "Bool".to_string()
        } else if sort == self.terms.sorts.int_sort {
            "Int".to_string()
        } else if sort == self.terms.sorts.real_sort {
            "Real".to_string()
        } else if let Some(s) = self.terms.sorts.get(sort) {
            if let Some(w) = s.bitvec_width() {
                format!("(_ BitVec {})", w)
            } else {
                "Unknown".to_string()
            }
        } else {
            "Unknown".to_string()
        }
    }

    /// Format a model value
    fn format_value(&self, term: TermId) -> String {
        match self.terms.get(term).map(|t| &t.kind) {
            Some(TermKind::True) => "true".to_string(),
            Some(TermKind::False) => "false".to_string(),
            Some(TermKind::IntConst(n)) => oxiz_core::smtlib::int_literal_smtlib(n),
            Some(TermKind::RealConst(r)) => {
                if *r.denom() == 1 {
                    format!("{}.0", r.numer())
                } else {
                    format!("(/ {} {})", r.numer(), r.denom())
                }
            }
            Some(TermKind::BitVecConst { value, width }) => {
                format!(
                    "#b{:0>width$}",
                    format!("{:b}", value),
                    width = *width as usize
                )
            }
            _ => "?".to_string(),
        }
    }

    /// Get a default value for a sort
    fn default_value(&self, sort: SortId) -> String {
        if sort == self.terms.sorts.bool_sort {
            "false".to_string()
        } else if sort == self.terms.sorts.int_sort {
            "0".to_string()
        } else if sort == self.terms.sorts.real_sort {
            "0.0".to_string()
        } else if let Some(s) = self.terms.sorts.get(sort) {
            if let Some(w) = s.bitvec_width() {
                format!("#b{:0>width$}", "0", width = w as usize)
            } else {
                "?".to_string()
            }
        } else {
            "?".to_string()
        }
    }

    /// Format the model as SMT-LIB2
    pub fn format_model(&self) -> String {
        match self.get_model() {
            None => "(error \"No model available\")".to_string(),
            Some(model) if model.is_empty() => "(model)".to_string(),
            Some(model) => {
                let mut lines = vec!["(model".to_string()];
                for (name, sort, value) in model {
                    lines.push(format!("  (define-fun {} () {} {})", name, sort, value));
                }
                lines.push(")".to_string());
                lines.join("\n")
            }
        }
    }

    /// Push a context level
    pub fn push(&mut self) {
        self.assertion_stack.push(self.assertions.len());
        self.const_stack.push(self.declared_consts.len());
        self.fun_stack.push(self.declared_funs.len());
        self.solver.push();
    }

    /// Pop a context level with incremental declaration removal
    pub fn pop(&mut self) {
        if let Some(len) = self.assertion_stack.pop() {
            self.assertions.truncate(len);
            if let Some(const_len) = self.const_stack.pop() {
                // Remove constants from the name-to-index mapping
                while self.declared_consts.len() > const_len {
                    if let Some(decl) = self.declared_consts.pop() {
                        self.const_name_to_index.remove(&decl.name);
                    }
                }
            }
            if let Some(fun_len) = self.fun_stack.pop() {
                // Remove functions from the name-to-index mapping
                while self.declared_funs.len() > fun_len {
                    if let Some(decl) = self.declared_funs.pop() {
                        self.fun_name_to_index.remove(&decl.name);
                    }
                }
            }
            self.solver.pop();
        }
    }

    /// Reset the context
    pub fn reset(&mut self) {
        self.solver.reset();
        self.assertions.clear();
        self.assertion_stack.clear();
        self.declared_consts.clear();
        self.const_stack.clear();
        self.const_name_to_index.clear();
        self.declared_funs.clear();
        self.fun_stack.clear();
        self.fun_name_to_index.clear();
        self.logic = None;
        self.last_result = None;
        self.options.clear();
    }

    /// Reset assertions (keep declarations and options)
    pub fn reset_assertions(&mut self) {
        self.solver.reset();
        self.assertions.clear();
        self.assertion_stack.clear();
        // Keep declared_consts, const_stack, const_name_to_index,
        // declared_funs, fun_stack, and fun_name_to_index
        // Re-assert nothing - solver is fresh
        self.last_result = None;
    }

    /// Get all current assertions
    #[must_use]
    pub fn get_assertions(&self) -> &[TermId] {
        &self.assertions
    }

    /// Format assertions as SMT-LIB2
    #[cfg(feature = "std")]
    pub fn format_assertions(&self) -> String {
        if self.assertions.is_empty() {
            return "()".to_string();
        }
        let printer = oxiz_core::smtlib::Printer::new(&self.terms);
        let mut parts = Vec::new();
        for &term in &self.assertions {
            parts.push(printer.print_term(term));
        }
        format!("({})", parts.join("\n "))
    }

    /// Set an option
    pub fn set_option(&mut self, key: &str, value: &str) {
        self.options.insert(key.to_string(), value.to_string());

        // Handle special options that affect the solver
        match key {
            "produce-proofs" => {
                let mut config = self.solver.config().clone();
                config.proof = value == "true";
                self.solver.set_config(config);
            }
            // #423 item 3 — wire the SMT-LIB/CLI front end's `(set-option
            // :simplify ..)` / `--preset minimal` (`ctx.set_option("simplify",
            // "false")`) through to `SolverConfig::simplify`. Previously this
            // fell through to the `_ => {}` no-op default: `simplify` was only
            // ever settable via direct Rust `SolverConfig` struct construction,
            // so the CLI's own minimal-preset call silently did nothing.
            "simplify" => {
                let mut config = self.solver.config().clone();
                config.simplify = value == "true";
                self.solver.set_config(config);
            }
            "produce-unsat-cores" => {
                self.solver.set_produce_unsat_cores(value == "true");
            }
            // §4 redesign (Phase 2): opt into the lock-step `TheoryHooks` CDCL(T)
            // driver instead of the legacy `TheoryCallback`. Off by default; both
            // run the same real theory state, so this only changes the driver.
            "oxiz.use-hooks-driver" => {
                let mut config = self.solver.config().clone();
                config.use_hooks_driver = value == "true";
                self.solver.set_config(config);
            }
            // The clean-room MBQI engine (`oxiz-mbqi`, never-conclude-unsat) is
            // the solver's only quantifier path (the legacy `mbqi/` heuristics
            // were removed, #262). `(set-option :oxiz.clean-mbqi false)` now
            // forces a ground-only solve (quantifiers encoded as opaque boolean
            // proxies, never instantiated) — incomplete, so production leaves it
            // on. The option is retained for A/B / ground-only diagnostics.
            "oxiz.clean-mbqi" => {
                let mut config = self.solver.config().clone();
                config.clean_mbqi = value == "true";
                self.solver.set_config(config);
            }
            // CCFV (Phase P2): opt-in congruence-aware single-pattern trigger
            // e-matching in the clean-MBQI engine. Off by default; this is the
            // SMT-LIB switch to A/B it (and to run the z3-parity corpus with it on
            // for the completeness/performance gate). Soundness is unaffected —
            // CCFV matching is a superset of syntactic, gated by the same firewall.
            "oxiz.ccfv-ematch" => {
                let mut config = self.solver.config().clone();
                config.ccfv_ematch = value == "true";
                self.solver.set_config(config);
            }
            // CCFV (Phase P4): opt-in model-completion verdict-flip — CCFV `¬ψ`
            // over the total view `E_TOT` lets a trigger-free universal the
            // structural recognizers miss contribute a `Sat`. OFF by default and
            // SOUNDNESS-CRITICAL (a missed conflict is a spurious `sat`); this
            // switch arms it for the corpus 0-spurious gate that precedes any
            // default flip. See `CCFV_UNIFIED_INSTANTIATION.md` §P4/§6.
            "oxiz.ccfv-model-compl" => {
                let mut config = self.solver.config().clone();
                config.ccfv_model_compl = value == "true";
                self.solver.set_config(config);
            }
            // E1 (#425): additive-patterns mode — when a clean-MBQI pass would
            // conclude `Saturated`/`Inconclusive`, augment parsed-trigger
            // universals with inferred groups (union, once per quantifier) and
            // re-pass. Sound-direction only (augmented quantifiers are
            // model-verified at saturation); OFF by default pending the corpus
            // A/B. Also armed by the `OXIZ_MBQI_ADDITIVE` env var.
            "oxiz.mbqi-additive-patterns" => {
                let mut config = self.solver.config().clone();
                config.mbqi_additive_patterns = value == "true";
                self.solver.set_config(config);
            }
            // Output mode for `(check-sat)`: `z3` (default, the collapsed 3-valued
            // `sat`/`unsat`/`unknown`) or `full` (the un-collapsed 5-level verdict
            // `definite-sat`/`possibly-sat`/`unknown`/`possibly-unsat`/
            // `definite-unsat`). Accepts a few spellings for convenience.
            "oxiz.output-mode" => {
                self.output_mode = match value {
                    "full" | "5" | "satlevel" => OutputMode::Full,
                    _ => OutputMode::Z3Compatible,
                };
            }
            _ => {}
        }
    }

    /// Get an option
    #[must_use]
    pub fn get_option(&self, key: &str) -> Option<&str> {
        self.options.get(key).map(String::as_str)
    }

    /// Format an option value
    fn format_option(&self, key: &str) -> String {
        match self.get_option(key) {
            Some(val) => val.to_string(),
            None => {
                // Return default values for well-known options
                match key {
                    "produce-models" => "false".to_string(),
                    "produce-unsat-cores" => "false".to_string(),
                    "produce-proofs" => "false".to_string(),
                    "produce-assignments" => "false".to_string(),
                    "print-success" => "true".to_string(),
                    _ => "unsupported".to_string(),
                }
            }
        }
    }

    /// Get assignment (for propositional variables with :named attribute)
    /// Returns an empty list as we don't track named literals yet
    pub fn get_assignment(&self) -> String {
        "()".to_string()
    }

    /// Get proof (if proof generation is enabled and result is unsat)
    pub fn get_proof(&self) -> String {
        if self.last_result != Some(SolverResult::Unsat) {
            return "(error \"Proof is only available after unsat result\")".to_string();
        }

        match self.solver.get_proof() {
            Some(proof) => proof.format(),
            None => {
                "(error \"Proof generation not enabled. Set :produce-proofs to true\")".to_string()
            }
        }
    }

    /// Get solver statistics
    /// Returns statistics about the last solving run
    pub fn get_statistics(&self) -> String {
        let stats = self.solver.get_statistics();
        format!(
            "(:decisions {} :conflicts {} :propagations {} :restarts {} :learned-clauses {} :theory-propagations {} :theory-conflicts {})",
            stats.decisions,
            stats.conflicts,
            stats.propagations,
            stats.restarts,
            stats.learned_clauses,
            stats.theory_propagations,
            stats.theory_conflicts
        )
    }

    /// Return the raw solver statistics (crate-internal use only).
    #[must_use]
    pub(crate) fn raw_statistics(&self) -> &crate::solver::Statistics {
        self.solver.get_statistics()
    }

    /// Return the current solver configuration (crate-internal use only).
    #[must_use]
    pub(crate) fn solver_config(&self) -> &crate::solver::SolverConfig {
        self.solver.config()
    }

    /// Update the solver configuration (crate-internal use only).
    pub(crate) fn set_solver_config(&mut self, config: crate::solver::SolverConfig) {
        self.solver.set_config(config);
    }

    /// Enable or disable the clean-room quantifier engine (`oxiz-mbqi`) for the
    /// model-based instantiation phase.
    ///
    /// The clean engine is sound by construction (it never fabricates a
    /// universe witness; the spurious-`unsat` bug class is structurally
    /// impossible) but currently less complete than the legacy `mbqi/` path on
    /// non-LIA+UF problems, so it is off by default and opted into by the
    /// verifier-backend path (e.g. the adsmt in-process OxiZ delegation that
    /// feeds the verus prelude). See `solver/mod.rs` and `clean_mbqi.rs`.
    pub fn set_clean_mbqi(&mut self, on: bool) {
        let mut cfg = self.solver.config().clone();
        cfg.clean_mbqi = on;
        self.solver.set_config(cfg);
    }

    /// Set the solver wall-clock budget in milliseconds (0 = the default
    /// non-termination guard). Doubles as the MBQI/quantifier loop deadline:
    /// on expiry the verdict is the sound `Unknown`, never a guess.
    pub fn set_timeout_ms(&mut self, ms: u64) {
        let mut cfg = self.solver.config().clone();
        cfg.timeout_ms = ms;
        self.solver.set_config(cfg);
    }

    /// Check satisfiability under temporary assumptions (crate-internal use only).
    pub(crate) fn check_with_assumptions_raw(
        &mut self,
        assumptions: &[oxiz_core::ast::TermId],
    ) -> crate::solver::SolverResult {
        self.solver
            .check_with_assumptions(assumptions, &mut self.terms)
    }

    /// Return the unsat core from the last check (crate-internal use only).
    #[must_use]
    pub(crate) fn get_unsat_core_raw(&self) -> Option<&crate::solver::UnsatCore> {
        self.solver.get_unsat_core()
    }

    /// Parse a sort name and return its SortId
    fn parse_sort_name(&mut self, name: &str) -> SortId {
        // Built-in scalar sorts and user-defined `define-sort` aliases.
        if let Some(sort_id) = self.terms.sorts.resolve_by_name(name) {
            return sort_id;
        }
        // `(_ BitVec N)`.
        if let Some(width_str) = name.strip_prefix("BitVec")
            && let Ok(width) = width_str.trim().parse::<u32>()
        {
            return self.terms.sorts.bitvec(width);
        }
        // Any other name is an UNINTERPRETED sort — a `(declare-sort S 0)`, or
        // a sort referenced before its declaration was processed (commands are
        // fed to `execute_script` one at a time).  It must have an UNBOUNDED
        // domain, NOT `Bool`: defaulting to `Bool` modelled every uninterpreted
        // sort with exactly two elements, so `(distinct c1 c2 c3 …)` over fresh
        // constants of the sort was unsatisfiable by pigeonhole — a soundness
        // bug for any UF problem (every Verus prelude sort: FuelId, Height,
        // Poly, Type, …).  `intern` dedups by name, so the same sort name maps
        // to the same `SortId` on every command, and the persistent
        // `TermManager` keeps it across calls.
        let key = self.terms.sorts.intern_str(name);
        self.terms.sorts.intern(SortKind::Uninterpreted(key))
    }

    /// Execute an SMT-LIB2 script
    #[cfg(feature = "std")]
    pub fn execute_script(&mut self, script: &str) -> Result<Vec<String>> {
        // Seed the parser with declarations from prior `execute_script` calls
        // (and persist this script's) so that applications of a function
        // declared in an EARLIER call still resolve to the function's real
        // sort.  A fed-one-command-at-a-time session (streaming CLI, embedded
        // per-command replay) would otherwise re-parse each command with an
        // empty symbol table, defaulting a non-Bool `(f x)` to `Bool` and
        // breaking theory reasoning over it.
        let commands = parse_script_with_env(script, &mut self.terms, &mut self.parser_env)?;
        let mut output = Vec::new();

        for cmd in commands {
            match cmd {
                Command::SetLogic(logic) => {
                    self.set_logic(&logic);
                }
                Command::DeclareConst(name, sort_name) => {
                    let sort = self.parse_sort_name(&sort_name);
                    self.declare_const(&name, sort);
                }
                Command::DeclareFun(name, arg_sorts, ret_sort) => {
                    // Treat nullary functions as constants
                    if arg_sorts.is_empty() {
                        let sort = self.parse_sort_name(&ret_sort);
                        self.declare_const(&name, sort);
                    } else {
                        // Parse argument sorts and return sort
                        let parsed_arg_sorts: Vec<SortId> =
                            arg_sorts.iter().map(|s| self.parse_sort_name(s)).collect();
                        let parsed_ret_sort = self.parse_sort_name(&ret_sort);
                        self.declare_fun(&name, parsed_arg_sorts, parsed_ret_sort);
                    }
                }
                Command::Assert(term) => {
                    self.assert(term);
                }
                Command::CheckSat => {
                    let level = self.check_sat_level();
                    output.push(self.render_verdict(level));
                }
                Command::Push(n) => {
                    for _ in 0..n {
                        self.push();
                    }
                }
                Command::Pop(n) => {
                    for _ in 0..n {
                        self.pop();
                    }
                }
                Command::Reset => {
                    self.reset();
                }
                Command::ResetAssertions => {
                    self.reset_assertions();
                }
                Command::Exit => {
                    break;
                }
                Command::Echo(msg) => {
                    output.push(msg);
                }
                Command::GetModel => {
                    output.push(self.format_model());
                }
                Command::GetAssertions => {
                    output.push(self.format_assertions());
                }
                Command::GetAssignment => {
                    output.push(self.get_assignment());
                }
                Command::GetProof => {
                    output.push(self.get_proof());
                }
                Command::GetOption(key) => {
                    output.push(self.format_option(&key));
                }
                Command::SetOption(key, value) => {
                    self.set_option(&key, &value);
                }
                Command::CheckSatAssuming(assumptions) => {
                    // For now, we push, assert all assumptions, check, then pop
                    self.push();
                    for assumption in assumptions {
                        self.assert(assumption);
                    }
                    let level = self.check_sat_level();
                    self.pop();
                    output.push(self.render_verdict(level));
                }
                Command::Simplify(term) => {
                    // Simplify and output the term
                    let simplified = self.terms.simplify(term);
                    let printer = oxiz_core::smtlib::Printer::new(&self.terms);
                    output.push(printer.print_term(simplified));
                }
                Command::GetUnsatCore => {
                    if let Some(core) = self.solver.get_unsat_core() {
                        if core.names.is_empty() {
                            output.push("()".to_string());
                        } else {
                            output.push(format!("({})", core.names.join(" ")));
                        }
                    } else {
                        output.push("(error \"No unsat core available\")".to_string());
                    }
                }
                Command::GetValue(terms) => {
                    if self.last_result != Some(SolverResult::Sat) {
                        output.push("(error \"No model available\")".to_string());
                    } else if let Some(model) = self.solver.model() {
                        let mut values = Vec::new();
                        for term in terms {
                            // Evaluate the term in the model first
                            let value = model.eval(term, &mut self.terms);
                            // Then create printer and format
                            let printer = oxiz_core::smtlib::Printer::new(&self.terms);
                            let term_str = printer.print_term(term);
                            let value_str = printer.print_term(value);
                            values.push(format!("({} {})", term_str, value_str));
                        }
                        output.push(format!("({})", values.join("\n ")));
                    } else {
                        output.push("(error \"No model available\")".to_string());
                    }
                }
                Command::GetInfo(keyword) => {
                    // Handle get-info command
                    if keyword == ":all-statistics" {
                        output.push(self.get_statistics());
                    } else {
                        output.push(format!("(error \"Unsupported info keyword: {}\")", keyword));
                    }
                }
                Command::DeclareSort(name, arity) => {
                    // Register the uninterpreted sort so references resolve to a
                    // proper unbounded sort (not the `Bool` fallback).  Arity-0
                    // is the common case (Verus's FuelId / Height / Poly / …);
                    // `parse_sort_name` also creates it on first use, but
                    // registering here covers a declared-but-unused sort and
                    // records the parametric arity.
                    if arity == 0 {
                        let _ = self.parse_sort_name(&name);
                    } else {
                        self.terms.sorts.declare_parametric_sort(&name, arity as usize);
                    }
                }
                Command::SetInfo(_, _)
                | Command::DefineSort(_, _, _)
                | Command::DefineFun(_, _, _, _)
                | Command::DeclareDatatype { .. } => {
                    // Ignore these commands for now
                }
            }
        }

        Ok(output)
    }

    /// Get solver statistics
    #[must_use]
    pub fn stats(&self) -> &oxiz_sat::SolverStats {
        self.solver.stats()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_context_basic() {
        let mut ctx = Context::new();

        ctx.set_logic("QF_UF");
        assert_eq!(ctx.logic(), Some("QF_UF"));

        let t = ctx.terms.mk_true();
        ctx.assert(t);

        let result = ctx.check_sat();
        assert_eq!(result, SolverResult::Sat);
    }

    #[test]
    fn test_context_push_pop() {
        let mut ctx = Context::new();

        let t = ctx.terms.mk_true();
        ctx.assert(t);
        ctx.push();

        let f = ctx.terms.mk_false();
        ctx.assert(f);

        // Should be unsat with false asserted
        let result = ctx.check_sat();
        assert_eq!(result, SolverResult::Unsat);

        ctx.pop();

        // After pop, should be sat again
        let result = ctx.check_sat();
        assert_eq!(result, SolverResult::Sat);
    }

    #[test]
    fn test_execute_script() {
        let mut ctx = Context::new();

        let script = r#"
            (set-logic QF_UF)
            (declare-const p Bool)
            (assert p)
            (check-sat)
        "#;

        let output = ctx
            .execute_script(script)
            .expect("test operation should succeed");
        assert_eq!(output, vec!["sat"]);
    }

    #[test]
    fn test_declare_const() {
        let mut ctx = Context::new();

        let bool_sort = ctx.terms.sorts.bool_sort;
        let int_sort = ctx.terms.sorts.int_sort;

        ctx.declare_const("x", bool_sort);
        ctx.declare_const("y", int_sort);

        let t = ctx.terms.mk_true();
        ctx.assert(t);
        let result = ctx.check_sat();
        assert_eq!(result, SolverResult::Sat);

        // Model should include both constants
        let model = ctx.get_model();
        assert!(model.is_some());
        let model = model.expect("test operation should succeed");
        assert_eq!(model.len(), 2);
    }

    #[test]
    fn test_format_model() {
        let mut ctx = Context::new();

        let bool_sort = ctx.terms.sorts.bool_sort;
        ctx.declare_const("p", bool_sort);

        let t = ctx.terms.mk_true();
        ctx.assert(t);
        let _ = ctx.check_sat();

        let model_str = ctx.format_model();
        assert!(model_str.contains("(model"));
        assert!(model_str.contains("define-fun p () Bool"));
    }

    #[test]
    fn test_get_model_script() {
        let mut ctx = Context::new();

        let script = r#"
            (set-logic QF_LIA)
            (declare-const x Int)
            (declare-const y Bool)
            (assert true)
            (check-sat)
            (get-model)
        "#;

        let output = ctx
            .execute_script(script)
            .expect("test operation should succeed");
        assert_eq!(output.len(), 2);
        assert_eq!(output[0], "sat");
        assert!(
            output[1].contains("(model"),
            "Expected '(model' in: {}",
            output[1]
        );
        // Note: Sorts may not always appear in model output if values are default
        // The model format is: (define-fun name () Sort value)
    }

    #[test]
    fn test_push_pop_consts() {
        let mut ctx = Context::new();

        let bool_sort = ctx.terms.sorts.bool_sort;
        ctx.declare_const("a", bool_sort);
        ctx.push();
        ctx.declare_const("b", bool_sort);

        let t = ctx.terms.mk_true();
        ctx.assert(t);
        let _ = ctx.check_sat();

        let model = ctx.get_model().expect("test operation should succeed");
        assert_eq!(model.len(), 2);

        ctx.pop();
        let _ = ctx.check_sat();

        let model = ctx.get_model().expect("test operation should succeed");
        assert_eq!(model.len(), 1);
        assert_eq!(model[0].0, "a");
    }

    #[test]
    fn test_get_assertions() {
        let mut ctx = Context::new();

        let script = r#"
            (set-logic QF_UF)
            (declare-const p Bool)
            (assert p)
            (assert (not p))
            (get-assertions)
        "#;

        let output = ctx
            .execute_script(script)
            .expect("test operation should succeed");
        assert_eq!(output.len(), 1);
        assert!(output[0].starts_with('('));
        // Should contain both assertions
        assert!(output[0].contains("p"));
    }

    #[test]
    fn test_check_sat_assuming_script() {
        let mut ctx = Context::new();

        let script = r#"
            (set-logic QF_UF)
            (declare-const p Bool)
            (declare-const q Bool)
            (assert p)
            (check-sat-assuming (q))
        "#;

        let output = ctx
            .execute_script(script)
            .expect("test operation should succeed");
        assert_eq!(output.len(), 1);
        assert_eq!(output[0], "sat");
    }

    #[test]
    fn test_get_option_script() {
        let mut ctx = Context::new();

        let script = r#"
            (set-option :produce-models true)
            (get-option :produce-models)
        "#;

        let output = ctx
            .execute_script(script)
            .expect("test operation should succeed");
        assert_eq!(output.len(), 1);
        assert_eq!(output[0], "true");
    }

    #[test]
    fn test_reset_assertions() {
        let mut ctx = Context::new();

        let script = r#"
            (set-logic QF_UF)
            (declare-const p Bool)
            (assert p)
            (reset-assertions)
            (get-assertions)
            (check-sat)
        "#;

        let output = ctx
            .execute_script(script)
            .expect("test operation should succeed");
        assert_eq!(output.len(), 2);
        assert_eq!(output[0], "()"); // No assertions after reset
        assert_eq!(output[1], "sat"); // Empty formula is SAT
    }

    #[test]
    fn test_simplify_command() {
        let mut ctx = Context::new();

        let script = r#"
            (simplify (+ 1 2))
        "#;

        let output = ctx
            .execute_script(script)
            .expect("test operation should succeed");
        assert_eq!(output.len(), 1);
        // Should simplify to 3
        assert_eq!(output[0], "3");
    }

    #[test]
    fn test_simplify_complex() {
        let mut ctx = Context::new();

        let script = r#"
            (simplify (* 2 3 4))
        "#;

        let output = ctx
            .execute_script(script)
            .expect("test operation should succeed");
        assert_eq!(output.len(), 1);
        // Should simplify to 24
        assert_eq!(output[0], "24");
    }

    #[test]
    fn test_get_value() {
        let mut ctx = Context::new();

        let script = r#"
            (set-logic QF_UF)
            (declare-const p Bool)
            (declare-const q Bool)
            (assert p)
            (assert (not q))
            (check-sat)
            (get-value (p q (and p q) (or p q)))
        "#;

        let output = ctx
            .execute_script(script)
            .expect("test operation should succeed");
        assert_eq!(output.len(), 2);
        assert_eq!(output[0], "sat");

        // Parse the get-value output
        let value_output = &output[1];
        assert!(value_output.contains("p"));
        assert!(value_output.contains("q"));
        // p should evaluate to true
        assert!(value_output.contains("true"));
        // q should evaluate to false
        assert!(value_output.contains("false"));
    }

    #[test]
    fn test_get_value_no_model() {
        let mut ctx = Context::new();

        let script = r#"
            (set-logic QF_UF)
            (declare-const p Bool)
            (get-value (p))
        "#;

        let output = ctx
            .execute_script(script)
            .expect("test operation should succeed");
        assert_eq!(output.len(), 1);
        assert!(output[0].contains("error") || output[0].contains("No model"));
    }

    #[test]
    fn test_get_value_after_unsat() {
        let mut ctx = Context::new();

        let script = r#"
            (set-logic QF_UF)
            (declare-const p Bool)
            (assert p)
            (assert (not p))
            (check-sat)
            (get-value (p))
        "#;

        let output = ctx
            .execute_script(script)
            .expect("test operation should succeed");
        assert_eq!(output.len(), 2);
        assert_eq!(output[0], "unsat");
        assert!(output[1].contains("error") || output[1].contains("No model"));
    }
}
