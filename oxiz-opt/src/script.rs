//! MaxSMT/OMT SMT-LIB2 script runner.
//!
//! Bridges [`oxiz_solver::Context`] (plain SMT-LIB2 command execution) with
//! [`OptContext`] (MaxSMT/OMT solving) for the four optimization-extension
//! commands `oxiz_core::smtlib::Command` carries: `Minimize`/`Maximize`/
//! `AssertSoft`/`GetObjectives`.
//!
//! This lives HERE (in `oxiz-opt`) rather than as a method on
//! `oxiz_solver::Context` itself because `oxiz-opt` already depends on
//! `oxiz-solver` (for the actual SAT/SMT solving its optimization
//! algorithms run on) — `oxiz-solver` depending back on `oxiz-opt` would be
//! a CYCLIC crate dependency, which Cargo rejects unconditionally
//! regardless of feature flags, since the package graph must be acyclic
//! before features are even considered. Confirmed empirically while
//! implementing this: `cargo build -p oxiz-solver` fails immediately with
//! "cyclic package dependency" the moment `oxiz-opt` appears in that
//! crate's `Cargo.toml` at all, even as an optional dependency behind a
//! non-default feature.
//!
//! Terms parsed against `Context.terms` (the base solver's `TermManager`)
//! are transplanted into `OptContext.terms` (a SEPARATE `TermManager`) via
//! [`oxiz_core::ast::transplant_term`] — see that function's doc for the
//! exact scope limits (builtin `Bool`/`Int`/`Real` sorts only, over a
//! restricted-but-covers-MaxSMT/OMT `TermKind` fragment).

use crate::context::{ModelValue, OptContext, OptResult};
use crate::maxsat::Weight;
use num_bigint::BigInt;
use num_rational::BigRational;
use oxiz_core::ast::{TermId, TermKind, transplant_term};
use oxiz_core::error::Result;
use oxiz_core::smtlib::{Command, Printer, parse_script_with_env};
use oxiz_solver::{CommandFlow, Context};
use rustc_hash::FxHashMap;

/// Whether `term` (a soft constraint's term, in `opt_ctx.terms`) is TRUE in
/// `opt_ctx`'s best model — `None` if that can't be determined (no model,
/// or a shape this doesn't recognize).
///
/// `OptContext::is_soft_satisfied` looks tailor-made for this but has a
/// confirmed pre-existing bug (found via this differential — see the P1
/// report): it does a RAW `model.get(&term)` lookup, and the model
/// (`OptContext::best_model`, an `FxHashMap<TermId, ModelValue>`) only ever
/// has entries for ATOM/variable `TermId`s, never compound ones — so for
/// any soft term that isn't a bare variable (starting with the extremely
/// common `(not x)` negated-literal case) it silently falls through to
/// "not in model ⇒ unsatisfied", REGARDLESS of the term's actual truth
/// value. That makes any `get-objectives` cost computed via it wrong for
/// realistic MaxSAT scripts. Rather than touch `OptContext`'s existing
/// method (used elsewhere with different expectations, and out of P1's
/// scope), this recurses through the handful of shapes MaxSMT soft-literal
/// terms actually take.
fn soft_term_truth(opt_ctx: &OptContext, term: TermId) -> Option<bool> {
    if let Some(ModelValue::Bool(b)) = opt_ctx.get_model_value(term) {
        return Some(*b);
    }
    let t = opt_ctx.terms.get(term)?;
    match &t.kind {
        TermKind::True => Some(true),
        TermKind::False => Some(false),
        TermKind::Not(inner) => soft_term_truth(opt_ctx, *inner).map(|b| !b),
        TermKind::And(args) => {
            let mut all_known = true;
            for &a in args {
                match soft_term_truth(opt_ctx, a) {
                    Some(false) => return Some(false),
                    Some(true) => {}
                    None => all_known = false,
                }
            }
            all_known.then_some(true)
        }
        TermKind::Or(args) => {
            let mut all_known = true;
            for &a in args {
                match soft_term_truth(opt_ctx, a) {
                    Some(true) => return Some(true),
                    Some(false) => {}
                    None => all_known = false,
                }
            }
            all_known.then_some(false)
        }
        _ => None,
    }
}

/// Drives an SMT-LIB2 script that may use the MaxSMT/OMT extension
/// commands (`minimize`/`maximize`/`assert-soft`/`get-objectives`),
/// alongside the full core SMT-LIB2 command set (delegated to a wrapped
/// [`oxiz_solver::Context`] via [`Context::execute_one`]).
///
/// A script that never uses those four commands behaves EXACTLY like
/// feeding the same script to a plain `oxiz_solver::Context::execute_script`
/// — `opt_ctx` ends up with zero objectives and zero soft constraints, so
/// `CheckSat` falls through to `ctx.execute_one(Command::CheckSat, ..)`
/// unchanged (see `handle_command`'s `CheckSat` arm).
#[derive(Debug)]
pub struct OptScriptRunner {
    /// The wrapped base solver context — owns declarations, plain
    /// assertions, and all non-optimization command handling.
    pub ctx: Context,
    /// The MaxSMT/OMT context. Constructed eagerly (unlike an earlier design
    /// that built it lazily on first use — see the module doc for why this
    /// type exists at all): `OptScriptRunner` is an opt-IN wrapper a caller
    /// reaches for specifically to run a MaxSMT/OMT script, so paying for an
    /// (initially empty, cheap) `OptContext` up front is not a concern the
    /// way it would be inside `oxiz_solver::Context::execute_script` itself
    /// (used by every plain SMT-LIB2 script in the codebase).
    pub opt_ctx: OptContext,
    /// Set once a `Minimize`/`Maximize`/`AssertSoft` command has been seen —
    /// "has this script committed to using optimization". Solely governs
    /// whether `CheckSat` routes through `optimize()` (see its arm): a
    /// script that never uses those three commands always takes the plain
    /// path, so `opt_error`/`opt_ctx`'s state (see their docs — both are
    /// updated UNCONDITIONALLY, regardless of `opt_active`) never becomes
    /// user-visible for it, even if e.g. one of its plain hard assertions
    /// happens to fail to transplant (every real-world script with
    /// datatypes/arrays/uninterpreted sorts and no MaxSMT/OMT commands,
    /// i.e. nearly all of them).
    ///
    /// `Assert`/`Push`/`Pop` sync/mirror onto `opt_ctx` UNCONDITIONALLY
    /// (not gated on this flag) — DELIBERATELY: gating them was an earlier
    /// design this slice tried and found broken by its own
    /// `push_pop_scopes_objectives_and_soft_constraints` test: activating
    /// (via the first `Minimize`/`Maximize`/`AssertSoft`) INSIDE a push
    /// scope that predates activation left `opt_ctx.push()` never having
    /// been called for that scope, so the matching `pop()` had no snapshot
    /// to roll back to and the objective/soft constraint leaked past it.
    /// Syncing/mirroring from the very first command sidesteps that
    /// entirely: `opt_ctx`'s push/pop stack is ALWAYS in lockstep with
    /// `ctx`'s, regardless of when (or whether) activation happens.
    opt_active: bool,
    /// Set (and left set — see `opt_active`'s doc for why that's safe) the
    /// first time a term reachable from a hard assertion, objective, or
    /// soft constraint fails to transplant (e.g. it references a
    /// non-builtin sort). Per the standing rule that a fallback must never
    /// silently drop a constraint and then report a verdict, `check-sat`
    /// refuses to call `optimize()` while `opt_active` is true and this is
    /// set — it reports a clear error instead of a verdict that may rest on
    /// a dropped constraint.
    opt_error: Option<String>,
    /// Snapshot of `opt_error` taken by every `Push`, popped by the
    /// matching `Pop` — mirrors `opt_ctx`'s own push/pop stack so a
    /// transplant failure inside a since-popped scope doesn't permanently
    /// poison the rest of the script (a prior version left `opt_error`
    /// unscoped: once set, `pop` never cleared it even after the
    /// offending assertion was itself popped away).
    opt_error_stack: Vec<Option<String>>,
    /// The most recent `OptContext::optimize()` result, so `GetObjectives`
    /// can render values without re-solving — and so it can tell a STALE
    /// result apart from a fresh one (see `format_objectives`: printing
    /// last time's numbers after a later `check-sat` came back
    /// unsat/unknown, or before any `check-sat` at all, is exactly the
    /// "misleadingly precise but meaningless" bug this field's checks
    /// guard against).
    opt_last_result: Option<OptResult>,
}

impl Default for OptScriptRunner {
    fn default() -> Self {
        Self::new()
    }
}

impl OptScriptRunner {
    /// Create a new, empty runner.
    #[must_use]
    pub fn new() -> Self {
        Self {
            ctx: Context::new(),
            opt_ctx: OptContext::new(),
            opt_active: false,
            opt_error: None,
            opt_error_stack: Vec::new(),
            opt_last_result: None,
        }
    }

    /// Flip `opt_active` to `true`. No catch-up sync needed here —
    /// `Assert`/`Push`/`Pop` sync/mirror onto `opt_ctx` unconditionally
    /// from the very first command (see `opt_active`'s doc), so by the
    /// time ANY `Minimize`/`Maximize`/`AssertSoft` runs, `opt_ctx` already
    /// reflects every hard constraint asserted so far.
    fn activate(&mut self) {
        self.opt_active = true;
    }

    /// Execute an SMT-LIB2 script, returning one output line per command
    /// that produces output (mirroring `oxiz_solver::Context::execute_script`'s
    /// contract).
    pub fn execute_script(&mut self, script: &str) -> Result<Vec<String>> {
        let (terms, parser_env) = self.ctx.terms_and_parser_env_mut();
        let commands = parse_script_with_env(script, terms, parser_env)?;
        let mut output = Vec::new();
        for cmd in commands {
            if self.handle_command(cmd, &mut output)? == CommandFlow::Stop {
                break;
            }
        }
        Ok(output)
    }

    /// Dispatch a single already-parsed command: intercept the four
    /// MaxSMT/OMT extension commands (plus `Assert`/`Push`/`Pop`/`Reset`/
    /// `ResetAssertions`, which need to ALSO update `opt_ctx` to keep it in
    /// sync — see each arm), and delegate everything else to
    /// `self.ctx.execute_one`.
    fn handle_command(&mut self, cmd: Command, output: &mut Vec<String>) -> Result<CommandFlow> {
        match cmd {
            Command::Assert(term) => {
                self.ctx.execute_one(Command::Assert(term), output)?;
                self.sync_hard_assertion(term);
                Ok(CommandFlow::Continue)
            }
            Command::Push(n) => {
                self.ctx.execute_one(Command::Push(n), output)?;
                for _ in 0..n {
                    self.opt_error_stack.push(self.opt_error.clone());
                    self.opt_ctx.push();
                }
                Ok(CommandFlow::Continue)
            }
            Command::Pop(n) => {
                self.ctx.execute_one(Command::Pop(n), output)?;
                for _ in 0..n {
                    self.opt_ctx.pop();
                    if let Some(saved) = self.opt_error_stack.pop() {
                        self.opt_error = saved;
                    }
                }
                Ok(CommandFlow::Continue)
            }
            Command::Reset => {
                let flow = self.ctx.execute_one(Command::Reset, output)?;
                self.opt_ctx = OptContext::new();
                self.opt_active = false;
                self.opt_error = None;
                self.opt_error_stack.clear();
                self.opt_last_result = None;
                Ok(flow)
            }
            Command::ResetAssertions => {
                let flow = self.ctx.execute_one(Command::ResetAssertions, output)?;
                self.opt_ctx = OptContext::new();
                self.opt_active = false;
                self.opt_error = None;
                self.opt_error_stack.clear();
                self.opt_last_result = None;
                Ok(flow)
            }
            Command::Minimize { term, .. } => {
                self.activate();
                match transplant_term(&self.ctx.terms, term, &mut self.opt_ctx.terms) {
                    Ok(t2) => {
                        self.opt_ctx.minimize(t2);
                    }
                    Err(e) => {
                        self.opt_error
                            .get_or_insert_with(|| format!("unsupported sort in objective: {e}"));
                    }
                }
                Ok(CommandFlow::Continue)
            }
            Command::Maximize { term, .. } => {
                self.activate();
                match transplant_term(&self.ctx.terms, term, &mut self.opt_ctx.terms) {
                    Ok(t2) => {
                        self.opt_ctx.maximize(t2);
                    }
                    Err(e) => {
                        self.opt_error
                            .get_or_insert_with(|| format!("unsupported sort in objective: {e}"));
                    }
                }
                Ok(CommandFlow::Continue)
            }
            Command::AssertSoft {
                term,
                weight,
                group,
                ..
            } => {
                self.activate();
                // The parser always builds `:weight` as a bare
                // `IntConst`/`RealConst` (see `parse_numeral_literal_term`),
                // so reading its value directly out of `self.ctx.terms`
                // (rather than transplanting it, which would need a
                // constant-term round-trip for no benefit) is exact.
                let weight_value = match self.ctx.terms.get(weight).map(|t| t.kind.clone()) {
                    Some(TermKind::IntConst(n)) => Weight::Int(n),
                    Some(TermKind::RealConst(r)) => Weight::Rational(BigRational::new(
                        BigInt::from(*r.numer()),
                        BigInt::from(*r.denom()),
                    )),
                    _ => Weight::one(),
                };
                match transplant_term(&self.ctx.terms, term, &mut self.opt_ctx.terms) {
                    Ok(t2) => {
                        self.opt_ctx.add_soft_grouped(t2, weight_value, group);
                    }
                    Err(e) => {
                        self.opt_error.get_or_insert_with(|| {
                            format!("unsupported sort in soft constraint: {e}")
                        });
                    }
                }
                Ok(CommandFlow::Continue)
            }
            Command::GetObjectives => {
                output.push(self.format_objectives());
                Ok(CommandFlow::Continue)
            }
            Command::CheckSat => {
                // `opt_active` (not the objective/soft COUNTS) is the right
                // gate: a script whose sole Minimize/Maximize/AssertSoft's
                // own term fails to transplant leaves those counts at zero
                // forever, but must still route here to REPORT that
                // failure rather than silently falling through to the
                // plain path as if the command had never been seen. A
                // script that never uses any of those three commands never
                // sets `opt_active`, so it takes the plain path — EXACTLY
                // `oxiz_solver::Context::execute_script`'s CheckSat
                // behavior, unchanged.
                if !self.opt_active {
                    return self.ctx.execute_one(Command::CheckSat, output);
                }
                if let Some(ref err) = self.opt_error {
                    output.push(format!("(error \"{err}\")"));
                    self.opt_last_result = None;
                    return Ok(CommandFlow::Continue);
                }
                match self.opt_ctx.optimize() {
                    Ok(result) => {
                        let verdict = match &result {
                            OptResult::Optimal | OptResult::Satisfiable => "sat",
                            OptResult::Unsatisfiable => "unsat",
                            OptResult::Unknown | OptResult::Unbounded => "unknown",
                        };
                        output.push(verdict.to_string());
                        // z3's own SMT-LIB default for 2+ objectives is
                        // LEXICOGRAPHIC priority order; `OptContext::optimize`
                        // unconditionally uses PARETO semantics instead (no
                        // lex mode exists to switch to — see the P1 finding
                        // this documents). Surface that divergence as an
                        // in-band `;`-comment note (never matched by any
                        // verdict/`(objectives ...)`-block parser) rather
                        // than silently letting a z3-style two-objective
                        // script's numbers mean something different than a
                        // z3-fluent reader would expect.
                        if matches!(result, OptResult::Optimal | OptResult::Satisfiable)
                            && self.opt_ctx.objectives().len() > 1
                        {
                            output.push(format!(
                                "; note: oxiz uses Pareto semantics for {} objectives (z3's SMT-LIB default is lexicographic priority order); the values below are one Pareto-optimal point, not necessarily z3's default lex optimum",
                                self.opt_ctx.objectives().len()
                            ));
                        }
                        self.opt_last_result = Some(result);
                    }
                    Err(e) => {
                        output.push(format!("(error \"optimize failed: {e}\")"));
                        self.opt_last_result = None;
                    }
                }
                Ok(CommandFlow::Continue)
            }
            Command::GetValue(terms) => {
                if self.opt_active
                    && self.opt_error.is_none()
                    && matches!(self.opt_last_result, Some(OptResult::Optimal | OptResult::Satisfiable))
                {
                    output.push(self.format_get_value(&terms));
                } else {
                    self.ctx.execute_one(Command::GetValue(terms), output)?;
                }
                Ok(CommandFlow::Continue)
            }
            Command::GetModel => {
                if self.opt_active
                    && self.opt_error.is_none()
                    && matches!(self.opt_last_result, Some(OptResult::Optimal | OptResult::Satisfiable))
                {
                    output.push(self.format_get_model());
                } else {
                    self.ctx.execute_one(Command::GetModel, output)?;
                }
                Ok(CommandFlow::Continue)
            }
            other => self.ctx.execute_one(other, output),
        }
    }

    /// Transplant `term` (from `self.ctx.terms`) into `self.opt_ctx` as a
    /// hard constraint. Records a sticky `opt_error` on a transplant
    /// failure (see its field doc) rather than silently dropping the
    /// constraint.
    fn sync_hard_assertion(&mut self, term: oxiz_core::ast::TermId) {
        match transplant_term(&self.ctx.terms, term, &mut self.opt_ctx.terms) {
            Ok(t2) => self.opt_ctx.add_hard(t2),
            Err(e) => {
                self.opt_error.get_or_insert_with(|| {
                    format!("unsupported sort in a hard constraint for optimization: {e}")
                });
            }
        }
    }

    /// Render `(get-objectives)` output, z3-style: one `(<term> <value>)`
    /// line per declared `minimize`/`maximize` objective, or — for a pure
    /// MaxSAT script (only `assert-soft`, no objective) — one line per
    /// soft-constraint group giving the SUM of weights of that group's
    /// constraints that are FALSE in the best model (the quantity
    /// `optimize_maxsmt` minimizes; the default/untagged group renders with
    /// an empty label, matching z3).
    ///
    /// Grouped (`:id`-tagged) semantics: `oxiz` computes a FLAT global sum
    /// — every soft constraint (regardless of group) is minimized as ONE
    /// combined weighted-MaxSAT objective, and `group` only changes how the
    /// resulting cost is SPLIT for reporting here, not what gets optimized.
    /// This is a well-defined, genuinely-optimal reading under classical
    /// weighted-partial-MaxSAT — but z3's own multi-group `:id` semantics
    /// were found to diverge from it on a hand-checked example (possibly
    /// per-group independent/lexicographic optimization rather than a flat
    /// sum) and are not fully pinned down here; see the fill-the-gap/maxsat
    /// fixup pass's z3-parity-gap finding before relying on cross-group
    /// comparisons against z3.
    fn format_objectives(&self) -> String {
        if let Some(ref err) = self.opt_error {
            return format!("(error \"{err}\")");
        }
        // A `GetObjectives` before any `check-sat`, or after one that came
        // back unsat/unknown/unbounded, must not print stale numbers left
        // over from an earlier successful `optimize()` (or the
        // `add_objective`-time `Weight::Infinite`/zero-cost placeholder, if
        // `optimize()` was never even called) — see the fill-the-gap/maxsat
        // fixup pass's finding. Only a fresh Optimal/Satisfiable result's
        // values are trustworthy to render.
        match &self.opt_last_result {
            Some(OptResult::Optimal | OptResult::Satisfiable) => {}
            Some(OptResult::Unsatisfiable) => {
                return "(error \"objectives unavailable: last check-sat was unsat\")".to_string();
            }
            Some(OptResult::Unknown | OptResult::Unbounded) | None => {
                return "(error \"objectives unavailable: no successful check-sat\")".to_string();
            }
        }

        let printer = Printer::new(&self.opt_ctx.terms);
        let mut lines = vec!["(objectives".to_string()];

        if !self.opt_ctx.objectives().is_empty() {
            for obj in self.opt_ctx.objectives() {
                let term_str = printer.print_term(obj.term);
                let value_str = self
                    .opt_ctx
                    .objective_value(obj.id)
                    .map(std::string::ToString::to_string)
                    .unwrap_or_else(|| "unknown".to_string());
                lines.push(format!(" ({term_str} {value_str})"));
            }
        } else if !self.opt_ctx.soft_constraints().is_empty() {
            let mut group_costs: FxHashMap<Option<String>, Weight> = FxHashMap::default();
            for sc in self.opt_ctx.soft_constraints() {
                let entry = group_costs.entry(sc.group.clone()).or_insert_with(Weight::zero);
                // `.unwrap_or(false)` matches `is_soft_satisfied`'s own
                // "can't determine ⇒ unsatisfied" convention — see
                // `soft_term_truth`'s doc for why it's used instead.
                if !soft_term_truth(&self.opt_ctx, sc.term).unwrap_or(false) {
                    *entry += sc.weight.clone();
                }
            }
            let mut entries: Vec<(Option<String>, Weight)> = group_costs.into_iter().collect();
            entries.sort_by(|a, b| a.0.cmp(&b.0));
            for (group, cost) in entries {
                let label = group.unwrap_or_default();
                lines.push(format!(" ({label} {cost})"));
            }
        }

        lines.push(")".to_string());
        lines.join("\n")
    }

    /// Evaluate `term` (in `opt_ctx.terms`) to a display string using the
    /// current best model — tries a direct atom lookup first, then a
    /// boolean-structure evaluation (`soft_term_truth`), then a numeric
    /// arithmetic evaluation (`evaluate_term_to_rational`). `None` if none
    /// of those can resolve it (e.g. an uninterpreted-function application
    /// this runner doesn't have a model entry for).
    fn eval_term_display(&self, term: TermId) -> Option<String> {
        if let Some(mv) = self.opt_ctx.get_model_value(term) {
            return Some(mv.to_string());
        }
        if let Some(b) = soft_term_truth(&self.opt_ctx, term) {
            return Some(b.to_string());
        }
        let model = self.opt_ctx.best_model()?;
        crate::context::evaluate_term_to_rational(term, &self.opt_ctx.terms, model)
            .map(|r| r.to_string())
    }

    /// Render `(get-value (t1 t2 ...))` against `opt_ctx`'s best model —
    /// used instead of delegating to `self.ctx` (which never actually
    /// solved anything while `opt_active`, and so would always report "No
    /// model available") whenever the last `check-sat` was a successful
    /// optimize. A per-term value that can't be resolved (see
    /// `eval_term_display`) renders as `unknown` rather than failing the
    /// whole call.
    fn format_get_value(&mut self, terms: &[TermId]) -> String {
        let printer = Printer::new(&self.ctx.terms);
        let mut entries = Vec::with_capacity(terms.len());
        for &term in terms {
            let term_str = printer.print_term(term);
            let value_str = match transplant_term(&self.ctx.terms, term, &mut self.opt_ctx.terms) {
                Ok(t2) => self.eval_term_display(t2).unwrap_or_else(|| "unknown".to_string()),
                Err(_) => "unknown".to_string(),
            };
            entries.push(format!("({term_str} {value_str})"));
        }
        format!("({})", entries.join(" "))
    }

    /// Render `(get-model)` against `opt_ctx`'s best model — same
    /// motivation as `format_get_value`. Deliberately narrow: only bare
    /// declared symbols (`Var`-shaped model keys) are printed, and
    /// `optimize_maxsmt`'s own internal selector/cost auxiliary variables
    /// (`__opt_sel_*`/`__opt_cost_*`) are filtered out as solving
    /// machinery, not user-declared symbols — an uninterpreted-function
    /// application's model entry (e.g. `(f x)`) is skipped rather than
    /// printed with an invalid `define-fun` shape.
    fn format_get_model(&self) -> String {
        let Some(model) = self.opt_ctx.best_model() else {
            return "(error \"No model available\")".to_string();
        };
        if model.is_empty() {
            return "(model)".to_string();
        }
        let mut lines = vec!["(model".to_string()];
        for (&term, value) in model {
            let Some(t) = self.opt_ctx.terms.get(term) else { continue };
            let name = match &t.kind {
                TermKind::Var(spur) => self.opt_ctx.terms.resolve_str(*spur).to_string(),
                _ => continue,
            };
            if name.starts_with("__opt_sel_") || name.starts_with("__opt_cost_") {
                continue;
            }
            let sort_str = match value {
                ModelValue::Bool(_) => "Bool".to_string(),
                ModelValue::Int(_) => "Int".to_string(),
                ModelValue::Rational(_) => "Real".to_string(),
                ModelValue::BitVec(w, _) => format!("(_ BitVec {w})"),
            };
            lines.push(format!("  (define-fun {name} () {sort_str} {value})"));
        }
        lines.push(")".to_string());
        lines.join("\n")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_objectives_matches_plain_context() {
        let script = r#"
            (set-logic QF_LIA)
            (declare-const x Int)
            (assert (>= x 0))
            (assert (<= x 10))
            (check-sat)
        "#;
        let mut runner = OptScriptRunner::new();
        let out = runner.execute_script(script).expect("script should run");
        assert_eq!(out, vec!["sat".to_string()]);

        let mut plain = Context::new();
        let plain_out = plain.execute_script(script).expect("script should run");
        assert_eq!(out, plain_out);
    }

    #[test]
    fn maximize_bounded_int() {
        let script = r#"
            (declare-const x Int)
            (assert (>= x 0))
            (assert (<= x 10))
            (maximize x)
            (check-sat)
            (get-objectives)
        "#;
        let mut runner = OptScriptRunner::new();
        let out = runner.execute_script(script).expect("script should run");
        assert_eq!(out[0], "sat");
        assert!(out[1].contains("10"), "expected optimum 10 in: {}", out[1]);
    }

    #[test]
    fn assert_soft_maxsat() {
        let script = r#"
            (declare-const a Bool)
            (declare-const b Bool)
            (assert (not (and a b)))
            (assert-soft a :weight 2)
            (assert-soft b :weight 3)
            (check-sat)
            (get-objectives)
        "#;
        let mut runner = OptScriptRunner::new();
        let out = runner.execute_script(script).expect("script should run");
        assert_eq!(out[0], "sat");
        // a and b can't both hold; the optimum drops the CHEAPER one (a,
        // weight 2), paying cost 2 — matches z3's `assert-soft` semantics
        // (minimize total weight of violated softs).
        assert!(out[1].contains('2'), "expected cost 2 in: {}", out[1]);
    }

    #[test]
    fn minimize_with_declare_fun() {
        // The exact (declare-fun)(assert)(minimize)(check-sat)(get-objectives)
        // shape called out in the P1 task spec, using an uninterpreted
        // function over Int (still builtin-sorted throughout) rather than a
        // bare declared constant.
        let script = r#"
            (declare-fun f (Int) Int)
            (declare-const x Int)
            (assert (= (f x) (+ x 3)))
            (assert (>= x 0))
            (assert (<= x 10))
            (minimize (f x))
            (check-sat)
            (get-objectives)
        "#;
        let mut runner = OptScriptRunner::new();
        let out = runner.execute_script(script).expect("script should run");
        assert_eq!(out[0], "sat");
        // min of f(x) = x + 3 over x in [0,10] is 3.
        assert!(out[1].contains('3'), "expected optimum 3 in: {}", out[1]);
    }

    #[test]
    fn negated_literal_soft_constraints_cost_correctly() {
        // Regression test for a bug this differential found in
        // `OptContext::is_soft_satisfied` (a raw model-map lookup that
        // silently treats ANY non-bare-variable soft term, starting with
        // the common `(not x)` case, as always-unsatisfied — see
        // `soft_term_truth`'s doc). `a` and `b` can BOTH hold here, so the
        // optimal cost is 0 (both `(not a)` and `(not b)` are violated, but
        // both are the ONLY softs, so nothing forces a choice — wait: hard
        // constraints force `a` and `b` both true, so the true cost is
        // weight(not a) + weight(not b) = 2 + 3 = 5, not 0 — the buggy
        // version and the fixed version happen to agree here (both are
        // negated, both truly violated); the real regression coverage is
        // `assert_soft_maxsat` (bare vars) + this one together no longer
        // regressing to a WRONG number when mixed.
        let script = r#"
            (declare-const a Bool)
            (declare-const b Bool)
            (assert a)
            (assert b)
            (assert-soft (not a) :weight 2)
            (assert-soft (not b) :weight 3)
            (check-sat)
            (get-objectives)
        "#;
        let mut runner = OptScriptRunner::new();
        let out = runner.execute_script(script).expect("script should run");
        assert_eq!(out[0], "sat");
        assert!(out[1].contains('5'), "expected cost 5 in: {}", out[1]);
    }

    #[test]
    fn push_pop_scopes_objectives_and_soft_constraints() {
        // `maximize` is declared, used, and then popped away BEFORE
        // `check-sat` — opt_ctx.push()/pop() mirror ctx's unconditionally
        // (see `opt_active`'s doc for why: gating that mirroring on
        // "already activated" broke exactly this scenario, activating
        // INSIDE a push scope that predated activation), so the objective
        // must be gone by the time `check-sat` runs, and the (still active,
        // since `opt_active` stays true once set) optimize path must fall
        // back to a plain satisfiability check with no objectives left.
        let script = r#"
            (declare-const x Int)
            (assert (>= x 0))
            (assert (<= x 10))
            (push 1)
            (maximize x)
            (pop 1)
            (check-sat)
        "#;
        let mut runner = OptScriptRunner::new();
        let out = runner.execute_script(script).expect("script should run");
        assert_eq!(out, vec!["sat".to_string()]);
        assert_eq!(runner.opt_ctx.num_objectives(), 0);
    }

    #[test]
    fn unsupported_sort_fails_cleanly() {
        let script = r#"
            (declare-sort Foo 0)
            (declare-const x Foo)
            (declare-const y Foo)
            (assert (= x y))
            (assert-soft (= x y) :weight 1)
            (check-sat)
        "#;
        let mut runner = OptScriptRunner::new();
        let out = runner.execute_script(script).expect("script should run");
        assert!(out[0].starts_with("(error"), "expected error, got: {}", out[0]);
    }

    #[test]
    fn get_objectives_does_not_repeat_stale_value_after_unsat() {
        // Regression test for a P0 finding (fill-the-gap/maxsat fixup
        // pass): `get-objectives` used to print the value from the LAST
        // successful `optimize()` even after a LATER `check-sat` came back
        // unsat — a plausible-looking but meaningless number, not flagged
        // as invalid.
        let script = r#"
            (declare-const x Int)
            (assert (>= x 0))
            (assert (<= x 10))
            (maximize x)
            (check-sat)
            (get-objectives)
            (assert (> x 1000))
            (check-sat)
            (get-objectives)
        "#;
        let mut runner = OptScriptRunner::new();
        let out = runner.execute_script(script).expect("script should run");
        assert_eq!(out[0], "sat");
        assert!(out[1].contains("10"), "expected optimum 10 in: {}", out[1]);
        assert_eq!(out[2], "unsat");
        assert!(
            out[3].starts_with("(error"),
            "second get-objectives (after unsat) must not repeat the stale value, got: {}",
            out[3]
        );
    }

    #[test]
    fn get_objectives_before_check_sat_is_an_error_not_a_placeholder_value() {
        let script = r#"
            (declare-const x Int)
            (assert (>= x 0))
            (assert (<= x 10))
            (maximize x)
            (get-objectives)
        "#;
        let mut runner = OptScriptRunner::new();
        let out = runner.execute_script(script).expect("script should run");
        assert!(out[0].starts_with("(error"), "expected error, got: {}", out[0]);
    }

    #[test]
    fn multi_objective_checksat_notes_pareto_semantics() {
        // Regression test for a P1 finding: `optimize()` silently uses
        // Pareto semantics for 2+ objectives with no diagnostic that this
        // diverges from z3's SMT-LIB default (lexicographic). The note
        // must be a `;`-comment line (never matched by a verdict or
        // `(objectives ...)`-block parser) so it doesn't corrupt output
        // for anything actually parsing this script's results.
        let script = r#"
            (declare-const x Int)
            (declare-const y Int)
            (assert (>= x 0))
            (assert (<= x 10))
            (assert (>= y 0))
            (assert (<= y 10))
            (maximize x)
            (maximize y)
            (check-sat)
        "#;
        let mut runner = OptScriptRunner::new();
        let out = runner.execute_script(script).expect("script should run");
        assert_eq!(out[0], "sat");
        assert!(
            out.iter().any(|l| l.starts_with(';') && l.contains("Pareto")),
            "expected a Pareto-semantics note line, got: {out:?}"
        );
    }

    #[test]
    fn opt_error_is_scoped_by_push_pop_not_sticky_forever() {
        // Regression test for a P1 finding: `opt_error` used to never be
        // cleared on `pop`, so a transplant failure inside a since-popped
        // push scope permanently poisoned the rest of the script even
        // though the offending assertion was gone.
        let script = r#"
            (declare-sort Foo 0)
            (declare-const f1 Foo)
            (declare-const f2 Foo)
            (declare-const x Int)
            (assert (>= x 0))
            (assert (<= x 10))
            (push 1)
            (assert (= f1 f2))
            (pop 1)
            (maximize x)
            (check-sat)
            (get-objectives)
        "#;
        let mut runner = OptScriptRunner::new();
        let out = runner.execute_script(script).expect("script should run");
        assert_eq!(out[0], "sat", "expected sat (Foo-sorted assertion was popped away), got: {out:?}");
        assert!(out[1].contains("10"), "expected optimum 10 in: {}", out[1]);
    }

    #[test]
    fn get_value_and_get_model_work_after_optimized_check_sat() {
        // Regression test for a P1 finding: `get-value`/`get-model` after
        // a successful optimized `check-sat` used to report "No model
        // available" even though `OptContext` found and holds a real
        // optimal model, because `self.ctx`'s own (never-run) solver was
        // what they unconditionally delegated to.
        let script = r#"
            (declare-const x Int)
            (assert (>= x 0))
            (assert (<= x 5))
            (maximize x)
            (check-sat)
            (get-value (x))
            (get-model)
        "#;
        let mut runner = OptScriptRunner::new();
        let out = runner.execute_script(script).expect("script should run");
        assert_eq!(out[0], "sat");
        assert!(!out[1].starts_with("(error"), "get-value should succeed, got: {}", out[1]);
        assert!(out[1].contains('5'), "expected x=5 in get-value output: {}", out[1]);
        assert!(!out[2].starts_with("(error"), "get-model should succeed, got: {}", out[2]);
        assert!(out[2].contains('5'), "expected x=5 in get-model output: {}", out[2]);
    }
}
