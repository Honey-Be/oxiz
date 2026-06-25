//! Nonlinear arithmetic (NLSAT/NIA/NRA) constraint checking
//!
//! This module implements early conflict detection for nonlinear arithmetic
//! constraints in QF_NIRA, QF_NIA, and QF_NRA benchmarks. It handles cases
//! where the main CDCL(T) loop with linear arithmetic cannot detect UNSAT
//! because the constraints involve nonlinear terms (e.g., x*x).
//!
//! ## Detected Patterns
//!
//! 1. `x^2 = c` where c < 0 → UNSAT (squares are non-negative)
//! 2. `x^2 = c` (integer x) where c is not a perfect square → UNSAT
//! 3. System contradictions: e.g., `sq > 0 ∧ sq + y = 0 ∧ y >= 0`
//!    (sq > 0 implies sq + y > 0 when y >= 0, contradicting sq + y = 0)

#[allow(unused_imports)]
use crate::prelude::*;
use num_rational::Rational64;
use num_traits::{One, ToPrimitive, Zero};
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_core::interner::Spur;
use oxiz_theories::nlsat::{NlDispatchResult, dispatch_nia_constraints, dispatch_nra_constraints};
use std::collections::HashMap;

use super::Solver;
use super::types::SolverResult;

/// A polynomial atom extracted from an assertion.
/// Represents: `coeff * square_term OP constant`
/// where `square_term` is a term of the form `x * x` (or product of identical terms).
#[derive(Debug, Clone)]
#[allow(dead_code)]
enum NlAtom {
    /// `sq_term = const` — the square term equals a constant
    SqEq {
        sq_term: TermId,
        val: Rational64,
        is_integer_sort: bool,
    },
    /// `sq_term > 0`
    SqGtZero { sq_term: TermId },
    /// `sq_term >= 0`
    SqGeZero { sq_term: TermId },
    /// `sq_term + linear_coeff * other_var = const`
    /// i.e., `sq + coeff * v = c`
    SqPlusLinearEq {
        sq_term: TermId,
        sq_coeff: Rational64,
        linear_var: TermId,
        linear_coeff: Rational64,
        rhs: Rational64,
    },
    /// `linear_var >= const`
    LinearGe { var: TermId, bound: Rational64 },
    /// `linear_var > const`
    LinearGt { var: TermId, bound: Rational64 },
}

impl Solver {
    /// Dispatch nonlinear arithmetic assertions to the full NIA/NRA polynomial
    /// solver.
    ///
    /// Translates all top-level assertions to polynomial form and runs either
    /// `NiaSolver` (integer) or `NlsatSolver` (real). Returns a definitive
    /// `SolverResult` when the solver is conclusive, or `None` to fall
    /// through to CDCL(T).
    ///
    /// Handles:
    /// - `x * y`, `x * y * z` (products of distinct variables)
    /// - `x * x` (squares / higher powers via repeated multiplication)
    /// - `(x + 1) * (y - 2)` (products of linear expressions)
    pub(super) fn dispatch_nl_solver(&self, manager: &mut TermManager) -> Option<SolverResult> {
        // ── Path 1: explicit logic string (UNCHANGED) ──────────────────────
        // When the benchmark declares its logic (`QF_NIA`/`QF_NRA`/`QF_NIRA`,
        // possibly with a leading `QF_`), key on the string exactly as before.
        // The z3-parity corpus hits this path and must stay byte-identical.
        if let Some(logic) = self.logic.as_deref() {
            let mut is_nia =
                logic.contains("NIA") || (logic.contains("NIRA") && !logic.contains("NRA"));
            // `NIRA` is MIXED integer+real. Routing it through the INTEGER nlsat
            // (`dispatch_nia_constraints(.., true)`) INTEGERIZES every variable,
            // including the real-sorted ones — so an independent real constraint
            // with no integer solution (e.g. `1.0 < y < 2.0`) is reported as a
            // SPURIOUS `unsat`. Only treat `NIRA` as pure-integer NIA when the
            // problem has NO real-sorted term; otherwise fall through to CDCL(T)
            // (sound: the linear-real part is handled there and the nonlinear
            // part yields the sound `Unknown`).
            if is_nia
                && logic.contains("NIRA")
                && self
                    .assertions
                    .iter()
                    .any(|&a| term_mentions_real_sort(manager, a, 64))
            {
                is_nia = false;
            }
            let is_nra = logic.contains("NRA") && !is_nia;

            if is_nia {
                return dispatch_nia_constraints(&self.assertions, manager, true).map(|r| match r {
                    NlDispatchResult::Sat => SolverResult::Sat,
                    NlDispatchResult::Unsat => SolverResult::Unsat,
                });
            } else if is_nra {
                return dispatch_nra_constraints(&self.assertions, manager).map(|r| match r {
                    NlDispatchResult::Sat => SolverResult::Sat,
                    NlDispatchResult::Unsat => SolverResult::Unsat,
                });
            }
            // An explicit logic that is neither NIA/NRA/NIRA (e.g. `QF_LIA`,
            // `QF_UF`) is a deliberate statement that the problem is linear /
            // not nonlinear-arithmetic — do NOT second-guess it with the
            // term-based path below. Fall through to CDCL(T).
            return None;
        }

        // ── Path 2: NO logic string — verus `by(nonlinear_arith)` shape ────
        // Verus emits NO `(set-logic …)` and never asserts native `(* …)` in a
        // goal. The nonlinear product is the UNINTERPRETED wrapper `Mul`/`RMul`
        // (`Mul`→Int, `RMul`→Real), tied to native multiplication ONLY by the
        // asserted bridge axioms `(forall ((x ..)(y ..)) (= (Mul x y) (* x y)))`.
        // Detect that shape term-wise and route it to nlsat.
        self.dispatch_nl_via_mul_bridge(manager)
    }

    /// Term-based nlsat activation for the verus `Mul`/`RMul`-encoded shape.
    ///
    /// SOUNDNESS — this only ever returns `Unsat`, never `Sat`. The focused
    /// constraint set we build is a logical CONSEQUENCE of (a subset of) the
    /// original assertions, so subset-UNSAT ⟹ full-UNSAT (sound). A `Sat`/model
    /// over that focused subset says nothing about the full formula, so we drop
    /// it to `None` (→ CDCL(T) → sound `Unknown`/`Sat`). See the per-step notes.
    fn dispatch_nl_via_mul_bridge(&self, manager: &mut TermManager) -> Option<SolverResult> {
        // (a) Scan the asserted set for `Mul`/`RMul` UF APPLICATIONS.
        let mut has_mul = false; // integer `Mul`
        let mut has_rmul = false; // real `RMul`
        for &a in &self.assertions {
            scan_mul_rmul_apps(a, manager, &mut has_mul, &mut has_rmul, 64);
        }
        if !has_mul && !has_rmul {
            return None;
        }

        // (b) BRIDGE-AXIOM PRESENCE CHECK. We may only treat `(Mul a b)` as the
        // product `(* a b)` because the bridge axiom `(= (Mul x y) (* x y))` is
        // asserted (so `Mul` IS multiplication in the theory). Without it, `Mul`
        // is a genuine uninterpreted function ⇒ leave it to EUF ⇒ never rewrite.
        // The SAME gating applies to every spine symbol we fold (`Add`/`Sub` and
        // the real analogs): a goal like `(Add (Sub (Mul x x) (Mul 2 x)) 1)`
        // (= `x² − 2x + 1`) only reaches the reduction-KB once the additive
        // wrappers are folded to native `+`/`-` too — but each only when ITS
        // bridge axiom is present.
        let has_bridge = |sym: &str| {
            self.assertions
                .iter()
                .any(|&a| assertion_is_bridge_axiom(a, manager, sym))
        };
        let spine = SpineRewrite {
            mul: has_mul && has_bridge("Mul"),
            rmul: has_rmul && has_bridge("RMul"),
            add: has_bridge("Add"),
            sub: has_bridge("Sub"),
            radd: has_bridge("RAdd"),
            rsub: has_bridge("RSub"),
        };

        // Only proceed when a rewritable nonlinear PRODUCT is present — the
        // additive spine alone is linear and never needs nlsat.
        if !spine.mul && !spine.rmul {
            // A `Mul`/`RMul` with no bridge axiom is genuinely uninterpreted.
            return None;
        }

        // (d) SYMBOL-BASED ROUTING with the never-integerize-a-real rule.
        //   - any `RMul` (real) present and rewritable  ⇒ NRA (reals);
        //   - `Mul`-only (integer)                       ⇒ NIA.
        // A MIXED obligation (both `Mul` and `RMul` used) must NOT be sent to
        // the INTEGER nlsat — it would integerize the real-sorted vars and could
        // fabricate a spurious `unsat` (the NIRA hazard). We route mixed to NRA
        // (which keeps reals real); but if the integer `Mul` would then be left
        // un-rewritten (no real bridge to carry it) the integer part is dropped,
        // which is fine for the `Unsat`-only trust we apply. When in doubt
        // (e.g. we cannot rewrite the symbol that drives the routing) → `None`.
        let route_real = spine.rmul;
        // If reals are involved we never integerize: route to NRA. Otherwise the
        // problem is pure-integer `Mul` and routes to NIA.
        let integer_mode = !route_real;

        // (c) Build the FOCUSED assertion set: walk each top-level assertion,
        // peel `Not`/`Implies` polarity to surface the goal's comparison atoms,
        // fold the verus arithmetic-spine UFs (`Mul`/`Add`/`Sub`/…) to native
        // operators inside them, and collect ONLY the arithmetic comparison atoms
        // we can model. Everything else (the prelude `Forall`/`Apply`/`Div`/`Mod`
        // noise) is intentionally dropped — which is exactly why we trust UNSAT
        // only.
        let mut focused: Vec<TermId> = Vec::new();
        for &a in &self.assertions {
            collect_focused_nl_atoms(
                a,
                true, // positive polarity at the top level
                manager,
                &spine,
                &mut focused,
            );
        }
        if focused.is_empty() {
            return None;
        }

        // Dispatch the focused, native-`*` set. `dispatch_n{ia,ra}_constraints`
        // already return `None` when they cannot decide, and the focused set is
        // a consequence of the originals — so a returned `Unsat` is sound for the
        // full formula. We MAP AWAY any `Sat`: subset-sat ⊭ full-sat.
        let result = if route_real {
            dispatch_nra_constraints(&focused, manager)
        } else {
            dispatch_nia_constraints(&focused, manager, integer_mode)
        };
        match result {
            Some(NlDispatchResult::Unsat) => Some(SolverResult::Unsat),
            // SOUNDNESS: never trust a focused-subset `Sat` for the full formula.
            Some(NlDispatchResult::Sat) | None => None,
        }
    }

    /// Check nonlinear arithmetic constraints for early UNSAT detection.
    ///
    /// Returns `true` if the constraint set is detected as UNSAT.
    pub(super) fn check_nonlinear_constraints(&self, manager: &TermManager) -> bool {
        // Only run for NIA/NRA logics
        let is_nl = self
            .logic
            .as_deref()
            .map(|l| l.contains("NIA") || l.contains("NRA") || l.contains("NIRA"))
            .unwrap_or(false);

        if !is_nl {
            return false;
        }

        // Collect nonlinear atoms from all top-level assertions
        let mut atoms: Vec<NlAtom> = Vec::new();
        for &assertion in &self.assertions {
            self.collect_nl_atoms(assertion, manager, &mut atoms);
        }

        if atoms.is_empty() {
            return false;
        }

        // Check pattern 1: x^2 = c where c < 0 (never has a real solution)
        for atom in &atoms {
            if let NlAtom::SqEq { val, .. } = atom {
                if *val < Rational64::zero() {
                    return true;
                }
            }
        }

        // Check pattern 2: x^2 = c where c is not a perfect square (integer context)
        for atom in &atoms {
            if let NlAtom::SqEq {
                val,
                is_integer_sort,
                ..
            } = atom
            {
                if *is_integer_sort && *val >= Rational64::zero() {
                    if let Some(n) = val.to_i64() {
                        if n >= 0 && !is_perfect_square(n as u64) {
                            return true;
                        }
                    }
                }
            }
        }

        // Check pattern 3: system contradictions involving squares.
        //
        // Look for triples:
        //   (A) sq_term > 0                    [or sq_term >= 1 in integer case]
        //   (B) sq_term * a + var * b = c      [sum constraint]
        //   (C) var >= d                        [lower bound on var]
        //
        // where sq > 0 and b * var = c - a * sq, so var = (c - a*sq) / b.
        // Combined with var >= d: (c - a*sq)/b >= d.
        // If sq > 0 (sq >= 1 for int, sq > 0 for real) and a > 0, then
        // a*sq >= a (int) or a*sq > 0 (real), so c - a*sq < c (for positive a).
        // When d = 0 (y >= 0) and c = 0: c - a*sq = -a*sq <= -a < 0,
        // but we need var >= 0 — contradiction.
        //
        // Concretely, check:
        //   sq > 0  AND  sq + v = 0  AND  v >= 0
        // → v = -sq < 0  contradicts  v >= 0
        if self.check_sq_sum_bound_contradiction(&atoms) {
            return true;
        }

        false
    }

    /// Check for the "sq > 0 AND sq + v = 0 AND v >= 0" type contradiction.
    fn check_sq_sum_bound_contradiction(&self, atoms: &[NlAtom]) -> bool {
        // Build sets for quick lookup
        let sq_gt_zero: Vec<TermId> = atoms
            .iter()
            .filter_map(|a| {
                if let NlAtom::SqGtZero { sq_term } = a {
                    Some(*sq_term)
                } else {
                    None
                }
            })
            .collect();

        // For each "sq + coeff * var = rhs" constraint, check if we have sq > 0
        // and var >= -rhs/coeff is violated
        for atom in atoms {
            let NlAtom::SqPlusLinearEq {
                sq_term,
                sq_coeff,
                linear_var,
                linear_coeff,
                rhs,
            } = atom
            else {
                continue;
            };

            // Only handle the case where both sq_coeff and linear_coeff are non-zero
            if sq_coeff.is_zero() || linear_coeff.is_zero() {
                continue;
            }

            // Check if sq_term is known to be > 0
            let sq_positive = sq_gt_zero.contains(sq_term);
            if !sq_positive {
                continue;
            }

            // From: sq_coeff * sq + linear_coeff * var = rhs
            // → var = (rhs - sq_coeff * sq) / linear_coeff
            // If sq > 0 (at least epsilon > 0):
            // For real: sq > 0, so sq_coeff * sq > 0 when sq_coeff > 0
            //   → rhs - sq_coeff * sq < rhs
            //   → var < rhs / linear_coeff  (when linear_coeff > 0)
            //   OR var > rhs / linear_coeff  (when linear_coeff < 0)

            // The var = (rhs - sq_coeff * sq) / linear_coeff must satisfy
            // any lower bounds we have on var.
            let var_expr_at_sq_zero = *rhs / *linear_coeff; // value of var if sq=0

            // The sign of d(var)/d(sq) = -sq_coeff / linear_coeff
            // If sq increases from 0 (since sq > 0), var moves in direction -sq_coeff/linear_coeff

            // Check against all >= bounds on linear_var
            for bound_atom in atoms {
                let bound = match bound_atom {
                    NlAtom::LinearGe { var, bound } if *var == *linear_var => bound,
                    _ => continue,
                };

                // We need: var >= bound
                // From the sum constraint, as sq→0+, var→var_expr_at_sq_zero
                // If the sum constraint requires var < bound for all sq > 0,
                // that contradicts var >= bound.

                // Direction: d(var)/d(sq) = -sq_coeff / linear_coeff
                let deriv_sign = -(*sq_coeff) / *linear_coeff;

                // If deriv_sign < 0, then as sq increases (sq > 0), var decreases.
                // At sq = 0: var = var_expr_at_sq_zero
                // For all sq > 0: var < var_expr_at_sq_zero
                // If var_expr_at_sq_zero <= bound, then for sq > 0: var < bound — contradiction with var >= bound.

                if deriv_sign < Rational64::zero() && var_expr_at_sq_zero <= *bound {
                    return true;
                }

                // If deriv_sign > 0, then as sq increases (sq > 0), var increases.
                // The infimum is at sq = 0 (var → var_expr_at_sq_zero from above).
                // For all sq > 0: var > var_expr_at_sq_zero.
                // If var_expr_at_sq_zero >= bound, no contradiction from this alone.
                // But if we also have an upper bound on var that forces a contradiction...
                // For now, skip this case.
            }

            // Also check against strict lower bounds (LinearGt)
            for bound_atom in atoms {
                let bound = match bound_atom {
                    NlAtom::LinearGt { var, bound } if *var == *linear_var => bound,
                    _ => continue,
                };

                let deriv_sign = -(*sq_coeff) / *linear_coeff;

                // If deriv_sign < 0, as sq > 0: var < var_expr_at_sq_zero
                // Contradiction if var_expr_at_sq_zero <= bound (need var > bound, but var < bound)
                if deriv_sign < Rational64::zero() && var_expr_at_sq_zero <= *bound {
                    return true;
                }
            }
        }

        false
    }

    /// Collect nonlinear atoms from a term (top-level assertion).
    fn collect_nl_atoms(&self, term_id: TermId, manager: &TermManager, atoms: &mut Vec<NlAtom>) {
        let Some(term) = manager.get(term_id) else {
            return;
        };

        match &term.kind {
            TermKind::Eq(lhs, rhs) => {
                self.extract_nl_eq(*lhs, *rhs, manager, atoms);
            }
            TermKind::Gt(lhs, rhs) => {
                // lhs > rhs  i.e. lhs - rhs > 0
                self.extract_nl_comparison(*lhs, *rhs, CompOp::Gt, manager, atoms);
            }
            TermKind::Ge(lhs, rhs) => {
                self.extract_nl_comparison(*lhs, *rhs, CompOp::Ge, manager, atoms);
            }
            TermKind::Lt(lhs, rhs) => {
                // lhs < rhs  →  rhs > lhs
                self.extract_nl_comparison(*rhs, *lhs, CompOp::Gt, manager, atoms);
            }
            TermKind::Le(lhs, rhs) => {
                // lhs <= rhs  →  rhs >= lhs
                self.extract_nl_comparison(*rhs, *lhs, CompOp::Ge, manager, atoms);
            }
            TermKind::And(args) => {
                for &arg in args {
                    self.collect_nl_atoms(arg, manager, atoms);
                }
            }
            _ => {}
        }
    }

    /// Extract atoms from an equality `lhs = rhs`.
    fn extract_nl_eq(
        &self,
        lhs: TermId,
        rhs: TermId,
        manager: &TermManager,
        atoms: &mut Vec<NlAtom>,
    ) {
        // Try: is lhs a pure square (x * x) and rhs a constant?
        if let Some((sq_term, sq_coeff, is_int)) = self.extract_pure_square(lhs, manager) {
            if let Some(rhs_val) = self.extract_rational_const(rhs, manager) {
                // sq_coeff * sq_term = rhs_val  →  sq_term = rhs_val / sq_coeff
                if !sq_coeff.is_zero() {
                    let val = rhs_val / sq_coeff;
                    atoms.push(NlAtom::SqEq {
                        sq_term,
                        val,
                        is_integer_sort: is_int,
                    });
                    return;
                }
            }
        }

        // Try reversed: rhs is pure square, lhs is constant
        if let Some((sq_term, sq_coeff, is_int)) = self.extract_pure_square(rhs, manager) {
            if let Some(lhs_val) = self.extract_rational_const(lhs, manager) {
                if !sq_coeff.is_zero() {
                    let val = lhs_val / sq_coeff;
                    atoms.push(NlAtom::SqEq {
                        sq_term,
                        val,
                        is_integer_sort: is_int,
                    });
                    return;
                }
            }
        }

        // Try: lhs = Add(...) where the Add contains a square term plus a linear var
        // Pattern: (* x x) + y = const  or  y + (* x x) = const
        self.extract_nl_sum_eq(lhs, rhs, manager, atoms);
        self.extract_nl_sum_eq(rhs, lhs, manager, atoms);
    }

    /// Extract "sq_term + linear_var = rhs" from a sum equality.
    fn extract_nl_sum_eq(
        &self,
        sum_side: TermId,
        const_side: TermId,
        manager: &TermManager,
        atoms: &mut Vec<NlAtom>,
    ) {
        let Some(rhs_val) = self.extract_rational_const(const_side, manager) else {
            return;
        };

        let Some(sum_term) = manager.get(sum_side) else {
            return;
        };

        let TermKind::Add(args) = &sum_term.kind else {
            return;
        };

        // Try to identify: one arg is a pure square, the rest are linear vars
        let mut sq_term_opt: Option<(TermId, Rational64)> = None;
        let mut linear_term_opt: Option<(TermId, Rational64)> = None;
        let mut ok = true;

        for &arg in args {
            if let Some((sq_term, sq_coeff, _)) = self.extract_pure_square(arg, manager) {
                if sq_term_opt.is_some() {
                    ok = false;
                    break;
                }
                sq_term_opt = Some((sq_term, sq_coeff));
            } else if let Some((var, coeff)) = self.extract_linear_var(arg, manager) {
                if linear_term_opt.is_some() {
                    ok = false;
                    break;
                }
                linear_term_opt = Some((var, coeff));
            } else {
                ok = false;
                break;
            }
        }

        if !ok {
            return;
        }

        if let (Some((sq_term, sq_coeff)), Some((linear_var, linear_coeff))) =
            (sq_term_opt, linear_term_opt)
        {
            atoms.push(NlAtom::SqPlusLinearEq {
                sq_term,
                sq_coeff,
                linear_var,
                linear_coeff,
                rhs: rhs_val,
            });
        }
    }

    /// Extract atoms from a comparison `lhs OP 0` or `lhs OP rhs`.
    fn extract_nl_comparison(
        &self,
        lhs: TermId,
        rhs: TermId,
        op: CompOp,
        manager: &TermManager,
        atoms: &mut Vec<NlAtom>,
    ) {
        // Check if lhs is a pure square and rhs is a constant.
        // After normalization: sq_term OP (rhs_val / sq_coeff)
        if let Some((sq_term, sq_coeff, _)) = self.extract_pure_square(lhs, manager) {
            if let Some(rhs_val) = self.extract_rational_const(rhs, manager) {
                if !sq_coeff.is_zero() {
                    // sq_coeff * sq_term OP rhs_val
                    // → sq_term OP rhs_val/sq_coeff  (flip op if sq_coeff < 0)
                    let normalized = rhs_val / sq_coeff;
                    let effective_op = if sq_coeff < Rational64::zero() {
                        op.flip()
                    } else {
                        op
                    };
                    match effective_op {
                        CompOp::Gt => {
                            if normalized < Rational64::zero() {
                                // sq > negative → always true, not useful
                            } else if normalized.is_zero() {
                                atoms.push(NlAtom::SqGtZero { sq_term });
                            }
                        }
                        CompOp::Ge => {
                            if normalized <= Rational64::zero() {
                                atoms.push(NlAtom::SqGeZero { sq_term });
                            }
                        }
                    }
                    return;
                }
            }
        }

        // Check if this is a simple linear comparison: var OP const
        if let Some((var, coeff)) = self.extract_linear_var(lhs, manager) {
            if let Some(rhs_val) = self.extract_rational_const(rhs, manager) {
                if !coeff.is_zero() {
                    // coeff * var OP rhs_val
                    // → var OP rhs_val/coeff (flip op if coeff < 0)
                    let bound = rhs_val / coeff;
                    let effective_op = if coeff < Rational64::zero() {
                        op.flip()
                    } else {
                        op
                    };
                    match effective_op {
                        CompOp::Gt => atoms.push(NlAtom::LinearGt { var, bound }),
                        CompOp::Ge => atoms.push(NlAtom::LinearGe { var, bound }),
                    }
                }
                return;
            }
        }

        // Also handle reversed (const OP lhs → lhs OP' const) but skip for now
        // since the benchmark uses canonical form (lhs > 0, var >= 0)
        let _ = (lhs, rhs, op, manager, atoms);
    }

    /// Extract a pure square: a Mul term where all factors are the same variable.
    /// Returns `(representative_var_term, coefficient, is_integer_sort)` or None.
    ///
    /// Handles patterns like:
    /// - `(* x x)` → Some((x_term, 1, is_int))
    /// - `(* 2 x x)` → Some((x_term, 2, is_int))  [if we ever see this]
    fn extract_pure_square(
        &self,
        term_id: TermId,
        manager: &TermManager,
    ) -> Option<(TermId, Rational64, bool)> {
        let term = manager.get(term_id)?;

        match &term.kind {
            TermKind::Mul(args) => {
                let mut const_coeff = Rational64::one();
                let mut var_factors: Vec<TermId> = Vec::new();

                for &arg in args {
                    let arg_term = manager.get(arg)?;
                    match &arg_term.kind {
                        TermKind::IntConst(n) => {
                            let v = n.to_i64()?;
                            const_coeff *= Rational64::from_integer(v);
                        }
                        TermKind::RealConst(r) => {
                            const_coeff *= *r;
                        }
                        TermKind::Var(_) => {
                            var_factors.push(arg);
                        }
                        _ => return None, // nested expressions not handled
                    }
                }

                // Must have exactly 2 variable factors and they must be the same
                if var_factors.len() == 2 && var_factors[0] == var_factors[1] {
                    let v = var_factors[0];
                    let vt = manager.get(v)?;
                    let is_int = vt.sort == manager.sorts.int_sort;
                    Some((v, const_coeff, is_int))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Extract a simple linear variable term with coefficient.
    /// Returns `(var_term_id, coefficient)` or None.
    ///
    /// Handles:
    /// - `x` → Some((x, 1))
    /// - `(* c x)` → Some((x, c))
    fn extract_linear_var(
        &self,
        term_id: TermId,
        manager: &TermManager,
    ) -> Option<(TermId, Rational64)> {
        let term = manager.get(term_id)?;

        match &term.kind {
            TermKind::Var(_) => Some((term_id, Rational64::one())),
            TermKind::Mul(args) => {
                let mut const_coeff = Rational64::one();
                let mut var_opt: Option<TermId> = None;

                for &arg in args {
                    let arg_term = manager.get(arg)?;
                    match &arg_term.kind {
                        TermKind::IntConst(n) => {
                            let v = n.to_i64()?;
                            const_coeff *= Rational64::from_integer(v);
                        }
                        TermKind::RealConst(r) => {
                            const_coeff *= *r;
                        }
                        TermKind::Var(_) => {
                            if var_opt.is_some() {
                                return None; // multiple vars → nonlinear
                            }
                            var_opt = Some(arg);
                        }
                        _ => return None,
                    }
                }

                var_opt.map(|v| (v, const_coeff))
            }
            TermKind::Neg(inner) => {
                let (v, coeff) = self.extract_linear_var(*inner, manager)?;
                Some((v, -coeff))
            }
            _ => None,
        }
    }

    /// Extract a rational constant from a term.
    ///
    /// Handles:
    /// - `IntConst(n)` → n
    /// - `RealConst(r)` → r
    /// - `Neg(x)` → -extract(x)
    /// - `Sub(0, x)` → -extract(x)  [unary minus is parsed as Sub(0, x)]
    /// - `Sub(x, y)` → extract(x) - extract(y)
    fn extract_rational_const(&self, term_id: TermId, manager: &TermManager) -> Option<Rational64> {
        let term = manager.get(term_id)?;

        match &term.kind {
            TermKind::IntConst(n) => {
                let v = n.to_i64()?;
                Some(Rational64::from_integer(v))
            }
            TermKind::RealConst(r) => Some(*r),
            TermKind::Neg(inner) => {
                let v = self.extract_rational_const(*inner, manager)?;
                Some(-v)
            }
            TermKind::Sub(lhs, rhs) => {
                let lv = self.extract_rational_const(*lhs, manager)?;
                let rv = self.extract_rational_const(*rhs, manager)?;
                Some(lv - rv)
            }
            TermKind::Add(args) => {
                let mut acc = Rational64::zero();
                for &arg in args {
                    acc += self.extract_rational_const(arg, manager)?;
                }
                Some(acc)
            }
            _ => None,
        }
    }

    /// SOUND early-UNSAT for ANY term (linear, nonlinear, or uninterpreted): if
    /// the asserted top-level conjuncts pin mutually-infeasible LITERAL bounds on
    /// the SAME hash-consed `TermId`, the formula is UNSAT regardless of what the
    /// term denotes. This is the TRICHOTOMY / total-order fact made operational —
    /// no real value is both `> c` and `< c`, nor in two disjoint intervals, nor
    /// equal to two distinct constants. It catches conjunctions like
    /// `x*y > 0 ∧ x*y < 0` where the nonlinear product is carried opaquely (its
    /// bounds never reach LRA as numeric bounds on a shared arith variable), which
    /// the CDCL(T) relaxation would otherwise report a spurious `sat`.
    ///
    /// SOUNDNESS — can NEVER produce a false `unsat`: every recorded bound is a
    /// DIRECTLY ASSERTED top-level conjunct `t OP c` with `c` a literal rational
    /// and `t` one shared `TermId`. The walk descends ONLY positive `And` (every
    /// conjunct of a top-level `∧` is asserted) and stops at `Not`/`Or`/`Implies`/
    /// `Ite`/`Distinct`/quantifiers — so it never assumes an un-asserted sub-bound.
    /// The emptiness tests are the trivial interval-emptiness of literal rationals;
    /// the term's meaning is irrelevant. An empty bound set on `t` ⟹ no value of
    /// `t` satisfies the asserted conjuncts ⟹ UNSAT.
    pub(super) fn check_term_bound_infeasible(&self, manager: &TermManager) -> bool {
        let mut bounds: HashMap<TermId, TermBounds> = HashMap::new();
        for &a in &self.assertions {
            self.collect_term_bounds(a, manager, &mut bounds);
        }
        bounds.values().any(TermBounds::is_infeasible)
    }

    /// Walk a top-level assertion, recording literal bounds per term. Descends
    /// ONLY positive `And` conjuncts (see [`Self::check_term_bound_infeasible`]).
    fn collect_term_bounds(
        &self,
        t: TermId,
        manager: &TermManager,
        bounds: &mut HashMap<TermId, TermBounds>,
    ) {
        let Some(term) = manager.get(t) else {
            return;
        };
        match &term.kind {
            TermKind::And(args) => {
                for &a in args.iter() {
                    self.collect_term_bounds(a, manager, bounds);
                }
            }
            // `l > r` (strict) / `l >= r`: a lower bound on the non-const side, or
            // a (flipped) upper bound when the const is on the left.
            TermKind::Gt(l, r) => self.record_ineq(*l, *r, true, manager, bounds),
            TermKind::Ge(l, r) => self.record_ineq(*l, *r, false, manager, bounds),
            // `l < r` ≡ `r > l`; `l <= r` ≡ `r >= l`.
            TermKind::Lt(l, r) => self.record_ineq(*r, *l, true, manager, bounds),
            TermKind::Le(l, r) => self.record_ineq(*r, *l, false, manager, bounds),
            TermKind::Eq(l, r) => {
                if let Some(c) = self.extract_rational_const(*r, manager) {
                    bounds.entry(*l).or_default().eqs.push(c);
                } else if let Some(c) = self.extract_rational_const(*l, manager) {
                    bounds.entry(*r).or_default().eqs.push(c);
                }
            }
            // Not / Or / Implies / Ite / Distinct / Forall / Exists / … are NOT
            // descended — their sub-atoms are not asserted conjuncts.
            _ => {}
        }
    }

    /// Record the atom `a OP b` (`OP` = `>` strict / `>=` non-strict) as a bound
    /// when EXACTLY one side is a literal rational: `b = c` ⇒ lower bound on `a`
    /// (`a > c` / `a >= c`); `a = c` ⇒ upper bound on `b` (`b < c` / `b <= c`).
    fn record_ineq(
        &self,
        a: TermId,
        b: TermId,
        strict: bool,
        manager: &TermManager,
        bounds: &mut HashMap<TermId, TermBounds>,
    ) {
        if let Some(c) = self.extract_rational_const(b, manager) {
            bounds.entry(a).or_default().add_lo(c, strict);
        } else if let Some(c) = self.extract_rational_const(a, manager) {
            bounds.entry(b).or_default().add_hi(c, strict);
        }
    }
}

/// Accumulated literal bounds on a single (shared) term, for
/// [`Solver::check_term_bound_infeasible`]. `lo`/`hi` carry `(value, strict)`.
#[derive(Default)]
struct TermBounds {
    lo: Option<(Rational64, bool)>,
    hi: Option<(Rational64, bool)>,
    eqs: Vec<Rational64>,
}

impl TermBounds {
    /// Keep the tightest lower bound (larger value wins; at equal value a strict
    /// bound beats a non-strict one).
    fn add_lo(&mut self, v: Rational64, strict: bool) {
        let tighter = self
            .lo
            .is_none_or(|(cv, cs)| v > cv || (v == cv && strict && !cs));
        if tighter {
            self.lo = Some((v, strict));
        }
    }
    fn add_hi(&mut self, v: Rational64, strict: bool) {
        let tighter = self
            .hi
            .is_none_or(|(cv, cs)| v < cv || (v == cv && strict && !cs));
        if tighter {
            self.hi = Some((v, strict));
        }
    }
    /// Are these bounds jointly unsatisfiable for ANY real value of the term?
    fn is_infeasible(&self) -> bool {
        // Two distinct asserted equalities `t = a ∧ t = b`, a ≠ b.
        if let Some(&first) = self.eqs.first() {
            if self.eqs.iter().any(|&e| e != first) {
                return true;
            }
        }
        // An equality lying outside an asserted lo/hi (strict boundary counts).
        for &e in &self.eqs {
            if let Some((lo, strict)) = self.lo {
                if e < lo || (e == lo && strict) {
                    return true;
                }
            }
            if let Some((hi, strict)) = self.hi {
                if e > hi || (e == hi && strict) {
                    return true;
                }
            }
        }
        // Empty interval: `lo > hi`, or `lo == hi` with EITHER side strict.
        // (`lo == hi` with both non-strict is feasible at `t = lo`.)
        if let (Some((lo, sl)), Some((hi, sh))) = (self.lo, self.hi) {
            if lo > hi || (lo == hi && (sl || sh)) {
                return true;
            }
        }
        false
    }
}

/// Comparison operator (strict or non-strict greater-than).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CompOp {
    Gt,
    Ge,
}

impl CompOp {
    fn flip(self) -> Self {
        match self {
            CompOp::Gt => CompOp::Ge, // flipping strict: -x > c → x < -c → -x >= c (approx)
            CompOp::Ge => CompOp::Gt,
        }
    }
}

/// Check if n is a perfect square (i.e., there exists k such that k*k = n).
fn is_perfect_square(n: u64) -> bool {
    if n == 0 {
        return true;
    }
    let r = (n as f64).sqrt() as u64;
    // Check r and r+1 in case of floating-point rounding
    (r * r == n) || ((r + 1) * (r + 1) == n)
}

/// Does `t` (or any sub-term) carry the `Real` sort? Used to detect a MIXED
/// `NIRA` problem so the integer nlsat is not handed real variables (which it
/// would integerize, turning e.g. `1.0 < y < 2.0` into a spurious `unsat`).
/// Depth-bounded; conservative (`false` only when no real sort is reached).
fn term_mentions_real_sort(manager: &TermManager, t: TermId, depth: u32) -> bool {
    if depth == 0 {
        return false;
    }
    let Some(term) = manager.get(t) else {
        return false;
    };
    if term.sort == manager.sorts.real_sort {
        return true;
    }
    let any = |xs: &[TermId]| xs.iter().any(|&c| term_mentions_real_sort(manager, c, depth - 1));
    match &term.kind {
        TermKind::Not(a) | TermKind::Neg(a) => term_mentions_real_sort(manager, *a, depth - 1),
        TermKind::And(a) | TermKind::Or(a) | TermKind::Add(a) | TermKind::Mul(a)
        | TermKind::Distinct(a) => any(a),
        TermKind::Xor(a, b)
        | TermKind::Implies(a, b)
        | TermKind::Eq(a, b)
        | TermKind::Sub(a, b)
        | TermKind::Div(a, b)
        | TermKind::Mod(a, b)
        | TermKind::Lt(a, b)
        | TermKind::Le(a, b)
        | TermKind::Gt(a, b)
        | TermKind::Ge(a, b) => any(&[*a, *b]),
        TermKind::Ite(a, b, c) => any(&[*a, *b, *c]),
        TermKind::Apply { args, .. } => any(args),
        _ => false,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Term-based `Mul`/`RMul` nlsat activation (verus `by(nonlinear_arith)` shape)
// ─────────────────────────────────────────────────────────────────────────────

/// Resolve an `Apply` function symbol and test it against `name`.
fn func_name_is(manager: &TermManager, func: Spur, name: &str) -> bool {
    manager.resolve_str(func) == name
}

/// The native arithmetic operator a verus arithmetic-spine UF symbol bridges to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NativeArith {
    /// `Add`/`RAdd` → native `+`.
    Add,
    /// `Sub`/`RSub` → native `-`.
    Sub,
    /// `Mul`/`RMul` → native `*`.
    Mul,
}

/// Map a verus arithmetic-spine UF symbol to the native operator it bridges to,
/// or `None` if the symbol is not part of the POLYNOMIAL spine.
///
/// The polynomial spine is exactly the additive + multiplicative wrappers verus
/// emits for nonlinear goals: `Add`/`Sub`/`Mul` (Int) and `RAdd`/`RSub`/`RMul`
/// (Real). `EucDiv`/`EucMod`/`RDiv` are DELIBERATELY excluded — division and
/// modulo are not polynomial, so they must stay uninterpreted (an atom carrying
/// one then fails to translate to a polynomial and is soundly dropped).
fn spine_native_op(sym: &str) -> Option<NativeArith> {
    match sym {
        "Add" | "RAdd" => Some(NativeArith::Add),
        "Sub" | "RSub" => Some(NativeArith::Sub),
        "Mul" | "RMul" => Some(NativeArith::Mul),
        _ => None,
    }
}

/// Which verus arithmetic-spine UF symbols may be folded to native operators.
///
/// A symbol is enabled ONLY when its bridge axiom `(= (sym x y) (nativeop x y))`
/// is asserted, so `(sym a b)` is provably equal to `nativeop(a, b)` and the
/// rewrite preserves the atom's truth under every model. `mul`/`rmul` are the
/// nonlinear product (the nlsat trigger + sort routing); `add`/`sub`/`radd`/`rsub`
/// are the additive spine that WRAPS a product in a multi-term goal such as
/// `(Add (Sub (Mul x x) (Mul 2 x)) 1)` = `x² − 2x + 1`. Folding them is what lets
/// the focused atom translate to a polynomial and reach the reduction-KB.
#[derive(Debug, Clone, Copy, Default)]
struct SpineRewrite {
    mul: bool,
    rmul: bool,
    add: bool,
    sub: bool,
    radd: bool,
    rsub: bool,
}

impl SpineRewrite {
    /// Is the 2-argument UF `sym` enabled for rewriting (its bridge axiom present)?
    fn enabled(&self, sym: &str) -> bool {
        match sym {
            "Mul" => self.mul,
            "RMul" => self.rmul,
            "Add" => self.add,
            "Sub" => self.sub,
            "RAdd" => self.radd,
            "RSub" => self.rsub,
            _ => false,
        }
    }
}

/// Recursively scan `t` for **ground** `(Mul ..)` / `(RMul ..)` UF
/// **applications** (binary, the verus shape). Sets `has_mul` / `has_rmul`.
/// Depth-bounded.
///
/// IMPORTANT: this does NOT descend into `Forall`/`Exists` bodies. The bridge
/// axioms `(forall ((x ..)(y ..)) (= (Mul x y) (* x y)))` themselves contain an
/// applied `(Mul x y)` / `(RMul x y)` at the head — counting those would make a
/// pure-`Mul` (integer) goal look like it "uses `RMul`" (the real bridge axiom
/// is always in the prelude), mis-routing it to the REAL nlsat. We only care
/// whether the symbol is applied in the GROUND part (the goal), which is never
/// under a quantifier in this shape.
fn scan_mul_rmul_apps(
    t: TermId,
    manager: &TermManager,
    has_mul: &mut bool,
    has_rmul: &mut bool,
    depth: u32,
) {
    if depth == 0 || (*has_mul && *has_rmul) {
        return;
    }
    let Some(term) = manager.get(t) else {
        return;
    };
    // Do not look inside quantifier bodies (see doc comment).
    if matches!(
        term.kind,
        TermKind::Forall { .. } | TermKind::Exists { .. }
    ) {
        return;
    }
    if let TermKind::Apply { func, args } = &term.kind {
        if args.len() == 2 {
            if func_name_is(manager, *func, "Mul") {
                *has_mul = true;
            } else if func_name_is(manager, *func, "RMul") {
                *has_rmul = true;
            }
        }
    }
    for child in term_children(&term.kind) {
        scan_mul_rmul_apps(child, manager, has_mul, has_rmul, depth - 1);
    }
}

/// Is `assertion` the bridge axiom for `sym` — a `forall` whose body equates
/// `(sym x y)` with the native operator `sym` bridges to (`Mul`/`RMul`→`*`,
/// `Add`/`RAdd`→`+`, `Sub`/`RSub`→`-`)? Matches structurally (the `:qid`
/// `prelude_mul`/`prelude_add`/… is metadata not retained on the term, so we
/// verify the body shape directly). Accepts the body equality in either
/// orientation. We require the native operator's operands to be exactly the two
/// bound-variable arguments of `(sym …)`, in order — so an unrelated
/// `(= (sym a b) (op c d))` (or a wrong-operator `(= (Add a b) (* a b))`) can
/// never license the rewrite.
fn assertion_is_bridge_axiom(assertion: TermId, manager: &TermManager, sym: &str) -> bool {
    let Some(term) = manager.get(assertion) else {
        return false;
    };
    let TermKind::Forall { body, .. } = &term.kind else {
        return false;
    };
    let Some(body_term) = manager.get(*body) else {
        return false;
    };
    let TermKind::Eq(lhs, rhs) = &body_term.kind else {
        return false;
    };
    eq_sides_are_bridge(*lhs, *rhs, manager, sym) || eq_sides_are_bridge(*rhs, *lhs, manager, sym)
}

/// `apply_side` is `(sym a b)` and `native_side` is `(nativeop a b)` — the native
/// operator `sym` bridges to — with the SAME two arguments, in order.
fn eq_sides_are_bridge(
    apply_side: TermId,
    native_side: TermId,
    manager: &TermManager,
    sym: &str,
) -> bool {
    let Some(native_op) = spine_native_op(sym) else {
        return false;
    };
    let (Some(app), Some(nat)) = (manager.get(apply_side), manager.get(native_side)) else {
        return false;
    };
    let TermKind::Apply { func, args } = &app.kind else {
        return false;
    };
    if !func_name_is(manager, *func, sym) || args.len() != 2 {
        return false;
    }
    // The native side must be EXACTLY the bridged operator applied to the two
    // application arguments in order — not just "some product/sum".
    match native_op {
        NativeArith::Add => {
            matches!(&nat.kind, TermKind::Add(a) if a.len() == 2 && a[0] == args[0] && a[1] == args[1])
        }
        NativeArith::Sub => {
            matches!(&nat.kind, TermKind::Sub(x, y) if *x == args[0] && *y == args[1])
        }
        NativeArith::Mul => {
            matches!(&nat.kind, TermKind::Mul(a) if a.len() == 2 && a[0] == args[0] && a[1] == args[1])
        }
    }
}

/// Rewrite every enabled verus arithmetic-spine UF application — `(Mul a b)`,
/// `(Add a b)`, `(Sub a b)` and the real analogs `(RMul/RAdd/RSub a b)`, each
/// gated by its bridge axiom via `spine` — into the corresponding NATIVE operator
/// (`*`, `+`, `-`), recursively. Returns the rewritten term id (interning new
/// nodes as needed). Leaves all other structure unchanged. `None` only on a
/// malformed/missing node.
///
/// This is sound: the bridge axiom `(= (sym x y) (op x y))` makes `(sym a b)`
/// and `(op a b)` provably equal, so replacing one by the other inside an atom
/// preserves the atom's truth value under every model of the bridge axiom. A UF
/// whose bridge is absent (or a non-spine UF like `EucDiv`) is NOT folded — it
/// stays uninterpreted, so the atom then fails to translate to a polynomial and
/// is soundly dropped rather than mis-decided.
fn rewrite_spine(t: TermId, manager: &mut TermManager, spine: &SpineRewrite) -> Option<TermId> {
    let term = manager.get(t)?;
    match term.kind.clone() {
        TermKind::Apply { func, args } if args.len() == 2 => {
            let fname = manager.resolve_str(func).to_string();
            if spine.enabled(&fname) {
                let a = rewrite_spine(args[0], manager, spine)?;
                let b = rewrite_spine(args[1], manager, spine)?;
                // `enabled` ⟹ the symbol is a spine symbol, so this is `Some`.
                return Some(match spine_native_op(&fname)? {
                    NativeArith::Add => manager.mk_add([a, b]),
                    NativeArith::Sub => manager.mk_sub(a, b),
                    NativeArith::Mul => manager.mk_mul([a, b]),
                });
            }
            // Non-enabled / non-spine application: rewrite inside its args (a
            // nested product may still be foldable), but keep the UF itself — it
            // is genuinely uninterpreted here.
            let new_args: Vec<TermId> = args
                .iter()
                .map(|&c| rewrite_spine(c, manager, spine))
                .collect::<Option<Vec<_>>>()?;
            let sort = manager.get(t).map(|x| x.sort)?;
            Some(manager.mk_apply(&fname, new_args, sort))
        }
        TermKind::Add(args) => {
            let new: Vec<TermId> = args
                .iter()
                .map(|&c| rewrite_spine(c, manager, spine))
                .collect::<Option<Vec<_>>>()?;
            Some(manager.mk_add(new))
        }
        TermKind::Mul(args) => {
            let new: Vec<TermId> = args
                .iter()
                .map(|&c| rewrite_spine(c, manager, spine))
                .collect::<Option<Vec<_>>>()?;
            Some(manager.mk_mul(new))
        }
        TermKind::Sub(a, b) => {
            let na = rewrite_spine(a, manager, spine)?;
            let nb = rewrite_spine(b, manager, spine)?;
            Some(manager.mk_sub(na, nb))
        }
        TermKind::Neg(a) => {
            let na = rewrite_spine(a, manager, spine)?;
            Some(manager.mk_neg(na))
        }
        // Leaves and everything else: unchanged.
        _ => Some(t),
    }
}

/// Walk a top-level assertion, peeling boolean structure to surface the goal's
/// arithmetic COMPARISON atoms (`>=,>,<=,<,=`), rewriting `Mul`/`RMul` → native
/// `*` inside them, and pushing the rewritten comparison into `out`.
///
/// `polarity` tracks negation: at the top level it is `true`; each `Not` flips
/// it. A comparison reached under NEGATIVE polarity is emitted as its negation
/// (`>=` ↦ `<`, etc.) so the emitted atom is a logical CONSEQUENCE of the
/// (possibly negated) assertion — e.g. `(not (=> L (>= (Mul x x) 0)))` entails
/// `(< (Mul x x) 0)` (P→Q false ⟹ Q false), which after rewrite is
/// `(< (* x x) 0)`. We only descend the connectives where each surfaced atom is
/// genuinely ENTAILED by the assertion:
///   - `Not φ`            → flip polarity, descend (`¬¬a = a`);
///   - positive `And`     → each conjunct is entailed; descend all;
///   - negative `Or`      → `¬(a∨b)=¬a∧¬b`, each is entailed; descend all flipped;
///   - `(not (=> a b))`   → `a ∧ ¬b`; the `¬b` consequent is entailed (so under
///     the flip a positive `Implies` whose polarity is now negative descends
///     into the consequent `b` with the flipped polarity).
/// Anything else (positive `Or`, `Ite`, bare `Forall`/`Apply`, etc.) is NOT a
/// per-disjunct entailment, so we stop — the atom would not be sound to assert.
/// Because we only ever EMIT entailed atoms and trust UNSAT only, dropping the
/// rest is sound.
fn collect_focused_nl_atoms(
    t: TermId,
    polarity: bool,
    manager: &mut TermManager,
    spine: &SpineRewrite,
    out: &mut Vec<TermId>,
) {
    let Some(term) = manager.get(t) else {
        return;
    };
    match term.kind.clone() {
        TermKind::Not(inner) => {
            collect_focused_nl_atoms(inner, !polarity, manager, spine, out);
        }
        TermKind::And(args) if polarity => {
            for a in args {
                collect_focused_nl_atoms(a, true, manager, spine, out);
            }
        }
        TermKind::Or(args) if !polarity => {
            // ¬(a ∨ b ∨ …) = ¬a ∧ ¬b ∧ … — each ¬aᵢ is entailed.
            for a in args {
                collect_focused_nl_atoms(a, false, manager, spine, out);
            }
        }
        TermKind::Implies(a, b) if !polarity => {
            // ¬(a ⇒ b) = a ∧ ¬b — both the antecedent (positive) and the negated
            // consequent are entailed.
            collect_focused_nl_atoms(a, true, manager, spine, out);
            collect_focused_nl_atoms(b, false, manager, spine, out);
        }
        TermKind::Eq(_, _)
        | TermKind::Ge(_, _)
        | TermKind::Gt(_, _)
        | TermKind::Le(_, _)
        | TermKind::Lt(_, _) => {
            if let Some(atom) =
                build_polarized_comparison(t, polarity, &term.kind.clone(), manager, spine)
            {
                out.push(atom);
            }
        }
        _ => {
            // Not a per-component entailment (positive Or, Ite, Forall, Apply,
            // arbitrary boolean glue, …) — stop; emitting here would be unsound.
        }
    }
}

/// Build the (possibly negated) comparison atom with `Mul`/`RMul` rewritten to
/// native `*`. With `polarity == true` the comparison is emitted as-is; with
/// `polarity == false` its NEGATION is emitted (`>=`↦`<`, `>`↦`<=`, `<=`↦`>`,
/// `<`↦`>=`). An `=` under negative polarity is a disequality, which the
/// polynomial path does not model as a single atom, so we drop it (returns
/// `None` → fall through; sound because dropping only loses precision).
fn build_polarized_comparison(
    orig: TermId,
    polarity: bool,
    kind: &TermKind,
    manager: &mut TermManager,
    spine: &SpineRewrite,
) -> Option<TermId> {
    // Pull the two sides.
    let (lhs, rhs) = match kind {
        TermKind::Eq(a, b)
        | TermKind::Ge(a, b)
        | TermKind::Gt(a, b)
        | TermKind::Le(a, b)
        | TermKind::Lt(a, b) => (*a, *b),
        _ => return None,
    };
    // Only bother when a rewritable `Mul`/`RMul` PRODUCT actually occurs in this
    // atom (otherwise it is plain linear/EUF glue, or a purely additive atom, and
    // adds nothing to the NONLINEAR sub-problem). The product may be nested under
    // `Add`/`Sub` wrappers — `scan_mul_rmul_apps` recurses into them.
    let mut hm = false;
    let mut hr = false;
    scan_mul_rmul_apps(orig, manager, &mut hm, &mut hr, 64);
    if !(hm && spine.mul) && !(hr && spine.rmul) {
        return None;
    }
    let l = rewrite_spine(lhs, manager, spine)?;
    let r = rewrite_spine(rhs, manager, spine)?;
    Some(match (kind, polarity) {
        (TermKind::Eq(..), true) => manager.mk_eq(l, r),
        (TermKind::Eq(..), false) => return None, // disequality — drop
        (TermKind::Ge(..), true) | (TermKind::Lt(..), false) => manager.mk_ge(l, r),
        (TermKind::Gt(..), true) | (TermKind::Le(..), false) => manager.mk_gt(l, r),
        (TermKind::Le(..), true) | (TermKind::Gt(..), false) => manager.mk_le(l, r),
        (TermKind::Lt(..), true) | (TermKind::Ge(..), false) => manager.mk_lt(l, r),
        _ => return None,
    })
}

/// Immediate sub-terms of `kind` (for the generic recursion in
/// [`scan_mul_rmul_apps`]). Skips quantifier bodies' bound-variable plumbing —
/// we still descend into a `Forall`/`Exists` body to find applied symbols.
fn term_children(kind: &TermKind) -> Vec<TermId> {
    match kind {
        TermKind::Not(a) | TermKind::Neg(a) => vec![*a],
        TermKind::And(a) | TermKind::Or(a) | TermKind::Add(a) | TermKind::Mul(a)
        | TermKind::Distinct(a) => a.to_vec(),
        TermKind::Xor(a, b)
        | TermKind::Implies(a, b)
        | TermKind::Eq(a, b)
        | TermKind::Sub(a, b)
        | TermKind::Div(a, b)
        | TermKind::Mod(a, b)
        | TermKind::Lt(a, b)
        | TermKind::Le(a, b)
        | TermKind::Gt(a, b)
        | TermKind::Ge(a, b) => vec![*a, *b],
        TermKind::Ite(a, b, c) => vec![*a, *b, *c],
        TermKind::Apply { args, .. } => args.to_vec(),
        TermKind::Forall { body, .. } | TermKind::Exists { body, .. } => vec![*body],
        _ => Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver::Solver;

    #[test]
    fn test_is_perfect_square() {
        assert!(is_perfect_square(0));
        assert!(is_perfect_square(1));
        assert!(is_perfect_square(4));
        assert!(is_perfect_square(9));
        assert!(is_perfect_square(16));
        assert!(is_perfect_square(25));
        assert!(!is_perfect_square(2));
        assert!(!is_perfect_square(3));
        assert!(!is_perfect_square(5));
        assert!(!is_perfect_square(6));
        assert!(!is_perfect_square(7));
        assert!(!is_perfect_square(8));
    }

    // ── Term-based `Mul`/`RMul` nlsat auto-detect (verus shape) ───────────────
    //
    // These build the post-`:pattern` shape lu-smt actually sees: NO logic
    // string, a `Mul`/`RMul` UF whose bridge axiom `(= (Mul x y) (* x y))` is
    // asserted, and a NEGATED goal `(not (=> label (>= (Mul x! x!) 0)))`.

    /// Build the integer `Mul` bridge axiom `∀ x y. (= (Mul x y) (* x y))`.
    fn mul_bridge(m: &mut TermManager) -> TermId {
        let int = m.sorts.int_sort;
        let x = m.mk_var("x", int);
        let y = m.mk_var("y", int);
        let app = m.mk_apply("Mul", [x, y], int);
        let native = m.mk_mul([x, y]);
        let body = m.mk_eq(app, native);
        m.mk_forall([("x", int), ("y", int)], body)
    }

    /// Build the real `RMul` bridge axiom `∀ x y. (= (RMul x y) (* x y))`.
    fn rmul_bridge(m: &mut TermManager) -> TermId {
        let real = m.sorts.real_sort;
        let x = m.mk_var("x", real);
        let y = m.mk_var("y", real);
        let app = m.mk_apply("RMul", [x, y], real);
        let native = m.mk_mul([x, y]);
        let body = m.mk_eq(app, native);
        m.mk_forall([("x", real), ("y", real)], body)
    }

    /// `(not (=> label cmp))` — verus's location-labelled negated goal.
    fn negated_goal(m: &mut TermManager, cmp: TermId) -> TermId {
        let boolsort = m.sorts.bool_sort;
        let label = m.mk_var("loclabel", boolsort);
        let imp = m.mk_implies(label, cmp);
        m.mk_not(imp)
    }

    fn solve_no_logic(assertions: Vec<TermId>, m: &mut TermManager) -> Option<SolverResult> {
        let mut s = Solver::new();
        // No logic string → the term-based path.
        s.logic = None;
        s.assertions = assertions;
        s.dispatch_nl_solver(m)
    }

    #[test]
    fn nl_provable_mul_square_reaches_nlsat_and_decides_unsat() {
        // `assert(x*x >= 0)` → negated goal `(not (=> L (>= (Mul x! x!) 0)))`.
        // The focused atom is `(< (* x! x!) 0)`, univariate, UNSAT → provable.
        let mut m = TermManager::new();
        let int = m.sorts.int_sort;
        let xv = m.mk_var("x!", int);
        let bridge = mul_bridge(&mut m);
        let mul = m.mk_apply("Mul", [xv, xv], int);
        let zero = m.mk_int(0);
        let ge = m.mk_ge(mul, zero);
        let goal = negated_goal(&mut m, ge);

        let r = solve_no_logic(vec![bridge, goal], &mut m);
        assert_eq!(
            r,
            Some(SolverResult::Unsat),
            "x*x>=0 obligation must reach nlsat and decide UNSAT (provable)"
        );
    }

    #[test]
    fn nl_invalid_mul_product_is_not_false_unsat() {
        // `assert(x*y >= 0)` → negated goal `(< (Mul x! y!) 0)` is SATISFIABLE
        // (x=-1, y=1). The bivariate atom is not univariate, so subset-UNSAT is
        // not trustworthy and subset-SAT is never trusted → sound `Unknown`
        // (None), NEVER a false UNSAT.
        let mut m = TermManager::new();
        let int = m.sorts.int_sort;
        let xv = m.mk_var("x!", int);
        let yv = m.mk_var("y!", int);
        let bridge = mul_bridge(&mut m);
        let mul = m.mk_apply("Mul", [xv, yv], int);
        let zero = m.mk_int(0);
        let ge = m.mk_ge(mul, zero);
        let goal = negated_goal(&mut m, ge);

        let r = solve_no_logic(vec![bridge, goal], &mut m);
        assert_ne!(
            r,
            Some(SolverResult::Unsat),
            "x*y>=0 obligation is INVALID — must NOT be a false UNSAT"
        );
    }

    #[test]
    fn mul_without_bridge_axiom_is_not_rewritten() {
        // Same `(Mul x! x!)` square goal but with NO bridge axiom asserted.
        // `Mul` is then a genuine uninterpreted function — we must NOT rewrite
        // it to `*`, so the nlsat path does not fire (sound Unknown / None).
        let mut m = TermManager::new();
        let int = m.sorts.int_sort;
        let xv = m.mk_var("x!", int);
        let mul = m.mk_apply("Mul", [xv, xv], int);
        let zero = m.mk_int(0);
        let ge = m.mk_ge(mul, zero);
        let goal = negated_goal(&mut m, ge);

        // Only the goal, no `(= (Mul x y) (* x y))` axiom.
        let r = solve_no_logic(vec![goal], &mut m);
        assert_eq!(
            r, None,
            "uninterpreted Mul (no bridge axiom) must not be rewritten → no nlsat verdict"
        );
    }

    #[test]
    fn rmul_real_square_routes_to_nra_not_nia() {
        // `assert(rx*rx >= 0)` over REALS via `RMul`. Routes to NRA (reals); the
        // focused atom `(< (* rx rx) 0)` is UNSAT (real squares ≥ 0) → provable.
        // Critically it must NOT integerize the real var (NRA, not NIA).
        let mut m = TermManager::new();
        let real = m.sorts.real_sort;
        let rx = m.mk_var("rx!", real);
        let bridge = rmul_bridge(&mut m);
        let mul = m.mk_apply("RMul", [rx, rx], real);
        let zero = m.mk_real(num_rational::Rational64::new(0, 1));
        let ge = m.mk_ge(mul, zero);
        let goal = negated_goal(&mut m, ge);

        let r = solve_no_logic(vec![bridge, goal], &mut m);
        assert_eq!(
            r,
            Some(SolverResult::Unsat),
            "rx*rx>=0 (RMul/real) must reach NRA and decide UNSAT (provable)"
        );
    }

    /// Build the integer `Add` bridge axiom `∀ x y. (= (Add x y) (+ x y))`.
    fn add_bridge(m: &mut TermManager) -> TermId {
        let int = m.sorts.int_sort;
        let x = m.mk_var("x", int);
        let y = m.mk_var("y", int);
        let app = m.mk_apply("Add", [x, y], int);
        let native = m.mk_add([x, y]);
        let body = m.mk_eq(app, native);
        m.mk_forall([("x", int), ("y", int)], body)
    }

    /// Build the integer `Sub` bridge axiom `∀ x y. (= (Sub x y) (- x y))`.
    fn sub_bridge(m: &mut TermManager) -> TermId {
        let int = m.sorts.int_sort;
        let x = m.mk_var("x", int);
        let y = m.mk_var("y", int);
        let app = m.mk_apply("Sub", [x, y], int);
        let native = m.mk_sub(x, y);
        let body = m.mk_eq(app, native);
        m.mk_forall([("x", int), ("y", int)], body)
    }

    /// The verus perfect-square goal body `(Add (Sub (Mul x x) (Mul 2 x)) 1)`
    /// (= `x² − 2x + 1`) built entirely from the `Add`/`Sub`/`Mul` UF spine.
    fn perfect_square_uf(m: &mut TermManager, xv: TermId) -> TermId {
        let int = m.sorts.int_sort;
        let xx = m.mk_apply("Mul", [xv, xv], int);
        let two = m.mk_int(2);
        let two_x = m.mk_apply("Mul", [two, xv], int);
        let sub = m.mk_apply("Sub", [xx, two_x], int);
        let one = m.mk_int(1);
        m.mk_apply("Add", [sub, one], int)
    }

    #[test]
    fn nl_perfect_square_additive_spine_reaches_kb_and_decides_unsat() {
        // THE perfect-square completeness lead, end-to-end at the unit level:
        // `(not (=> L (>= (Add (Sub (Mul x! x!) (Mul 2 x!)) 1) 0)))`. Only with the
        // `Add`/`Sub` bridges folded too does the focused atom translate to the
        // univariate quadratic `x²−2x+1 < 0`, which §G decides UNSAT (D=0, a>0).
        let mut m = TermManager::new();
        let int = m.sorts.int_sort;
        let xv = m.mk_var("x!", int);
        let mb = mul_bridge(&mut m);
        let ab = add_bridge(&mut m);
        let sb = sub_bridge(&mut m);
        let f = perfect_square_uf(&mut m, xv);
        let zero = m.mk_int(0);
        let ge = m.mk_ge(f, zero);
        let goal = negated_goal(&mut m, ge);

        let r = solve_no_logic(vec![mb, ab, sb, goal], &mut m);
        assert_eq!(
            r,
            Some(SolverResult::Unsat),
            "(x-1)^2 >= 0 obligation must reach the reduction-KB via the folded \
             additive spine and decide UNSAT (provable)"
        );
    }

    #[test]
    fn additive_spine_without_add_bridge_is_not_rewritten() {
        // SOUNDNESS / scope: the SAME perfect-square goal but with NO `Add` bridge
        // asserted. `Add` is then a genuine uninterpreted function — the focused
        // atom cannot translate to a polynomial, so the path declines (None). It
        // must never fabricate a verdict from an un-folded spine.
        let mut m = TermManager::new();
        let int = m.sorts.int_sort;
        let xv = m.mk_var("x!", int);
        let mb = mul_bridge(&mut m);
        let sb = sub_bridge(&mut m);
        let f = perfect_square_uf(&mut m, xv);
        let zero = m.mk_int(0);
        let ge = m.mk_ge(f, zero);
        let goal = negated_goal(&mut m, ge);

        // Mul + Sub bridges present, but Add is NOT bridged.
        let r = solve_no_logic(vec![mb, sb, goal], &mut m);
        assert_ne!(
            r,
            Some(SolverResult::Unsat),
            "an un-folded uninterpreted Add must not yield a verdict"
        );
    }

    #[test]
    fn nl_invalid_indefinite_quadratic_additive_spine_not_false_unsat() {
        // SOUNDNESS: `x² − 1 >= 0` is INVALID (false at x=0). Negated goal
        // `(< (Sub (Mul x! x!) 1) 0)` = `x²−1 < 0` is satisfiable (x=0) and has
        // D=4>0 (indefinite) — §G must DECLINE, never a false UNSAT.
        let mut m = TermManager::new();
        let int = m.sorts.int_sort;
        let xv = m.mk_var("x!", int);
        let mb = mul_bridge(&mut m);
        let sb = sub_bridge(&mut m);
        let xx = m.mk_apply("Mul", [xv, xv], int);
        let one = m.mk_int(1);
        let body = m.mk_apply("Sub", [xx, one], int);
        let zero = m.mk_int(0);
        let ge = m.mk_ge(body, zero);
        let goal = negated_goal(&mut m, ge);

        let r = solve_no_logic(vec![mb, sb, goal], &mut m);
        assert_ne!(
            r,
            Some(SolverResult::Unsat),
            "x^2 - 1 >= 0 is INVALID — its negation must NOT be a false UNSAT"
        );
    }

    #[test]
    fn nl_multivariate_sos_form_reaches_kb_and_decides_unsat() {
        // The verus SOS lead end-to-end: `(x − y)² ≥ 0` as the UF spine
        // `(Add (Sub (Mul x! x!) (Mul 2 (Mul x! y!))) (Mul y! y!))` (note the
        // NESTED `(Mul 2 (Mul x! y!))`). The spine folds every `Mul`/`Add`/`Sub`,
        // the focused atom becomes `x² − 2xy + y² < 0`, and §G-SOS decides it UNSAT
        // (the Gram matrix `[[1,−1],[−1,1]]` is PSD).
        let mut m = TermManager::new();
        let int = m.sorts.int_sort;
        let xv = m.mk_var("x!", int);
        let yv = m.mk_var("y!", int);
        let mb = mul_bridge(&mut m);
        let ab = add_bridge(&mut m);
        let sb = sub_bridge(&mut m);
        let xx = m.mk_apply("Mul", [xv, xv], int);
        let yy = m.mk_apply("Mul", [yv, yv], int);
        let xy = m.mk_apply("Mul", [xv, yv], int);
        let two = m.mk_int(2);
        let two_xy = m.mk_apply("Mul", [two, xy], int);
        let sub = m.mk_apply("Sub", [xx, two_xy], int);
        let f = m.mk_apply("Add", [sub, yy], int);
        let zero = m.mk_int(0);
        let ge = m.mk_ge(f, zero);
        let goal = negated_goal(&mut m, ge);

        let r = solve_no_logic(vec![mb, ab, sb, goal], &mut m);
        assert_eq!(
            r,
            Some(SolverResult::Unsat),
            "(x-y)² >= 0 obligation must reach §G-SOS and decide UNSAT (provable)"
        );
    }

    #[test]
    fn explicit_qf_nia_logic_path_unchanged() {
        // With an explicit `QF_NIA` logic and a NATIVE `(* x x)` square, the
        // UNCHANGED logic-string path must still fire (sanity that Path 1 stays
        // live and is not shadowed by the new term-based Path 2).
        let mut m = TermManager::new();
        let int = m.sorts.int_sort;
        let xv = m.mk_var("x", int);
        let sq = m.mk_mul([xv, xv]);
        let neg1 = m.mk_int(-1);
        let eq = m.mk_eq(sq, neg1); // x*x = -1  → UNSAT

        let mut s = Solver::new();
        s.logic = Some("QF_NIA".to_string());
        s.assertions = vec![eq];
        let r = s.dispatch_nl_solver(&mut m);
        assert_eq!(
            r,
            Some(SolverResult::Unsat),
            "explicit QF_NIA + (x*x = -1) must stay UNSAT on the unchanged logic path"
        );
    }

    #[test]
    fn fd_core_addon_decides_nonperfect_square_unsat() {
        // `x*x = 3` with `-3 ≤ x ≤ 3` is real-SAT (x = ±√3) but integer-UNSAT (3 is
        // not a perfect square) — the fragment the legacy `NiaSolver` is unsound on
        // (so its degree-2 `unsat` is NOT trusted) and §G's real-domain
        // discriminant cannot refute (it IS real-sat). Only the bounded `fd_core`
        // add-on decides it, soundly (interval over-approximation + G-UNSAT
        // re-verify). Validates the live dispatch consults fd_core for nonlinear
        // integer UNSAT.
        let mut m = TermManager::new();
        let int = m.sorts.int_sort;
        let xv = m.mk_var("x", int);
        let sq = m.mk_mul([xv, xv]);
        let three = m.mk_int(3);
        let eq = m.mk_eq(sq, three); // x*x = 3
        let lo = m.mk_int(-3);
        let hi = m.mk_int(3);
        let lob = m.mk_ge(xv, lo); // -3 ≤ x
        let hib = m.mk_le(xv, hi); //  x ≤ 3

        let mut s = Solver::new();
        s.logic = Some("QF_NIA".to_string());
        s.assertions = vec![eq, lob, hib];
        let r = s.dispatch_nl_solver(&mut m);
        assert_eq!(
            r,
            Some(SolverResult::Unsat),
            "bounded x*x=3 has no integer root — the fd_core add-on must decide UNSAT"
        );
    }

    #[test]
    fn fd_core_addon_zero_absorbing_disequality_unsat() {
        // `x = 0 ∧ x*x ≠ 0` is UNSAT by the zero-absorbing element (0·_ = 0 in any
        // ring), but a disequality over a product was historically reported sat
        // because the negated atom never reached the nonlinear engine. Now the
        // disequality is surfaced and fd_core's interval evaluation folds the zero
        // factor (`[0,0]·_ = [0,0]`), deciding UNSAT.
        let mut m = TermManager::new();
        let int = m.sorts.int_sort;
        let xv = m.mk_var("x", int);
        let zero = m.mk_int(0);
        let xeq0 = m.mk_eq(xv, zero); // x = 0
        let sq = m.mk_mul([xv, xv]);
        let sq_ne_0 = m.mk_distinct([sq, zero]); // x*x ≠ 0
        let conj = m.mk_and([xeq0, sq_ne_0]);

        let mut s = Solver::new();
        s.logic = Some("QF_NIA".to_string());
        s.assertions = vec![conj];
        let r = s.dispatch_nl_solver(&mut m);
        assert_eq!(
            r,
            Some(SolverResult::Unsat),
            "x=0 ∧ x²≠0 is UNSAT by the zero-absorbing element"
        );
    }
}
