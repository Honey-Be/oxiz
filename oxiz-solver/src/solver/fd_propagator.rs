//! `FdPropagator` — the finite-domain integer CP theory on the §4.2 `TheoryHooks`
//! bus.
//!
//! The `TheoryHooks` **bus-citizen wrapper** around the shared
//! [`fd_core`](oxiz_theories::fd_core) decision engine (the `oxiz-nl2` `fdlcg`
//! core). The pure engine lives in `oxiz-theories` so that BOTH consumers — the
//! live SMT nonlinear-integer dispatch (`dispatch_nia_constraints`) and this bus
//! citizen — reuse one verified core (a single funnel). This file is only the
//! glue that makes that engine a citizen of the **shared CDCL(T) trail** instead
//! of a private solver: it is the constraint-programming slice of the
//! multi-paradigm propagator bus (`AD1/docs/design/UNIFIED_VERIFICATION_GATE.md`)
//! and the reference implementation of the verified keystone
//! `oxiz-nl2-verification/src/cp_propagator.rs`.
//!
//! ## Where the trail draws the line (CDCL(T), not MCSAT)
//! The bus trail carries Boolean `Lit`s — it decides **which polynomial atoms are
//! asserted**, not integer variable values. So:
//!   * the Boolean-structure branching (which constraints hold) is the **trail's**;
//!   * the integer-variable search (bound propagation + bisection) stays **inside
//!     this theory** ([`fd_core`]'s own decision procedure), invoked at the trail's
//!     fixpoints.
//!
//! `final_check` runs the **cheap** [`fd_core::cheap_refute`] (linear
//! bound-propagation + interval conflict) after every Boolean fixpoint;
//! `final_check_complete` runs the **complete** [`fd_core::decide`] once per full
//! assignment, authorising `Sat` only with an exact integer model.
//!
//! ## Soundness (FALSE_UNSAT = 0, FALSE_SAT = 0)
//! The engine's guarantees (single-interval domains, monomial-wise interval
//! over-approximation, G-UNSAT re-verify, G-SAT model) are argued once in
//! [`fd_core`]. The bus adapter adds one contract: **the CDCL(T) bus has no
//! `Unknown` step**, so when the engine returns `Open`, `final_check_complete`
//! returns `Ok` (it cannot refute) but records [`FdVerdict::Open`] in
//! [`FdPropagator::verdict`]; the caller MUST downgrade a resulting `Sat` to
//! `Unknown` — the same `had_opaque` discipline adsmt uses for opaque asserts.
//! Returning `Ok` on `Open` is sound ONLY under that contract.

use smallvec::SmallVec;

use oxiz_math::polynomial::Polynomial;
use oxiz_sat::{Lit, TheoryHooks, TheoryReason, TheoryStep, Var};
use oxiz_theories::fd_core::{self, FdCmp, FdDecision};

/// The theory's completeness verdict for the caller's `Open ⇒ Unknown` downgrade.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FdVerdict {
    /// No assertion processed yet / nothing to decide.
    Trivial,
    /// The conjunction is integer-UNSAT (G-UNSAT re-verified by `fd_core`).
    Unsat,
    /// A concrete integer model was found and exactly checked (G-SAT).
    Sat,
    /// Could not decide soundly (open axis / budget). The caller MUST treat a
    /// resulting solver `Sat` as `Unknown`.
    Open,
}

/// A finite-domain integer CP theory on the `TheoryHooks` bus.
///
/// Each input atom `poly ⋈ 0` is abstracted by a Boolean `Var`; the trail decides
/// the `Var`, this theory decides integer feasibility of the resulting conjunction
/// through [`fd_core`].
pub struct FdPropagator {
    /// The atoms, indexed by the position the Boolean `Var` maps to.
    atoms: Vec<(Polynomial, FdCmp)>,
    /// Boolean atom `Var` → index into `atoms`.
    var_to_atom: rustc_hash::FxHashMap<Var, usize>,
    /// Index into `atoms` → its Boolean `Var` (the inverse of `var_to_atom`, for
    /// building propagations).
    atom_vars: Vec<Var>,
    /// Currently-asserted `(lit, atom index, polarity)`, in trail order.
    asserted: Vec<(Lit, usize, bool)>,
    /// `asserted.len()` checkpoints, one per live decision level (scoped rollback).
    frame_marks: Vec<usize>,
    /// The last completeness verdict (see [`FdPropagator::verdict`]).
    verdict: FdVerdict,
}

impl FdPropagator {
    /// Build a propagator from `(poly, cmp, boolean-var)` triples. The `Var` is the
    /// trail's Boolean abstraction of the atom `poly cmp 0`.
    #[must_use]
    pub fn new(atoms: Vec<(Polynomial, FdCmp, Var)>) -> Self {
        let mut polys = Vec::with_capacity(atoms.len());
        let mut atom_vars = Vec::with_capacity(atoms.len());
        let mut var_to_atom = rustc_hash::FxHashMap::default();
        for (poly, cmp, var) in atoms {
            var_to_atom.insert(var, polys.len());
            polys.push((poly, cmp));
            atom_vars.push(var);
        }
        FdPropagator {
            atoms: polys,
            var_to_atom,
            atom_vars,
            asserted: Vec::new(),
            frame_marks: Vec::new(),
            verdict: FdVerdict::Trivial,
        }
    }

    /// The theory's last completeness verdict. After `solve_with_hooks` returns
    /// `Sat`, the caller MUST downgrade it to `Unknown` if this is
    /// [`FdVerdict::Open`] (the CDCL(T) bus has no `Unknown` step — see the module
    /// docs; this is the `had_opaque` Sat→Unknown discipline).
    #[must_use]
    pub fn verdict(&self) -> FdVerdict {
        self.verdict
    }

    /// The polarity-resolved atoms currently asserted on the trail (a false-asserted
    /// atom contributes the negated comparison).
    fn active_atoms(&self) -> Vec<(Polynomial, FdCmp)> {
        self.asserted
            .iter()
            .map(|&(_, idx, polarity)| {
                let (poly, cmp) = &self.atoms[idx];
                (poly.clone(), if polarity { *cmp } else { cmp.negate() })
            })
            .collect()
    }

    /// The conflict clause: the negation of the asserted literals (all currently
    /// true), so the learned clause's literals are all currently false — the shape
    /// `TheoryStep::Conflict` consumes. A sound (whole-set) explanation;
    /// minimisation is a later optimisation.
    fn explanation(&self) -> SmallVec<[Lit; 8]> {
        self.asserted.iter().map(|&(lit, _, _)| lit.negate()).collect()
    }
}

impl TheoryHooks for FdPropagator {
    fn assign_hook(&mut self, lit: Lit, _level: u32) -> TheoryStep {
        if let Some(&idx) = self.var_to_atom.get(&lit.var()) {
            self.asserted.push((lit, idx, !lit.is_neg()));
        }
        TheoryStep::Ok
    }

    fn unassign_hook(&mut self, lit: Lit, _level: u32) {
        if let Some(pos) = self.asserted.iter().rposition(|&(l, _, _)| l == lit) {
            self.asserted.remove(pos);
        }
    }

    fn push_frame(&mut self, _level: u32) {
        self.frame_marks.push(self.asserted.len());
    }

    fn pop_frame(&mut self, _level: u32) {
        if let Some(mark) = self.frame_marks.pop() {
            self.asserted.truncate(mark);
        }
    }

    fn final_check(&mut self) -> TheoryStep {
        // CHEAP per-fixpoint check: linear bound-propagation + interval conflict.
        let active = self.active_atoms();
        if active.is_empty() {
            return TheoryStep::Ok;
        }
        if fd_core::cheap_refute(&active) {
            return TheoryStep::Conflict { explanation: self.explanation() };
        }
        // Theory PROPAGATION: emit a literal the asserted atoms FORCE, among the
        // not-yet-asserted atoms — sound by the keystone
        // `box_forced_lit_is_valid_propagation` (the literal holds on the whole box,
        // which over-approximates the asserted feasible set). Prunes the SAT search
        // exactly as the legacy eager theory path does.
        let asserted_idx: rustc_hash::FxHashSet<usize> =
            self.asserted.iter().map(|&(_, idx, _)| idx).collect();
        let cand: Vec<(usize, (Polynomial, FdCmp))> = self
            .atoms
            .iter()
            .enumerate()
            .filter(|(i, _)| !asserted_idx.contains(i))
            .map(|(i, (p, o))| (i, (p.clone(), *o)))
            .collect();
        if !cand.is_empty() {
            let cand_atoms: Vec<(Polynomial, FdCmp)> = cand.iter().map(|(_, a)| a.clone()).collect();
            if let Some(&(ci, truth)) = fd_core::forced_literals(&active, &cand_atoms).first() {
                let var = self.atom_vars[cand[ci].0];
                let lit = if truth { Lit::pos(var) } else { Lit::neg(var) };
                let reason = TheoryReason { asserting: lit, explanation: self.explanation() };
                return TheoryStep::Propagate { lit, reason };
            }
        }
        TheoryStep::Ok
    }

    fn final_check_complete(&mut self) -> TheoryStep {
        // COMPLETE check (full assignment): fd_core's branch-and-prune. `Unsat` ⇒ a
        // sound `Conflict`; otherwise `Ok`, with the completeness verdict recorded
        // for the caller's Sat→Unknown downgrade.
        let active = self.active_atoms();
        if active.is_empty() {
            self.verdict = FdVerdict::Trivial;
            return TheoryStep::Ok;
        }
        match fd_core::decide(&active) {
            FdDecision::Unsat => {
                self.verdict = FdVerdict::Unsat;
                TheoryStep::Conflict { explanation: self.explanation() }
            }
            FdDecision::Sat(_) => {
                self.verdict = FdVerdict::Sat;
                TheoryStep::Ok
            }
            FdDecision::Open => {
                self.verdict = FdVerdict::Open;
                TheoryStep::Ok
            }
        }
    }

    fn eval(&mut self, _atom: Var) -> Option<bool> {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use oxiz_math::polynomial::Var as PolyVar;
    use oxiz_sat::{Solver, SolverResult};

    fn poly(coeffs: &[(i64, &[(PolyVar, u32)])]) -> Polynomial {
        Polynomial::from_coeffs_int(coeffs)
    }

    #[test]
    fn fd_conjunction_unsat_is_solver_unsat() {
        // 0 < x ∧ x - 1 < 0  (integer)  ⇒ no integer ⇒ the trail must report UNSAT.
        let mut solver = Solver::new();
        let a0 = solver.new_var(); // abstracts  x > 0
        let a1 = solver.new_var(); // abstracts  x - 1 < 0
        solver.add_clause([Lit::pos(a0)]);
        solver.add_clause([Lit::pos(a1)]);
        let theory = FdPropagator::new(vec![
            (poly(&[(1, &[(0, 1)])]), FdCmp::Gt, a0),
            (poly(&[(1, &[(0, 1)]), (-1, &[])]), FdCmp::Lt, a1),
        ]);
        let (result, theory) = solver.solve_with_hooks(theory);
        assert_eq!(result, SolverResult::Unsat, "0<x<1 has no integer");
        assert_ne!(theory.verdict(), FdVerdict::Sat);
    }

    #[test]
    fn fd_bounded_box_is_sat() {
        // 0 ≤ x ∧ x ≤ 2 ∧ y = 1 ∧ x - y ≥ 0 : sat (x∈{1,2}, y=1).
        let mut solver = Solver::new();
        let a0 = solver.new_var();
        let a1 = solver.new_var();
        let a2 = solver.new_var();
        let a3 = solver.new_var();
        for a in [a0, a1, a2, a3] {
            solver.add_clause([Lit::pos(a)]);
        }
        let theory = FdPropagator::new(vec![
            (poly(&[(1, &[(0, 1)])]), FdCmp::Ge, a0),
            (poly(&[(1, &[(0, 1)]), (-2, &[])]), FdCmp::Le, a1),
            (poly(&[(1, &[(1, 1)]), (-1, &[])]), FdCmp::Eq, a2),
            (poly(&[(1, &[(0, 1)]), (-1, &[(1, 1)])]), FdCmp::Ge, a3),
        ]);
        let (result, theory) = solver.solve_with_hooks(theory);
        assert_eq!(result, SolverResult::Sat);
        assert_eq!(theory.verdict(), FdVerdict::Sat, "a concrete integer model exists");
    }

    #[test]
    fn fd_open_axis_is_not_false_unsat() {
        // x > 0 (integer): satisfiable but unbounded ⇒ Open, never Unsat.
        let mut solver = Solver::new();
        let a0 = solver.new_var();
        solver.add_clause([Lit::pos(a0)]);
        let theory = FdPropagator::new(vec![(poly(&[(1, &[(0, 1)])]), FdCmp::Gt, a0)]);
        let (result, theory) = solver.solve_with_hooks(theory);
        assert_ne!(result, SolverResult::Unsat, "an open-axis sat problem must not be unsat");
        assert_eq!(theory.verdict(), FdVerdict::Open, "unbounded ⇒ sound Open, not Sat");
    }

    #[test]
    fn fd_false_asserted_atom_negates() {
        // Assert ¬(x ≤ 0) i.e. x > 0, plus x - 1 < 0 ⇒ 0 < x < 1 ⇒ UNSAT, via the
        // false-polarity negation path (a0 forced FALSE).
        let mut solver = Solver::new();
        let a0 = solver.new_var(); // x ≤ 0, asserted FALSE ⇒ x > 0
        let a1 = solver.new_var(); // x - 1 < 0
        solver.add_clause([Lit::neg(a0)]);
        solver.add_clause([Lit::pos(a1)]);
        let theory = FdPropagator::new(vec![
            (poly(&[(1, &[(0, 1)])]), FdCmp::Le, a0),
            (poly(&[(1, &[(0, 1)]), (-1, &[])]), FdCmp::Lt, a1),
        ]);
        let (result, _theory) = solver.solve_with_hooks(theory);
        assert_eq!(result, SolverResult::Unsat, "¬(x≤0) ∧ x<1 has no integer");
    }

    #[test]
    fn fd_propagates_forced_true_literal() {
        // a0 = (x - 5 ≥ 0)  [x≥5];  a1 = (x - 3 ≥ 0)  [x≥3]. Asserting a0 FORCES a1
        // true ⇒ final_check must Propagate a1=true (sound by the keystone).
        let mut solver = Solver::new();
        let a0 = solver.new_var();
        let a1 = solver.new_var();
        let mut theory = FdPropagator::new(vec![
            (poly(&[(1, &[(0, 1)]), (-5, &[])]), FdCmp::Ge, a0),
            (poly(&[(1, &[(0, 1)]), (-3, &[])]), FdCmp::Ge, a1),
        ]);
        let _ = theory.assign_hook(Lit::pos(a0), 0); // trail asserts x≥5
        match theory.final_check() {
            TheoryStep::Propagate { lit, reason } => {
                assert_eq!(lit, Lit::pos(a1), "x≥5 forces x≥3 true");
                assert_eq!(reason.asserting, lit, "§4.3: reason.asserting == lit");
            }
            TheoryStep::Conflict { .. } => panic!("expected Propagate, got Conflict"),
            TheoryStep::Ok => panic!("expected Propagate of a1, got Ok"),
        }
    }

    #[test]
    fn fd_propagates_forced_false_literal() {
        // a0 = (x ≤ 2) via ¬(x-2 > 0) is awkward; use a0 = (x - 0 ≤ 0) i.e. x ≤ 0
        // asserted true [x≤0]; a1 = (x - 3 ≥ 0) [x≥3]. x≤0 FORCES a1 FALSE ⇒
        // Propagate a1=false.
        let mut solver = Solver::new();
        let a0 = solver.new_var();
        let a1 = solver.new_var();
        let mut theory = FdPropagator::new(vec![
            (poly(&[(1, &[(0, 1)])]), FdCmp::Le, a0), // x ≤ 0
            (poly(&[(1, &[(0, 1)]), (-3, &[])]), FdCmp::Ge, a1), // x ≥ 3
        ]);
        let _ = theory.assign_hook(Lit::pos(a0), 0); // trail asserts x≤0
        match theory.final_check() {
            TheoryStep::Propagate { lit, .. } => {
                assert_eq!(lit, Lit::neg(a1), "x≤0 forces x≥3 false");
            }
            TheoryStep::Conflict { .. } => panic!("expected Propagate, got Conflict"),
            TheoryStep::Ok => panic!("expected Propagate of ¬a1, got Ok"),
        }
    }
}
