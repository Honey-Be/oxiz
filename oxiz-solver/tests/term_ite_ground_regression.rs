//! Permanent (z3+cvc5-cross-checked) regressions for the ground term-ite
//! opacity found while localizing adsmt #397 (the verus AIR-path 1v/2e,
//! 2026-07-04).
//!
//! Only the BOOL-sorted `ite` had a Tseitin arm in `encode`, and only the BV
//! bit-blaster interpreted `TermKind::Ite` on the theory side — an Int-sorted
//! `ite` reaching a theory atom made the whole atom opaque, so even
//! `(= a (ite p 1 2)) ∧ a≠1 ∧ a≠2` read a confident spurious `sat`. The verus
//! fuel-unfolding definition axioms instantiate to exactly this shape
//! (`abs(x) = ite(x≥0, x, Sub(0,x))`), which is why the whole AIR fixture
//! family failed; the `div`-presence Sat→Unknown downgrade had been masking
//! the wrong `sat` as an honest-looking `unknown`.
//!
//! Fixed by `Solver::eliminate_term_ites` (fresh constant + Bool-ite
//! definition, applied at `assert`/`assert_named`/the instance-lemma sites).

use oxiz_solver::Context;

fn verdict(script: &str) -> &'static str {
    let mut ctx = Context::new();
    ctx.set_timeout_ms(10_000);
    match ctx.execute_script(script) {
        Ok(out) => out
            .iter()
            .rev()
            .find_map(|l| match l.trim() {
                "sat" => Some("sat"),
                "unsat" => Some("unsat"),
                "unknown" => Some("unknown"),
                _ => None,
            })
            .unwrap_or("unknown"),
        Err(_) => "unknown",
    }
}

/// The maximally minimal shape: an ite pinned between two excluded branches.
#[test]
fn ground_ite_branch_exclusion_is_unsat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-const p Bool)\n(declare-const a Int)\n\
         (assert (= a (ite p 1 2)))\n\
         (assert (not (= a 1)))\n(assert (not (= a 2)))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "unsat", "a must be one of the two branches");
}

/// Positive control: choosing a branch stays satisfiable.
#[test]
fn ground_ite_chosen_branch_is_sat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-const p Bool)\n(declare-const a Int)\n\
         (assert (= a (ite p 1 2)))\n(assert (= a 2))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "sat");
}

/// The abs shape, ground: both branches are ≥ 0.
#[test]
fn ground_abs_ite_is_nonnegative() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-const y Int)\n(declare-const a Int)\n\
         (assert (= a (ite (>= y 0) y (- 0 y))))\n\
         (assert (not (>= a 0)))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "unsat");
}

/// An ite directly under the asserted atom (no intermediary constant).
#[test]
fn ground_abs_ite_atom_is_unsat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-const y Int)\n\
         (assert (not (>= (ite (>= y 0) y (- 0 y)) 0)))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "unsat");
}

/// Sat control for the atom form.
#[test]
fn ground_abs_ite_atom_positive_is_sat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-const y Int)\n\
         (assert (>= (ite (>= y 0) y (- 0 y)) 0))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "sat");
}

/// The QUANTIFIED verus definitional-axiom shape: the instance lemma carries
/// the ground ite, so the elimination must also fire on the lemma path.
#[test]
fn quantified_abs_definition_instance_is_unsat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-fun absI (Int) Int)\n\
         (assert (forall ((x Int)) (! (= (absI x) (ite (>= x 0) x (- 0 x))) :pattern ((absI x)))))\n\
         (declare-const y Int)\n\
         (assert (not (>= (absI y) 0)))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "unsat");
}

/// The fuel-gated chain over an uninterpreted Poly sort — the exact 6-assert
/// AIR core (minus the inert EucDiv axiom) the #397 ddmin isolated, with the
/// guard chain `fuel_defaults ⇒ fuel_bool = fuel_bool_default ⇒ definition`.
#[test]
fn fuel_gated_abs_chain_is_unsat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-sort FuelId 0)\n(declare-sort Poly 0)\n\
         (declare-fun fuel_bool (FuelId) Bool)\n\
         (declare-fun fuel_bool_default (FuelId) Bool)\n\
         (declare-const fuel_defaults Bool)\n\
         (declare-const f FuelId)\n\
         (declare-fun abs? (Poly) Int)\n\
         (declare-fun I (Int) Poly)\n(declare-fun %I (Poly) Int)\n\
         (assert (=> fuel_defaults (forall ((id FuelId)) (! (= (fuel_bool id) (fuel_bool_default id)) :pattern ((fuel_bool id))))))\n\
         (assert (fuel_bool_default f))\n\
         (assert (=> (fuel_bool f) (forall ((x Poly)) (! (= (abs? x) (ite (>= (%I x) 0) (%I x) (- 0 (%I x)))) :pattern ((abs? x))))))\n\
         (assert fuel_defaults)\n\
         (declare-const y Int)\n\
         (assert (not (>= (abs? (I y)) 0)))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "unsat");
}
