//! Regression (#427): integrality must follow the TERM'S SORT, never the
//! `(set-logic …)` NAME.
//!
//! `Solver::set_logic` (`oxiz-solver/src/solver/config.rs`) picks the
//! arithmetic solver by substring-matching the logic string —
//! `NIA`/`NRA`/`LIA`/`IDL`/`LRA`/`RDL`/`BV` — and falls through to the DEFAULT
//! `ArithSolver::lra()` for everything else. `ALL` matches none of them. So do
//! a missing `(set-logic)` and the mixed names `AUFLIRA` / `QF_LIRA`. Every
//! Int-sorted constraint submitted that way was therefore solved over the
//! RATIONALS:
//!
//!   - `ArithSolver::check` only ran the #289 integer branch-and-bound under
//!     the global `is_integer` flag, so an LP-feasible-but-integer-infeasible
//!     assignment was certified `Sat` outright;
//!   - `assert_lt`/`assert_gt` only applied the `x < k ⇒ x ≤ k−1` strengthening
//!     under that same flag, so `0 < x < 1` stayed the δ-rational relaxation
//!     `x ≥ 0+δ ∧ x ≤ 1−δ`, which is feasible.
//!
//! The originally-reported shape was a bounded pigeonhole (three `hole i` in
//! `{1,2}`, pairwise distinct by a quantified injectivity axiom) — rationally
//! feasible at `1, 3/2, 2`, hence a false `sat`. It needs neither quantifiers
//! nor a counting argument: `(declare-const x Int)` with `0 < x < 1` reproduces
//! it under `ALL` while the SAME script under `UFLIA`/`QF_LIA` was already
//! `unsat`.
//!
//! The fix makes integrality per-TERM (`ArithSolver::declare_sort` /
//! `term_is_integer`, fed from the sort by `Solver::track_theory_vars`,
//! `Solver::encode` and `TheoryManager::declare_arith_sorts`), with the old
//! logic-derived flag kept only as the fallback for an undeclared term.
//!
//! The `stays_sat` cases are the other-direction controls, and they are not
//! hypothetical: the naive fix — mapping `ALL` to `ArithSolver::lia()` — makes
//! every one of them report a false `unsat`, because a global integer mode
//! forces Real-sorted variables to integer values too. That failure mode was
//! reproduced on this tree before the per-term fix was written.
//!
//! z3 independently agrees with every verdict pinned below.

use oxiz_solver::Context;

fn verdict(script: &str) -> &'static str {
    let mut ctx = Context::new();
    ctx.set_timeout_ms(20_000);
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

/// The reported #427 repro: bounded pigeonhole under `(set-logic ALL)`.
/// Three holes forced into `{1,2}` plus a quantified injectivity axiom over the
/// index range `[0,2]`. Reported `sat` (the rational witness `1, 3/2, 2`).
#[test]
fn all_logic_bounded_pigeonhole_is_unsat() {
    let script = "\
(set-logic ALL)
(declare-fun hole (Int) Int)
(assert (and (>= (hole 0) 1) (<= (hole 0) 2)))
(assert (and (>= (hole 1) 1) (<= (hole 1) 2)))
(assert (and (>= (hole 2) 1) (<= (hole 2) 2)))
(assert (forall ((i Int) (j Int)) (=> (and (>= i 0) (<= i 2) (>= j 0) (<= j 2) (not (= i j))) (not (= (hole i) (hole j))))))
(check-sat)
";
    assert_eq!(
        verdict(script),
        "unsat",
        "three Int-sorted holes cannot be pairwise distinct inside the \
         two-element range {{1,2}}; `sat` means the integrality of `hole i` \
         was dropped and the LP relaxation certified instead"
    );
}

/// The same formula with the quantifier eliminated by hand — the bug is in the
/// arithmetic layer, not in MBQI/CDQI instantiation.
#[test]
fn all_logic_ground_pigeonhole_is_unsat() {
    let script = "\
(set-logic ALL)
(declare-fun hole (Int) Int)
(assert (and (>= (hole 0) 1) (<= (hole 0) 2)))
(assert (and (>= (hole 1) 1) (<= (hole 1) 2)))
(assert (and (>= (hole 2) 1) (<= (hole 2) 2)))
(assert (not (= (hole 0) (hole 1))))
(assert (not (= (hole 0) (hole 2))))
(assert (not (= (hole 1) (hole 2))))
(check-sat)
";
    assert_eq!(verdict(script), "unsat");
}

/// Fully minimized: one Int constant, two strict bounds, no UF, no quantifier,
/// no counting. This is the smallest witness of #427.
#[test]
fn all_logic_empty_int_interval_is_unsat() {
    let script = "\
(set-logic ALL)
(declare-const x Int)
(assert (> x 0))
(assert (< x 1))
(check-sat)
";
    assert_eq!(
        verdict(script),
        "unsat",
        "no integer lies strictly between 0 and 1; `sat` means `x` was solved \
         over the rationals because `ALL` matched no logic-name substring"
    );
}

/// The identical constraint under a logic name that DOES contain `LIA` was
/// always `unsat` — pinning the pair keeps the two paths from drifting apart
/// again.
#[test]
fn uflia_empty_int_interval_is_unsat() {
    let script = "\
(set-logic UFLIA)
(declare-const x Int)
(assert (> x 0))
(assert (< x 1))
(check-sat)
";
    assert_eq!(verdict(script), "unsat");
}

/// No `(set-logic)` at all: `Solver::logic` stays `None` and the arithmetic
/// solver keeps its `lra()` default, so this had the same false `sat`.
#[test]
fn no_set_logic_empty_int_interval_is_unsat() {
    let script = "\
(declare-const x Int)
(assert (> x 0))
(assert (< x 1))
(check-sat)
";
    assert_eq!(verdict(script), "unsat");
}

/// A named-but-unmatched logic: `AUFLIRA` contains neither `LIA` nor `LRA` as a
/// substring, so it fell through to the LRA default exactly like `ALL`.
#[test]
fn auflira_empty_int_interval_is_unsat() {
    let script = "\
(set-logic AUFLIRA)
(declare-const x Int)
(assert (> x 0))
(assert (< x 1))
(check-sat)
";
    assert_eq!(verdict(script), "unsat");
}

/// An Int-sorted UF APPLICATION (not a plain constant) — the `hole i` shape,
/// registered through the `TermKind::Apply` arm of `track_theory_vars`.
#[test]
fn all_logic_empty_int_interval_on_uf_application_is_unsat() {
    let script = "\
(set-logic ALL)
(declare-fun h (Int) Int)
(assert (> (h 0) 0))
(assert (< (h 0) 1))
(check-sat)
";
    assert_eq!(verdict(script), "unsat");
}

/// Integer infeasibility with only NON-STRICT bounds, so the fix's
/// `assert_lt`/`assert_gt` strengthening cannot be what closes it — this one
/// exercises the branch-and-bound integrality gate in `ArithSolver::check`.
/// A sound engine may answer `unknown` here (B&B reports infeasibility as
/// `Unknown`, never as a theory conflict); what it must NOT answer is `sat`.
#[test]
fn all_logic_gcd_infeasible_equality_is_not_sat() {
    let script = "\
(set-logic ALL)
(declare-const x Int)
(assert (= (+ x x) 3))
(check-sat)
";
    assert_ne!(
        verdict(script),
        "sat",
        "`2x = 3` has no integer solution; `sat` means the rational witness \
         `x = 3/2` was accepted for an Int-sorted variable"
    );
}

/// Other-direction control: a Real-sorted variable in the SAME empty-integer
/// interval is genuinely satisfiable (`x = 1/2`). The naive `ALL ⇒ lia()` fix
/// reports `unsat` here.
#[test]
fn all_logic_real_in_unit_interval_stays_sat() {
    let script = "\
(set-logic ALL)
(declare-const r Real)
(assert (> r 0.0))
(assert (< r 1.0))
(check-sat)
";
    assert_eq!(
        verdict(script),
        "sat",
        "`r` is Real-sorted, so `0 < r < 1` is satisfiable; `unsat` means \
         integrality was applied to a variable that has none"
    );
}

/// Other-direction control, MIXED sorts in one problem: the Int variable is
/// integrality-constrained while the Real one must not be. Neither a global
/// LRA mode (false `sat` on the Int half) nor a global LIA mode (false `unsat`
/// on the Real half) gets this right — only per-term integrality does.
#[test]
fn all_logic_mixed_int_real_stays_sat() {
    let script = "\
(set-logic ALL)
(declare-const x Int)
(declare-const r Real)
(assert (> x 0))
(assert (< x 2))
(assert (> r 0.0))
(assert (< r 1.0))
(check-sat)
";
    assert_eq!(verdict(script), "sat");
}

/// Other-direction control, mixed sorts where the INT half is infeasible and
/// the Real half is not: the verdict must be driven by the Int half.
#[test]
fn all_logic_mixed_int_infeasible_real_feasible_is_unsat() {
    let script = "\
(set-logic ALL)
(declare-const x Int)
(declare-const r Real)
(assert (> x 0))
(assert (< x 1))
(assert (> r 0.0))
(assert (< r 1.0))
(check-sat)
";
    assert_eq!(verdict(script), "unsat");
}

/// Other-direction control: a Real-sorted variable declared under a logic name
/// that DOES match `LIA`. This was a pre-existing latent false `unsat` of the
/// same root cause read the other way — the global integer mode forced `r` to
/// an integer value — and per-term integrality closes it too.
#[test]
fn lia_named_logic_real_in_unit_interval_stays_sat() {
    let script = "\
(set-logic QF_UFLIA)
(declare-const r Real)
(assert (> r 0.0))
(assert (< r 1.0))
(check-sat)
";
    assert_eq!(
        verdict(script),
        "sat",
        "the logic NAME says LIA but `r`'s SORT says Real; the sort wins"
    );
}

/// Other-direction control: the pigeonhole becomes satisfiable as soon as the
/// range has room for all three holes, so the fix must not blanket-refute the
/// shape.
#[test]
fn all_logic_pigeonhole_with_enough_holes_stays_sat() {
    let script = "\
(set-logic ALL)
(declare-fun hole (Int) Int)
(assert (and (>= (hole 0) 1) (<= (hole 0) 3)))
(assert (and (>= (hole 1) 1) (<= (hole 1) 3)))
(assert (and (>= (hole 2) 1) (<= (hole 2) 3)))
(assert (not (= (hole 0) (hole 1))))
(assert (not (= (hole 0) (hole 2))))
(assert (not (= (hole 1) (hole 2))))
(check-sat)
";
    assert_eq!(verdict(script), "sat");
}

/// Other-direction control: `distinct` over more Int-sorted terms than the
/// bounded range can hold, without any UF — the same counting argument reached
/// through a different front-end path.
#[test]
fn all_logic_distinct_over_narrow_int_range_is_unsat() {
    let script = "\
(set-logic ALL)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(assert (and (>= a 1) (<= a 2)))
(assert (and (>= b 1) (<= b 2)))
(assert (and (>= c 1) (<= c 2)))
(assert (distinct a b c))
(check-sat)
";
    assert_eq!(verdict(script), "unsat");
}
