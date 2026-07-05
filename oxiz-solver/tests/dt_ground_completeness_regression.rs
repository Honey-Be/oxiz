//! Permanent (z3-cross-checked) regressions for #404 phase 2 — GROUND
//! datatype exhaustiveness completeness (the corpus decreases-check wall).
//!
//! Three independent gaps, each with its own pin below:
//!
//! 1. TESTER-SHAPE diseqs (check_dt): `v ≠ C(sel_{C,0}(v), …)` is exactly
//!    `¬is-C(v)` for ANY arity — rebuilding `v` from its own C-fields equals
//!    `v` iff `v` is C-shaped. #399 collected only negative testers and
//!    negative NULLARY ctor equalities, so excluding all three field-bearing
//!    ctors of an `Expr` datatype read `sat` (z3: unsat). The recognizer must
//!    match selectors POSITIONALLY and accept the parser's `Apply`
//!    representation of a selector application.
//!
//! 2. CONSTRUCTOR-COVER + EXCLUSION at the SAT level (encode): the static
//!    pass reads only top-level And/Or/Not polarity, so a shape diseq under
//!    `=>`/branch structure — the verus decreases-check goal shape — never
//!    reaches it. `add_dt_cover_axioms` encodes, per ground datatype-sorted
//!    subterm `t`, the valid axioms `(or s₁ … sₙ)` (≥1 shape) and pairwise
//!    `¬sᵢ ∨ ¬sⱼ` (≤1 shape) over the shape atoms `sᵢ = (= t (Cᵢ sels(t)))`,
//!    making the exhaustiveness conflict purely propositional. Without the
//!    ≤1 half, a model takes TWO shapes at once, which falsifies every
//!    `¬is-C`-guard in sight and lets guarded axiom instances vanish.
//!
//! 3. EUF congruence over datatype nodes (theory_manager): `DtConstructor` /
//!    `DtSelector` interned as OPAQUE leaves meant `x=y` never derived
//!    `C(sel(x)…) = C(sel(y)…)`, so a shape equality established at one term
//!    never reached the congruent shape atom of an equal term — the
//!    `decrease%init0 ≡ E` bridge the decreases-check goal needs.

use oxiz_solver::Context;

fn verdict(script: &str) -> &'static str {
    let mut ctx = Context::new();
    ctx.set_timeout_ms(5000);
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

const EXPR_DT: &str = "(set-logic ALL)\n\
     (declare-datatypes ((E 0)) (((Lit (Lit!sel0 Int)) (Neg (Neg!sel0 E)) \
     (Add (Add!sel0 E) (Add!sel1 E)))))\n\
     (declare-const x E)\n";

/// Gap 1 pin — all three FIELD-BEARING ctor shapes excluded by tester-shape
/// diseqs: ground conflict (z3: unsat; pre-fix OxiZ: sat).
#[test]
fn tester_shape_all_ctors_excluded_is_unsat() {
    let v = verdict(&format!(
        "{EXPR_DT}\
         (assert (not (= x (Lit (Lit!sel0 x)))))\n\
         (assert (not (= x (Neg (Neg!sel0 x)))))\n\
         (assert (not (= x (Add (Add!sel0 x) (Add!sel1 x)))))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// Sat control — excluding only 2 of 3 shapes leaves the third open.
#[test]
fn tester_shape_partial_exclusion_stays_sat() {
    let v = verdict(&format!(
        "{EXPR_DT}\
         (assert (not (= x (Lit (Lit!sel0 x)))))\n\
         (assert (not (= x (Neg (Neg!sel0 x)))))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// Sat control — SWAPPED selector positions are NOT the tester shape
/// (`Add(Add!sel1 x, Add!sel0 x)` excludes one instance, not the class).
#[test]
fn tester_shape_swapped_selectors_stay_sat() {
    let v = verdict(&format!(
        "{EXPR_DT}\
         (assert (not (= x (Lit (Lit!sel0 x)))))\n\
         (assert (not (= x (Neg (Neg!sel0 x)))))\n\
         (assert (not (= x (Add (Add!sel1 x) (Add!sel0 x)))))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// Sat control — a selector applied to a DIFFERENT variable is not the
/// tester shape either.
#[test]
fn tester_shape_other_var_arg_stays_sat() {
    let v = verdict(&format!(
        "{EXPR_DT}\
         (declare-const y E)\n\
         (assert (not (= x (Lit (Lit!sel0 x)))))\n\
         (assert (not (= x (Neg (Neg!sel0 x)))))\n\
         (assert (not (= x (Add (Add!sel0 y) (Add!sel1 x)))))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// Gap 2 pin — the same exclusions buried under a top-level `=>` (invisible
/// to the static polarity walk; the cover clauses close it at the SAT level).
#[test]
fn exhaustiveness_under_implication_is_unsat() {
    let v = verdict(&format!(
        "{EXPR_DT}\
         (declare-const p Bool)\n\
         (assert p)\n\
         (assert (=> p (and (not (= x (Lit (Lit!sel0 x)))) \
         (not (= x (Neg (Neg!sel0 x)))) \
         (not (= x (Add (Add!sel0 x) (Add!sel1 x)))))))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// Gap 2 pin — exclusions split across SEARCH branches: whichever way `p`
/// goes, all three shapes are excluded (needs per-branch reasoning no static
/// pre-pass can do).
#[test]
fn exhaustiveness_across_branches_is_unsat() {
    let v = verdict(&format!(
        "{EXPR_DT}\
         (declare-const p Bool)\n\
         (assert (=> p (and (not (= x (Lit (Lit!sel0 x)))) \
         (not (= x (Neg (Neg!sel0 x)))))))\n\
         (assert (=> (not p) (and (not (= x (Lit (Lit!sel0 x)))) \
         (not (= x (Neg (Neg!sel0 x)))))))\n\
         (assert (not (= x (Add (Add!sel0 x) (Add!sel1 x)))))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// Gap 3 pin — the congruence bridge: `a = b` must carry a shape equality
/// from `a` to the CONGRUENT shape atom of `b`. Guarded under `p` so the
/// static pass cannot close it — this is the in-search EUF path (pre-fix:
/// `DtConstructor` was an opaque EUF leaf, spurious sat).
#[test]
fn ctor_congruence_bridges_equal_terms() {
    let v = verdict(&format!(
        "{EXPR_DT}\
         (declare-const b E)\n\
         (declare-const p Bool)\n\
         (assert p)\n\
         (assert (=> p (= x b)))\n\
         (assert (=> p (= x (Lit (Lit!sel0 x)))))\n\
         (assert (=> p (not (= b (Lit (Lit!sel0 b))))))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// Cover-axiom soundness control — an unconstrained datatype constant is
/// still satisfiable with the cover + exclusion clauses present.
#[test]
fn unconstrained_dt_var_stays_sat() {
    let v = verdict(&format!("{EXPR_DT}(check-sat)\n"));
    assert_eq!(v, "sat");
}
