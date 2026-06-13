//! Permanent (z3-free) regressions for the two ground-soundness bugs found by
//! the differential fuzzer (`ground_soundness_fuzz.rs`) and the bounded
//! injectivity audit (`injective_min.rs`).  Each case has an obvious
//! ground-truth verdict noted inline, asserted directly so these run in CI
//! without an external oracle.

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

/// GCD-infeasibility reason bug: an infeasible integer equality `2c = 3` inside
/// an OR with a satisfiable disjunct (`10 >= 3`) must NOT make the whole script
/// unsat — the OR is satisfiable via the other disjunct.  The arith solver's
/// GCD-infeasibility branch used to tag the contradictory simplex bounds with a
/// hardcoded reason `0`, so the learned conflict clause was built over an
/// unrelated term and OMITTED the disjunct literal → the SAT solver could not
/// flip the OR → spurious UNSAT.  The second assertion is only a catalyst that
/// perturbs decision order to expose the latent reason loss.
#[test]
fn gcd_infeasible_disjunct_is_sat() {
    let script = "\
(set-logic QF_LIA)
(declare-const c Int)
(declare-const x Int)
(declare-const y Int)
(declare-const p Bool)
(assert (or (= c (- 3 c)) (>= 10 3)))
(assert (=> p (= x y)))
(check-sat)
";
    assert_eq!(verdict(script), "sat", "GCD-infeasible OR disjunct must not force unsat");
}

/// The companion genuine-UNSAT cases the GCD reason fix must preserve: an
/// unconditionally-asserted infeasible integer equality is still unsat.
#[test]
fn gcd_infeasible_equality_is_unsat() {
    // 2c = 3 has no integer solution.
    assert_eq!(
        verdict("(set-logic QF_LIA)\n(declare-const c Int)\n(assert (= c (- 3 c)))\n(check-sat)\n"),
        "unsat",
        "2c=3 is genuinely unsat",
    );
    // 2x + 2y = 7: gcd(2,2)=2 does not divide 7.
    assert_eq!(
        verdict("(set-logic QF_LIA)\n(declare-const x Int)\n(declare-const y Int)\n(assert (= (+ (* 2 x) (* 2 y)) 7))\n(check-sat)\n"),
        "unsat",
        "2x+2y=7 is genuinely unsat (GCD)",
    );
}

/// Stale-bound pseudo-conflict: a SAT backtrack + re-decision left the atom
/// `(>= (f 2) 5)` asserted into the simplex under BOTH polarities (`f(2)<=4` AND
/// `f(2)>=5`), so arith reported a vacuous self-conflict over a single atom →
/// the SAT layer learned a malformed `[¬v, ¬v]` unit and concluded a spurious
/// UNSAT.  The whole script is satisfiable.  Detected by
/// `ArithSolver::last_conflict_is_stale_bound` (>=2 distinct reason-ids
/// collapsing onto <2 distinct atom terms) and suppressed at the theory-manager
/// conflict sites.  NOTE: this is a surgical guard against the dangerous
/// (accepts-invalid) direction; the underlying theory-frame/SAT-trail desync is
/// documented as a known root-cause for a later resync fix.
#[test]
fn stale_bound_pseudo_conflict_is_sat() {
    let script = "\
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun d () Int)
(assert (or (>= (+ a 5) 3) (> a 0)))
(assert (=> (>= (- c a) 5) (>= (f 2) 5)))
(assert (or (< d (- c a)) (< 10 (f 2))))
(assert (not (< c 10)))
(assert (not (<= c 5)))
(assert (=> (> (- c a) c) (>= d 3)))
(assert (and (= c d) (<= 5 5)))
(assert (or (>= (g 5) 5) (> (f 2) (- c a))))
(assert (=> (> 5 1) (< (f 2) b)))
(check-sat)
";
    assert_eq!(verdict(script), "sat", "stale-bound pseudo-conflict must not force unsat");
}

/// Bug (a): a nested application carrying a DIRECT numeric constraint must reach
/// the arithmetic solver.  `f(g(10)) = 20` together with `f(g(10)) <= 10` is a
/// contradiction (20 <= 10 is false), so the script is UNSAT.  Dropping the
/// nested app from arith previously lost the bound and returned a spurious SAT.
#[test]
fn nested_app_direct_bound_is_unsat() {
    let script = "\
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert (= (g 10) 5))
(assert (= (f (g 10)) 20))
(assert (<= (f (g 10)) 10))
(check-sat)
";
    assert_eq!(verdict(script), "unsat", "nested-app direct bound contradiction");
}

/// Bug (a), congruence variant: when `g(10) = 5`, congruence gives
/// `f(g(10)) = f(5)`.  With `f(5) = 7` and `f(g(10)) = 20` that forces `7 = 20`,
/// UNSAT.  Exercises EUF→arith equality propagation on a kept nested app.
#[test]
fn nested_app_congruence_is_unsat() {
    let script = "\
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert (= (g 10) 5))
(assert (= (f 5) 7))
(assert (= (f (g 10)) 20))
(check-sat)
";
    assert_eq!(verdict(script), "unsat", "f(g(10))=f(5) congruence contradiction");
}

/// A satisfiable companion to guard against the OPPOSITE regression (a spurious
/// UNSAT from keeping nested apps in arith): here the two congruent values agree
/// (`f(g(10)) = f(5) = 7`) and the bound is consistent, so the script is SAT.
#[test]
fn nested_app_consistent_is_sat() {
    let script = "\
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert (= (g 10) 5))
(assert (= (f 5) 7))
(assert (= (f (g 10)) 7))
(assert (<= (f (g 10)) 10))
(check-sat)
";
    assert_eq!(verdict(script), "sat", "consistent nested-app model exists");
}

/// Bug (b): the bounded-injectivity corpus that drove OxiZ into a spurious
/// `unsat` (root cause: the EUF proof forest was not backtracked with the union
/// trail, so `explain_equality` cited retracted merges → invalid learned
/// clauses).  The whole corpus is satisfiable, so OxiZ must NOT report unsat.
#[test]
fn bounded_injectivity_nested_is_sat() {
    let pool = [
        "1", "2", "3", "10", "20", "30", "(f 1)", "(f 2)", "(f 3)", "(f 10)", "(f 20)", "(f 30)",
    ];
    let mut s = String::from("(set-logic QF_UFLIA)\n(declare-fun f (Int) Int)\n");
    for fact in ["(= (f 1) 10)", "(= (f 2) 20)", "(= (f 3) 30)"] {
        s.push_str(&format!("(assert {fact})\n"));
    }
    for &x in &pool {
        for &y in &pool {
            if x == y {
                continue;
            }
            s.push_str(&format!(
                "(assert (=> (and (>= {x} 0) (<= {x} 10) (>= {y} 0) (<= {y} 10) (= (f {x}) (f {y}))) (= {x} {y})))\n"
            ));
        }
    }
    s.push_str("(check-sat)\n");
    assert_eq!(verdict(&s), "sat", "bounded-injectivity corpus is satisfiable");
}

/// §4 Phase-2 completeness fix: arith→EUF entailed-equality propagation.
///
/// `f(1)` is pinned to 5 by its two bounds; that ENTAILED equality must be
/// propagated into EUF so congruence derives `f(f(1)) = f(5)`, closing the
/// contradiction `f(5) >= 10` (via `f(f(1))`) vs `f(5) <= 1`.  Before the fix
/// `model_based_combination` only DETECTED disagreements and never propagated an
/// arith-fixed term into EUF, so this was a spurious SAT (oxiz=sat, z3=unsat).
#[test]
fn arith_fixed_value_drives_congruence_is_unsat() {
    let script = "\
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(assert (>= (f 1) 5))
(assert (>= (f (f 1)) 10))
(assert (<= (f 1) 5))
(assert (<= (f 5) 1))
(check-sat)
";
    assert_eq!(
        verdict(script),
        "unsat",
        "f(1)=5 ⊢ f(f(1))=f(5); f(5)>=10 vs f(5)<=1 is unsat",
    );
}

/// Companion that the fix must NOT over-strengthen into a spurious UNSAT:
/// identical shape but the second-level bound is satisfiable (`f(5) >= 1`
/// instead of `<= 1`), so the whole thing is SAT.  A too-eager conflict clause
/// (omitting a pinning bound) would wrongly report unsat here.
#[test]
fn arith_fixed_value_congruence_consistent_is_sat() {
    let script = "\
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(assert (>= (f 1) 5))
(assert (>= (f (f 1)) 10))
(assert (<= (f 1) 5))
(assert (>= (f 5) 1))
(check-sat)
";
    assert_eq!(
        verdict(script),
        "sat",
        "f(f(1))=f(5)>=10 is consistent with f(5)>=1 — must stay sat",
    );
}

/// Deeper arith→EUF congruence chains the fixed-value propagation must close
/// (one merge fixes a deeper term — the bounded fixpoint loop in
/// `model_based_combination`). All z3-confirmed `unsat`.
#[test]
fn arith_fixed_value_congruence_deep_and_negative_are_unsat() {
    // 3-level nesting: f(1)=5 ⊢ f(f(1))=f(5)=7 ⊢ f(f(f(1)))=f(7); f(f(f(1)))>=100 vs f(7)<=1.
    let deep = "\
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(assert (>= (f 1) 5))(assert (<= (f 1) 5))
(assert (>= (f 5) 7))(assert (<= (f 5) 7))
(assert (>= (f (f (f 1))) 100))(assert (<= (f 7) 1))
(check-sat)
";
    assert_eq!(verdict(deep), "unsat", "3-level fixed-value congruence chain");

    // Negative constant: the `mk_neg` sanitizer makes `(- 3)` an IntConst(-3) so it
    // has a canonical EUF node. f(1)=-3 ⊢ f(f(1))=f(-3); f(f(1))>=9 vs f(-3)<=2.
    let neg = "\
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(assert (>= (f 1) (- 3)))(assert (<= (f 1) (- 3)))
(assert (>= (f (f 1)) 9))(assert (<= (f (- 3)) 2))
(check-sat)
";
    assert_eq!(verdict(neg), "unsat", "negative fixed value drives congruence");

    // Two functions, both nested-fixed, sharing a value: f(f(1))=g(g(1)) but f(2)!=g(3).
    let twofun = "\
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert (>= (f 1) 2))(assert (<= (f 1) 2))
(assert (>= (g 1) 3))(assert (<= (g 1) 3))
(assert (= (f (f 1)) (g (g 1))))
(assert (not (= (f 2) (g 3))))
(check-sat)
";
    assert_eq!(verdict(twofun), "unsat", "two-function fixed-value congruence");
}
