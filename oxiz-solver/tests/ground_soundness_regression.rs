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
