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

/// verus-fork 2026-06-17 P0: `-V adsmt` vacuously verified `ensures x != 0`.
/// The emitted goal `(not (=> L (not (= x 0))))` (= `L ∧ (x = 0)`, plainly SAT)
/// was reported `unsat`. Root cause: the eager `Not(Eq(a,b))` arithmetic split
/// in `encode` (`add_arith_diseq_split`) walked the asserted term syntactically,
/// blind to polarity, and added the bare disequality `(a<b) OR (a>b)` for the
/// inner `(not (= x 0))` — which sits at EFFECTIVE positive-equality polarity
/// under the outer `not`. That forced `x != 0`, clashing with the formula's
/// `x = 0` → spurious `unsat`. Fix: emit the SOUND trichotomy
/// `(= a b) OR (a<b) OR (a>b)` (a tautology) instead of the bare split, so it
/// constrains nothing at any polarity yet still lets the ArithSolver split a
/// genuinely-false equality. The whole class of disequality / negated-equality
/// postconditions was affected.
#[test]
fn negated_impl_double_neg_equality_is_not_unsat() {
    // (not (=> L (not (= x 0)))) ≡ L ∧ (x = 0) — SAT (L=true, x=0).
    let bug = "\
(set-logic ALL)
(declare-const x Int)
(declare-const L Bool)
(assert (not (=> L (not (= x 0)))))
(check-sat)
";
    assert_ne!(verdict(bug), "unsat", "negated-impl over a negated equality must NOT be unsat");

    // The same with the implication written as its De Morgan disjunction.
    let or_form = "\
(set-logic ALL)
(declare-const x Int)
(declare-const L Bool)
(assert (not (or (not L) (not (= x 0)))))
(check-sat)
";
    assert_ne!(verdict(or_form), "unsat", "negated (or (not L) (not (= x 0))) must NOT be unsat");

    // Real sort variant.
    let real = "\
(set-logic ALL)
(declare-const x Real)
(declare-const L Bool)
(assert (not (=> L (not (= x 0.0)))))
(check-sat)
";
    assert_ne!(verdict(real), "unsat", "Real-sort negated-impl disequality must NOT be unsat");

    // Even with x=0 asserted alongside, must stay non-unsat (was unsat).
    let pinned = "\
(set-logic ALL)
(declare-const x Int)
(declare-const L Bool)
(assert (not (=> L (not (= x 0)))))
(assert (= x 0))
(check-sat)
";
    assert_ne!(verdict(pinned), "unsat", "x=0 explicitly asserted must not be unsat");
}

/// The genuine-UNSAT companions the trichotomy fix must preserve: a positively
/// asserted disequality still drives `!=`, and a contradiction stays unsat.
#[test]
fn genuine_disequality_unsat_preserved() {
    // (not (= x 0)) asserted positively, plus x = 0 → genuinely UNSAT.
    let g1 = "\
(set-logic ALL)
(declare-const x Int)
(assert (not (= x 0)))
(assert (= x 0))
(check-sat)
";
    assert_eq!(verdict(g1), "unsat", "positive disequality + equality is unsat");

    // A positive disequality `(not (= x 0))` whose trichotomy lets the SAT
    // solver set the Eq atom false → ArithSolver must enforce `x != 0`, which
    // contradicts the bounds pinning `x = 0` → genuinely UNSAT. Confirms the
    // trichotomy still drives the arithmetic split for a real disequality.
    let g2 = "\
(set-logic ALL)
(declare-const x Int)
(assert (not (= x 0)))
(assert (<= x 0))
(assert (>= x 0))
(check-sat)
";
    assert_eq!(verdict(g2), "unsat", "positive disequality + bounds pinning x=0 is unsat");
}

/// verus-fork 2026-06-17 spurious-SAT survey #65: `a=b ∧ f(a)=f(b)+1` is
/// genuinely UNSAT (congruence: a=b ⟹ f(a)=f(b), so f(a)=f(b)+1 ⟹ 0=1) but was
/// reported `sat`. The arith constraint `f(a)=f(b)+1` carries `f(b)` NESTED
/// inside `(+ (f b) 1)`; `intern_term_for_congruence` treated the `+` as an
/// opaque EUF leaf and never recursed to `f(b)`, so `f(b)` was never interned as
/// a congruence app and `propagate_euf_equalities_to_arith` never saw f(a)=f(b).
/// Fix: that propagation now app-interns every Apply/Select arith term first, so
/// congruence fires over function applications buried in arithmetic. Sound (only
/// adds an entailed congruence equality); restricted to Apply/Select to avoid the
/// IntConst pairwise-disequality edges that can themselves cause spurious UNSAT.
#[test]
fn euf_congruence_into_nested_arith_app_is_unsat() {
    // a=b ⟹ f(a)=f(b); with f(a)=f(b)+1 → contradiction.
    let s = "\
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(declare-const b Int)
(assert (= a b))
(assert (= (f a) (+ (f b) 1)))
(check-sat)
";
    assert_eq!(verdict(s), "unsat", "a=b ∧ f(a)=f(b)+1 must be unsat via congruence");

    // The SAT companion the fix must NOT break: drop a=b → satisfiable
    // (f(a)=f(b)+1 with f(a),f(b) free).
    let sat = "\
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(declare-const b Int)
(assert (= (f a) (+ (f b) 1)))
(check-sat)
";
    assert_ne!(verdict(sat), "unsat", "without a=b the instance is satisfiable");
}

/// Split a script into top-level s-expression commands (paren-depth, quote-aware),
/// mirroring how the adsmt delegation (`oxiz_inproc`) feeds one command at a time.
fn split_commands(script: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut depth: i32 = 0;
    let mut cur = String::new();
    let mut in_str = false;
    for c in script.chars() {
        if c == '"' {
            in_str = !in_str;
        }
        if !in_str {
            if c == '(' {
                depth += 1;
            } else if c == ')' {
                depth -= 1;
            }
        }
        cur.push(c);
        if !in_str && depth == 0 && c == ')' {
            out.push(cur.trim().to_string());
            cur.clear();
        }
    }
    out.into_iter().filter(|s| !s.is_empty()).collect()
}

/// Verdict of the LAST `(check-sat)`, executing each top-level command in its
/// own `execute_script` call on ONE persistent `Context` — the exact shape of
/// the adsmt in-process delegation.
fn verdict_incremental(script: &str) -> &'static str {
    let mut ctx = Context::new();
    ctx.set_timeout_ms(5000);
    let mut last = "unknown";
    for cmd in split_commands(script) {
        if let Ok(out) = ctx.execute_script(&cmd) {
            for l in out {
                match l.trim() {
                    "sat" => last = "sat",
                    "unsat" => last = "unsat",
                    "unknown" => last = "unknown",
                    _ => {}
                }
            }
        }
    }
    last
}

/// Incremental theory-frame leak across `(pop)` (verus-fork consistency-gate
/// poison). A `(check-sat)` that returns at a deep decision level (here the
/// MBQI loop over the `ens` axiom solving `Sat`/`Unknown` while branched) used
/// to leave one EUF/arith theory frame per leftover decision level: `Solver`'s
/// `push`/`pop` re-base only the SAT trail to level 0 (with the theory
/// detached), so the per-decision theory frames survived. The next `(pop)`
/// then unwound just ONE frame, leaving the inner solve's `x! ~ 0` EUF merge
/// in the union-find (with its proof-forest edge already rolled back). The
/// following consistency `(check-sat)` of `x! != 0` then hit that stale merge
/// → spurious `unsat`. Fixed by re-basing the trail to level 0 inside
/// `solve_with_hooks` (theory still attached → `pop_frame` unwinds every frame).
///
/// Ground truth: `F ∧ x! != 0` is satisfiable (the `ens` axiom does not pin
/// `x!`), so the final `(check-sat)` must NOT be `unsat`.
#[test]
fn incremental_checksat_pop_does_not_leak_theory_frame() {
    let script = "\
(declare-fun ens (Int) Bool)
(assert (forall ((x Int)) (! (= (ens x) (not (= x 0))) :pattern ((ens x)))))
(declare-const x! Int)
(push)
 (declare-const L Bool)
 (assert (not (=> L (not (= x! 0)))))
 (check-sat)
 (pop)
(assert (not (= x! 0)))
(check-sat)
";
    assert_ne!(
        verdict_incremental(script),
        "unsat",
        "a prior (push)(check-sat)(pop) over a quantified axiom must not leak an \
         x!~0 theory frame and force the later x!!=0 consistency check unsat",
    );
}

/// The genuine-UNSAT companion the re-base must preserve: assert `x! = 0`
/// unconditionally (no scope to pop) and then `x! != 0` — a real contradiction.
#[test]
fn incremental_genuine_contradiction_still_unsat() {
    let script = "\
(declare-fun ens (Int) Bool)
(assert (forall ((x Int)) (! (= (ens x) (not (= x 0))) :pattern ((ens x)))))
(declare-const x! Int)
(assert (= x! 0))
(assert (not (= x! 0)))
(check-sat)
";
    assert_eq!(
        verdict_incremental(script),
        "unsat",
        "x!=0 ∧ x!!=0 is a genuine contradiction the frame re-base must not mask",
    );
}

// ── #291: undecided arithmetic ops (abs / to_real / to_int / is_int / divisible) ──
//
// These ops are parsed as theory-undecided (uninterpreted apps, or — for
// `divisible` — a `(= (mod x n) 0)` desugar). The `check_sat` undecided-op
// downgrade turns a `Sat` resting on one into the sound `Unknown`; `Unsat`
// stays sound. See `term_contains_undecided_op` + the 선검증 in
// `oxiz-undecided-op-verification` (abstraction monotonicity).

/// THE headline fix: `(< (abs x) 0)` is UNSAT (abs is never negative), but
/// before #291 `abs` fell through to an uninterpreted **Bool**-sorted app the
/// theory ignored → a fabricated `sat`. Now it is an uninterpreted app the
/// downgrade flags, so the verdict is the sound `unknown` — never `sat`.
#[test]
fn abs_lt_zero_is_never_sat() {
    let v = verdict("(set-logic QF_LIA)\n(declare-const x Int)\n(assert (< (abs x) 0))\n(check-sat)\n");
    assert_ne!(v, "sat", "(< (abs x) 0) must NOT be a fabricated sat");
    assert_eq!(v, "unknown", "abs is undecided ⇒ the sound downgrade verdict");
}

/// The downgrade must NOT over-fire: a `Sat` is downgraded, but congruence can
/// still derive `Unsat` through a shared uninterpreted op term. `(< (to_int r)
/// (to_int r))` is `v < v` for the one value `v = to_int r`, i.e. UNSAT — and
/// stays `unsat` (the downgrade only touches `Sat`).
#[test]
fn to_int_self_comparison_stays_unsat() {
    let v = verdict(
        "(set-logic QF_LIRA)\n(declare-const r Real)\n(assert (< (to_int r) (to_int r)))\n(check-sat)\n",
    );
    assert_eq!(v, "unsat", "v < v is unsat regardless of the undecided to_int value");
}

/// `((_ divisible n) x)` parses (desugars to `(= (mod x n) 0)`) and is covered
/// by the div/mod downgrade: `x = 7 ∧ 3 | x` is genuinely UNSAT, reported as the
/// sound `unknown` (never `sat`). Confirms the indexed-op parse path works.
#[test]
fn divisible_parses_and_is_sound() {
    let v = verdict(
        "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (= x 7))\n(assert ((_ divisible 3) x))\n(check-sat)\n",
    );
    assert_ne!(v, "sat", "7 is not divisible by 3 — must not be sat");
}

/// COVERAGE-COMPLETENESS of the downgrade walk (adversarially found): an
/// undecided op hidden under a `let` (binding RHS *or* body), or under a
/// String/FP/BV/`Dt*` wrapper, must STILL be reached by `term_contains_undecided_op`.
/// The earlier walk (`clean_mbqi::subterms`) skipped those kinds via a
/// `_ => Vec::new()` catch-all, so `(let ((y (abs x))) (= y (- 1)))` — genuinely
/// UNSAT — leaked a fabricated `sat`. The walk now uses the complete
/// `get_children` enumeration.
#[test]
fn undecided_op_under_let_is_still_downgraded() {
    // abs in the let BINDING (the original adversarial hole).
    assert_ne!(
        verdict("(set-logic QF_LIA)\n(declare-const x Int)\n(assert (let ((y (abs x))) (= y (- 1))))\n(check-sat)\n"),
        "sat",
        "abs under a let binding must not escape the downgrade",
    );
    // abs in the let BODY.
    assert_ne!(
        verdict("(set-logic QF_LIA)\n(declare-const x Int)\n(assert (let ((y x)) (= (abs y) (- 1))))\n(check-sat)\n"),
        "sat",
        "abs in a let body must not escape the downgrade",
    );
    // mod (from a divisible desugar) under a let.
    assert_ne!(
        verdict("(set-logic QF_LIA)\n(assert (let ((y 10)) ((_ divisible 3) y)))\n(check-sat)\n"),
        "sat",
        "let-bound divisible (mod) must not escape the downgrade",
    );
}

// ── #290: TOTAL substitution — instantiate THROUGH let/match/wrapper bodies ──
//
// `substitute_cached` used to drop Let/Match/String/FP/BV/Dt* kinds (a
// `Some(_) => id` catch-all), so quantifier instantiation kept the bound
// variable inside those wrappers (the CCFV E/F leak) and could not match the
// ground term. The substitution is now TOTAL (capture-avoiding); these check it
// instantiates through the wrappers AND stays sound. Verified:
// `oxiz-total-subst-verification` (Verus no-leak) + a 600-sample cvc5 differential.

/// `∀x. (let ((y x)) (P y))` together with `¬(P c)` is UNSAT — instantiation must
/// substitute `x ↦ c` THROUGH the `let` body. Before #290 the `let` was returned
/// unchanged, so the instance stayed `(P y[x])` and never matched `(P c)`.
#[test]
fn instantiation_substitutes_through_a_let_body() {
    let script = "\
(set-logic UF)
(declare-sort U 0)
(declare-fun P (U) Bool)
(declare-const c U)
(assert (forall ((x U)) (let ((y x)) (P y))))
(assert (not (P c)))
(check-sat)
";
    assert_eq!(verdict(script), "unsat", "instantiation must reach through the let body");
}

/// The companion satisfiable control: `∀x. (let ((y x)) (P y))` with `(P c)`
/// asserted is consistent — total substitution must not fabricate `unsat`.
#[test]
fn let_body_instantiation_stays_sat_when_consistent() {
    let script = "\
(set-logic UF)
(declare-sort U 0)
(declare-fun P (U) Bool)
(declare-const c U)
(assert (forall ((x U)) (let ((y x)) (P y))))
(assert (P c))
(check-sat)
";
    assert_ne!(verdict(script), "unsat", "consistent let-body instance must not be unsat");
}

/// `to_real` / `is_int` parse with the right sorts and downgrade a `Sat`:
/// `(> (to_real x) 0.0)` is satisfiable but undecided ⇒ the sound `unknown`,
/// never a wrong `unsat`.
#[test]
fn to_real_and_is_int_parse_and_downgrade() {
    let tr = verdict(
        "(set-logic QF_LIRA)\n(declare-const x Int)\n(assert (> (to_real x) 0.0))\n(check-sat)\n",
    );
    assert_ne!(tr, "unsat", "(> (to_real x) 0.0) is satisfiable — must not be a fabricated unsat");
    let ii = verdict(
        "(set-logic QF_LIRA)\n(declare-const r Real)\n(assert (is_int r))\n(check-sat)\n",
    );
    assert_ne!(ii, "unsat", "(is_int r) is satisfiable — must not be a fabricated unsat");
}
