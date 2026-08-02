//! Regression (#429): an Int-sorted term produced by a NON-arithmetic theory is
//! an INTERFACE VARIABLE between that theory and LIA — its bounds must reach the
//! simplex, and its integrality must come from its SMT sort.
//!
//! Four independently-reported false-`sat`s shared one shape: `0 < e < 1` over
//! an Int-sorted `e` whose head belongs to another theory (a datatype selector,
//! `str.len`, `bv2nat`, or a UF application only MBQI could produce). All four
//! also reproduce under a `…LIA…`-named logic where #427's per-term integrality
//! is already correct, so none of them is a sort-declaration gap — the
//! constraints were not reaching integrality reasoning at all.
//!
//! Three distinct mechanisms were behind them:
//!
//! 1. **The whole atom was dropped from arithmetic.**
//!    `Solver::extract_linear_terms` (`solver/encode.rs`) whitelists the term
//!    kinds it can linearize (`Var`, numeric `Apply`, numeric `Select`, `Add`,
//!    `Sub`, `Neg`, `Mul`, numerals) and returns `None` for everything else.
//!    That `None` propagates out of `parse_arith_comparison`, so
//!    `var_to_parsed_arith` gets no entry, so `TheoryManager::process_constraint`
//!    asserts NOTHING into the simplex — the comparison survives only as a free
//!    Boolean the SAT solver satisfies by fiat. `(> (fst p) 0) ∧ (< (fst p) 1)`
//!    was therefore `sat`. Fixed by admitting an undecomposable sub-term as one
//!    opaque Nelson-Oppen interface variable (a relaxation: every conflict it
//!    yields is genuine, and it can never manufacture a `sat`), with integrality
//!    supplied from the term's own sort by `track_theory_vars` /
//!    `declare_arith_sorts`.
//!
//!    NOTE `check_term_bound_infeasible` (`solver/check_nlsat.rs`) already
//!    caught the narrow case of literal bounds on ONE shared term in top-level
//!    `And` position — but only over the RATIONALS (`0 < e < 1` is a perfectly
//!    nonempty rational interval), and never under `Or`/`Implies`/`Ite`.
//!
//! 2. **The interface variable carried no domain axiom.** `str.len` is
//!    non-negative, and nothing in this solver ever told arithmetic so. Once (1)
//!    made `(str.len s)` a live arithmetic variable, `(< (str.len s) 0)` was
//!    still `sat`. Fixed by `Solver::add_str_len_domain_axioms`.
//!
//! 3. **MBQI's constant-range completion assumed a DENSE order.**
//!    `try_range_completion` / `try_threshold_guard` (`clean_mbqi.rs`) certify a
//!    saturated universal by exhibiting a constant `k` in the intersected
//!    interval of `∀x̄. ⋀ cmp(f(x̄), cᵢ)`, testing emptiness with
//!    `interval_nonempty` — a rational test. For `f : Int → Int` and
//!    `∀i. 0 < f(i) < 1` the interval is rationally nonempty and integrally
//!    EMPTY, so the recognizer returned `Some(true)` and the engine reported
//!    `Saturated` → `sat`. Fixed by `interval_has_integer` when `f`'s result
//!    sort is `Int`.
//!
//! `bv2nat` is NOT decided by this fix: the parser has no such builtin, so
//! `(bv2nat a)` is a bare uninterpreted `Apply` carrying none of the operator's
//! semantics (range `0 ≤ bv2nat(a) < 2^w`, injectivity, the bit-level link to
//! `a`). It is registered as an undecided op (`context.rs`), which downgrades a
//! resulting `DefiniteSat` to `PossiblySat` ⇒ the sound `unknown`. The `unsat`
//! side stays available (an over-approximation's `unsat` is sound), which is why
//! `bv2nat_empty_int_interval_is_not_sat` accepts `unsat` OR `unknown` but never
//! `sat`.
//!
//! z3 AND cvc5 independently agree with every verdict pinned below.

use oxiz_solver::Context;

fn verdict(script: &str) -> &'static str {
    let mut ctx = Context::new();
    ctx.set_timeout_ms(30_000);
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

// ───────────────────────── mechanism 1: dropped atom ────────────────────────

/// The reported datatype-selector repro. `(fst p)` is `Int`-sorted, but
/// `TermKind::DtSelector` is outside the linearizer's whitelist, so BOTH
/// comparisons vanished from the simplex.
#[test]
fn dt_selector_empty_int_interval_is_unsat() {
    let script = "\
(set-logic ALL)
(declare-datatypes ((P 0)) (((mk (fst Int) (snd Int)))))
(declare-const p P)
(assert (> (fst p) 0))
(assert (< (fst p) 1))
(check-sat)
";
    assert_eq!(
        verdict(script),
        "unsat",
        "no integer lies strictly between 0 and 1; `sat` means the two bounds \
         on the shared selector term never reached the arithmetic solver"
    );
}

/// The same shape under a `…LIA…`-named logic — proving this is NOT #427's
/// logic-name/integrality gap (that flag is already `true` here).
#[test]
fn dt_selector_empty_int_interval_is_unsat_under_lia_logic() {
    let script = "\
(set-logic QF_UFDTLIA)
(declare-datatypes ((P 0)) (((mk (fst Int) (snd Int)))))
(declare-const p P)
(assert (> (fst p) 0))
(assert (< (fst p) 1))
(check-sat)
";
    assert_eq!(verdict(script), "unsat");
}

/// Buried under `Or`, where the `check_term_bound_infeasible` net (top-level
/// `And` conjuncts only) cannot reach it — so this pins the arithmetic path
/// specifically, not the trichotomy pre-pass.
#[test]
fn dt_selector_empty_int_interval_under_or_is_unsat() {
    let script = "\
(set-logic ALL)
(declare-datatypes ((P 0)) (((mk (fst Int) (snd Int)))))
(declare-const p P)
(declare-const b Bool)
(assert (or b (> (fst p) 0)))
(assert (or b (< (fst p) 1)))
(assert (not b))
(check-sat)
";
    assert_eq!(verdict(script), "unsat");
}

/// The reported `str.len` repro.
#[test]
fn str_len_empty_int_interval_is_unsat() {
    let script = "\
(set-logic ALL)
(declare-const s String)
(assert (> (str.len s) 0))
(assert (< (str.len s) 1))
(check-sat)
";
    assert_eq!(verdict(script), "unsat");
}

/// A foreign Int term inside a LINEAR COMBINATION, not bare, where the
/// refutation needs a PARITY argument (`2·(fst p) = 1`) rather than an interval.
///
/// PARITY TEST, not a completeness test. The plain-`Int` mirror
/// (`(= (+ (* 2 x) y) 1) ∧ (= y 0)`, `x : Int`) is `unknown` on this solver —
/// a pre-existing incompleteness of the integer branch-and-bound that predates
/// and is untouched by this fix. What #429 changed is that the FOREIGN-headed
/// version used to be a confident false `sat` while its native mirror was
/// already the sound `unknown`; both are now `unknown`. Pinning "not `sat`"
/// keeps the two paths from diverging again without pinning a completeness
/// level the native path does not have either.
#[test]
fn dt_selector_parity_refutation_is_not_sat() {
    let foreign = "\
(set-logic ALL)
(declare-datatypes ((P 0)) (((mk (fst Int) (snd Int)))))
(declare-const p P)
(declare-const y Int)
(assert (= (+ (* 2 (fst p)) y) 1))
(assert (= y 0))
(check-sat)
";
    let native = "\
(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ (* 2 x) y) 1))
(assert (= y 0))
(check-sat)
";
    let (vf, vn) = (verdict(foreign), verdict(native));
    assert_ne!(
        vf, "sat",
        "`2·(fst p) = 1` has no integer solution; `sat` means the selector's \
         bounds never reached integrality reasoning"
    );
    assert_eq!(
        vf, vn,
        "the foreign-headed term must reach exactly the same verdict as its \
         plain-Int mirror (got foreign={vf}, native={vn})"
    );
}

/// Two DIFFERENT foreign heads sharing one constraint — the interface variables
/// must be per-term and must compose. Same parity framing as above: the
/// plain-`Int` mirror (`a = b ∧ 0 < a+b < 2`) is also `unknown` here.
#[test]
fn mixed_foreign_heads_match_their_native_mirror() {
    let foreign = "\
(set-logic ALL)
(declare-datatypes ((P 0)) (((mk (fst Int) (snd Int)))))
(declare-const p P)
(declare-const s String)
(assert (= (fst p) (str.len s)))
(assert (> (+ (fst p) (str.len s)) 0))
(assert (< (+ (fst p) (str.len s)) 2))
(check-sat)
";
    let native = "\
(set-logic ALL)
(declare-const a Int)
(declare-const b Int)
(assert (= a b))
(assert (> (+ a b) 0))
(assert (< (+ a b) 2))
(check-sat)
";
    let (vf, vn) = (verdict(foreign), verdict(native));
    assert_ne!(
        vf, "sat",
        "the sum of two equal integers is even, so it cannot be the only \
         integer strictly inside (0,2), namely 1"
    );
    assert_eq!(vf, vn, "foreign={vf} must match native={vn}");
}

// ─────────────────── mechanism 2: missing domain axiom ──────────────────────

/// `str.len` is non-negative in the SMT-LIB string theory. Making it an
/// arithmetic interface variable is not enough on its own — the variable is
/// unconstrained unless the producing theory states its domain.
#[test]
fn negative_str_len_is_unsat() {
    let script = "\
(set-logic ALL)
(declare-const s String)
(assert (< (str.len s) 0))
(check-sat)
";
    assert_eq!(verdict(script), "unsat");
}

/// Same, reached only through a linear combination (the axiom must be attached
/// to the TERM, not pattern-matched on the atom's shape).
#[test]
fn negative_str_len_in_sum_is_unsat() {
    let script = "\
(set-logic ALL)
(declare-const s String)
(declare-const t String)
(assert (< (+ (str.len s) (str.len t)) 0))
(check-sat)
";
    assert_eq!(verdict(script), "unsat");
}

// ────────────── mechanism 3: MBQI dense-order range completion ──────────────

/// The reported quantified-UF repro. Nothing is ground here, so e-matching
/// yields zero bindings and the verdict is decided entirely by
/// `try_range_completion`, which certified the axiom off a rationally-nonempty
/// `(0,1)`.
#[test]
fn quantified_uf_empty_int_range_is_not_sat() {
    let script = "\
(set-logic AUFLIA)
(declare-fun f (Int) Int)
(assert (forall ((i Int)) (and (> (f i) 0) (< (f i) 1))))
(check-sat)
";
    let v = verdict(script);
    assert!(
        v == "unsat" || v == "unknown",
        "`f : Int -> Int` has no value strictly inside (0,1), so the axiom is \
         UNSAT; the model-completion recognizer must not certify it off a dense \
         interval test (got {v})"
    );
}

/// The same axiom with one ground `f`-point, which gives MBQI something to
/// instantiate on — this reaches the arithmetic refutation and must be `unsat`.
#[test]
fn quantified_uf_empty_int_range_with_ground_point_is_unsat() {
    let script = "\
(set-logic AUFLIA)
(declare-fun f (Int) Int)
(declare-const c Int)
(assert (forall ((i Int)) (and (> (f i) 0) (< (f i) 1))))
(assert (= c (f 7)))
(check-sat)
";
    assert_eq!(verdict(script), "unsat");
}

// ─────────────────────────── bv2nat: sound, not decided ─────────────────────

/// `bv2nat` is unimplemented; the verdict must not be `sat`.
#[test]
fn bv2nat_empty_int_interval_is_not_sat() {
    let script = "\
(set-logic ALL)
(declare-const a (_ BitVec 8))
(assert (> (bv2nat a) 0))
(assert (< (bv2nat a) 1))
(check-sat)
";
    let v = verdict(script);
    assert!(
        v != "sat",
        "`bv2nat` carries none of its semantics in this solver, so a `sat` \
         resting on it is untrustworthy — the undecided-op downgrade must fire \
         (got {v})"
    );
}

/// A bound no 8-bit value can satisfy. Also must not be `sat` — and this one is
/// beyond what the interface-variable abstraction alone can refute, which is
/// exactly why the downgrade (not a "fix") is the honest answer for `bv2nat`.
#[test]
fn bv2nat_out_of_range_bound_is_not_sat() {
    let script = "\
(set-logic ALL)
(declare-const a (_ BitVec 8))
(assert (> (bv2nat a) 300))
(check-sat)
";
    assert_ne!(verdict(script), "sat");
}

// ──────────────────────── over-fix controls (stay sat) ──────────────────────
//
// The interface-variable abstraction adds constraints, so its own failure mode
// is a FALSE UNSAT. Each control below is the genuinely-satisfiable sibling of
// a case pinned above.

/// A Real-sorted selector field: `(0,1)` IS nonempty over the reals.
#[test]
fn real_selector_open_interval_stays_sat() {
    let script = "\
(set-logic ALL)
(declare-datatypes ((R 0)) (((mk (re Real) (im Real)))))
(declare-const z R)
(assert (> (re z) 0.0))
(assert (< (re z) 1.0))
(check-sat)
";
    assert_eq!(
        verdict(script),
        "sat",
        "integrality must follow the FIELD's sort; forcing every interface \
         variable integral is the mirror false-unsat"
    );
}

/// A selector interval that does contain an integer.
#[test]
fn dt_selector_nonempty_int_interval_stays_sat() {
    let script = "\
(set-logic ALL)
(declare-datatypes ((P 0)) (((mk (fst Int) (snd Int)))))
(declare-const p P)
(assert (> (fst p) 0))
(assert (< (fst p) 5))
(check-sat)
";
    assert_eq!(verdict(script), "sat");
}

/// A non-negative `str.len` bound: the domain axiom must not over-constrain.
#[test]
fn nonnegative_str_len_stays_sat() {
    let script = "\
(set-logic ALL)
(declare-const s String)
(assert (> (str.len s) 3))
(check-sat)
";
    assert_eq!(verdict(script), "sat");
}

/// A Real-sorted range-completion axiom: `∀x. 0 < g(x) < 1` over
/// `g : Int → Real` is satisfiable (`g ≡ 1/2`) and the recognizer must still
/// certify it.
#[test]
fn quantified_real_range_stays_sat() {
    let script = "\
(set-logic AUFLIRA)
(declare-fun g (Int) Real)
(assert (forall ((i Int)) (and (> (g i) 0.0) (< (g i) 1.0))))
(check-sat)
";
    assert_eq!(
        verdict(script),
        "sat",
        "the integer-point test must be gated on the completed function's \
         RESULT SORT, not applied unconditionally"
    );
}

/// An Int-sorted range-completion axiom whose interval DOES contain integers —
/// the recognizer must keep certifying it.
#[test]
fn quantified_int_nonempty_range_stays_sat() {
    let script = "\
(set-logic AUFLIA)
(declare-fun f (Int) Int)
(assert (forall ((i Int)) (and (> (f i) 0) (< (f i) 5))))
(check-sat)
";
    assert_eq!(verdict(script), "sat");
}

/// A satisfiable array-`select` bound: the `Select` arm already worked and must
/// keep working (the two-pass parser must not perturb terms the STRICT pass
/// already handles).
#[test]
fn array_select_int_bound_stays_sat() {
    let script = "\
(set-logic ALL)
(declare-const arr (Array Int Int))
(assert (> (select arr 0) 0))
(assert (< (select arr 0) 5))
(check-sat)
";
    assert_eq!(verdict(script), "sat");
}

/// The array-`select` mirror of the core shape (this path was already correct;
/// pinned so the two-pass parser cannot silently regress it).
#[test]
fn array_select_empty_int_interval_is_unsat() {
    let script = "\
(set-logic ALL)
(declare-const arr (Array Int Int))
(assert (> (select arr 0) 0))
(assert (< (select arr 0) 1))
(check-sat)
";
    assert_eq!(verdict(script), "unsat");
}

// ──────────────────────────── push/pop discipline ───────────────────────────

/// The `str.len` domain axiom is a SAT-level unit clause, so its emitted-marker
/// must be trail-undone on `pop()` — otherwise the second scope believes the
/// axiom is present while the clause is gone (the "cache mutated at assert
/// time, never scrubbed on pop" bug class).
#[test]
fn str_len_domain_axiom_survives_push_pop() {
    let script = "\
(set-logic ALL)
(declare-const s String)
(push 1)
(assert (< (str.len s) 0))
(check-sat)
(pop 1)
(push 1)
(assert (< (str.len s) 0))
(check-sat)
(pop 1)
";
    let mut ctx = Context::new();
    ctx.set_timeout_ms(30_000);
    let out = ctx.execute_script(script).expect("script runs");
    let verdicts: Vec<&str> = out
        .iter()
        .filter_map(|l| match l.trim() {
            "sat" => Some("sat"),
            "unsat" => Some("unsat"),
            "unknown" => Some("unknown"),
            _ => None,
        })
        .collect();
    assert_eq!(
        verdicts,
        vec!["unsat", "unsat"],
        "the re-asserted scope must re-emit the domain axiom the pop discarded"
    );
}
