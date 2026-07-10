//! Permanent (z3-cross-checked) regressions for #419 items 1 & 2 — the
//! shared iterative equality/binding closure
//! (`check_dt.rs::compute_dt_equality_closure`) that closes:
//!
//!   1. INJECTIVITY-TRANSITIVITY LOSS: `collect_var_ctor_bindings` used to
//!      keep only the FIRST ctor-term binding per equivalence class, so a
//!      variable bound to the SAME constructor by two SEPARATE assertions
//!      (`x = cons(a,b)`, `x = cons(c,d)`) never surfaced the entailed
//!      `a = c` fact. Closed by: (a) `add_dt_multi_binding_selector_reduction_axioms`
//!      re-running the audited selector-reduction walk once per EXTRA
//!      binding (the mechanism that actually produces the conflicting
//!      ground facts for a selector-mentioning repro), and (b)
//!      `inject_dt_derived_ctor_equalities` asserting the ground
//!      `binding1 = binding2` fact THROUGH THE SIMPLIFIER so
//!      `DatatypeRewriter::rewrite_constructor_eq` decomposes it into
//!      pairwise field equalities (the mechanism for a repro that never
//!      mentions any selector at all).
//!   2. ACYCLICITY / `resolve_dt_normal_form` NON-COMPOSITION:
//!      `check_dt_acyclicity` only ever saw RAW syntactic var=var /
//!      var=ctor-term equalities, never a selector-shaped equality
//!      (`(= (tl z) z)`) resolved through a SEPARATELY-asserted binding.
//!      Closed by folding a resolved selector-equality into the SAME
//!      closure the acyclicity check consumes.
//!
//! See `check_dt.rs::compute_dt_equality_closure`'s doc comment for the full
//! algorithm and termination argument, and
//! `encode.rs::add_dt_multi_binding_selector_reduction_axioms`/
//! `inject_dt_derived_ctor_equalities`'s doc comments for the two-part
//! axiom-injection wiring.

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

fn verdicts(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.set_timeout_ms(5000);
    match ctx.execute_script(script) {
        Ok(out) => out
            .iter()
            .filter_map(|l| match l.trim() {
                "sat" => Some("sat".to_string()),
                "unsat" => Some("unsat".to_string()),
                "unknown" => Some("unknown".to_string()),
                _ => None,
            })
            .collect(),
        Err(_) => vec![],
    }
}

const PAIR_DT: &str = "(set-logic ALL)\n\
     (declare-datatypes ((MyPair 0)) (((cons (hd Int) (tl Int)))))\n";

const LST_DT: &str = "(set-logic ALL)\n\
     (declare-datatypes ((MyList 0)) (((nil) (cons (hd Int) (tl MyList)))))\n";

/// #419 item 1's EXACT target repro: `x=cons(a,b)`, `x=cons(c,d)`, and
/// `(hd x) != c` — since `x` is congruent to BOTH `cons(a,b)` and
/// `cons(c,d)`, injectivity forces `a=c`, and (via the SAME selector
/// re-derived against the SECOND binding) `(hd x) = c` directly — so the
/// user's `(not (= (hd x) c))` is a direct ground conflict. z3: `unsat`.
#[test]
fn injectivity_via_hd_selector_is_unsat() {
    let v = verdict(&format!(
        "{PAIR_DT}(declare-const x MyPair)\n\
         (declare-const a Int) (declare-const b Int)\n\
         (declare-const c Int) (declare-const d Int)\n\
         (assert (= x (cons a b)))\n\
         (assert (= x (cons c d)))\n\
         (assert (not (= (hd x) c)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// The SAME repro shape, but forcing the SECOND field (`tl`) instead of the
/// first — confirms the multi-binding selector-reduction pass isn't
/// accidentally hard-coded to field index 0.
#[test]
fn injectivity_via_tl_selector_is_unsat() {
    let v = verdict(&format!(
        "{PAIR_DT}(declare-const x MyPair)\n\
         (declare-const a Int) (declare-const b Int)\n\
         (declare-const c Int) (declare-const d Int)\n\
         (assert (= x (cons a b)))\n\
         (assert (= x (cons c d)))\n\
         (assert (not (= (tl x) d)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// #419 item 2's EXACT target repro: `z = cons(x,y)` then `(tl z) = z` —
/// `tl(z)` structurally reduces to `y` given `z`'s binding, so the second
/// assertion is really `y = z`, which combined with `z = cons(x,y)` gives
/// `y = cons(x,y)` — a direct well-foundedness cycle. Pre-fix this read
/// `sat` because `check_dt_acyclicity` never resolved the selector-shaped
/// equality through `z`'s binding. z3: `unsat`.
#[test]
fn selector_derived_equality_composes_with_acyclicity_is_unsat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const z MyList)\n\
         (declare-const x Int)\n\
         (declare-const y MyList)\n\
         (assert (= z (cons x y)))\n\
         (assert (= (tl z) z))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// Item 2's own control, isolating the exact gap: replacing the `(tl z) = z`
/// selector-shaped equality with the ALREADY-RESOLVED `y = z` (same
/// semantic fact, spelled out directly) was ALWAYS correctly `unsat` even
/// before this fix — confirms the fix didn't change behavior on the
/// already-working direct-equality path, only added the selector-shaped
/// case.
#[test]
fn selector_derived_equality_control_direct_var_equality_is_unsat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const z MyList)\n\
         (declare-const x Int)\n\
         (declare-const y MyList)\n\
         (assert (= z (cons x y)))\n\
         (assert (= y z))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// SOUNDNESS CONTROL — two ctor bindings to two DIFFERENT, otherwise
/// UNRELATED variables must never be unioned together. `x = cons(a,b)` and
/// `w = cons(c,d)` share NO asserted equality between `x` and `w`, so `a`
/// and `c` are free to differ. Must stay `sat`.
#[test]
fn unrelated_vars_not_spuriously_unioned_stays_sat() {
    let v = verdict(&format!(
        "{PAIR_DT}(declare-const x MyPair) (declare-const w MyPair)\n\
         (declare-const a Int) (declare-const b Int)\n\
         (declare-const c Int) (declare-const d Int)\n\
         (assert (= x (cons a b)))\n\
         (assert (= w (cons c d)))\n\
         (assert (not (= a c)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// SOUNDNESS CONTROL — a ctor binding established only inside an INACTIVE
/// `or` branch must not leak into the global closure. `(or (= x
/// (cons a b)) (= x (cons c d)))` is a genuine disjunction (x is ONE of the
/// two shapes, not both at once), so `a = c` is NOT entailed. Must stay
/// `sat` — `compute_dt_equality_closure`'s base inputs come from
/// `collect_dt_constraints_v2`'s existing polarity gating, which never
/// collects an `Or`-branch-local equality as globally true.
#[test]
fn or_branch_local_binding_does_not_leak_into_global_closure_stays_sat() {
    let v = verdict(&format!(
        "{PAIR_DT}(declare-const x MyPair)\n\
         (declare-const a Int) (declare-const b Int)\n\
         (declare-const c Int) (declare-const d Int)\n\
         (assert (or (= x (cons a b)) (= x (cons c d))))\n\
         (assert (not (= a c)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// SOUNDNESS CONTROL — a selector application whose argument does NOT
/// resolve to any known constructor must stay fully unconstrained: no
/// fabricated equality. `p` has no ctor binding at all, so `(hd p) = 7` is
/// just an ordinary, satisfiable constraint. Must stay `sat`.
#[test]
fn selector_on_non_resolving_arg_stays_unconstrained_sat() {
    let v = verdict(&format!(
        "{PAIR_DT}(declare-const p MyPair)\n\
         (assert (= (hd p) 7))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// SOUNDNESS CONTROL — the different-CONSTRUCTOR case (already handled
/// elsewhere, e.g. #399 exhaustiveness / direct name-keyed cross-checks)
/// must remain caught, unduplicated and unregressed by the new closure:
/// `x = nil` and `x = cons(a,b)` is a direct ground conflict regardless of
/// this fix.
#[test]
fn different_constructor_case_still_caught_is_unsat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const x MyList)\n\
         (declare-const a Int) (declare-const b MyList)\n\
         (assert (= x nil))\n\
         (assert (= x (cons a b)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// A 3-WAY ctor-binding case: `x` bound to the SAME constructor from THREE
/// separate assertions. Injectivity forces `a = c = e` transitively; probed
/// here via the selector-reduction mechanism (`(hd x) != e`).
#[test]
fn three_way_binding_via_selector_forces_pairwise_equality_is_unsat() {
    let v = verdict(&format!(
        "{PAIR_DT}(declare-const x MyPair)\n\
         (declare-const a Int) (declare-const b Int)\n\
         (declare-const c Int) (declare-const d Int)\n\
         (declare-const e Int) (declare-const f Int)\n\
         (assert (= x (cons a b)))\n\
         (assert (= x (cons c d)))\n\
         (assert (= x (cons e f)))\n\
         (assert (not (= (hd x) e)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// The SAME 3-way binding case, but with NO selector mentioned ANYWHERE —
/// probing pure injectivity (`a = e`) directly. This is the harder case:
/// closed entirely by `inject_dt_derived_ctor_equalities` routing the
/// injected `cons(a,b) = cons(e,f)` fact THROUGH THE SIMPLIFIER (so
/// `DatatypeRewriter::rewrite_constructor_eq` decomposes it into `a=e ∧
/// b=f`) rather than encoding the raw equality directly (which would leave
/// it an opaque, non-decomposed EUF congruence fact — plain congruence
/// closure does not derive `a=e` from `cons(a,b)=cons(e,f)` on its own).
#[test]
fn three_way_binding_bare_no_selector_forces_pairwise_equality_is_unsat() {
    let v = verdict(&format!(
        "{PAIR_DT}(declare-const x MyPair)\n\
         (declare-const a Int) (declare-const b Int)\n\
         (declare-const c Int) (declare-const d Int)\n\
         (declare-const e Int) (declare-const f Int)\n\
         (assert (= x (cons a b)))\n\
         (assert (= x (cons c d)))\n\
         (assert (= x (cons e f)))\n\
         (assert (not (= a e)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// The most direct form of the bare-injectivity case: asserting
/// `(cons a b) = (cons c d)` with NO variable and NO selector at all still
/// forces `a = c`. (This path is actually handled upstream by
/// `DatatypeRewriter::rewrite_constructor_eq` alone, with no closure
/// involvement — kept here as a baseline sanity check that
/// `inject_dt_derived_ctor_equalities`'s simplifier routing is consistent
/// with the pre-existing direct-equality behavior it relies on.)
#[test]
fn direct_ctor_equality_injectivity_baseline_is_unsat() {
    let v = verdict(&format!(
        "{PAIR_DT}(declare-const a Int) (declare-const b Int)\n\
         (declare-const c Int) (declare-const d Int)\n\
         (assert (= (cons a b) (cons c d)))\n\
         (assert (not (= a c)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// MULTI-STEP fixpoint case: closing `(hd w) = r` genuinely requires TWO
/// rounds of `compute_dt_equality_closure`'s fixpoint loop. Round 1 resolves
/// `(tl z) = w` (using `z`'s BASE binding `z = cons(3, q)`) into the derived
/// equality `w = q`; only THEN, in round 2, does `q`'s BASE binding
/// `q = cons(5, nil)` become reachable from `w` (through the round-1-derived
/// `w = q`), letting `(hd w)` resolve to `5`. A single-pass (non-iterating)
/// version of this closure would miss this and stay `sat`; z3: `unsat`
/// (`r` must be `5`).
#[test]
fn multi_round_fixpoint_selector_chain_is_unsat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const z MyList) (declare-const w MyList) (declare-const q MyList)\n\
         (declare-const r Int)\n\
         (assert (= z (cons 3 q)))\n\
         (assert (= q (cons 5 nil)))\n\
         (assert (= (tl z) w))\n\
         (assert (= (hd w) r))\n\
         (assert (not (= r 5)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// PUSH/POP SOUNDNESS — the new `dt_selector_extra_reduced` /
/// `dt_ctor_eq_injected` trail-undone dedup sets must not leak a derived
/// fact from a popped scope into a later, unrelated scope. Inside the
/// `push`, `x` gets a 2-way SAME-constructor binding and the injectivity
/// conflict correctly fires (`unsat`). After `pop`, `x`'s bindings are gone
/// entirely, so the SAME `a != c` probe (now with `a`/`c` totally
/// unconstrained) must read `sat` — if either new dedup/trail-op pairing
/// were wrong, a stale unit clause could survive the pop and wrongly keep
/// this `unsat`.
#[test]
fn popped_multi_binding_axioms_do_not_leak_into_later_scope() {
    let v = verdicts(&format!(
        "{PAIR_DT}(declare-const x MyPair)\n\
         (declare-const a Int) (declare-const b Int)\n\
         (declare-const c Int) (declare-const d Int)\n\
         (push 1)\n\
         (assert (= x (cons a b)))\n\
         (assert (= x (cons c d)))\n\
         (assert (not (= (hd x) c)))\n\
         (check-sat)\n\
         (pop 1)\n\
         (assert (not (= a c)))\n\
         (check-sat)\n"
    ));
    assert_eq!(
        v,
        vec!["unsat".to_string(), "sat".to_string()],
        "the popped scope's 2-way binding (and its derived injectivity \
         facts) must not survive to constrain `a`/`c` in the later, \
         binding-free scope"
    );
}

/// Idempotency control — re-running `check-sat` multiple times in the SAME
/// scope over the SAME multi-binding class must not duplicate clauses or
/// otherwise misbehave (mirrors `dt_indirect_var_pop_soundness.rs`'s
/// analogous control for the #418 item 2 pass).
#[test]
fn multi_binding_reduction_is_idempotent_across_repeated_check_sat() {
    let v = verdicts(&format!(
        "{PAIR_DT}(declare-const x MyPair)\n\
         (declare-const a Int) (declare-const b Int)\n\
         (declare-const c Int) (declare-const d Int)\n\
         (assert (= x (cons a b)))\n\
         (assert (= x (cons c d)))\n\
         (check-sat)\n\
         (check-sat)\n\
         (assert (not (= (hd x) c)))\n\
         (check-sat)\n\
         (check-sat)\n"
    ));
    assert_eq!(
        v,
        vec![
            "sat".to_string(),
            "sat".to_string(),
            "unsat".to_string(),
            "unsat".to_string(),
        ],
        "repeated check-sat calls over the same (or monotonically growing) \
         assertion set must be stable and idempotent"
    );
}

// ---------------------------------------------------------------------
// Post-landing follow-up, found by this integration pass's OWN 1000-seed
// z3-differential re-verification of the already-landed items 1+2 (NOT one
// of the originally-scoped #419 repros above): `compute_dt_equality_
// closure`'s step (b) only ever added a same-constructor pair's WHOLE ctor
// terms to `eqs` (`c1 = c2`), never decomposing them field-by-field —
// invisible to `cycle_exists_given`'s class-based edges and to a LATER
// closure round's own selector-resolution step, both of which need the
// per-FIELD equality, not just the opaque container-level fact. Closed by
// step (b2): whenever two same-constructor ctor terms are found in one
// class (whether that whole-term pair is freshly derived or came straight
// from `base_ctor_bindings`), also zip their argument lists and fold
// `args1[i] = args2[i]` into the SAME growing `eqs` set. See
// `compute_dt_equality_closure`'s doc comment, "Step (b2)".
// ---------------------------------------------------------------------

/// The MINIMIZED repro this follow-up fix targets: `mbx` bound to
/// `c01(vBool1, 4, vDt0)` and, separately, to `c01(vBool0, vInt1,
/// c01(vBool0, 0, vDt0))` — TWO same-constructor bindings (item 1's shape),
/// where decomposing them field-by-field forces, on the THIRD field,
/// `vDt0 = c01(vBool0, 0, vDt0)` — a direct well-foundedness cycle (item
/// 2's domain) that is only reachable by FIRST performing item 1's
/// decomposition. Pre-fix this read `sat` (found via a 1000-seed
/// z3-differential fuzz re-run of the already-landed #419 items, seed 123);
/// z3: `unsat`.
#[test]
fn multi_binding_field_decomposition_reveals_cycle_is_unsat() {
    let dt = "(set-logic ALL)\n\
        (declare-datatypes ((Node 0)) (((leaf) \
            (mk (mkf0 Bool) (mkf1 Int) (mkf2 Node)))))\n";
    let v = verdict(&format!(
        "{dt}(declare-const vb0 Bool) (declare-const vb1 Bool)\n\
         (declare-const vi0 Int) (declare-const vi1 Int)\n\
         (declare-const vn Node) (declare-const mbx Node)\n\
         (assert (= mbx (mk vb1 4 vn)))\n\
         (assert (= mbx (mk vb0 vi1 (mk vb0 0 vn))))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// SOUNDNESS CONTROL for the same shape: identical to the test above except
/// the inner binding's datatype-sorted field is a FRESH, otherwise-free
/// variable (`vn2`) instead of `vn` itself — so no cycle is forced (the
/// decomposition still derives `vb1 = vb0`, `4 = vi1`, and `vn = mk(vb0, 0,
/// vn2)`, but `vn2` is unconstrained, so this last fact is just an ordinary
/// acyclic binding, not a self-containment). Must stay `sat` — confirms the
/// fix's field decomposition doesn't fabricate a conflict out of an
/// otherwise-satisfiable multi-binding.
#[test]
fn multi_binding_field_decomposition_without_cycle_stays_sat() {
    let dt = "(set-logic ALL)\n\
        (declare-datatypes ((Node 0)) (((leaf) \
            (mk (mkf0 Bool) (mkf1 Int) (mkf2 Node)))))\n";
    let v = verdict(&format!(
        "{dt}(declare-const vb0 Bool) (declare-const vb1 Bool)\n\
         (declare-const vi0 Int) (declare-const vi1 Int)\n\
         (declare-const vn Node) (declare-const vn2 Node)\n\
         (declare-const mbx Node)\n\
         (assert (= mbx (mk vb1 4 vn)))\n\
         (assert (= mbx (mk vb0 vi1 (mk vb0 0 vn2))))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}
