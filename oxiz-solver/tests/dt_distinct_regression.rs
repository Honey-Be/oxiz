//! Permanent (z3/cvc5-cross-checked) regressions for #422 item 2 —
//! `TermKind::Distinct` was NOT handled in any polarity by
//! `collect_dt_constraints_v2`.
//!
//! A 2-ary `(distinct a b)` is a real, non-desugared `TermKind::Distinct`
//! AST node (confirmed: never rewritten to `Not(Eq(a,b))` at parse/build
//! time — `oxiz-core/src/ast/manager/builder.rs::mk_distinct` only collapses
//! arity ≤ 1). Before this fix, `collect_dt_constraints_v2` had NO `Distinct`
//! arm at all, so neither a positive `(distinct a b)` (a disequality) nor a
//! negated `(not (distinct a b))` (semantically an equality) was ever
//! recognized — a ground conflict expressed either way was invisible to
//! every check in `check_dt.rs`.
//!
//! Fixed by a new `TermKind::Distinct(args) if args.len() == 2` arm in
//! `collect_dt_constraints_v2`, reusing the EXACT SAME `record_dt_positive_
//! eq_fact`/`record_dt_negative_eq_fact` helpers `Eq`'s own arms use (no
//! hand-duplicated polarity logic):
//!   - POSITIVE `(distinct a b)` → `record_dt_negative_eq_fact` (both ways)
//!     + a `dt_diseq_pairs` entry, feeding `DtEqualityClosure::
//!     forces_disequality_conflict`.
//!   - NEGATIVE `(not (distinct a b))` → `record_dt_positive_eq_fact` (i.e.
//!     treated exactly like `(= a b)`).
//!
//! See `check_dt.rs::collect_dt_constraints_v2`'s doc comment, "`Distinct`
//! polarity mapping", for the full soundness argument — including the
//! N-ARY GUARD (`args.len() == 2` only) this file's own tests specifically
//! stress: an N-ARY `distinct` negated is a genuine DISJUNCTION (`¬distinct
//! (a,b,c) ≡ a=b ∨ a=c ∨ b=c`), NOT a single equality, and treating it as
//! one would be UNSOUND (a spurious conflict). `args.len() != 2` therefore
//! falls through uncollected (safe, if incomplete).

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

const D2: &str = "(set-logic ALL)\n\
     (declare-datatypes ((D2 0)) (((c0) (c1))))\n";

const D3: &str = "(set-logic ALL)\n\
     (declare-datatypes ((D3 0)) (((c0) (c1) (c2))))\n";

const LST_DT: &str = "(set-logic ALL)\n\
     (declare-datatypes ((LstD 0)) (((nilD) (consD (hdD Int) (tlD LstD)))))\n";

// ---------------------------------------------------------------------
// Full 2-ary polarity matrix, each cross-checked against its sibling `(= a
// b)` / `(not (= a b))` shape (z3/cvc5 for every case).
// ---------------------------------------------------------------------

/// POSITIVE `distinct`, no other constraint — a disequality alone is always
/// satisfiable over a 2+-element datatype. z3/cvc5: `sat`.
#[test]
fn distinct_positive_alone_is_sat() {
    let v = verdict(&format!(
        "{D2}(declare-const x D2) (declare-const y D2)\n\
         (assert (distinct x y))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// POSITIVE `distinct` combined with a forcing `(= x y)` — item 2's core
/// positive-polarity repro. Pre-fix: `sat` (the `distinct` fact was
/// invisible; `x=y` alone is satisfiable and nothing ever contradicted it).
/// z3/cvc5: `unsat`.
#[test]
fn distinct_positive_forces_conflict_is_unsat() {
    let v = verdict(&format!(
        "{D2}(declare-const x D2) (declare-const y D2)\n\
         (assert (= x y))\n\
         (assert (distinct x y))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// SIBLING of the test above, expressed with plain `=`/`not` instead of
/// `distinct` at all — confirms the SAME semantic conflict is caught
/// (trivially, at the Boolean/CNF level even, since both assertions share
/// the literal same atom) regardless of which surface syntax reaches it.
#[test]
fn eq_sibling_of_distinct_positive_forces_conflict_is_unsat() {
    let v = verdict(&format!(
        "{D2}(declare-const x D2) (declare-const y D2)\n\
         (assert (= x y))\n\
         (assert (not (= x y)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// NEGATIVE `(not (distinct x y))` alone — semantically `(= x y)`, always
/// satisfiable (e.g. both `c0`). z3/cvc5: `sat`.
#[test]
fn distinct_negative_alone_is_sat() {
    let v = verdict(&format!(
        "{D2}(declare-const x D2) (declare-const y D2)\n\
         (assert (not (distinct x y)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// NEGATIVE `(not (distinct x y))` combined with `x=c0`, `y=c1` — item 2's
/// core negative-polarity repro (`(not (distinct x y))` forces `x=y`, which
/// contradicts the two different constructor bindings). Pre-fix: `sat` (no
/// `Distinct` arm at all meant `(not (distinct x y))` contributed NOTHING —
/// not even recognized as `(= x y)`). z3/cvc5: `unsat`.
#[test]
fn distinct_negative_forces_conflict_is_unsat() {
    let v = verdict(&format!(
        "{D2}(declare-const x D2) (declare-const y D2)\n\
         (assert (= x c0))\n\
         (assert (= y c1))\n\
         (assert (not (distinct x y)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// SIBLING of the test above, using `(= x y)` directly instead of `(not
/// (distinct x y))` — confirms the negative-`distinct` path now produces
/// the IDENTICAL verdict as its direct-equality equivalent.
#[test]
fn eq_sibling_of_distinct_negative_forces_conflict_is_unsat() {
    let v = verdict(&format!(
        "{D2}(declare-const x D2) (declare-const y D2)\n\
         (assert (= x c0))\n\
         (assert (= y c1))\n\
         (assert (= x y))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

// ---------------------------------------------------------------------
// N-ARY GUARD — the single most important soundness guard in this whole
// task. `args.len() != 2` must NEVER be treated as a single equality.
// ---------------------------------------------------------------------

/// Positive 3-ary `distinct` alone, over a 3-element datatype — trivially
/// satisfiable (one value per variable). Confirms the `args.len() == 2`
/// guard doesn't somehow also mis-fire (e.g. panic, or silently drop) on
/// arity 3 in the POSITIVE direction. z3/cvc5: `sat`.
#[test]
fn distinct_nary_positive_basic_is_sat() {
    let v = verdict(&format!(
        "{D3}(declare-const a D3) (declare-const b D3) (declare-const c D3)\n\
         (assert (distinct a b c))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// Positive 3-ary `distinct` over a 2-element datatype — a genuine
/// PIGEONHOLE conflict (only 2 distinct values exist, so 3 pairwise-distinct
/// variables is impossible). This is NOT the shape #422 targets (item 2 is
/// about POLARITY recognition, not N-ary cardinality reasoning) — recorded
/// here purely as a sanity/no-regression control, confirming whatever
/// EXISTING machinery already closes N-ary `distinct` cardinality conflicts
/// continues to do so unaffected by this pass. z3/cvc5: `unsat`.
#[test]
fn distinct_nary_positive_pigeonhole_is_unsat() {
    let v = verdict(&format!(
        "{D2}(declare-const a D2) (declare-const b D2) (declare-const c D2)\n\
         (assert (distinct a b c))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// THE decisive N-ary guard test: `(not (distinct a b c))` (3-ary, negated)
/// means "at least two of a,b,c are equal" — a genuine DISJUNCTION (`a=b ∨
/// a=c ∨ b=c`), NOT a single forced equality. Combined with `(distinct a
/// b)` and `(distinct a c)` (forcing `a≠b` and `a≠c`), the ONLY remaining
/// way to satisfy the disjunction is `b=c` — perfectly satisfiable (e.g.
/// `a=c0, b=c1, c=c1`).
///
/// If the N-ary guard were MISSING or broken (e.g. if `collect_dt_
/// constraints_v2` wrongly treated the 3-ary negated `distinct` as if it
/// were `record_dt_positive_eq_fact(a, b)` — forcing `a=b` unconditionally,
/// ignoring `c` and the disjunctive structure entirely), this would
/// WRONGLY read `unsat` (a fabricated conflict: `a=b` forced, combined with
/// `(distinct a b)` forcing `a≠b`). The guard's presence keeps this
/// correctly `sat`, matching z3/cvc5 exactly — the critical soundness
/// property this whole task's highest-risk item protects.
#[test]
fn distinct_nary_negative_guard_prevents_spurious_unsat() {
    let v = verdict(&format!(
        "{D3}(declare-const a D3) (declare-const b D3) (declare-const c D3)\n\
         (assert (not (distinct a b c)))\n\
         (assert (distinct a b))\n\
         (assert (distinct a c))\n\
         (check-sat)\n"
    ));
    assert_eq!(
        v, "sat",
        "an N-ary negated distinct must NEVER be collected as a single \
         equality — doing so would fabricate an UNSAT here"
    );
}

/// The SAME N-ary guard shape, but pushed to 4-ary, and a different pairing
/// forced equal — generalizes the discriminator test to confirm the guard
/// isn't somehow specifically tuned to arity 3.
#[test]
fn distinct_nary4_negative_guard_prevents_spurious_unsat() {
    let dt = "(set-logic ALL)\n\
        (declare-datatypes ((D4 0)) (((c0) (c1) (c2) (c3))))\n";
    let v = verdict(&format!(
        "{dt}(declare-const a D4) (declare-const b D4) (declare-const c D4)\n\
         (declare-const d D4)\n\
         (assert (not (distinct a b c d)))\n\
         (assert (distinct a b)) (assert (distinct a c)) (assert (distinct a d))\n\
         (assert (distinct b c)) (assert (distinct b d))\n\
         (check-sat)\n"
    ));
    assert_eq!(
        v, "sat",
        "only the (c,d) pairing remains free to satisfy the 4-ary negated \
         distinct's disjunction — must stay sat, not fabricate unsat"
    );
}

// ---------------------------------------------------------------------
// `distinct` + datatype-specific combinations (testers, acyclicity) —
// broader sweep of previously entirely-unexercised interactions.
// ---------------------------------------------------------------------

/// `distinct` combined with POSITIVE testers pinning both variables to the
/// SAME NULLARY constructor — `is-c0 x`, `is-c0 y` force `x=y` (a nullary
/// constructor's tester is a true equivalence, `is-C(arg) ⟺ arg = C()` —
/// see `record_dt_nullary_tester_eq_fact`'s doc comment), contradicting
/// `(distinct x y)`.
///
/// CLOSED, #423 item 2 (this is the item's own literal motivating repro,
/// discovered by re-auditing this file's tests during #423 — it was
/// previously recorded here as `distinct_with_same_ctor_testers_pre_
/// existing_gap_not_regressed`, an honest "sat in both pre- and post-#422
/// binaries" residual note for the THEN-separate "nullary tester implies
/// exact value" gap; #423 item 2 is exactly that gap's fix). z3/cvc5:
/// `unsat`.
#[test]
fn distinct_with_same_nullary_ctor_testers_is_unsat() {
    let v = verdict(&format!(
        "{D2}(declare-const x D2) (declare-const y D2)\n\
         (assert ((_ is c0) x))\n\
         (assert ((_ is c0) y))\n\
         (assert (distinct x y))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// `distinct` combined with a tester on only ONE variable — genuinely
/// satisfiable (the untested variable can take the OTHER constructor).
/// z3/cvc5: `sat`.
#[test]
fn distinct_with_one_tester_stays_sat() {
    let v = verdict(&format!(
        "{D2}(declare-const x D2) (declare-const y D2)\n\
         (assert ((_ is c0) x))\n\
         (assert (distinct x y))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// NEGATIVE `distinct` (⇒ equality) composed with the PRE-EXISTING
/// acyclicity check: `(not (distinct x (cons a x)))` forces `x = cons(a,
/// x)` — a direct well-foundedness cycle. This is item 2's negative-context
/// handling feeding STRAIGHT into `#406`'s already-audited acyclicity
/// machinery (via `record_dt_positive_eq_fact` populating `var_ctor_term_
/// eqs`, exactly like a literal `(= x (cons a x))` would). Pre-fix: `sat`
/// (the whole fact was invisible). z3/cvc5: `unsat`.
#[test]
fn distinct_negative_composes_with_acyclicity_is_unsat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const x LstD) (declare-const a Int)\n\
         (assert (not (distinct x (consD a x))))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// The SAME acyclicity-via-negative-distinct fact, OR-WRAPPED alongside an
/// ordinary already-supported flat cycle as the sibling branch — exercises
/// `dt_items_force_conflict`'s leaf delegation to the new `Distinct` arm
/// (both branches conflict-forced ⇒ whole `or` unsat). Pre-fix: `sat`.
/// z3/cvc5: `unsat`.
#[test]
fn distinct_negative_composes_with_acyclicity_or_wrapped_is_unsat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const x LstD) (declare-const a Int)\n\
         (declare-const w LstD) (declare-const wi Int)\n\
         (assert (or\n\
           (not (distinct x (consD a x)))\n\
           (= w (consD wi w))\n\
         ))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// SOUNDNESS CONTROL for the OR-wrapped test above: the SAME
/// always-conflicting first branch, but paired with an ORDINARY
/// satisfiable second branch instead of another forced cycle — NOT every
/// branch is conflict-forced, so the whole `or` must stay `sat` (the
/// solver simply picks the second branch true, first branch false).
#[test]
fn distinct_negative_or_wrapped_other_branch_sat_stays_sat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const x LstD) (declare-const a Int)\n\
         (declare-const y LstD) (declare-const b Int)\n\
         (assert (or\n\
           (not (distinct x (consD a x)))\n\
           (= y (consD b nilD))\n\
         ))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// `distinct` between two manifest constructor applications directly (no
/// mediating variable at all) — composes item 2 (disequality collection,
/// unconditional/ungated by sort — `Distinct`'s push was always
/// unconditional; #423 item 1 later made the sibling `Eq` negative arm
/// unconditional too, so both arms are now identically ungated, not a
/// contrast anymore) with item 3 (`dt_ctor_ctor_eqs`, since NEITHER side
/// here is a variable, only the `Eq` positive arm's ctor-ctor collection —
/// exercised via the OTHER assertion below — feeds the closure). `x=cons(a,
/// b)`, `x=cons(c,b)` forces `a=c` (injectivity); `(distinct a c)` directly
/// contradicts. z3/cvc5: `unsat`.
#[test]
fn distinct_intfields_composes_with_item1_injectivity_is_unsat() {
    let dt = "(set-logic ALL)\n\
        (declare-datatypes ((PairD 0)) (((consP (hdP Int) (tlP Int)))))\n";
    let v = verdict(&format!(
        "{dt}(declare-const x PairD) (declare-const a Int) (declare-const b Int)\n\
         (declare-const c Int)\n\
         (assert (= x (consP a b)))\n\
         (assert (= x (consP c b)))\n\
         (assert (distinct a c))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// SOUNDNESS CONTROL for the test above: identical shape, but WITHOUT the
/// `distinct` — `a` and `c` being forced equal (injectivity) is not itself
/// a conflict with anything, so this must stay `sat`.
#[test]
fn distinct_intfields_composes_with_item1_injectivity_no_conflict_stays_sat() {
    let dt = "(set-logic ALL)\n\
        (declare-datatypes ((PairD2 0)) (((consP2 (hdP2 Int) (tlP2 Int)))))\n";
    let v = verdict(&format!(
        "{dt}(declare-const x PairD2) (declare-const a Int) (declare-const b Int)\n\
         (declare-const c Int)\n\
         (assert (= x (consP2 a b)))\n\
         (assert (= x (consP2 c b)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// Idempotency / push-pop control — `distinct`-sourced facts must not leak
/// across a `pop`, mirroring the existing controls for `#419`'s
/// `derived_ctor_eqs`/multi-binding mechanisms (both `check_dt_constraints`
/// and `dt_items_force_conflict` are rebuilt fresh from `self.assertions`
/// on every call — no persistent dedup/trail state of their own — so this
/// is expected to already hold, but verified explicitly since #422 adds new
/// out-params to that same rebuild-from-scratch collector).
#[test]
fn distinct_conflict_does_not_leak_across_pop() {
    let v: Vec<String> = {
        let mut ctx = Context::new();
        ctx.set_timeout_ms(5000);
        let script = format!(
            "{D2}(declare-const x D2) (declare-const y D2)\n\
             (push 1)\n\
             (assert (= x y))\n\
             (assert (distinct x y))\n\
             (check-sat)\n\
             (pop 1)\n\
             (assert (not (= x y)))\n\
             (check-sat)\n"
        );
        match ctx.execute_script(&script) {
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
    };
    assert_eq!(
        v,
        vec!["unsat".to_string(), "sat".to_string()],
        "the popped scope's (= x y)+(distinct x y) conflict must not survive \
         to constrain the later, unrelated (not (= x y)) scope"
    );
}
