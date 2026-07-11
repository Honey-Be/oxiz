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

// ---------------------------------------------------------------------
// #424 item 2 — POSITIVE-context N-ARY `distinct` (arity >= 3) decomposition.
//
// The `args.len() == 2` arm's own doc comment explicitly left this
// generalization "for a separate, distinctly-scoped follow-up... to keep
// this diff small" — this section is that follow-up. A new sibling arm,
// `TermKind::Distinct(args) if args.len() >= 3 && in_positive_context`,
// decomposes `distinct(a,b,c,...)` into ALL `C(n,2)` pairwise disequalities
// (a sound CONJUNCTION, unlike the negative-context N-ary case, which stays
// a genuine DISJUNCTION and remains completely unhandled forever — see the
// guard tests already above, unaffected by this section).
//
// Every "forced conflict" test below uses constructor INJECTIVITY (two
// bindings of the SAME variable to the SAME constructor with a differing
// field) to force an equality that is invisible to plain EUF/congruence
// closure — unlike simply asserting `x = C(7)` twice with a LITERAL
// argument (hash-consed to the identical term, which core equality
// reasoning already closes with no help from this arm at all). This is
// confirmed by a live pre-fix/post-fix differential: every "forced conflict"
// test below reads spurious `sat` on the pre-#424 binary and correctly
// `unsat` after the fix (cross-checked against z3/cvc5 too).
// ---------------------------------------------------------------------

const PAIR_INT_DT: &str = "(set-logic ALL)\n\
     (declare-datatypes ((PairID 0)) (((consI (hdI Int) (tlI Int)))))\n";

/// 3-ary positive `distinct`, injectivity-forced conflict at the ADJACENT
/// pair (indices 0,1): `distinct(a, c, q)` where `a`/`c` are forced equal by
/// injectivity through a shared `xw` binding. z3/cvc5: `unsat`.
#[test]
fn distinct_nary3_positive_forces_conflict_adjacent_pair_is_unsat() {
    let v = verdict(&format!(
        "{PAIR_INT_DT}(declare-const xw PairID) (declare-const a Int)\n\
         (declare-const b Int) (declare-const c Int) (declare-const q Int)\n\
         (assert (= xw (consI a b)))\n\
         (assert (= xw (consI c b)))\n\
         (assert (distinct a c q))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// SAME shape, `:simplify false` — isolates the pre-check machinery this
/// item actually touches from the SAT-level `DatatypeRewriter`-driven
/// decomposition (`config.simplify`-gated), which alone would otherwise
/// mask the gap. This is the TRUE pre-fix/post-fix differential: `sat`
/// (spurious) on the pre-#424 binary, `unsat` after.
#[test]
fn distinct_nary3_positive_forces_conflict_adjacent_pair_simplify_false_is_unsat() {
    let v = verdict(&format!(
        "{PAIR_INT_DT}(set-option :simplify false)\n\
         (declare-const xw PairID) (declare-const a Int)\n\
         (declare-const b Int) (declare-const c Int) (declare-const q Int)\n\
         (assert (= xw (consI a b)))\n\
         (assert (= xw (consI c b)))\n\
         (assert (distinct a c q))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// 4-ary positive `distinct`, injectivity-forced conflict at a NON-ADJACENT
/// pair (indices 1,3): `distinct(p, a, q, c)` — `a`/`c` (positions 1 and 3,
/// skipping both `p` at 0 and `q` at 2) are the forced-equal pair. This is
/// the decisive off-by-one discriminator: a loop that hard-coded
/// `args[0]`/`args[1]` (copy-paste from the 2-ary arm) instead of genuinely
/// iterating `args[i]`/`args[j]` would MISS this pair entirely and wrongly
/// stay `sat`. `:simplify false` isolates this arm specifically. z3/cvc5:
/// `unsat`.
#[test]
fn distinct_nary4_positive_forces_conflict_nonadjacent_pair_simplify_false_is_unsat() {
    let v = verdict(&format!(
        "{PAIR_INT_DT}(set-option :simplify false)\n\
         (declare-const xw PairID) (declare-const a Int) (declare-const b Int)\n\
         (declare-const c Int) (declare-const p Int) (declare-const q Int)\n\
         (assert (= xw (consI a b)))\n\
         (assert (= xw (consI c b)))\n\
         (assert (distinct p a q c))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// SAME 4-ary non-adjacent shape, DEFAULT `simplify: true` — confirms no
/// regression on the already-working SAT-level route (which independently
/// closes this via `DatatypeRewriter`), matching z3/cvc5.
#[test]
fn distinct_nary4_positive_forces_conflict_nonadjacent_pair_default_simplify_is_unsat() {
    let v = verdict(&format!(
        "{PAIR_INT_DT}(declare-const xw PairID) (declare-const a Int) (declare-const b Int)\n\
         (declare-const c Int) (declare-const p Int) (declare-const q Int)\n\
         (assert (= xw (consI a b)))\n\
         (assert (= xw (consI c b)))\n\
         (assert (distinct p a q c))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// EXHAUSTIVENESS-COMPOSITION control: a positive 4-ary `distinct` alone
/// (no injectivity forcing anything) over a 4-element enum datatype must
/// stay `sat` — a genuine no-conflict baseline, confirming the new arm
/// doesn't fabricate anything on its own.
#[test]
fn distinct_nary4_positive_alone_no_forcing_stays_sat() {
    let dt = "(set-logic ALL)\n\
        (declare-datatypes ((D4b 0)) (((e0) (e1) (e2) (e3))))\n";
    let v = verdict(&format!(
        "{dt}(declare-const a D4b) (declare-const b D4b) (declare-const c D4b)\n\
         (declare-const d D4b)\n\
         (assert (distinct a b c d))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// EXHAUSTIVENESS-COMPOSITION control #2: the SAME 4-ary `distinct`, but the
/// underlying datatype only has 3 elements — a genuine PIGEONHOLE conflict,
/// independent of this item's own injectivity-decomposition target (already
/// covered by `distinct_nary_positive_pigeonhole_is_unsat` at arity 3;
/// re-confirmed at arity 4 here since the new arm now ALSO decomposes this
/// shape into pairwise facts — must still agree with the pre-existing
/// cardinality machinery, not conflict with or duplicate-miscount it).
#[test]
fn distinct_nary4_positive_pigeonhole_is_unsat() {
    let v = verdict(&format!(
        "{D3}(declare-const a D3) (declare-const b D3) (declare-const c D3)\n\
         (declare-const d D3)\n\
         (assert (distinct a b c d))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// NULLARY-CTOR-EXCLUSION special case, triggered at the NON-(0,1) pair
/// (indices 1,2): `distinct(a, b, N)` where `N` is a NULLARY constructor —
/// `record_dt_negative_eq_fact`'s nullary-exclusion branch fires for the
/// `(b, N)` pair (index 1 vs 2), excluding `b` from the whole `N` class;
/// combined with an independently-asserted `(is-N b)`, this is a direct
/// conflict. `:simplify false` isolates the FLAT pre-check path this
/// special case actually feeds (`negative_ctor_equalities`/exhaustiveness),
/// confirmed as a true pre-fix(spurious sat)/post-fix(unsat) differential.
/// z3/cvc5: `unsat`.
#[test]
fn distinct_nary3_nullary_exclusion_at_nonzero_one_index_simplify_false_is_unsat() {
    let dt = "(set-logic ALL)\n\
        (declare-datatypes ((DNul 0)) (((Cf (fld Int)) (N))))\n";
    let v = verdict(&format!(
        "{dt}(set-option :simplify false)\n\
         (declare-const a DNul) (declare-const b DNul)\n\
         (assert ((_ is N) b))\n\
         (assert (distinct a b N))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// CONTROL for the test above: identical shape, WITHOUT the forcing
/// `(is-N b)` assertion — genuinely satisfiable (`b` simply takes the OTHER
/// constructor, `Cf`, and the `N` in the `distinct` triple is its own
/// distinct value). Confirms the nullary-exclusion arm doesn't fabricate a
/// conflict from the `distinct` fact alone.
#[test]
fn distinct_nary3_nullary_exclusion_control_without_forcing_stays_sat() {
    let dt = "(set-logic ALL)\n\
        (declare-datatypes ((DNul2 0)) (((Cf2 (fld Int)) (N2))))\n";
    let v = verdict(&format!(
        "{dt}(declare-const a DNul2) (declare-const b DNul2)\n\
         (assert (distinct a b N2))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// TESTER-SHAPE special case (`#404 phase 2`'s `v ≠ C(sel_{C,0}(v), ...)` ≡
/// `¬is-C(v)` recognizer, reused by `record_dt_negative_eq_fact`), triggered
/// at the NON-(0,1) pair (indices 1,2): `distinct(a, b, C(fld(b)))` — the
/// `(b, C(fld(b)))` pair (index 1 vs 2) matches the tester shape, deriving
/// `¬is-C(b)`; combined with the independently-asserted `b = C(7)` (which
/// makes `is-C(b)` true), this is a direct conflict. Cross-checked against
/// z3 AND cvc5 (`unsat` on both).
#[test]
fn distinct_nary3_tester_shape_at_nonzero_one_index_is_unsat() {
    let dt = "(set-logic ALL)\n\
        (declare-datatypes ((DTs 0)) (((Ct (fld Int)) (Nt))))\n";
    let v = verdict(&format!(
        "{dt}(declare-const a DTs) (declare-const b DTs)\n\
         (assert (distinct a b (Ct (fld b))))\n\
         (assert (= b (Ct 7)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// CONTROL for the test above: identical shape, WITHOUT the forcing `b =
/// C(7)` assertion — genuinely satisfiable.
#[test]
fn distinct_nary3_tester_shape_control_without_forcing_stays_sat() {
    let dt = "(set-logic ALL)\n\
        (declare-datatypes ((DTs2 0)) (((Ct2 (fld Int)) (Nt2))))\n";
    let v = verdict(&format!(
        "{dt}(declare-const a DTs2) (declare-const b DTs2)\n\
         (assert (distinct a b (Ct2 (fld b))))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// NEGATIVE-CONTEXT N-ARY CONTROL — re-confirms, byte-for-byte, the EXACT
/// SAME guard scenario as `distinct_nary_negative_guard_prevents_spurious_
/// unsat` above (unaffected by this item: the new arm's own `&&
/// in_positive_context` guard structurally excludes the negative context,
/// so this MUST stay whatever it was before this change — `sat`, never a
/// fabricated `unsat`). Kept as its own explicitly-#424-scoped test (rather
/// than relying solely on the pre-existing test above) so a future reader
/// auditing #424's diff sees the negative-context invariant re-verified
/// right alongside the new positive-context tests it sits next to.
#[test]
fn distinct_nary_negative_context_still_unhandled_no_regression() {
    let v = verdict(&format!(
        "{D3}(declare-const a D3) (declare-const b D3) (declare-const c D3)\n\
         (assert (not (distinct a b c)))\n\
         (assert (distinct a b))\n\
         (assert (distinct a c))\n\
         (check-sat)\n"
    ));
    assert_eq!(
        v, "sat",
        "#424 item 2 only adds a POSITIVE-context N-ary arm; the negative-\
         context N-ary case must remain completely unhandled (safe, if \
         incomplete) — exactly as before this change"
    );
}
