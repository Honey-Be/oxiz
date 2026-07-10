//! Permanent (z3/cvc5-cross-checked) regressions for #423 item 2 —
//! nullary-constructor tester implies equality.
//!
//! `(is-c0 x) ∧ (is-c0 y) ∧ (distinct x y)` read spurious `sat`:
//! `collect_dt_constraints_v2`'s `DtTester` arm ONLY ever accumulated
//! constructor-name-tag strings (`constructor_testers`/`negative_testers` —
//! used elsewhere for pairwise-tester-conflict and `#399`'s exhaustiveness
//! checks) — it never derived an equality/disequality FACT from a tester,
//! regardless of arity.
//!
//! # Soundness argument: equivalence, not implication
//!
//! A NULLARY constructor `C` (zero fields) has exactly ONE possible value,
//! so `is-C(arg) ⟺ arg = C()` is a TRUE EQUIVALENCE — not merely an
//! implication in one direction. `C()` is the unique value of shape `C`, and
//! constructor injectivity/distinctness (already pervasively trusted by this
//! file's `#419`/`#422` machinery — e.g. `compute_dt_equality_closure`'s
//! same-constructor pairwise/field-decomposition derivations) makes
//! "not C-shaped" exactly "not equal to `C()`". This does NOT depend on
//! exhaustiveness (unlike `#399`'s nullary-ctor exhaustiveness check, a
//! DIFFERENT, unrelated mechanism in this same file) or any assumption
//! beyond what `compute_dt_equality_closure` already trusts:
//!   - POSITIVE `is-C(arg)` known true ⟹ `arg = C()` (an equality fact, fed
//!     into `var_ctor_term_eqs` — the SAME pipeline #422 item 3 built for
//!     direct ctor=ctor equalities).
//!   - NEGATIVE `¬is-C(arg)` known true ⟹ `arg ≠ C()` (a disequality fact,
//!     fed into `dt_diseq_pairs`).
//! A NON-nullary tester (arity > 0) contributes NOTHING: `is-C(arg)` for a
//! field-bearing `C` does not pin `arg` to any single ground value, so no
//! equality/disequality follows — see the arity>0 control below.
//!
//! # Cross-interner discipline
//!
//! The fix (`Solver::record_dt_nullary_tester_eq_fact` in `check_dt.rs`)
//! compares constructor NAMES as STRINGS, never raw `Spur`s across the TWO
//! DIFFERENT interners in play: `TermKind::DtTester`'s own `constructor`
//! field is a `Spur` from the TERM MANAGER's interner (confirmed: both
//! `TermManager::mk_dt_constructor` and `mk_dt_tester` intern their
//! constructor name via `self.intern_str`, i.e. the SAME interner — so
//! reusing that Spur directly as the key for the new
//! `TermManager::find_nullary_dt_constructor_term` cache lookup is exactly
//! correct), while `SortManager::datatype_constructors_of` (used to look up
//! the constructor's arity) resolves names through the SORT manager's OWN,
//! DIFFERENT interner and returns already-resolved `String`s. Comparing
//! those two Spur spaces directly would be the EXACT cross-interner mistake
//! that caused a real, documented `#399` bug — so the arity lookup compares
//! resolved `&str`s, never Spurs, across that boundary.
//!
//! Ground truths verified against both z3 4.16 and cvc5.

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
     (declare-datatypes ((D2n 0)) (((c0n) (c1n))))\n";

const DA: &str = "(set-logic ALL)\n\
     (declare-datatypes ((DAn 0)) (((c0an) (c1an (f0an Int))))) \n";

const PAIR_DT: &str = "(set-logic ALL)\n\
     (declare-datatypes ((D2p 0)) (((c0p) (c1p))))\n\
     (declare-datatypes ((PTypeN 0)) (((mkPn (f0n D2p) (f1n D2p)))))\n";

const LST_DT: &str = "(set-logic ALL)\n\
     (declare-datatypes ((D2o 0)) (((c0o) (c1o))))\n\
     (declare-datatypes ((LstN 0)) (((nilN) (lconsN (lhdN Int) (ltlN LstN)))))\n";

// ---------------------------------------------------------------------
// The item's own literal motivating repro + no-distinct sat control.
// ---------------------------------------------------------------------

/// `(is-c0n x) ∧ (is-c0n y) ∧ (distinct x y)`: both testers pin their
/// argument to the SAME unique nullary value, contradicting `distinct`.
/// Pre-#423: `sat` (the tester facts were invisible to any
/// equality/disequality collection). z3/cvc5: `unsat`.
#[test]
fn same_nullary_ctor_testers_with_distinct_is_unsat() {
    let v = verdict(&format!(
        "{D2}(declare-const x D2n) (declare-const y D2n)\n\
         (assert ((_ is c0n) x))\n\
         (assert ((_ is c0n) y))\n\
         (assert (distinct x y))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// SOUNDNESS CONTROL — the identical pair of testers WITHOUT `distinct`:
/// perfectly satisfiable (both `x` and `y` equal `c0n`). Confirms the new
/// derivation doesn't somehow fabricate a conflict on its own. z3/cvc5:
/// `sat`.
#[test]
fn same_nullary_ctor_testers_no_distinct_stays_sat() {
    let v = verdict(&format!(
        "{D2}(declare-const x D2n) (declare-const y D2n)\n\
         (assert ((_ is c0n) x))\n\
         (assert ((_ is c0n) y))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// Two DIFFERENT nullary testers combined with `(= x y)` — `is-c0n(x)` gives
/// `x=c0n()`, `is-c1n(y)` gives `y=c1n()`; `x=y` would force `c0n()=c1n()`,
/// impossible by constructor distinctness. z3/cvc5: `unsat`. (This
/// particular shape also composes with the PRE-EXISTING
/// constructor-tester/equality cross-checks in `check_dt_constraints`, but
/// is included here as a direct positive-context sanity check on the new
/// derivation specifically, independent of `distinct`.)
#[test]
fn different_nullary_ctor_testers_with_eq_is_unsat() {
    let v = verdict(&format!(
        "{D2}(declare-const x D2n) (declare-const y D2n)\n\
         (assert ((_ is c0n) x))\n\
         (assert ((_ is c1n) y))\n\
         (assert (= x y))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

// ---------------------------------------------------------------------
// Composition with #419's injectivity machinery (NOT caught by the
// pre-existing pairwise tester-conflict checks, which only correlate
// through DIRECT var-var equalities, not injectivity-DERIVED ones).
// ---------------------------------------------------------------------

/// `p=mkPn(x,y) ∧ p=mkPn(x,z) ∧ is-c0p(y) ∧ ¬is-c0p(z)`: injectivity
/// (already-landed #419/#422 field-decomposition machinery) derives `y=z`
/// from the two `mkPn` bindings sharing `p` and `x`; the new positive-tester
/// derivation gives `y=c0p()`; the new negative-tester derivation gives
/// `z≠c0p()`. Union-find then finds `y` and `z` share a root (both equal
/// `c0p()`) while `z≠c0p()` is a known diseq pair — a conflict genuinely
/// NEW to item 2 (not reachable via the pre-existing direct-tester-conflict
/// cross-checks, since `y`/`z` are never directly compared — only
/// TRANSITIVELY, through injectivity). z3/cvc5: `unsat`.
#[test]
fn injectivity_composition_forces_conflict_is_unsat() {
    let v = verdict(&format!(
        "{PAIR_DT}(declare-const p PTypeN)\n\
         (declare-const x D2p) (declare-const y D2p) (declare-const z D2p)\n\
         (assert (= p (mkPn x y)))\n\
         (assert (= p (mkPn x z)))\n\
         (assert ((_ is c0p) y))\n\
         (assert (not ((_ is c0p) z)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// SOUNDNESS CONTROL for the composition repro above: identical shape, but
/// BOTH testers are POSITIVE (`is-c0p(y)` and `is-c0p(z)`, not negated) —
/// injectivity still forces `y=z`, and now BOTH resolve to `c0p()`, which is
/// perfectly consistent (no conflict). Must stay `sat`.
#[test]
fn injectivity_composition_no_conflict_stays_sat() {
    let v = verdict(&format!(
        "{PAIR_DT}(declare-const p PTypeN)\n\
         (declare-const x D2p) (declare-const y D2p) (declare-const z D2p)\n\
         (assert (= p (mkPn x y)))\n\
         (assert (= p (mkPn x z)))\n\
         (assert ((_ is c0p) y))\n\
         (assert ((_ is c0p) z))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

// ---------------------------------------------------------------------
// Arity>0 control — the single most important soundness guard for this
// item: a NON-nullary tester must NEVER be treated as pinning its argument
// to a single value.
// ---------------------------------------------------------------------

/// `is-c1an(x) ∧ is-c1an(y) ∧ distinct(x,y)` where `c1an` carries an Int
/// field — `is-c1an` does NOT pin its argument to one ground value (there
/// are infinitely many `c1an(_)` values), so `x` and `y` can be
/// `c1an(0)`/`c1an(1)` respectively. MUST stay `sat` — confirms the arity
/// check in `record_dt_nullary_tester_eq_fact` correctly skips non-nullary
/// constructors instead of (unsoundly) treating every tester as an
/// equivalence. z3/cvc5: `sat`.
#[test]
fn arity_gt_zero_tester_with_distinct_stays_sat() {
    let v = verdict(&format!(
        "{DA}(declare-const x DAn) (declare-const y DAn)\n\
         (assert ((_ is c1an) x))\n\
         (assert ((_ is c1an) y))\n\
         (assert (distinct x y))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

// ---------------------------------------------------------------------
// OR-wrapped coverage — confirms the OR-branch case-split evaluator
// (`dt_items_force_conflict`) benefits automatically, via the shared
// `collect_dt_constraints_v2` leaf delegation (no separate wiring needed).
// ---------------------------------------------------------------------

/// The motivating repro's shape, OR-WRAPPED alongside an ordinary
/// already-supported flat cycle as the sibling branch. Neither branch is
/// unconditionally forcing on its own syntax outside this context, but BOTH
/// are conflict-forced, so the whole `or` is `unsat`. Pre-#423: `sat`
/// (branch 1's tester-derived conflict was invisible to the OR-branch
/// evaluator). z3/cvc5: `unsat`.
#[test]
fn or_branch_nullary_tester_conflict_is_unsat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const x D2o) (declare-const y D2o)\n\
         (declare-const w LstN) (declare-const wi Int)\n\
         (assert (or\n\
           (and ((_ is c0o) x) ((_ is c0o) y) (distinct x y))\n\
           (= w (lconsN wi w))\n\
         ))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// SAT-CONTROL sibling of the OR-wrapped test above: the SAME
/// always-conflicting first branch, but the second branch is an ORDINARY
/// satisfiable fact instead of another forced conflict — NOT every branch
/// is conflict-forced, so the whole `or` must stay `sat`.
#[test]
fn or_branch_nullary_tester_conflict_other_branch_not_stays_sat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const x D2o) (declare-const y D2o)\n\
         (declare-const w LstN) (declare-const wi Int)\n\
         (assert (or\n\
           (and ((_ is c0o) x) ((_ is c0o) y) (distinct x y))\n\
           (= w (lconsN wi nilN))\n\
         ))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

// ---------------------------------------------------------------------
// Push/pop isolation — `check_dt_constraints`/`dt_items_force_conflict` are
// stateless/rebuilt-per-call from `self.assertions`, so this is expected to
// already hold, but verified explicitly (mirroring
// `dt_distinct_regression.rs::distinct_conflict_does_not_leak_across_pop`).
// ---------------------------------------------------------------------

/// Assert the conflicting tester+distinct combination inside a `push`,
/// confirm `unsat`, `pop`, then assert a DIFFERENT, non-conflicting fact and
/// confirm `sat` — the popped scope's tester-derived conflict must not
/// leak into the later, unrelated scope.
#[test]
fn nullary_tester_conflict_does_not_leak_across_pop() {
    let v: Vec<String> = {
        let mut ctx = Context::new();
        ctx.set_timeout_ms(5000);
        let script = format!(
            "{D2}(declare-const x D2n) (declare-const y D2n)\n\
             (push 1)\n\
             (assert ((_ is c0n) x))\n\
             (assert ((_ is c0n) y))\n\
             (assert (distinct x y))\n\
             (check-sat)\n\
             (pop 1)\n\
             (assert ((_ is c0n) x))\n\
             (assert ((_ is c1n) y))\n\
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
        "the popped scope's tester-derived conflict must not survive to \
         constrain the later, unrelated scope"
    );
}
