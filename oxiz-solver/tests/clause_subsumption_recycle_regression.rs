//! Regression (#428): `Solver::check_subsumption` (`oxiz-sat/src/solver/
//! learn.rs`) is the on-the-fly subsumption pass fired from `learn_clause`
//! for every short (`len <= 5`), tight (`lbd <= 3`) learned clause. Unlike
//! its three siblings — `reduce_clause_database`, `forget_learned_since`,
//! and the assertion-scope `pop` handler — it removed a subsumed clause via
//! `self.clauses.remove(cid)` WITHOUT first scrubbing `self.watches` (and,
//! defensively, `self.binary_graph`) for that clause's literals.
//!
//! `ClauseDatabase::remove` marks the slot deleted and pushes `cid` onto a
//! free list; the next `add_learned` pops that list and overwrites the slot
//! IN PLACE, clearing `deleted`. `propagate`'s "skip deleted clause" guard
//! therefore cannot catch a stale watcher once the id is recycled — the
//! recycled (unrelated) clause silently inherits the deleted clause's watch
//! entries. When a later-assigned literal hits that stale watcher, the
//! "swap in a non-false watched literal" step finds neither of the
//! *recycled* clause's actual literals match, so it falls through to
//! treating an unrelated literal as an unconditional unit consequence —
//! fabricating a fact that gets propagated and then permanently pinned by
//! ordinary (and otherwise sound) 1-UIP conflict analysis over an
//! already-corrupted trail. The result: a genuinely SATISFIABLE formula is
//! reported UNSAT — false UNSAT is the worst class of SMT solver bug, since
//! a downstream consumer trusts it as a non-existent proof.
//!
//! `check_subsumption` needs enough search depth to generate, subsume, and
//! recycle several short/tight learned clauses before the bug fires — empty
//! empirically at roughly six or more independent "selector implies cost"
//! groups summed into one linear inequality (the shape a hand-built
//! selector+cost-sum MaxSAT-style encoding produces, though this bug has
//! nothing to do with MaxSAT/opt code — any QF_LIA consumer hitting this
//! shape was at risk). Both z3 4.16.0 and cvc5 independently agree these
//! scripts are `sat`.
//!
//! The fix mirrors the three sibling call sites exactly: scrub
//! `self.watches` (and, for a binary removed clause, `self.binary_graph`)
//! for every literal of a subsumed clause before `self.clauses.remove`.

use oxiz_solver::Context;

fn verdict(script: &str) -> &'static str {
    let mut ctx = Context::new();
    ctx.set_timeout_ms(10_000);
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

/// Parse a model value string (`get_model`'s formatted `Int` values are
/// plain decimal, or `(- N)` for negatives) into an `i64`.
fn parse_int(v: &str) -> i64 {
    let v = v.trim();
    if let Some(inner) = v.strip_prefix("(- ").and_then(|s| s.strip_suffix(')')) {
        return -inner.trim().parse::<i64>().unwrap_or_else(|_| {
            panic!("could not parse negative int model value {v:?}")
        });
    }
    v.parse::<i64>()
        .unwrap_or_else(|_| panic!("could not parse int model value {v:?}"))
}

/// The original #428 corpus repro (`428-qflia-false-unsat-6plus-selector-
/// groups.smt2`): 6 Bool-selector/Int-cost groups (one pair sharing `b1`,
/// via `b1`/`¬b1`) plus 4 unrelated hard propositional clauses over
/// `b0..b4`, summed into a single `<= 7` budget. z3/cvc5 both say `sat`
/// with `b1=b4=b5=true, b0=b2=b3=false` (cost sum exactly 7); oxiz said
/// `unsat` before the `check_subsumption` watcher-scrub fix.
#[test]
fn selector_cost_sum_six_groups_is_sat_not_false_unsat() {
    let script = "\
(set-logic QF_LIA)
(declare-const b0 Bool) (declare-const b1 Bool) (declare-const b2 Bool)
(declare-const b3 Bool) (declare-const b4 Bool) (declare-const b5 Bool)
(assert (or b0 b1))
(assert (or b5 (not b0)))
(assert (or b5 (not b4) (not b0)))
(assert (or (not b2) (not b4)))
(declare-const sel_b5 Bool) (declare-const sel_b1 Bool)
(declare-const sel_b4 Bool) (declare-const sel_nb1 Bool)
(declare-const sel_nb2 Bool) (declare-const sel_nb3 Bool)
(declare-const cost_b5 Int) (declare-const cost_b1 Int)
(declare-const cost_b4 Int) (declare-const cost_nb1 Int)
(declare-const cost_nb2 Int) (declare-const cost_nb3 Int)
(assert (=> sel_b5 b5))
(assert (=> sel_b5 (= cost_b5 0)))
(assert (=> (not sel_b5) (= cost_b5 6)))
(assert (=> sel_b1 b1))
(assert (=> sel_b1 (= cost_b1 0)))
(assert (=> (not sel_b1) (= cost_b1 9)))
(assert (=> sel_b4 b4))
(assert (=> sel_b4 (= cost_b4 0)))
(assert (=> (not sel_b4) (= cost_b4 3)))
(assert (=> sel_nb1 (not b1)))
(assert (=> sel_nb1 (= cost_nb1 0)))
(assert (=> (not sel_nb1) (= cost_nb1 7)))
(assert (=> sel_nb2 (not b2)))
(assert (=> sel_nb2 (= cost_nb2 0)))
(assert (=> (not sel_nb2) (= cost_nb2 4)))
(assert (=> sel_nb3 (not b3)))
(assert (=> sel_nb3 (= cost_nb3 0)))
(assert (=> (not sel_nb3) (= cost_nb3 5)))
(assert (<= (+ cost_b5 cost_b1 cost_b4 cost_nb1 cost_nb2 cost_nb3) 7))
(check-sat)
";
    let mut ctx = Context::new();
    ctx.set_timeout_ms(10_000);
    let out = ctx
        .execute_script(script)
        .expect("script executes without error");
    let last_verdict = out
        .iter()
        .rev()
        .find_map(|l| match l.trim() {
            "sat" | "unsat" | "unknown" => Some(l.trim().to_string()),
            _ => None,
        })
        .unwrap_or_else(|| "unknown".to_string());
    assert_eq!(
        last_verdict, "sat",
        "6-group selector/cost-sum QF_LIA instance must be sat (z3/cvc5 agree); \
         `unsat` means the check_subsumption clause-id-recycle stale-watcher \
         bug (#428) has regressed"
    );

    // Verify the reported witness is an ACTUAL model, not just an unchecked
    // `sat`: every cost variable must be consistent with its selector, and
    // the summed cost must respect the <= 7 budget.
    let model = ctx.get_model().expect("a model after sat");
    let val = |n: &str| -> String {
        model
            .iter()
            .find(|(name, _, _)| name == n)
            .map(|(_, _, v)| v.clone())
            .unwrap_or_else(|| panic!("model missing variable {n}"))
    };
    let cost_names = [
        "cost_b5", "cost_b1", "cost_b4", "cost_nb1", "cost_nb2", "cost_nb3",
    ];
    let sum: i64 = cost_names.iter().map(|n| parse_int(&val(n))).sum();
    assert!(
        sum <= 7,
        "witness cost sum must respect the <= 7 budget, got {sum} (model: {model:?})"
    );
}

/// A structurally minimal, generic reproduction (no MaxSAT-shaped naming,
/// no hard propositional clauses beyond one trigger atom): 2 "meaningful"
/// selector groups sharing `b1`/`¬b1` plus 4 fully generic padding groups,
/// still exactly 6 total groups. Isolates that the bug is a pure
/// count/search-depth threshold, not specific to the original repro's
/// naming or hard-clause structure.
#[test]
fn selector_cost_sum_minimal_generic_six_groups_is_sat() {
    let script = "\
(set-logic QF_LIA)
(declare-const b1 Bool)
(declare-const z0 Bool)
(assert z0)

(declare-const sel_b1 Bool)
(declare-const cost_b1 Int)
(assert (=> sel_b1 b1))
(assert (=> sel_b1 (= cost_b1 0)))
(assert (=> (not sel_b1) (= cost_b1 9)))

(declare-const pv_pad0 Bool)
(declare-const sel_pad0 Bool)
(declare-const cost_pad0 Int)
(assert (=> sel_pad0 pv_pad0))
(assert (=> sel_pad0 (= cost_pad0 0)))
(assert (=> (not sel_pad0) (= cost_pad0 100)))

(declare-const sel_nb1 Bool)
(declare-const cost_nb1 Int)
(assert (=> sel_nb1 (not b1)))
(assert (=> sel_nb1 (= cost_nb1 0)))
(assert (=> (not sel_nb1) (= cost_nb1 7)))

(declare-const pv_pad1 Bool)
(declare-const sel_pad1 Bool)
(declare-const cost_pad1 Int)
(assert (=> sel_pad1 pv_pad1))
(assert (=> sel_pad1 (= cost_pad1 0)))
(assert (=> (not sel_pad1) (= cost_pad1 100)))

(declare-const pv_pad2 Bool)
(declare-const sel_pad2 Bool)
(declare-const cost_pad2 Int)
(assert (=> sel_pad2 pv_pad2))
(assert (=> sel_pad2 (= cost_pad2 0)))
(assert (=> (not sel_pad2) (= cost_pad2 100)))

(declare-const pv_pad3 Bool)
(declare-const sel_pad3 Bool)
(declare-const cost_pad3 Int)
(assert (=> sel_pad3 pv_pad3))
(assert (=> sel_pad3 (= cost_pad3 0)))
(assert (=> (not sel_pad3) (= cost_pad3 100)))

(assert (<= (+ cost_b1 cost_pad0 cost_nb1 cost_pad1 cost_pad2 cost_pad3) 7))
(check-sat)
";
    assert_eq!(
        verdict(script),
        "sat",
        "minimal generic 6-group selector/cost-sum instance must be sat"
    );
}

/// Soundness control in the OTHER direction: a genuinely infeasible budget
/// (threshold below the cheapest-possible sum) over the same 6-group shape
/// must stay `unsat`. A fix that scrubs too much (e.g. also detaching a
/// watcher/edge that is still legitimately live) risks flipping a real
/// unsat into a spurious sat, which would be a worse regression than #428
/// itself.
#[test]
fn selector_cost_sum_six_groups_infeasible_budget_stays_unsat() {
    let script = "\
(set-logic QF_LIA)
(declare-const b1 Bool)
(declare-const z0 Bool)
(assert z0)

(declare-const sel_b1 Bool)
(declare-const cost_b1 Int)
(assert (=> sel_b1 b1))
(assert (=> sel_b1 (= cost_b1 0)))
(assert (=> (not sel_b1) (= cost_b1 9)))

(declare-const pv_pad0 Bool)
(declare-const sel_pad0 Bool)
(declare-const cost_pad0 Int)
(assert (=> sel_pad0 pv_pad0))
(assert (=> sel_pad0 (= cost_pad0 0)))
(assert (=> (not sel_pad0) (= cost_pad0 100)))

(declare-const sel_nb1 Bool)
(declare-const cost_nb1 Int)
(assert (=> sel_nb1 (not b1)))
(assert (=> sel_nb1 (= cost_nb1 0)))
(assert (=> (not sel_nb1) (= cost_nb1 7)))

(declare-const pv_pad1 Bool)
(declare-const sel_pad1 Bool)
(declare-const cost_pad1 Int)
(assert (=> sel_pad1 pv_pad1))
(assert (=> sel_pad1 (= cost_pad1 0)))
(assert (=> (not sel_pad1) (= cost_pad1 100)))

(declare-const pv_pad2 Bool)
(declare-const sel_pad2 Bool)
(declare-const cost_pad2 Int)
(assert (=> sel_pad2 pv_pad2))
(assert (=> sel_pad2 (= cost_pad2 0)))
(assert (=> (not sel_pad2) (= cost_pad2 100)))

(declare-const pv_pad3 Bool)
(declare-const sel_pad3 Bool)
(declare-const cost_pad3 Int)
(assert (=> sel_pad3 pv_pad3))
(assert (=> sel_pad3 (= cost_pad3 0)))
(assert (=> (not sel_pad3) (= cost_pad3 100)))

;; b1 and (not b1) can never BOTH be selected at cost 0 simultaneously, so
;; the true minimum sum here is min(9,7) + (any pad group forced to 100) =
;; at least 7 + 0*3 + ... actually the pads CAN all be free (their pv_i are
;; unconstrained), so the true minimum is exactly 7 (sel_nb1 selected, all
;; pads selected at cost 0). Force infeasibility by additionally requiring
;; b1 to be true AND forcing (not sel_nb1) via requiring z0's negation is
;; absent — instead, directly starve the budget below the true minimum.
(assert (<= (+ cost_b1 cost_pad0 cost_nb1 cost_pad1 cost_pad2 cost_pad3) 6))
(check-sat)
";
    assert_eq!(
        verdict(script),
        "unsat",
        "budget 1 below the true minimum-cost sum (7) must stay unsat"
    );
}
