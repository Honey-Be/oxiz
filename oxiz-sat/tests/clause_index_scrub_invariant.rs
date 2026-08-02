//! Class-level regression for the **clause-id-recycle / stale-index** bug
//! family — the one that produced four independent soundness fixes
//! (`reduce_clause_database`, `forget_learned_since`, the assertion-scope `pop`
//! handler, and `check_subsumption` / issue #428), each a one-off at a single
//! call site.
//!
//! The mechanism, once: `ClauseDatabase::remove` does not destroy a clause. It
//! marks the slot `deleted` and pushes the id onto a free list, and the next
//! `add` pops that id and overwrites the slot **in place, clearing `deleted`**.
//! So every structure keyed on a `ClauseId` — the watch lists, the binary
//! implication graph — silently re-points at an unrelated clause the moment its
//! own clause is removed. `propagate`'s "skip deleted clause" guard cannot see
//! it (the slot is live again) and the binary graph has no guard at all.
//!
//! The structural answer lives in the library, not here:
//! `ClauseDatabase::remove` now **requires** a `ClauseIndexScrub` argument and
//! performs the scrub itself, so "free an id without detaching it" is no longer
//! expressible (there is a `compile_fail` doctest on the trait pinning that),
//! and `propagate` carries O(1) `debug_assert`s that catch a corrupt entry at
//! its first use. The in-crate tests in
//! `solver::learn::clause_index_scrub_regressions` pin those two devices
//! directly, on the exact shapes the four bugs had.
//!
//! What *this* file adds is the outside-in half: end-to-end verdicts checked
//! against brute-force ground truth, under configurations that maximise
//! id-recycling churn (a small `clause_deletion_threshold` forces frequent
//! database reduction, which frees ids that the next learned clause reclaims).
//! A leaked index entry shows up here as a wrong verdict or an invalid model,
//! independent of whether anyone remembered to write an assertion.
//!
//! ## Why the thresholds here are 64+ and not 1
//!
//! Thresholds ≤ 8 expose a **separate, pre-existing** unsoundness in this crate
//! (both false-`Sat` and false-`Unsat`, reproducible on `822e1f1` with the
//! whole `ClauseIndexScrub` change reverted, and with the propagation
//! backstops silent — so it is *not* this bug class). Pinning it here would
//! make this file red for an unrelated reason; it is reported separately.
//! Thresholds 64 and above were clean over a 400-instance × 7-threshold sweep,
//! and still trigger clause-database reduction many times per solve on these
//! instances, which is all this file needs.

use oxiz_sat::{LBool, Lit, Solver, SolverConfig, SolverResult, Var};

/// A tiny xorshift PRNG, so the corpus is deterministic and dependency-free.
struct Rng(u64);

impl Rng {
    fn next_u32(&mut self) -> u32 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        (x >> 32) as u32
    }

    fn below(&mut self, n: u32) -> u32 {
        self.next_u32() % n
    }
}

/// Ground truth by exhaustive enumeration. Only used for small `num_vars`.
fn brute_force_sat(num_vars: usize, clauses: &[Vec<Lit>]) -> bool {
    (0u32..(1u32 << num_vars)).any(|bits| {
        clauses.iter().all(|clause| {
            clause
                .iter()
                .any(|lit| ((bits >> lit.var().index()) & 1 == 1) == lit.is_pos())
        })
    })
}

/// Does `model` actually satisfy every clause?
fn model_satisfies(model: &[LBool], clauses: &[Vec<Lit>]) -> bool {
    clauses.iter().all(|clause| {
        clause.iter().any(|lit| {
            let value = model[lit.var().index()];
            if lit.is_pos() {
                value == LBool::True
            } else {
                value == LBool::False
            }
        })
    })
}

fn random_3sat(rng: &mut Rng, num_vars: usize, num_clauses: usize) -> Vec<Vec<Lit>> {
    let mut clauses = Vec::with_capacity(num_clauses);
    for _ in 0..num_clauses {
        let mut clause: Vec<Lit> = Vec::with_capacity(3);
        while clause.len() < 3 {
            let var = Var::new(rng.below(num_vars as u32));
            if clause.iter().any(|l| l.var() == var) {
                continue;
            }
            clause.push(if rng.below(2) == 0 {
                Lit::pos(var)
            } else {
                Lit::neg(var)
            });
        }
        clauses.push(clause);
    }
    clauses
}

/// Churn config: reduce the clause database often enough that learned-clause
/// ids are freed and immediately reclaimed — the regime all four historical
/// bugs needed. See the module header for why this floor is 64.
fn churn_config(threshold: usize) -> SolverConfig {
    SolverConfig {
        clause_deletion_threshold: threshold,
        ..SolverConfig::default()
    }
}

fn expected_result(sat: bool) -> SolverResult {
    if sat {
        SolverResult::Sat
    } else {
        SolverResult::Unsat
    }
}

#[test]
fn random_3sat_verdicts_match_brute_force_under_id_recycling_churn() {
    let mut rng = Rng(0x5EED_1234_ABCD_0001);
    let mut sat_count = 0usize;
    let mut unsat_count = 0usize;

    for case in 0..300 {
        // 8..=14 vars: 2^14 brute force is cheap, and at ratio ~4.3 (the phase
        // transition) both verdicts appear and the search learns enough to
        // trigger reduction repeatedly.
        let num_vars = 8 + (case % 7);
        let num_clauses = (num_vars as f64 * 4.3) as usize + (case % 5);
        let clauses = random_3sat(&mut rng, num_vars, num_clauses);
        let expected = brute_force_sat(num_vars, &clauses);

        for threshold in [64usize, 256] {
            let mut solver = Solver::with_config(churn_config(threshold));
            for _ in 0..num_vars {
                solver.new_var();
            }
            for clause in &clauses {
                solver.add_clause(clause.iter().copied());
            }

            let verdict = solver.solve();
            assert_eq!(
                verdict,
                expected_result(expected),
                "case {case} (threshold {threshold}): wrong verdict on a {num_vars}-var \
                 instance. A stale watcher from a recycled clause id silently stops enforcing \
                 whichever clause now occupies that id (→ false Sat); a leaked binary \
                 implication edge fabricates conflicts (→ false Unsat)"
            );

            if verdict == SolverResult::Sat {
                assert!(
                    model_satisfies(solver.model(), &clauses),
                    "case {case} (threshold {threshold}): the reported model does not satisfy \
                     the formula — the classic symptom of a clause that stopped being watched"
                );
            }
        }

        if expected {
            sat_count += 1;
        } else {
            unsat_count += 1;
        }
    }

    // Guard against the corpus degenerating: the two verdicts fail in
    // *opposite* directions for this bug class (a dropped clause manufactures
    // Sat, a leaked edge manufactures Unsat), so both must be represented for
    // this test to mean anything.
    assert!(
        sat_count >= 30 && unsat_count >= 30,
        "corpus is lopsided ({sat_count} sat / {unsat_count} unsat); it must cover both \
         directions of the bug class"
    );
}

#[test]
fn push_pop_recycle_cycles_stay_sound() {
    // `pop` frees every clause id recorded in the scope, and the next
    // `add_clause` reclaims them — the tightest recycling loop in the solver,
    // and the shape of both the `pop`-handler bug and `forget_learned_since`.
    let mut rng = Rng(0xC0FF_EE00_1234_5678);

    for case in 0..120 {
        let num_vars = 8 + (case % 5);
        let base = random_3sat(&mut rng, num_vars, num_vars * 2);
        let scoped = random_3sat(&mut rng, num_vars, num_vars * 3);

        let mut solver = Solver::with_config(churn_config(64));
        for _ in 0..num_vars {
            solver.new_var();
        }
        for clause in &base {
            solver.add_clause(clause.iter().copied());
        }

        // Solve inside a scope, then drop it. Everything learned under the
        // scope — including binary lemmas, which live in the guard-less binary
        // implication graph — must leave no trace behind.
        let committed = solver.trail_size();
        for _ in 0..3 {
            solver.push();
            for clause in &scoped {
                solver.add_clause(clause.iter().copied());
            }
            let _ = solver.solve();
            solver.pop();
            solver.restore_to_trail_size(committed);
        }

        let expected = brute_force_sat(num_vars, &base);
        let verdict = solver.solve();
        assert_eq!(
            verdict,
            expected_result(expected),
            "case {case}: after three push/solve/pop cycles the solver must answer the BASE \
             formula. A clause id freed by `pop` and reclaimed by a later add carries the \
             popped scope's watchers/implication edges with it unless the free is scrubbed"
        );

        if verdict == SolverResult::Sat {
            assert!(
                model_satisfies(solver.model(), &base),
                "case {case}: model does not satisfy the base formula"
            );
        }
    }
}

#[test]
fn incremental_probe_sequence_reuses_ids_soundly() {
    // The `BvSolver::check()` protocol: snapshot the committed trail prefix,
    // solve, roll back, assert more, solve again. Each round drops and
    // re-derives learned clauses, recycling ids every time. Verdicts are
    // checked against brute force over the prefix asserted so far.
    let mut rng = Rng(0x1234_5678_9ABC_DEF0);

    for case in 0..120 {
        let num_vars = 8 + (case % 5);
        let clauses = random_3sat(&mut rng, num_vars, num_vars * 5);

        let mut solver = Solver::with_config(churn_config(64));
        for _ in 0..num_vars {
            solver.new_var();
        }

        let mut asserted: Vec<Vec<Lit>> = Vec::new();
        for chunk in clauses.chunks(num_vars) {
            let committed = solver.trail_size();
            for clause in chunk {
                solver.add_clause(clause.iter().copied());
                asserted.push(clause.clone());
            }

            let expected = brute_force_sat(num_vars, &asserted);
            let verdict = solver.solve();
            assert_eq!(
                verdict,
                expected_result(expected),
                "case {case}: wrong verdict after {} asserted clauses",
                asserted.len()
            );

            if verdict == SolverResult::Sat {
                assert!(
                    model_satisfies(solver.model(), &asserted),
                    "case {case}: model does not satisfy the asserted prefix"
                );
            } else {
                // Once UNSAT, later chunks cannot change that.
                break;
            }

            // Discard this probe's model-specific assignments before the next,
            // augmented probe — `solve()` deliberately does not reset the
            // persisted trail on entry.
            solver.restore_to_trail_size(committed);
        }
    }
}
