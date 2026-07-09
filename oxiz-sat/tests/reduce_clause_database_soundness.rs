//! Regression (audit 2026-07-09): `reduce_clause_database` must detach a
//! deleted learned clause's watchers BEFORE freeing its id — the same lesson
//! `forget_learned_since` already applies to the incremental-probe path (see
//! `pop_binary_graph_soundness.rs`), but this ordinary CDCL clause-database
//! garbage-collection path (triggered by `clause_deletion_threshold`, used on
//! every plain `solve()`, not just incremental probing) never got the fix.
//!
//! `ClauseDatabase::remove` marks the slot `deleted` and pushes its id onto a
//! free list; the next `add_learned` pops that id and overwrites the slot,
//! clearing `deleted`. `propagate`'s only defense against a stale watcher is
//! `Some(c) if !c.deleted` — which the recycled slot defeats, since it is a
//! live (different) clause again. A watcher left behind for the OLD clause's
//! literals then aliases the NEW clause under an unrelated trigger literal,
//! and `propagate`'s two-watched-literal bookkeeping (which assumes the
//! triggering literal is one of the clause's first two) corrupts the watch
//! invariant for whichever clause now lives at that id — silently dropping it
//! from checking, which can manufacture a spurious `Sat`.
//!
//! Caught via the `pure_sat_runner` fuzz harness's own self-detected
//! `MODEL-INVALID` check on the pigeonhole family (`gen_php`), whose random
//! range (`2..6`) had never sampled large enough to reach the
//! `clause_deletion_threshold` conflict volume this needs — PHP(9) (10
//! pigeons, 9 holes) was the smallest manual instance that reproduced it,
//! deterministically, across every `ConfigPreset` (including ones with
//! inprocessing/CHB/LRB/chronological-backtracking all OFF, so the bug is in
//! the always-on core, not an optional feature). Ground truth (minisat,
//! cadical, z3 `-dimacs`) all agree PHP(9) is UNSAT; pre-fix, oxiz-sat
//! reported `Sat` with a model that failed its own re-check.
use oxiz_sat::{Solver, SolverConfig, SolverResult};

/// `p cnf` clauses for PHP(n): `n+1` pigeons into `n` holes (UNSAT).
/// `var(p, h) = p*n + h + 1` (1-indexed pigeon `p`, hole `h`).
fn php_clauses(n: i32) -> Vec<Vec<i32>> {
    let pigeons = n + 1;
    let var = |p: i32, h: i32| p * n + h + 1;
    let mut clauses = Vec::new();
    for p in 0..pigeons {
        clauses.push((0..n).map(|h| var(p, h)).collect());
    }
    for h in 0..n {
        for p1 in 0..pigeons {
            for p2 in (p1 + 1)..pigeons {
                clauses.push(vec![-var(p1, h), -var(p2, h)]);
            }
        }
    }
    clauses
}

#[test]
#[ignore] // PHP(9) is a genuinely hard CDCL instance; slow under a debug build.
fn php9_is_unsat_across_deletion_thresholds() {
    // A tight threshold forces MANY reduce_clause_database passes (hence many
    // id-recycling opportunities) well before the search converges — the
    // regime the bug needs. Every preset reproduced it pre-fix; a handful of
    // thresholds here stand in for that sweep without re-running all ten.
    for threshold in [100usize, 1000, 10_000] {
        let mut sat = Solver::with_config(SolverConfig {
            clause_deletion_threshold: threshold,
            ..SolverConfig::default()
        });
        for _ in 0..(10 * 9) {
            sat.new_var();
        }
        for clause in php_clauses(9) {
            sat.add_clause_dimacs(&clause);
        }
        assert_eq!(
            sat.solve(),
            SolverResult::Unsat,
            "PHP(9) (10 pigeons/9 holes) is UNSAT by the pigeonhole principle \
             (minisat/cadical/z3 agree) — a Sat verdict here means a deleted \
             learned clause's watchers survived into a recycled id and \
             silently stopped enforcing whichever clause now occupies it \
             (threshold={threshold})"
        );
    }
}
