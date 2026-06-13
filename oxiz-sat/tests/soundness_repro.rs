//! Soundness regression repro for the pure oxiz-sat CDCL engine.
//!
//! Found by differential fuzzing (`tests/sat_diff_fuzz_pure.py`) against cadical,
//! z3, and cryptominisat5. The default `SolverConfig` (`random_polarity_prob =
//! 0.02`) drives `Solver::solve()` to report UNSAT on a SATISFIABLE instance —
//! a spurious-UNSAT in the 1-UIP conflict-analysis path (`solver/conflict.rs`).
//!
//! Minimal reproducer (6 vars, 7 clauses); the UNIQUE model is
//!   v1=F v2=F v3=F v4=T v5=T v6=T
//! which all four reference solvers confirm.
//!
//! STATUS: FIXED. The 1-UIP defect was corrected in `cc3872c` (process every
//! reason literal; never assume the implied literal sits at `lits[0]`). This is
//! now a regular `#[test]` (no longer `#[ignore]`d) and PASSES, guarding against
//! regression of the spurious-UNSAT. Run with
//!   cargo test -p oxiz-sat --test soundness_repro
use oxiz_sat::{Lit, Solver, SolverResult};

fn lit(d: i32) -> Lit {
    Lit::from_dimacs(d)
}

/// The minimal spurious-UNSAT instance, solved with the *default* config
/// (`Solver::new()`), which is what every library consumer gets.
#[test]
fn minimal_spurious_unsat_default_config() {
    // p cnf 6 7
    // 6 -5 / -4 -3 / 2 -1 / 2 4 / 3 5 / 4 -2 / -6 -2
    let clauses: &[&[i32]] = &[
        &[6, -5],
        &[-4, -3],
        &[2, -1],
        &[2, 4],
        &[3, 5],
        &[4, -2],
        &[-6, -2],
    ];

    let mut solver = Solver::new(); // default config, random_polarity_prob = 0.02
    solver.ensure_vars(6);
    for c in clauses {
        solver.add_clause(c.iter().map(|&d| lit(d)));
    }

    let result = solver.solve();

    // The instance is SAT (unique model v4=v5=v6=T, v1=v2=v3=F), confirmed by
    // cadical + z3 + cryptominisat5 + minisat. The engine must NOT say Unsat.
    assert_ne!(
        result,
        SolverResult::Unsat,
        "UNSOUND: pure SAT engine reported UNSAT for a satisfiable instance"
    );

    // Stronger: if Sat, the returned model must satisfy every clause.
    if result == SolverResult::Sat {
        use oxiz_sat::{LBool, Var};
        for c in clauses {
            let any_true = c.iter().any(|&d| {
                let v = Var::new((d.unsigned_abs() - 1) as u32);
                match solver.model_value(v) {
                    LBool::True => d > 0,
                    LBool::False => d < 0,
                    LBool::Undef => false,
                }
            });
            assert!(any_true, "model fails clause {c:?}");
        }
    }
}
