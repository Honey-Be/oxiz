//! The z3-differential soundness gate as a test (DESIGN.md §8).
//!
//! Runs `oxiz-nl2`'s [`check`](oxiz_nl2::check) against z3 over the seeded
//! failing shapes plus a deterministic random batch, and asserts the hard
//! invariant **`FALSE_UNSAT = 0` and `FALSE_SAT = 0`**. The Unknown-rate is
//! printed as completeness telemetry, never gated.
//!
//! * `cargo test` runs a **scoped** batch (seeded + 60 random) — fast.
//! * `cargo test -- --ignored` runs the **full** sweep (seeded + 1000 random) —
//!   the user's `!` gate, and the always-add-`--ignored` pass.
//!
//! If no `z3` binary is reachable, the test prints a skip notice and passes
//! (the harness wiring is still exercised by the unit tests).

use oxiz_nl2::corpus::{random_problems, seeded_shapes, Problem};
use oxiz_nl2::differential::{classify, run_z3, to_smtlib, z3_available, Tally};

fn run_gate(problems: &[Problem], label: &str) {
    if !z3_available() {
        eprintln!("[differential:{label}] z3 not available — skipping (wiring exercised by unit tests)");
        return;
    }
    let mut tally = Tally::default();
    let mut failures: Vec<String> = Vec::new();
    for p in problems {
        let script = to_smtlib(&p.atoms, p.sort);
        let Some(oracle) = run_z3(&script) else {
            // oracle hiccup on this one — skip, don't fail the soundness gate
            continue;
        };
        let ours = oxiz_nl2::check(&p.atoms);
        let class = classify(&ours, oracle);
        tally.record(class);
        use oxiz_nl2::differential::Class;
        if matches!(class, Class::FalseUnsat | Class::FalseSat) {
            failures.push(format!("  {} :: {:?}  (oracle={oracle:?})\n{script}", p.name, class));
        }
    }
    eprintln!(
        "[differential:{label}] total={} agree={} ours_unknown={} oracle_unknown={} \
         FALSE_UNSAT={} FALSE_SAT={}",
        tally.total(),
        tally.agree,
        tally.ours_unknown,
        tally.oracle_unknown,
        tally.false_unsat,
        tally.false_sat,
    );
    assert!(
        tally.is_sound(),
        "SOUNDNESS GATE FAILED ({label}): {} false-unsat, {} false-sat\n{}",
        tally.false_unsat,
        tally.false_sat,
        failures.join("\n"),
    );
}

#[test]
fn differential_scoped() {
    let mut problems = seeded_shapes();
    problems.extend(random_problems(0xA11CE, 60));
    run_gate(&problems, "scoped");
}

#[test]
#[ignore = "full sweep — run with -- --ignored; the user's ! gate"]
fn differential_full() {
    let mut problems = seeded_shapes();
    // a few seeds to vary the shape distribution
    for seed in [1u64, 7, 42, 0xBEEF, 0xC0FFEE] {
        problems.extend(random_problems(seed, 200));
    }
    run_gate(&problems, "full");
}
