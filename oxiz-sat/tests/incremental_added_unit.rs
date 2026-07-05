//! #404 phase 2 — an INCREMENTALLY added clause that is already unit under
//! the level-0 trail must bite.
//!
//! Watch events fire only on NEW falsifications, so a clause added AFTER
//! its false literals were assigned was never visited by propagation again:
//! silently inert, and the next solve could return a model that plainly
//! violated it. (The corpus decreases-check wall: the MBQI instance lemma's
//! guard Tseitin `[g₁, g₂, and]` was added after a Sat round with `g₁`,`g₂`
//! already pinned false at level 0 — `and` was never forced, the guarded
//! instance never fired, and the ground core stayed "Sat".) The fix is
//! two-part: `propagate_added_unit` (force the lone survivor at the root,
//! with the clause as its reason) and non-false-preferring watch selection
//! that keeps the `propagate()` front-position invariant (watched literals
//! ARE `lits[0]`/`lits[1]` — the first attempt watched arbitrary positions
//! and the hooks fuzz immediately caught the mis-propagation).

use oxiz_sat::{Lit, Solver, SolverResult};

/// 3+-literal shape (the decreases-check wall): `[a, b, c]` added when `a`,
/// `b` are already false at level 0 must force `c` — pinned by following up
/// with `[¬c]`, which must flip the whole set UNSAT (the inert-clause bug
/// kept it Sat).
#[test]
fn added_ternary_unit_under_trail_bites() {
    let mut solver = Solver::new();
    let a = solver.new_var();
    let b = solver.new_var();
    let c = solver.new_var();

    solver.add_clause([Lit::neg(a)]);
    solver.add_clause([Lit::neg(b)]);
    assert_eq!(solver.solve(), SolverResult::Sat);

    // Added post-solve: unit under the level-0 trail (a=F, b=F ⇒ c forced).
    solver.add_clause([Lit::pos(a), Lit::pos(b), Lit::pos(c)]);
    solver.add_clause([Lit::neg(c)]);
    assert_eq!(
        solver.solve(),
        SolverResult::Unsat,
        "the post-solve ternary must have forced c"
    );
}

/// Binary shape: `[a, b]` added when `a` is already false at level 0 must
/// force `b` (the old comment claimed "propagate via next solve()" — but
/// nothing re-visits an old falsification).
#[test]
fn added_binary_unit_under_trail_bites() {
    let mut solver = Solver::new();
    let a = solver.new_var();
    let b = solver.new_var();

    solver.add_clause([Lit::neg(a)]);
    assert_eq!(solver.solve(), SolverResult::Sat);

    solver.add_clause([Lit::pos(a), Lit::pos(b)]);
    solver.add_clause([Lit::neg(b)]);
    assert_eq!(
        solver.solve(),
        SolverResult::Unsat,
        "the post-solve binary must have forced b"
    );
}

/// The satisfiable control: the forced survivor is consistent with the rest
/// — the fix must not over-constrain into a spurious unsat.
#[test]
fn added_unit_under_trail_stays_sat_when_consistent() {
    let mut solver = Solver::new();
    let a = solver.new_var();
    let b = solver.new_var();
    let c = solver.new_var();

    solver.add_clause([Lit::neg(a)]);
    solver.add_clause([Lit::neg(b)]);
    assert_eq!(solver.solve(), SolverResult::Sat);

    solver.add_clause([Lit::pos(a), Lit::pos(b), Lit::pos(c)]);
    solver.add_clause([Lit::pos(c)]); // agrees with the forced value
    assert_eq!(solver.solve(), SolverResult::Sat);
}
