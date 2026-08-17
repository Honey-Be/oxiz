// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors

//! A `pop()` must not discard a contradiction established BEFORE the matching
//! `push()`.
//!
//! `Solver::pop` used to end with `self.trivially_unsat = false`, justified by
//! "we've removed problematic clauses" — true only for clauses the popped scope
//! introduced. The flag is also set by contradictions that predate the push, and
//! for one of them it is the ONLY record: `add_clause`'s `level == 0` arm sets
//! it and returns WITHOUT storing a clause when a unit conflicts with an
//! existing level-0 assignment. Clearing it therefore left nothing for
//! propagation to re-derive.
//!
//! Witness, at the SMT-LIB level: `(assert p) (assert (not p)) (push 1)
//! (pop 1) (check-sat)` answered `sat` while `(get-assertions)` still listed
//! both, and z3 and cvc5 both answer `unsat`. A BARE matched push/pop, nothing
//! inside it, discarded a propositional contradiction.
//!
//! Seventh member of the pop-scrub family (assert-time state with no
//! scope-aware undo), after the four clause-id-recycle recurrences, the EUF
//! use-list, and `term_to_node`.

use oxiz_sat::{Lit, Solver, SolverResult, Var};

fn p() -> Lit {
    Lit::pos(Var::new(0))
}

/// Contradiction BEFORE the push: the pop must preserve it.
#[test]
fn pop_preserves_a_contradiction_established_before_the_push() {
    let mut s = Solver::new();
    s.new_var();
    assert!(s.add_clause([p()]));
    // Conflicts with the level-0 assignment of `p`: sets the flag, stores no clause.
    assert!(!s.add_clause([p().negate()]));
    assert_eq!(s.solve(), SolverResult::Unsat, "before any push");

    s.push();
    s.pop();
    assert_eq!(
        s.solve(),
        SolverResult::Unsat,
        "a bare matched push/pop must not resurrect an unsatisfiable formula"
    );
}

/// The same, with the scope non-empty — the clause added inside is dropped by
/// the pop, but the OUTER contradiction still stands.
#[test]
fn pop_preserves_it_across_a_non_empty_scope() {
    let mut s = Solver::new();
    s.new_var();
    s.new_var();
    let q = Lit::pos(Var::new(1));
    assert!(s.add_clause([p()]));
    assert!(!s.add_clause([p().negate()]));

    s.push();
    let _ = s.add_clause([q]);
    s.pop();
    assert_eq!(s.solve(), SolverResult::Unsat);
}

/// THE ANTI-OVER-FIX CONTROL. A contradiction introduced INSIDE the scope must
/// still be forgotten by the pop — restoring the saved value has to mean
/// "restore", not "latch forever". Without this test, `pop` could simply stop
/// touching the flag and every other test here would still pass.
#[test]
fn pop_discards_a_contradiction_introduced_inside_the_scope() {
    let mut s = Solver::new();
    s.new_var();
    assert!(s.add_clause([p()]));
    assert_eq!(s.solve(), SolverResult::Sat, "satisfiable before the scope");

    s.push();
    assert!(!s.add_clause([p().negate()]));
    assert_eq!(s.solve(), SolverResult::Unsat, "unsat inside the scope");
    s.pop();
    assert_eq!(
        s.solve(),
        SolverResult::Sat,
        "the pop must retract the scope's own contradiction"
    );
}

/// Nesting: the flag is per-scope, not a single saved slot.
#[test]
fn nested_scopes_restore_the_right_value_at_each_level() {
    let mut s = Solver::new();
    s.new_var();
    assert!(s.add_clause([p()]));

    s.push(); // depth 1 — still satisfiable here
    s.push(); // depth 2
    assert!(!s.add_clause([p().negate()]));
    assert_eq!(s.solve(), SolverResult::Unsat);
    s.pop(); // back to depth 1: the contradiction was depth-2's
    assert_eq!(s.solve(), SolverResult::Sat);
    s.pop(); // back to depth 0
    assert_eq!(s.solve(), SolverResult::Sat);
}
