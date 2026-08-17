// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors

//! `define-fun` expansion must substitute the formals the body was BUILT with.
//!
//! Expansion re-derived each formal's term from its bare name — a declared-
//! globals lookup for the sort, falling back to `Bool` — and terms are
//! hash-consed on `(name, sort)`. A formal whose name did not happen to collide
//! with a same-sorted global therefore got a DIFFERENT `TermId` than the body
//! held, the substitution matched nothing, and the formal stayed FREE in the
//! "expanded" body. Every call to the macro collapsed to the same open term.
//!
//! The tests below assert on the EXPANDED TERM rather than on a solver verdict,
//! because the defect is a parser defect: a verdict test would also pass if the
//! solver happened to compensate.
//!
//! Reported by upstream OxiZ v0.3.2 as "define-fun call-site arguments could
//! silently vanish". The false-UNSAT direction below is ours.

use oxiz_core::ast::TermManager;
use oxiz_core::smtlib::{Command, parse_script};

/// Parse `script` and return the term of its LAST `assert`.
fn last_assert(script: &str, mgr: &mut TermManager) -> oxiz_core::ast::TermId {
    let cmds = parse_script(script, mgr).expect("parses");
    cmds.iter()
        .rev()
        .find_map(|c| match c {
            Command::Assert(t) => Some(*t),
            _ => None,
        })
        .expect("the script has an assert")
}

/// The reported shape. `(double z)` with `double(n) = n + n` must expand to
/// `z + z`, so the expansion must contain NO free `n`.
#[test]
fn a_non_bool_formal_is_actually_substituted() {
    let mut mgr = TermManager::new();
    let t = last_assert(
        "(set-logic QF_LIA)\n\
         (define-fun double ((n Int)) Int (+ n n))\n\
         (declare-fun z () Int)\n\
         (assert (= (double z) 10))\n",
        &mut mgr,
    );
    let printed = oxiz_core::smtlib::Printer::new(&mgr).print_term(t);
    assert!(
        !printed.contains('n'),
        "the formal survived the expansion: {printed}"
    );
    assert!(
        printed.contains('z'),
        "the argument never reached the body: {printed}"
    );
}

/// THE FATAL DIRECTION, and the one upstream's report does not name. If every
/// call collapses to the same open body, two calls that should be INDEPENDENT
/// become one shared constraint — so two trivially TRUE assertions become a
/// contradiction and the script reports `unsat`. For a caller that verifies by
/// negate-and-refute, a false `unsat` is a false proof.
///
/// `(isfive 5)` is `(= 5 5)` and `(not (isfive 6))` is `(not (= 6 5))`; both
/// hold, so the conjunction is satisfiable. Corrupted, they are `(= k 5)` and
/// `(not (= k 5))`.
#[test]
fn two_independent_calls_do_not_collapse_into_one_constraint() {
    let mut mgr = TermManager::new();
    let cmds = parse_script(
        "(set-logic QF_LIA)\n\
         (define-fun isfive ((k Int)) Bool (= k 5))\n\
         (assert (isfive 5))\n\
         (assert (not (isfive 6)))\n",
        &mut mgr,
    )
    .expect("parses");
    let asserts: Vec<_> = cmds
        .iter()
        .filter_map(|c| match c {
            Command::Assert(t) => Some(*t),
            _ => None,
        })
        .collect();
    assert_eq!(asserts.len(), 2);
    let p = oxiz_core::smtlib::Printer::new(&mgr);
    let (a, b) = (p.print_term(asserts[0]), p.print_term(asserts[1]));
    // Correctly expanded, both fold to `true` — which is the point: they are
    // two independently TRUE facts. Corrupted, they were `(= k 5)` and
    // `(not (= k 5))`, an outright contradiction. So the contract is "the
    // second is not the negation of the first", which the folded pair passes
    // and the corrupted pair fails.
    assert_ne!(
        b,
        format!("(not {a})"),
        "the two calls collapsed into a contradiction: {a} / {b}"
    );
    assert!(!a.contains('k') && !b.contains('k'), "formal survived: {a} / {b}");
}

/// DISCRIMINATOR — a `Bool` formal used to work by pure coincidence, because
/// `Bool` was the re-derivation's fallback sort. It must keep working.
#[test]
fn a_bool_formal_still_expands() {
    let mut mgr = TermManager::new();
    let t = last_assert(
        "(set-logic QF_UF)\n\
         (define-fun negate ((b Bool)) Bool (not b))\n\
         (declare-fun p () Bool)\n\
         (assert (negate p))\n",
        &mut mgr,
    );
    let printed = oxiz_core::smtlib::Printer::new(&mgr).print_term(t);
    assert!(printed.contains('p'), "the argument vanished: {printed}");
}

/// DISCRIMINATOR — a formal whose name COLLIDES with a same-sorted global also
/// used to work by coincidence: the hash-cons handed back the same `TermId`.
/// The collision must no longer matter in EITHER direction — in particular the
/// global `n` must not be captured by the expansion.
#[test]
fn a_formal_colliding_with_a_global_does_not_capture_it() {
    let mut mgr = TermManager::new();
    let t = last_assert(
        "(set-logic QF_LIA)\n\
         (declare-fun n () Int)\n\
         (define-fun double ((n Int)) Int (+ n n))\n\
         (declare-fun z () Int)\n\
         (assert (= (double z) 10))\n",
        &mut mgr,
    );
    let printed = oxiz_core::smtlib::Printer::new(&mgr).print_term(t);
    assert!(printed.contains('z'), "the argument vanished: {printed}");
    assert!(
        !printed.contains('n'),
        "the expansion captured the global of the same name: {printed}"
    );
}

/// ANTI-OVER-FIX control: a multi-parameter macro must bind formals
/// POSITIONALLY. Recording terms in a map keyed by name — or zipping the wrong
/// pair of iterators — would pass every test above and swap these two.
#[test]
fn formals_bind_positionally() {
    let mut mgr = TermManager::new();
    let t = last_assert(
        "(set-logic QF_LIA)\n\
         (define-fun sub ((a Int) (b Int)) Int (- a b))\n\
         (declare-fun p () Int)\n\
         (declare-fun q () Int)\n\
         (assert (= (sub p q) 0))\n",
        &mut mgr,
    );
    let printed = oxiz_core::smtlib::Printer::new(&mgr).print_term(t);
    let (ip, iq) = (printed.find('p'), printed.find('q'));
    assert!(ip.is_some() && iq.is_some(), "an argument vanished: {printed}");
    assert!(
        ip < iq,
        "the formals were bound in the wrong order — `(- p q)` expected: {printed}"
    );
}
