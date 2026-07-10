//! Permanent regression tests for #419 item 3 — the `is-<ctor>` shorthand
//! datatype tester syntax (a plain, non-indexed applied symbol, as opposed to
//! the standard `(_ is <ctor>)` indexed-identifier form).
//!
//! Root cause (pre-fix): the parser only recognized `(_ is <ctor>)`. Some
//! tooling instead emits the plain-symbol shorthand `(is-<ctor> arg)`, which
//! previously fell through to the generic "unknown function -> opaque Apply"
//! path (see the `_ =>` arm in `terms.rs`'s applied-symbol parser), silently
//! treating it as a free uninterpreted predicate with no tester semantics —
//! producing spurious `sat`.
//!
//! Fix (`oxiz-core/src/smtlib/parser/terms.rs`, the applied-symbol `_ =>` arm):
//! when the operator name is NOT a real declared function (`self.functions`),
//! strip an `is-` prefix and check the remainder against `dt_constructors`;
//! if it matches, build the exact same `TermKind::DtTester` node the `(_ is
//! <ctor>)` path builds. A real user declaration of a function literally
//! named `is-<ctor>` always takes priority and is checked first, so the
//! shorthand sugar never hijacks a genuine declaration.
//!
//! Cross-checked against z3 and cvc5 directly (see the #419 task notes):
//! both accept `is-cons`-style syntax and agree with oxiz on every verdict
//! for the (sat/unsat) probes this fix was built against.

use oxiz_core::ast::{TermKind, TermManager};
use oxiz_core::smtlib::{Command, parse_script};

/// Datatype declaration shared by every test below: `List = nil | cons(hd:
/// Int, tl: List)`.
const LIST_DECL: &str = "(declare-datatypes ((List 0)) (((nil) (cons (hd Int) (tl List)))))\n";

/// The `is-cons` shorthand and the standard `(_ is cons)` indexed form must
/// build the IDENTICAL term (same hash-consed `TermId`) when applied to the
/// same argument in the same manager — proving the shorthand routes through
/// the same `mk_dt_tester` construction, not some parallel/divergent path.
#[test]
fn is_cons_shorthand_and_indexed_form_build_identical_term() {
    let mut manager = TermManager::new();
    let script = format!(
        "{LIST_DECL}\
         (declare-const x Int)\n\
         (declare-const y List)\n\
         (assert (is-cons (cons x y)))\n\
         (assert ((_ is cons) (cons x y)))\n\
         (check-sat)\n"
    );

    let commands = parse_script(&script, &mut manager).expect("script should parse");
    let asserted: Vec<_> = commands
        .iter()
        .filter_map(|c| match c {
            Command::Assert(t) => Some(*t),
            _ => None,
        })
        .collect();
    assert_eq!(asserted.len(), 2, "expected exactly 2 asserts");
    assert_eq!(
        asserted[0], asserted[1],
        "the is-cons shorthand and (_ is cons) indexed form must hash-cons to the SAME term"
    );
}

/// The shorthand must build an actual `TermKind::DtTester` node (not an
/// opaque `Apply`), with the constructor resolved to the exact name used in
/// `(_ is cons)`.
#[test]
fn is_cons_shorthand_builds_dt_tester_node() {
    let mut manager = TermManager::new();
    let script = format!(
        "{LIST_DECL}\
         (declare-const x Int)\n\
         (declare-const y List)\n\
         (assert (is-cons (cons x y)))\n\
         (check-sat)\n"
    );

    let commands = parse_script(&script, &mut manager).expect("script should parse");
    let assert_term = commands
        .iter()
        .find_map(|c| match c {
            Command::Assert(t) => Some(*t),
            _ => None,
        })
        .expect("expected an assert command");

    let term = manager.get(assert_term).expect("term must be interned");
    match &term.kind {
        TermKind::DtTester { constructor, .. } => {
            assert_eq!(
                manager.resolve_str(*constructor),
                "cons",
                "shorthand must resolve to the 'cons' constructor"
            );
        }
        other => panic!("expected TermKind::DtTester from is-cons shorthand, got {other:?}"),
    }
}

/// `is-nil` (a nullary constructor) must also work through the shorthand —
/// not just the multi-field `cons` case.
#[test]
fn is_nil_shorthand_builds_dt_tester_node() {
    let mut manager = TermManager::new();
    let script = format!(
        "{LIST_DECL}\
         (declare-const l List)\n\
         (assert (is-nil l))\n\
         (check-sat)\n"
    );

    let commands = parse_script(&script, &mut manager).expect("script should parse");
    let assert_term = commands
        .iter()
        .find_map(|c| match c {
            Command::Assert(t) => Some(*t),
            _ => None,
        })
        .expect("expected an assert command");

    let term = manager.get(assert_term).expect("term must be interned");
    match &term.kind {
        TermKind::DtTester { constructor, .. } => {
            assert_eq!(manager.resolve_str(*constructor), "nil");
        }
        other => panic!("expected TermKind::DtTester from is-nil shorthand, got {other:?}"),
    }
}

/// A REAL user declaration of a function literally named `is-cons` must take
/// priority over the shorthand sugar: applying it must build an ordinary
/// opaque `Apply` node, NOT a `TermKind::DtTester`, and it must NOT be
/// confused with the genuine tester on the same constructor name.
#[test]
fn declared_is_cons_function_is_not_hijacked_by_shorthand() {
    let mut manager = TermManager::new();
    let script = format!(
        "{LIST_DECL}\
         (declare-fun is-cons (List) Bool)\n\
         (declare-const l List)\n\
         (assert (is-cons l))\n\
         (check-sat)\n"
    );

    let commands = parse_script(&script, &mut manager).expect("script should parse");
    let assert_term = commands
        .iter()
        .find_map(|c| match c {
            Command::Assert(t) => Some(*t),
            _ => None,
        })
        .expect("expected an assert command");

    let term = manager.get(assert_term).expect("term must be interned");
    assert!(
        !matches!(term.kind, TermKind::DtTester { .. }),
        "a user-declared `is-cons` function must NOT be hijacked into a DtTester, got {:?}",
        term.kind
    );
}

/// End-to-end polarity check mirroring the standard `(_ is cons)` semantics:
/// `(is-cons (cons x y))` must be satisfiable, `(not (is-cons (cons x y)))`
/// must NOT be (parse-level shape check only — this test file is parser-
/// scoped and doesn't invoke the solver, but it confirms both polarities
/// parse to the expected term shapes without conflating tester and negated
/// tester).
#[test]
fn is_cons_shorthand_negated_still_builds_dt_tester_under_not() {
    let mut manager = TermManager::new();
    let script = format!(
        "{LIST_DECL}\
         (declare-const x Int)\n\
         (declare-const y List)\n\
         (assert (not (is-cons (cons x y))))\n\
         (check-sat)\n"
    );

    let commands = parse_script(&script, &mut manager).expect("script should parse");
    let assert_term = commands
        .iter()
        .find_map(|c| match c {
            Command::Assert(t) => Some(*t),
            _ => None,
        })
        .expect("expected an assert command");

    let term = manager.get(assert_term).expect("term must be interned");
    match &term.kind {
        TermKind::Not(inner) => {
            let inner_term = manager.get(*inner).expect("inner term must be interned");
            match &inner_term.kind {
                TermKind::DtTester { constructor, .. } => {
                    assert_eq!(manager.resolve_str(*constructor), "cons");
                }
                other => panic!("expected DtTester under Not, got {other:?}"),
            }
        }
        other => panic!("expected TermKind::Not at the top, got {other:?}"),
    }
}
