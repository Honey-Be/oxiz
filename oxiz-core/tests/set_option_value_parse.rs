// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors

//! `(set-option :key value)` must deliver the value it was given.
//!
//! The value was read with `expect_symbol().unwrap_or_default()`, and
//! `expect_symbol` accepts ONLY `TokenKind::Symbol` — so every NUMERIC option
//! was silently reduced to the empty string. `(set-option :timeout 5000)`, the
//! standard spelling, set nothing and reported nothing.
//!
//! The failure mode is what makes it worth a test: an option handler that
//! receives a value it cannot interpret does nothing, which is
//! indistinguishable from the option never having been written. Found while
//! wiring a numeric option (`:oxiz.mbqi-instance-budget`) and watching it have
//! no effect through this path while the equivalent env var worked.

use oxiz_core::ast::TermManager;
use oxiz_core::smtlib::{Command, parse_script};

fn options(script: &str) -> Vec<(String, String)> {
    let mut mgr = TermManager::new();
    parse_script(script, &mut mgr)
        .expect("parses")
        .into_iter()
        .filter_map(|c| match c {
            Command::SetOption(k, v) => Some((k, v)),
            _ => None,
        })
        .collect()
}

/// The reported shape: a numeral value.
#[test]
fn a_numeral_option_value_survives() {
    assert_eq!(
        options("(set-option :timeout 5000)"),
        vec![("timeout".to_owned(), "5000".to_owned())]
    );
}

/// Every scalar the SMT-LIB `<attribute_value>` grammar allows here, since a
/// fix that special-cased numerals alone would leave the rest dropped.
#[test]
fn every_scalar_option_value_survives() {
    let cases = [
        ("(set-option :a sym)", "sym"),
        ("(set-option :b 42)", "42"),
        ("(set-option :c 3.5)", "3.5"),
        ("(set-option :d true)", "true"),
        ("(set-option :e \"text\")", "text"),
    ];
    for (script, want) in cases {
        let got = options(script);
        assert_eq!(got.len(), 1, "{script}");
        assert_eq!(got[0].1, want, "{script}");
    }
}

/// A valueless option is legal, and reading it must not consume the `)` — the
/// caller's `expect_rparen` still has to line up, and a command that ate its own
/// closing paren would desynchronize everything after it.
#[test]
fn a_valueless_option_does_not_eat_the_closing_paren() {
    let opts = options("(set-option :flag)\n(set-option :next 7)\n");
    assert_eq!(
        opts,
        vec![
            ("flag".to_owned(), String::new()),
            ("next".to_owned(), "7".to_owned()),
        ],
        "the second command must still parse"
    );
}

/// ANTI-OVER-FIX control: a numeral immediately after a valueless option must
/// not be swallowed as that option's value. Combined with the test above this
/// pins both halves of the peek — that it looks, and that it does not consume.
#[test]
fn commands_after_a_valueless_option_still_parse() {
    let mut mgr = TermManager::new();
    let cmds = parse_script(
        "(set-logic QF_LIA)\n(set-option :flag)\n(declare-fun x () Int)\n\
         (assert (= x 3))\n(check-sat)\n",
        &mut mgr,
    )
    .expect("parses");
    assert!(
        cmds.iter().any(|c| matches!(c, Command::CheckSat)),
        "the script lost its check-sat: {cmds:?}"
    );
    assert!(
        cmds.iter().any(|c| matches!(c, Command::Assert(_))),
        "the script lost its assertion: {cmds:?}"
    );
}
