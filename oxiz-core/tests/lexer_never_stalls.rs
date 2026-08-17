// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors

//! `Lexer::next_token` must always advance.
//!
//! A character that can neither START nor CONTINUE an SMT-LIB simple symbol
//! made `read_symbol_chars` consume nothing, so the default arm handed back a
//! zero-width `Symbol("")` with `self.pos` unmoved — and every subsequent call
//! minted the same token at the same offset for ever. Any caller that scans to
//! `Eof` (the parser's balanced-paren error recovery, a token counter, a
//! highlighter) never terminates on input containing one such character, and
//! `,` is one: the symbol set is alphanumerics plus
//! `+ - / * = % ? ! . $ _ ~ & ^ < > @`.
//!
//! The step budget is the point. A test that looped until `Eof` would HANG the
//! whole test binary rather than fail, which is how the defect survived: it is
//! invisible to any harness that assumes progress.

use oxiz_core::smtlib::{Lexer, TokenKind};

/// Drain `input`, returning the token kinds read, or `Err(n)` if `n` steps went
/// by without reaching `Eof`.
fn drain(input: &str) -> Result<Vec<TokenKind>, usize> {
    const MAX_STEPS: usize = 4_000;
    let mut lexer = Lexer::new(input);
    let mut kinds = Vec::new();
    for _ in 0..MAX_STEPS {
        let Some(tok) = lexer.next_token() else {
            return Ok(kinds);
        };
        let done = tok.kind == TokenKind::Eof;
        kinds.push(tok.kind);
        if done {
            return Ok(kinds);
        }
    }
    Err(MAX_STEPS)
}

/// The reported shape: a comma inside an otherwise well-formed script.
#[test]
fn a_comma_does_not_stall_the_lexer() {
    let src = "(set-logic QF_UF)\n(declare-fun a () Bool)\n(assert (and a , a))\n(check-sat)\n";
    match drain(src) {
        Ok(kinds) => assert!(
            kinds.len() < 64,
            "reached Eof but minted {} tokens for a 4-command script",
            kinds.len()
        ),
        Err(n) => panic!("lexer made no progress: {n} tokens without reaching Eof"),
    }
}

/// Every character outside the symbol set, one at a time. A fix that special-
/// cases the comma alone would pass the test above and fail here.
#[test]
fn no_single_character_stalls_the_lexer() {
    for c in [
        ',', '\'', '`', '[', ']', '{', '}', '\\', '\u{7f}', '\u{a0}', '€', '→',
    ] {
        let src = format!("(assert {c})");
        assert!(
            drain(&src).is_ok(),
            "lexer made no progress on U+{:04X}",
            u32::from(c)
        );
    }
}

/// Progress must not come at the cost of SILENCE. This fork's `Lexer` has no
/// error vector (upstream 0.3.3 records a `LexError`; that infrastructure does
/// not exist here), so the guarantee has to hold one layer up: the offending
/// character must reach the parser AS A NAMED SYMBOL and be rejected there. If
/// it were swallowed, the script would parse as though the character had never
/// been written — the `feedback-soundness-opaque-fallback` shape at the lexer
/// level.
#[test]
fn an_unlexable_character_survives_as_a_named_symbol() {
    let kinds = drain("(assert ,)").expect("no stall");
    assert!(
        kinds.iter().any(|k| matches!(k, TokenKind::Symbol(s) if s == ",")),
        "the comma was consumed without being handed to the parser: {kinds:?}"
    );
}

/// ANTI-OVER-FIX control: the fix must not make ordinary scripts lex
/// differently. A guard that consumed a character whenever
/// `read_symbol_chars` returned early — rather than only when it returned
/// EMPTY — would eat the delimiter after every symbol.
#[test]
fn ordinary_scripts_are_unaffected() {
    let src = "(set-logic QF_LIA)\n(declare-fun x () Int)\n(assert (>= x 0))\n(check-sat)\n";
    let kinds = drain(src).expect("no stall");
    assert!(
        !kinds.iter().any(|k| matches!(k, TokenKind::Symbol(s) if s.len() == 1
            && !s.chars().next().is_some_and(|c| c.is_alphanumeric() || c == '>'))),
        "the fix ate a delimiter and minted a stray one-character symbol: {kinds:?}"
    );
    let symbols = kinds
        .iter()
        .filter(|k| matches!(k, TokenKind::Symbol(_)))
        .count();
    assert!(
        symbols >= 6,
        "expected the script's symbols to survive, saw {symbols}"
    );
}

/// END TO END, and the reason the lexer-level guarantee is load-bearing: the
/// parser's unknown-command recovery (`parser/commands.rs`, the `_` arm) skips
/// balanced parens by pulling tokens until depth reaches zero or `Eof` arrives.
/// Neither happens when the lexer stalls, so a script with an unknown command
/// containing one unlexable character hangs `parse_script` for ever. Measured
/// on the CLI before the fix: `timeout 20` returned 124; after it, `sat`, which
/// is what z3 answers (z3 prints `unsupported` for the command and continues).
///
/// Run on a worker thread with a join deadline so a regression FAILS instead of
/// wedging the test binary — the same reason the lexer tests above carry a step
/// budget.
#[test]
fn an_unknown_command_with_an_unlexable_char_does_not_hang_the_parser() {
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let src = "(set-logic QF_UF)\n(some-unknown-command a , b)\n\
                   (declare-fun p () Bool)\n(assert p)\n(check-sat)\n";
        let mut mgr = oxiz_core::ast::TermManager::new();
        let parsed = oxiz_core::smtlib::parse_script(src, &mut mgr).is_ok();
        let _ = tx.send(parsed);
    });
    match rx.recv_timeout(std::time::Duration::from_secs(20)) {
        Ok(_) => {}
        Err(_) => panic!("parse_script did not terminate — the lexer stalled"),
    }
}
