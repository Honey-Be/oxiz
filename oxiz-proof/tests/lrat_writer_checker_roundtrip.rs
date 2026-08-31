// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors

//! The LRAT PRODUCER and the LRAT CHECKER in this tree must agree on the format.
//!
//! `oxiz-proof`'s `lrat_check` was ported verbatim from upstream v0.3.3 as the
//! first rung of `adsmt-delegate/DELEGATION_TRUST_REDESIGN.md` §S2 ("a delegated
//! `unsat` must EARN `DefiniteUnsat`"). A checker is only worth anything if it
//! accepts what our own writer emits, and it did not: `LratWriter::add_clause`
//! wrote the hint-terminating `0` only when the hint list was NON-empty, while
//! the checker requires it unconditionally. Since `add_original_clause` always
//! passes an empty hint slice, EVERY original-clause line it produced was
//! unparseable — "line 1: addition line missing hint terminator 0".
//!
//! Nothing caught it because the two halves had never been run against each
//! other; each was tested against its own idea of the format. That is the gap
//! this file exists to close, and why it lives in `oxiz-proof` (which can see
//! both) rather than in either crate alone.
//!
//! Gated on the `sat-integration` feature, which is what pulls `oxiz-sat` in.

#![cfg(feature = "sat-integration")]

use oxiz_proof::lrat_check::check_lrat_proof;
use oxiz_sat::LratWriter;
use oxiz_sat::{Lit, Var};

fn lit(d: i32) -> Lit {
    let v = Var::new(d.unsigned_abs() - 1);
    if d > 0 { Lit::pos(v) } else { Lit::neg(v) }
}

/// Capture what the writer emits, through the real file sink a producer uses.
fn emit(tag: &str, f: impl FnOnce(&mut LratWriter)) -> String {
    let path = std::env::temp_dir().join(format!(
        "oxiz_lrat_roundtrip_{}_{tag}.lrat",
        std::process::id()
    ));
    let mut w = LratWriter::new();
    w.enable(&path).expect("enable");
    f(&mut w);
    w.flush().expect("flush");
    drop(w);
    let text = std::fs::read_to_string(&path).expect("read back");
    let _ = std::fs::remove_file(&path);
    text
}

/// THE REGRESSION. An addition line with NO hints must still carry the hint
/// terminator, so `<id> <lits> 0 0`. Before the backport this produced
/// `<id> <lits> 0`, which the checker rejects outright.
#[test]
fn an_empty_hint_list_still_writes_its_terminator() {
    let text = emit("empty_hints", |w| {
        w.add_clause(&[lit(1), lit(-2)], &[]).expect("write");
    });
    let line = text.lines().next().expect("one line");
    assert!(
        line.trim_end().ends_with("0 0"),
        "empty-hint line must end with both terminators, got {line:?}"
    );
}

/// END TO END, which is the point of the file: a proof this tree's WRITER
/// produced is accepted by this tree's CHECKER.
///
/// The formula is the four-clause 2-variable contradiction
/// `(a∨b) ∧ (¬a∨b) ∧ (a∨¬b) ∧ (¬a∨¬b)`, and the proof derives `b`, then `¬b`,
/// then the empty clause — each with an explicit hint chain, which is what
/// makes LRAT checkable by forward propagation alone.
#[test]
fn a_writer_produced_proof_passes_the_checker() {
    let originals: Vec<Vec<i32>> = vec![vec![1, 2], vec![-1, 2], vec![1, -2], vec![-1, -2]];
    let text = emit("roundtrip", |w| {
        // Originals occupy ids 1..=4 — the checker numbers the input formula
        // that way, so the writer must reserve them rather than emit them.
        for _ in 0..originals.len() {
            let _ = w.reserve_original_id();
        }
        // id 5: `b`, from clauses 1 and 2 (resolve on `a`).
        w.add_clause(&[lit(2)], &[1, 2]).expect("write");
        // id 6: `¬b`, from clauses 3 and 4.
        w.add_clause(&[lit(-2)], &[3, 4]).expect("write");
        // id 7: the empty clause, from the two units just derived.
        w.add_clause(&[], &[5, 6]).expect("write");
    });

    let report = check_lrat_proof(&originals, &text);
    assert!(
        report.verified,
        "the checker rejected our own writer's output: {:?}\n--- proof ---\n{text}",
        report.failure
    );
}

/// ANTI-VACUITY. The test above would pass just as well against a checker that
/// accepts anything, so pin that the checker still REJECTS a proof whose hint
/// chain does not actually propagate — here the empty clause claims to follow
/// from two clauses that do not conflict.
#[test]
fn the_checker_still_rejects_a_bogus_chain() {
    let originals: Vec<Vec<i32>> = vec![vec![1, 2], vec![-1, 2], vec![1, -2], vec![-1, -2]];
    let text = emit("bogus", |w| {
        for _ in 0..originals.len() {
            let _ = w.reserve_original_id();
        }
        // Claim the empty clause straight from clauses 1 and 2, which are
        // jointly satisfiable (b = true).
        w.add_clause(&[], &[1, 2]).expect("write");
    });
    let report = check_lrat_proof(&originals, &text);
    assert!(!report.verified, "a non-propagating chain must not verify");
}
