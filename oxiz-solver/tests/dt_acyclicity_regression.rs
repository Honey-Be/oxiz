//! Permanent (z3-cross-checked) regressions for #406 — ground datatype
//! ACYCLICITY.
//!
//! SMT-LIB datatypes denote the INITIAL (free, well-founded) algebra: every
//! element is built by FINITELY many constructor applications, so no ground
//! term may be equal to a proper constructor-subterm of itself. Before this
//! fix oxiz had NO acyclicity check at all — `(assert (= y (cons x y)))` read
//! `sat` (z3: `unsat`).
//!
//! Fixed by `Solver::check_dt_acyclicity` (`check_dt.rs`): build a
//! Union-Find over TermIds using ONLY the genuinely-positively-asserted
//! equalities `collect_dt_constraints_v2` already collects (`dt_var_equalities`
//! for var=var, a new `var_ctor_term_eqs` for var=ConstructorTerm), then add a
//! directed edge from every manifest `DtConstructor` application's
//! equivalence-class root to each of its datatype-sorted arguments'
//! equivalence-class roots (recorded by an unconditional structural walk — a
//! term's shape is a fact about the term, not a proposition, so it needs no
//! polarity gating). A cycle in this graph is a genuine ground conflict.

use oxiz_solver::Context;

fn verdict(script: &str) -> &'static str {
    let mut ctx = Context::new();
    ctx.set_timeout_ms(5000);
    match ctx.execute_script(script) {
        Ok(out) => out
            .iter()
            .rev()
            .find_map(|l| match l.trim() {
                "sat" => Some("sat"),
                "unsat" => Some("unsat"),
                "unknown" => Some("unknown"),
                _ => None,
            })
            .unwrap_or("unknown"),
        Err(_) => "unknown",
    }
}

const LST_DT: &str = "(set-logic ALL)\n\
     (declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))\n";

/// The exact #406 minimal repro: `y = cons(x, y)` — a list equal to its own
/// tail-extension — is UNSAT (pre-fix: `sat`; z3: `unsat`).
#[test]
fn direct_self_cycle_is_unsat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const x Int)\n\
         (declare-const y Lst)\n\
         (assert (= y (cons x y)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// Indirect / longer cycle: `y = cons(x, z)`, `z = cons(w, y)` — a 2-step
/// cycle through two distinct variables, neither of which is directly
/// self-referential on its own.
#[test]
fn two_step_indirect_cycle_is_unsat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const x Int)\n\
         (declare-const w Int)\n\
         (declare-const y Lst)\n\
         (declare-const z Lst)\n\
         (assert (= y (cons x z)))\n\
         (assert (= z (cons w y)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// A cycle chained transitively through PLAIN variable equalities (not a
/// direct constructor argument): `y = cons(x, w)`, `w = z`, `z = y` implies
/// `w`'s equivalence class also contains `y`'s constructor-equality, closing
/// the same cycle as the direct case. Exercises that the Union-Find merges
/// classes across chains of `dt_var_equalities`, not just the single
/// var-to-constructor-term hop.
#[test]
fn cycle_through_chained_var_equalities_is_unsat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const x Int)\n\
         (declare-const y Lst)\n\
         (declare-const w Lst)\n\
         (declare-const z Lst)\n\
         (assert (= y (cons x w)))\n\
         (assert (= w z))\n\
         (assert (= z y))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// SOUNDNESS CONTROL — two SEPARATE variables of the same datatype sort with
/// NO asserted relationship between them must never be conflated into a
/// spurious cycle. Must stay `sat`.
#[test]
fn two_unrelated_vars_same_sort_stay_sat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const y1 Lst)\n\
         (declare-const y2 Lst)\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// SOUNDNESS CONTROL — a disequality between two same-sort variables is not
/// an equality and must not seed any union/edge. Must stay `sat`.
#[test]
fn disequal_vars_same_sort_stay_sat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const y1 Lst)\n\
         (declare-const y2 Lst)\n\
         (assert (not (= y1 y2)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// SOUNDNESS CONTROL — plain mutual variable equality (`y = z` and `z = y`,
/// both directions asserted) merges the two into one class but adds NO
/// containment edge by itself, so it must never be flagged as a cycle. Must
/// stay `sat`.
#[test]
fn plain_mutual_var_equality_stays_sat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const y Lst)\n\
         (declare-const z Lst)\n\
         (assert (= y z))\n\
         (assert (= z y))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// ACYCLIC self-referential-LOOKING case: `y = cons(x, nil)` is a perfectly
/// ordinary one-element list — NOT a cycle, since `nil` terminates the
/// recursion. Must stay `sat` (a naive "any self-mention" heuristic would
/// wrongly flag this; the real check must follow actual argument identity,
/// not mere recursive-sort membership).
#[test]
fn acyclic_base_case_terminates_and_stays_sat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const x Int)\n\
         (declare-const y Lst)\n\
         (assert (= y (cons x nil)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// A DIFFERENT recursive datatype (binary tree: `Leaf` / `Node(left, val,
/// right)`) to confirm the graph construction is fully generic — not
/// list-specific. Direct self-cycle through the `left` field: `t = Node(t, v,
/// r)` is UNSAT (no finite tree equals its own left subtree).
#[test]
fn binary_tree_direct_cycle_is_unsat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((Tree 0)) (((Leaf) (Node (left Tree) (val Int) (right Tree)))))\n\
         (declare-const t Tree)\n\
         (declare-const v Int)\n\
         (declare-const r Tree)\n\
         (assert (= t (Node t v r)))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "unsat");
}

/// SOUNDNESS + generality CONTROL — the SAME binary tree datatype, but a
/// perfectly acyclic (two-leaf) tree assignment. Must stay `sat`.
#[test]
fn binary_tree_acyclic_assignment_stays_sat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((Tree 0)) (((Leaf) (Node (left Tree) (val Int) (right Tree)))))\n\
         (declare-const t Tree)\n\
         (declare-const v Int)\n\
         (assert (= t (Node Leaf v Leaf)))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "sat");
}

/// SOUNDNESS CONTROL — multiple constructor equalities to the SAME variable
/// with the SAME constructor name but syntactically DIFFERENT argument terms
/// must not spuriously interact (each just contributes its own edges; no
/// false cycle from `t1`/`t2` merely coexisting as unrelated fields of the
/// same `y`). Must stay `sat`.
#[test]
fn multiple_ctor_equalities_same_var_different_args_stay_sat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const x1 Int)\n\
         (declare-const x2 Int)\n\
         (declare-const t1 Lst)\n\
         (declare-const t2 Lst)\n\
         (declare-const y Lst)\n\
         (assert (= y (cons x1 t1)))\n\
         (assert (= y (cons x2 t2)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}
