//! Permanent regression tests for #418 item 4 — `declare-datatypes`/
//! `declare-datatype` well-foundedness (strict positivity) checking.
//!
//! Root cause (pre-fix): the parser accepted ANY `declare-datatypes`/
//! `declare-datatype` group unconditionally, including a mutually-recursive
//! group where NO datatype in the group has a base case reachable without
//! infinite recursion (e.g. `(declare-datatype D ((mk (self D))))`). Such a
//! sort is provably UNINHABITED — z3/cvc5 both reject it at declaration time
//! with a parse error — but oxiz previously registered it silently, which
//! could make the solver report `sat` for a datatype sort with no possible
//! value.
//!
//! Fix: `Parser::check_dt_group_well_founded` (in
//! `oxiz-core/src/smtlib/parser/commands.rs`) computes the standard
//! founded/productive-nonterminal fixpoint (Coq/Agda "strict positivity",
//! equivalent to z3/cvc5's own check) over the raw parsed constructor/field
//! structure, BEFORE any sort/constructor registration, and rejects
//! (`OxizError::ParseError`, the same error type/convention every other
//! declare-datatypes-time error already uses in this parser) a group where
//! the fixpoint leaves any datatype unfounded.
//!
//! Every case below was cross-checked against z3 and cvc5 directly (see the
//! #418 task notes): z3/cvc5 accept (b)-(c)-(f)-shaped declarations and
//! reject (d)-(e)-shaped ones with their own "not well-founded" parse error.

use oxiz_core::ast::TermManager;
use oxiz_core::smtlib::parse_script;

/// Returns `true` if the WHOLE script parses without error, `false` if
/// `parse_script` returns `Err` (which is exactly what a non-well-founded
/// `declare-datatypes`/`declare-datatype` now does).
fn parses_ok(script: &str) -> bool {
    let mut manager = TermManager::new();
    parse_script(script, &mut manager).is_ok()
}

/// (a) Simple non-recursive datatype (enum-style) — sanity: must still be
/// accepted (no group member has ANY recursive field at all, so the fixpoint
/// founds every member trivially on the first pass).
#[test]
fn simple_nonrecursive_datatype_accepted() {
    let script = "\
        (declare-datatypes ((Color 0)) (((red) (green) (blue))))\n\
        (declare-const c Color)\n\
        (assert (= c red))\n\
        (check-sat)\n";
    assert!(parses_ok(script), "non-recursive enum datatype must be accepted");
}

/// (b) Single self-recursive datatype with a nullary base case (`Lst`/
/// `cons`/`nil`, used throughout the #406/#418 session) — must still be
/// accepted, via BOTH the plural `declare-datatypes` and singular
/// `declare-datatype` surface forms.
#[test]
fn self_recursive_list_with_base_case_accepted_plural_form() {
    let script = "\
        (declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))\n\
        (declare-const l Lst)\n\
        (assert (= l (cons 1 nil)))\n\
        (check-sat)\n";
    assert!(parses_ok(script), "List with a nullary base case must be accepted (plural form)");
}

#[test]
fn self_recursive_list_with_base_case_accepted_singular_form() {
    let script = "\
        (declare-datatype Lst ((nil) (cons (hd Int) (tl Lst))))\n\
        (declare-const l Lst)\n\
        (assert (= l (cons 1 nil)))\n\
        (check-sat)\n";
    assert!(parses_ok(script), "List with a nullary base case must be accepted (singular form)");
}

/// (c) Two well-founded mutually-recursive datatypes (an Expr/Stmt AST pair),
/// each with some non-recursive-into-the-cycle base case — must be accepted.
#[test]
fn mutually_recursive_expr_stmt_accepted() {
    let script = "\
        (declare-datatypes ((Expr 0) (Stmt 0))\n\
          (((lit (val Int)) (bin (l Expr) (r Expr)))\n\
           ((skip) (seq (s1 Stmt) (s2 Stmt) (sexpr Expr)))))\n\
        (declare-const ev Expr)\n\
        (assert (= ev (lit 3)))\n\
        (check-sat)\n";
    assert!(parses_ok(script), "well-founded mutually-recursive Expr/Stmt group must be accepted");
}

/// (d) A genuinely non-well-founded SINGLE datatype — every constructor
/// recursive, no base case — must now be REJECTED (parse-time error),
/// matching z3 (`datatype is not well-founded`) and cvc5 (`Datatype sort ...
/// is not well-founded`).
#[test]
fn non_well_founded_single_datatype_rejected_plural_form() {
    let script = "(declare-datatypes ((D 0)) (((mk (self D)))))\n(check-sat)\n";
    assert!(
        !parses_ok(script),
        "a single datatype with every constructor recursive and no base case must be REJECTED"
    );
}

#[test]
fn non_well_founded_single_datatype_rejected_singular_form() {
    let script = "(declare-datatype D2 ((mk2 (self2 D2))))\n(check-sat)\n";
    assert!(
        !parses_ok(script),
        "a single self-recursive datatype with no base case must be REJECTED (singular form)"
    );
}

/// (e) A genuinely non-well-founded 2-datatype mutually-recursive group —
/// every constructor of every datatype recursively depends on the group,
/// with no way out — must be REJECTED.
#[test]
fn non_well_founded_mutual_group_of_2_rejected() {
    let script = "\
        (declare-datatypes ((A 0) (B 0))\n\
          (((mkA (bfield B)))\n\
           ((mkB (afield A)))))\n\
        (check-sat)\n";
    assert!(!parses_ok(script), "a 2-datatype mutually-recursive group with no base case anywhere must be REJECTED");
}

/// (e) A genuinely non-well-founded 3-datatype mutually-recursive cycle —
/// must also be REJECTED.
#[test]
fn non_well_founded_mutual_group_of_3_rejected() {
    let script = "\
        (declare-datatypes ((X 0) (Y 0) (Z 0))\n\
          (((mkX (yf Y)))\n\
           ((mkY (zf Z)))\n\
           ((mkZ (xf X)))))\n\
        (check-sat)\n";
    assert!(!parses_ok(script), "a 3-datatype mutually-recursive cycle with no base case anywhere must be REJECTED");
}

/// (f) Trickier well-founded case #1: the base case is NOT the
/// first-declared constructor of its datatype — must be ACCEPTED (the
/// fixpoint doesn't care about constructor declaration order).
#[test]
fn well_founded_base_case_not_first_constructor_accepted() {
    let script = "\
        (declare-datatypes ((Tr 0)) (((mkRecFirst (child Tr)) (leaf))))\n\
        (declare-const t Tr)\n\
        (assert (= t leaf))\n\
        (check-sat)\n";
    assert!(
        parses_ok(script),
        "a self-recursive datatype whose base-case constructor is declared LAST must still be accepted"
    );
}

/// (f) Trickier well-founded case #2: founding one datatype in the group
/// requires FIRST founding another — a genuine multi-step (>1 iteration)
/// fixpoint, not just a single pass. `G1`'s only constructor recurses into
/// `G2`; `G1` becomes founded only once `G2` is founded (which happens on
/// pass 1, since `G2` has its own nullary `mkG2base` constructor) — so `G1`
/// is founded on pass 2. Must be ACCEPTED.
#[test]
fn well_founded_multi_step_fixpoint_accepted() {
    let script = "\
        (declare-datatypes ((G1 0) (G2 0))\n\
          (((mkG1rec (g2f G2)))\n\
           ((mkG2rec (g1f G1)) (mkG2base))))\n\
        (check-sat)\n";
    assert!(
        parses_ok(script),
        "a group requiring a 2-step (not just single-pass) founding fixpoint must still be accepted"
    );
}

/// Defensive regression: a malformed script that declares MORE datatype
/// names than it supplies constructor groups for (a separate, unrelated
/// grammar error the rest of this parser already tolerates without a panic,
/// via `.get()`/fallback-name handling) must be rejected cleanly by the
/// well-foundedness check too — NOT panic with an out-of-bounds index. A
/// name with no constructor group at all has zero constructors, so it is
/// (correctly) never founded.
#[test]
fn mismatched_name_group_count_does_not_panic() {
    let script = "(declare-datatypes ((A 0) (B 0)) (((mkA))))\n(check-sat)\n";
    // Must not panic; whether it's accepted or rejected is secondary here
    // (it happens to reject, since `B` ends up with zero constructors).
    let _ = parses_ok(script);
}
