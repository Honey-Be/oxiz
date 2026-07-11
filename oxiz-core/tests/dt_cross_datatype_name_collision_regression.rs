//! Permanent regression tests for #424 item 1 — cross-datatype
//! constructor/selector name collision, now rejected at parse time.
//!
//! Two bugs used to stack when the SAME constructor or selector name was
//! (re)used by a SECOND, different datatype:
//!
//!   (a) `TermManager::intern`'s general cache keys purely on the
//!       `TermKind` value, and `TermKind::DtConstructor { constructor, args
//!       }` carries no sort field at all — so `mk_dt_constructor("c0", [],
//!       sortA)` followed by `mk_dt_constructor("c0", [], sortB)` (two
//!       DIFFERENT datatypes' same-named nullary constructor) collapsed to
//!       ONE term; `sortB`'s binding was silently discarded.
//!   (b) The parser's own `dt_constructors`/`dt_selectors` maps are flat,
//!       single-entry-per-name, with NO duplicate-name check — a second
//!       datatype's same-named constructor/selector silently OVERWROTE the
//!       first's map entry.
//!
//! CONFIRMED via z3/cvc5: `(declare-datatypes ((A 0) (B 0)) (((c0)) ((c0))))`
//! parses fine in BOTH — they instead reject a LATER *ambiguous bare
//! reference* to `c0` ("ambiguous constant reference... use (as c0 A) to
//! disambiguate"). oxiz implements no sort-based overload resolution at all,
//! so the DECIDED SCOPE here is intentionally MORE restrictive than z3/cvc5:
//! reject the SECOND (and any subsequent) `declare-datatypes`/
//! `declare-datatype` that tries to register a constructor OR selector name
//! already used by a PREVIOUSLY DECLARED datatype, as a parse-time error —
//! closing both bugs above by construction (a rejected declaration never
//! reaches `mk_dt_constructor` or the `dt_constructors`/`dt_selectors` map
//! insertion for the colliding name).
//!
//! Fix: new `Parser::check_dt_group_no_name_collisions` (in
//! `oxiz-core/src/smtlib/parser/commands.rs`), mirroring #418's
//! `check_dt_group_well_founded`'s "raw pre-registration structure,
//! check-before-commit" pattern — called from both `parse_declare_datatypes`
//! and `parse_declare_datatype`, strictly BEFORE any
//! `SortManager`/`dt_constructors`/`dt_selectors`/`TermManager` registration
//! for the current command. Checks WITHIN-NAMESPACE only (constructor names
//! vs constructor names, selector names vs selector names) — a constructor
//! name colliding with an unrelated datatype's SELECTOR name is a separate,
//! pre-existing routing quirk (`terms.rs`'s selector-before-constructor
//! lookup order), out of scope here.

use oxiz_core::ast::TermManager;
use oxiz_core::smtlib::{ParserEnv, parse_script, parse_script_with_env};

/// Returns `true` if the WHOLE script parses without error.
fn parses_ok(script: &str) -> bool {
    let mut manager = TermManager::new();
    parse_script(script, &mut manager).is_ok()
}

// ---------------------------------------------------------------------
// Core rejection cases.
// ---------------------------------------------------------------------

/// THE exact z3/cvc5-tested collision repro from the task: two
/// single-datatype-arity-0 groups declared in ONE `declare-datatypes` call,
/// sharing the nullary constructor name `c0`. z3/cvc5 both ACCEPT this at
/// declaration time (only later rejecting an ambiguous bare reference) —
/// oxiz's decided, more-restrictive scope rejects the DECLARATION itself.
#[test]
fn exact_z3_cvc5_tested_collision_repro_rejected() {
    let script = "(declare-datatypes ((A 0) (B 0)) (((c0)) ((c0))))\n(check-sat)\n";
    assert!(
        !parses_ok(script),
        "a second datatype's same-named nullary constructor within one \
         declare-datatypes group must be REJECTED (decided scope, stricter \
         than z3/cvc5)"
    );
}

/// The SAME collision, but across TWO SEPARATE `declare-datatype` commands
/// (not one `declare-datatypes` group) — must also be rejected, confirming
/// the check consults `self.dt_constructors` AS IT STANDS from an EARLIER
/// command, not just within-group state.
#[test]
fn cross_command_constructor_collision_rejected() {
    let script = "\
        (declare-datatype A ((c0)))\n\
        (declare-datatype B ((c0)))\n\
        (check-sat)\n";
    assert!(
        !parses_ok(script),
        "a second, separate declare-datatype command reusing an earlier \
         command's constructor name must be REJECTED"
    );
}

/// Cross-command collision via the PLURAL `declare-datatypes` form on both
/// sides (not just singular `declare-datatype`).
#[test]
fn cross_command_constructor_collision_plural_form_rejected() {
    let script = "\
        (declare-datatypes ((A 0)) (((c0))))\n\
        (declare-datatypes ((B 0)) (((c0))))\n\
        (check-sat)\n";
    assert!(
        !parses_ok(script),
        "a second declare-datatypes command reusing an earlier command's \
         constructor name must be REJECTED"
    );
}

/// Selector-name collision, PLURAL `declare-datatypes` form: two different
/// datatypes' constructors both declare a field selector named `fld`.
#[test]
fn selector_name_collision_plural_form_rejected() {
    let script = "\
        (declare-datatypes ((A 0) (B 0))\n\
          (((mk-a (fld Int))) ((mk-b (fld Int)))))\n\
        (check-sat)\n";
    assert!(
        !parses_ok(script),
        "a second datatype's same-named selector within one declare-datatypes \
         group must be REJECTED"
    );
}

/// Selector-name collision, SINGULAR `declare-datatype` form, across two
/// separate commands.
#[test]
fn selector_name_collision_singular_form_rejected() {
    let script = "\
        (declare-datatype A ((mk-a (fld Int))))\n\
        (declare-datatype B ((mk-b (fld Int))))\n\
        (check-sat)\n";
    assert!(
        !parses_ok(script),
        "a second declare-datatype command reusing an earlier command's \
         selector name must be REJECTED"
    );
}

/// BONUS case (not #424's primary target, but z3/cvc5 also reject this): a
/// duplicate constructor name WITHIN one single datatype's own constructor
/// list — `check_dt_group_no_name_collisions` also catches within-group
/// duplicates via its `seen_ctors` bookkeeping.
#[test]
fn within_one_datatype_duplicate_constructor_rejected() {
    let script = "(declare-datatype A ((c0) (c0)))\n(check-sat)\n";
    assert!(
        !parses_ok(script),
        "a single datatype declaring the same constructor name twice must \
         be REJECTED (z3/cvc5 also reject this)"
    );
}

/// BONUS case: duplicate SELECTOR name within one single constructor's own
/// field list.
#[test]
fn within_one_constructor_duplicate_selector_rejected() {
    let script = "(declare-datatype A ((mk (fld Int) (fld Bool))))\n(check-sat)\n";
    assert!(
        !parses_ok(script),
        "a single constructor declaring the same selector name twice must \
         be REJECTED"
    );
}

// ---------------------------------------------------------------------
// `ParserEnv` / `parse_script_with_env` cross-call surface — a front-end
// that feeds commands ONE slice at a time (see `ParserEnv`'s own doc
// comment) must ALSO have its accumulated `dt_constructors`/`dt_selectors`
// state consulted by the collision check on a LATER slice.
// ---------------------------------------------------------------------

/// A collision split across two SEPARATE `parse_script_with_env` calls
/// (simulating a streaming front-end that feeds one command per call) must
/// still be rejected on the second call, since `env.dt_constructors` from
/// the first call is seeded into the second `Parser` before its own
/// `check_dt_group_no_name_collisions` runs.
#[test]
fn parser_env_seeded_cross_call_collision_rejected() {
    let mut manager = TermManager::new();
    let mut env = ParserEnv::default();

    let first = "(declare-datatype A ((c0)))\n";
    let r1 = parse_script_with_env(first, &mut manager, &mut env);
    assert!(r1.is_ok(), "first slice (no collision yet) must parse fine");

    let second = "(declare-datatype B ((c0)))\n";
    let r2 = parse_script_with_env(second, &mut manager, &mut env);
    assert!(
        r2.is_err(),
        "a LATER slice's datatype reusing an EARLIER slice's constructor \
         name (via ParserEnv-seeded state) must be REJECTED"
    );
}

/// SAME cross-call shape, but for a selector-name collision.
#[test]
fn parser_env_seeded_cross_call_selector_collision_rejected() {
    let mut manager = TermManager::new();
    let mut env = ParserEnv::default();

    let first = "(declare-datatype A ((mk-a (fld Int))))\n";
    let r1 = parse_script_with_env(first, &mut manager, &mut env);
    assert!(r1.is_ok(), "first slice (no collision yet) must parse fine");

    let second = "(declare-datatype B ((mk-b (fld Int))))\n";
    let r2 = parse_script_with_env(second, &mut manager, &mut env);
    assert!(
        r2.is_err(),
        "a LATER slice's selector reusing an EARLIER slice's selector name \
         (via ParserEnv-seeded state) must be REJECTED"
    );
}

// ---------------------------------------------------------------------
// FALSE-REJECTION CONTROLS — these are the highest-severity checks in this
// file: a script with NO actual cross-datatype name collision must parse
// EXACTLY as before. A false rejection here is treated as equally severe as
// a spurious Unsat by this project's doctrine.
// ---------------------------------------------------------------------

/// Sanity control: two datatypes with entirely DISJOINT constructor and
/// selector names must still parse fine.
#[test]
fn disjoint_names_sanity_control_accepted() {
    let script = "\
        (declare-datatype A ((c0)))\n\
        (declare-datatype B ((c1)))\n\
        (check-sat)\n";
    assert!(
        parses_ok(script),
        "two datatypes with entirely disjoint constructor names must NOT be \
         rejected"
    );
}

/// SAME disjoint-names control, but with field-bearing constructors and
/// disjoint selector names too.
#[test]
fn disjoint_names_with_selectors_sanity_control_accepted() {
    let script = "\
        (declare-datatype A ((mk-a (fld-a Int))))\n\
        (declare-datatype B ((mk-b (fld-b Int))))\n\
        (declare-const x A)\n\
        (declare-const y B)\n\
        (assert (= (fld-a x) (fld-b y)))\n\
        (check-sat)\n";
    assert!(
        parses_ok(script),
        "two datatypes with entirely disjoint constructor AND selector \
         names must NOT be rejected"
    );
}

/// A single self-recursive datatype (the #418 well-foundedness test suite's
/// own base case) must be unaffected — no cross-datatype collision
/// machinery should ever reject a lone, non-colliding declaration.
#[test]
fn single_self_recursive_datatype_still_accepted() {
    let script = "\
        (declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))\n\
        (declare-const l Lst)\n\
        (assert (= l (cons 1 nil)))\n\
        (check-sat)\n";
    assert!(
        parses_ok(script),
        "a single non-colliding datatype must NOT be rejected by the new \
         collision check"
    );
}

/// A well-founded MUTUALLY-recursive group (Expr/Stmt) with disjoint
/// constructor/selector names across both members — regression control
/// mirroring `dt_well_foundedness_regression.rs`'s own
/// `mutually_recursive_expr_stmt_accepted` case, confirming the NEW
/// collision check composes cleanly with the EXISTING well-foundedness
/// check (both run, in order, before any registration) without spuriously
/// rejecting a group the well-foundedness check alone would accept.
#[test]
fn mutually_recursive_group_disjoint_names_still_accepted() {
    let script = "\
        (declare-datatypes ((Expr 0) (Stmt 0))\n\
          (((lit (val Int)) (bin (l Expr) (r Expr)))\n\
           ((skip) (seq (s1 Stmt) (s2 Stmt) (sexpr Expr)))))\n\
        (declare-const ev Expr)\n\
        (assert (= ev (lit 3)))\n\
        (check-sat)\n";
    assert!(
        parses_ok(script),
        "a well-founded mutually-recursive group with disjoint names must \
         NOT be rejected by the new collision check"
    );
}

/// Re-declaring the SAME datatype name is a SEPARATE, pre-existing
/// (out-of-scope) matter — this test only confirms the collision check
/// itself doesn't crash/misbehave on a same-shaped repeat; whether it's
/// accepted or rejected is secondary (recorded, not asserted strictly, to
/// avoid over-claiming scope this task didn't decide).
#[test]
fn identical_redeclaration_does_not_panic() {
    let script = "\
        (declare-datatype A ((c0)))\n\
        (declare-datatype A ((c0)))\n\
        (check-sat)\n";
    // Must not panic. A same-name-AND-same-constructor redeclaration is
    // caught by the SAME collision check as any other constructor-name
    // reuse (it doesn't special-case "identical" redeclarations), so this
    // is expected to reject too — asserted for documentation, not just a
    // smoke test.
    assert!(
        !parses_ok(script),
        "redeclaring the exact same datatype+constructor name is still a \
         constructor-name collision by this check's own (conservative) rule"
    );
}

// ---------------------------------------------------------------------
// `(reset)`-boundary false-rejection controls — #424 adversarial review
// (verifier "soundness" lens) found that a `(reset)` between two
// datatypes reusing a constructor/selector name was wrongly rejected,
// even though `(reset)` genuinely erases all prior declarations
// (z3/cvc5 both accept the equivalent script). Root cause:
// `Context::execute_script` parses a WHOLE script into a `Vec<Command>`
// in ONE `parse_script_with_env` call before any command — including
// `Command::Reset` — actually executes, so the parser's own
// `dt_constructors`/`dt_selectors` maps must be cleared the instant
// `Command::Reset` is PARSED (not when it's later executed) for a
// same-script reset boundary to have any effect. Fixed in the "reset"
// arm of `Parser::parse_command` (`commands.rs`).
// ---------------------------------------------------------------------

/// THE exact minimal repro from the soundness verifier's report: a
/// constructor name reused by a second datatype AFTER a `(reset)` must be
/// ACCEPTED (z3 and cvc5 both accept it — `(reset)` makes the two
/// datatypes genuinely unrelated), all within ONE `parse_script` call
/// (mirroring `Context::execute_script`'s single-parse-then-execute
/// shape).
#[test]
fn constructor_collision_across_reset_within_one_script_accepted() {
    let script = "\
        (declare-datatype A ((c0)))\n\
        (reset)\n\
        (declare-datatype B ((c0)))\n\
        (check-sat)\n";
    assert!(
        parses_ok(script),
        "a constructor name reused by a second datatype AFTER a (reset) \
         must NOT be rejected — (reset) erases the first datatype's \
         declaration entirely, matching z3/cvc5"
    );
}

/// SAME shape, but for a selector name instead of a constructor name.
#[test]
fn selector_collision_across_reset_within_one_script_accepted() {
    let script = "\
        (declare-datatype A ((mk (fld Int))))\n\
        (reset)\n\
        (declare-datatype B ((mk2 (fld Int))))\n\
        (check-sat)\n";
    assert!(
        parses_ok(script),
        "a selector name reused by a second datatype AFTER a (reset) must \
         NOT be rejected"
    );
}

/// Two consecutive `(reset)`s must not misbehave (e.g. clearing an
/// already-empty map) — still accepted.
#[test]
fn constructor_collision_across_double_reset_accepted() {
    let script = "\
        (declare-datatype A ((c0)))\n\
        (reset)\n\
        (reset)\n\
        (declare-datatype B ((c0)))\n\
        (check-sat)\n";
    assert!(
        parses_ok(script),
        "a constructor name reused after TWO consecutive (reset)s must NOT \
         be rejected"
    );
}

/// A genuine collision occurring ENTIRELY AFTER a `(reset)` (i.e. the
/// reset itself is irrelevant to the collision — both colliding
/// datatypes are declared post-reset) must still be correctly rejected —
/// confirms clearing on `(reset)` doesn't disable the check going
/// forward, only erases STALE pre-reset state.
#[test]
fn collision_entirely_after_reset_still_rejected() {
    let script = "\
        (declare-datatype Unrelated ((u0)))\n\
        (reset)\n\
        (declare-datatype A ((c0)))\n\
        (declare-datatype B ((c0)))\n\
        (check-sat)\n";
    assert!(
        !parses_ok(script),
        "a genuine post-reset collision (between two datatypes BOTH \
         declared after the reset) must still be REJECTED"
    );
}

/// `(reset-assertions)` — unlike `(reset)` — does NOT erase declarations
/// in real solvers, so a collision spanning a `(reset-assertions)`
/// boundary is a genuine, still-applicable collision and must remain
/// REJECTED (confirms the fix is scoped to `Command::Reset` only, not
/// `Command::ResetAssertions`).
#[test]
fn constructor_collision_across_reset_assertions_still_rejected() {
    let script = "\
        (declare-datatype A ((c0)))\n\
        (reset-assertions)\n\
        (declare-datatype B ((c0)))\n\
        (check-sat)\n";
    assert!(
        !parses_ok(script),
        "(reset-assertions) does not erase declarations, so a constructor \
         name reused across it is still a genuine collision and must \
         remain REJECTED"
    );
}

/// The SAME reset-boundary shape, but split across two SEPARATE
/// `parse_script_with_env` calls (simulating a streaming/interactive
/// front-end that executes each command — including `(reset)` — before
/// feeding the next one, i.e. `Context::parser_env`'s persistence path
/// rather than a single whole-script parse).
#[test]
fn parser_env_seeded_cross_call_reset_boundary_accepted() {
    let mut manager = TermManager::new();
    let mut env = ParserEnv::default();

    let first = "(declare-datatype A ((c0)))\n";
    let r1 = parse_script_with_env(first, &mut manager, &mut env);
    assert!(r1.is_ok(), "first slice (no collision yet) must parse fine");

    let reset = "(reset)\n";
    let r2 = parse_script_with_env(reset, &mut manager, &mut env);
    assert!(r2.is_ok(), "a lone (reset) slice must parse fine");
    assert!(
        env.dt_constructors.is_empty(),
        "ParserEnv.dt_constructors must be cleared after a (reset) slice \
         is parsed, so it's empty when persisted for the NEXT slice"
    );
    assert!(
        env.dt_selectors.is_empty(),
        "ParserEnv.dt_selectors must be cleared after a (reset) slice is \
         parsed"
    );

    let third = "(declare-datatype B ((c0)))\n";
    let r3 = parse_script_with_env(third, &mut manager, &mut env);
    assert!(
        r3.is_ok(),
        "a THIRD slice's datatype reusing the FIRST slice's constructor \
         name, with an intervening (reset) slice in between, must NOT be \
         rejected — the reset legitimately erased the first declaration"
    );
}
