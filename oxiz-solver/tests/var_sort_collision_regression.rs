//! Permanent (z3+cvc5-cross-checked) regressions for the hash-cons variable
//! conflation found while localizing adsmt #397 part C (2026-07-04).
//!
//! `TermManager::intern` keyed its structural-sharing cache on `TermKind`
//! alone; `TermKind::Var(spur)` carries no sort, so two same-named variables
//! of DIFFERENT sorts collapsed to whichever was interned FIRST. In the verus
//! AIR stream the abs axiom binds `x!: Poly` and the query later declares a
//! global `x!: Int`: the goal's ground `x!` literally BECAME the axiom's
//! bound-variable term, so every e-match instance "retained a bound var" and
//! was dropped — an ORDER-SENSITIVE spurious unknown/sat (declaring the
//! constant before the axiom flipped the verdict). Fixed by keying variable
//! interning on (name, sort) (`TermManager::var_cache`).
//!
//! The same-name SAME-sort flavour (a bound var vs a later-declared constant
//! sharing both) was closed separately (#400): quantifier binders are now
//! alpha-renamed UNCONDITIONALLY into the reserved `!q<N>` namespace at parse,
//! so no later declaration can collide in either order.

use oxiz_solver::Context;

fn verdict(script: &str) -> &'static str {
    let mut ctx = Context::new();
    ctx.set_timeout_ms(10_000);
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

const AXIOM: &str = "(assert (forall ((x! Poly)) (! (= (abs? x!) (ite (>= (%I x!) 0) (%I x!) (- 0 (%I x!)))) :pattern ((abs? x!)))))";

fn script(decl_order: &str) -> String {
    format!(
        "(set-logic ALL)\n\
         (declare-sort Poly 0)\n\
         (declare-fun abs? (Poly) Int)\n\
         (declare-fun I (Int) Poly)\n\
         (declare-fun %I (Poly) Int)\n\
         {decl_order}\n\
         (assert (not (>= (abs? (I x!)) 0)))\n\
         (check-sat)\n"
    )
}

/// The AIR order: the axiom binding `x!: Poly` is asserted BEFORE the
/// colliding `x!: Int` constant is declared. Pre-fix this read `sat`.
#[test]
fn colliding_const_declared_after_axiom_is_unsat() {
    let v = verdict(&script(&format!("{AXIOM}\n(declare-const x! Int)")));
    assert_eq!(v, "unsat");
}

/// The reverse order must agree (pre-fix the two orders DISAGREED).
#[test]
fn colliding_const_declared_before_axiom_is_unsat() {
    let v = verdict(&script(&format!("(declare-const x! Int)\n{AXIOM}")));
    assert_eq!(v, "unsat");
}

/// A declared-but-unused colliding constant is harmless in both orders.
#[test]
fn unused_colliding_const_is_harmless() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-sort Poly 0)\n\
         (declare-fun abs? (Poly) Int)\n\
         (declare-fun I (Int) Poly)\n\
         (declare-fun %I (Poly) Int)\n\
         (assert (forall ((x! Poly)) (! (= (abs? x!) (ite (>= (%I x!) 0) (%I x!) (- 0 (%I x!)))) :pattern ((abs? x!)))))\n\
         (declare-const x! Int)\n\
         (declare-const w Int)\n\
         (assert (not (>= (abs? (I w)) 0)))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "unsat");
}

/// Same-named vars of different sorts are DISTINCT terms end-to-end: using
/// both in one script must not cross-contaminate (`p` at Int vs Bool sorts).
#[test]
fn same_name_different_sort_constants_are_distinct() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-sort S 0)\n\
         (declare-fun f (S) Int)\n\
         (declare-const a S)\n\
         (declare-const b Int)\n\
         (assert (= (f a) 1))\n\
         (assert (= b 2))\n\
         (assert (= (f a) b))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "unsat", "1 = f(a) = b = 2 is a plain conflict");
}

/// The full live AIR 5-query stream's first obligation shape, end-to-end:
/// fuel chain + Sub + ite definition + Poly boxing (the #397 fixture core,
/// exact assert set the r1 ddmin isolated), raw AIR command order.
#[test]
fn air_fuel_chain_raw_order_is_unsat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-sort FuelId 0)\n(declare-sort Poly 0)\n\
         (declare-fun fuel_bool (FuelId) Bool)\n\
         (declare-fun fuel_bool_default (FuelId) Bool)\n\
         (declare-const fuel_defaults Bool)\n\
         (declare-const fuel%abs FuelId)\n\
         (declare-fun abs? (Poly) Int)\n\
         (declare-fun I (Int) Poly)\n(declare-fun %I (Poly) Int)\n\
         (declare-fun Sub (Int Int) Int)\n\
         (assert (=> fuel_defaults (forall ((id FuelId)) (! (= (fuel_bool id) (fuel_bool_default id)) :pattern ((fuel_bool id))))))\n\
         (assert (forall ((x Int) (y Int)) (! (= (Sub x y) (- x y)) :pattern ((Sub x y)))))\n\
         (assert (fuel_bool_default fuel%abs))\n\
         (assert (=> (fuel_bool fuel%abs) (forall ((x! Poly)) (! (= (abs? x!) (ite (>= (%I x!) 0) (%I x!) (Sub 0 (%I x!)))) :pattern ((abs? x!))))))\n\
         (assert fuel_defaults)\n\
         (declare-const x! Int)\n\
         (assert (not (>= (abs? (I x!)) 0)))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "unsat");
}

/// #400 — the same-name SAME-sort collision (bound `x!: Poly` vs a
/// later-declared constant `x!: Poly`, the witness being the constant
/// itself). Closed by the unconditional binder alpha-rename.
#[test]
fn same_sort_colliding_const_declared_after_axiom_is_unsat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-sort Poly 0)\n\
         (declare-fun abs? (Poly) Int)\n\
         (declare-fun I (Int) Poly)\n\
         (declare-fun %I (Poly) Int)\n\
         (assert (forall ((x! Poly)) (! (= (abs? x!) (ite (>= (%I x!) 0) (%I x!) (- 0 (%I x!)))) :pattern ((abs? x!)))))\n\
         (declare-const x! Poly)\n\
         (assert (not (>= (abs? x!) 0)))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "unsat");
}
