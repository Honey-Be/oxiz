//! Regression tests for the quantifier / EUF soundness bug fixed alongside
//! adsmt rc.36 — see `docs/QUANTIFIER_EMATCH_SOUNDNESS_BUG.md`.
//!
//! Root cause: when a front-end feeds commands to `Context::execute_script`
//! ONE at a time (streaming stdin, or an embedder replaying commands
//! incrementally), each call built a fresh parser whose declared-function
//! table was empty, so a later `(f 3)` defaulted to `Bool` sort. That broke
//! every theory's reasoning about `f(3)`: `(= (f 3) 3)` and `(= (f 3) 4)`
//! were no longer a contradiction, and quantifier instantiation over `Add`
//! produced inverted verdicts. The fix persists the parser symbol tables
//! across `execute_script` calls (`ParserEnv`), pins distinct integer
//! constants apart in EUF on the equality path, and bounds the MBQI loop.
//!
//! These tests drive the solver the way the bug manifested — command by
//! command — and cross-check the verdict against the SMT-LIB semantics
//! (z3 is the reference oracle for each).

use oxiz_solver::{Context, SolverResult};

/// Feed each command to `execute_script` separately (so the parser symbol
/// tables only survive if they are persisted in the `Context`), returning the
/// final `(check-sat)` verdict.
fn solve_streamed(commands: &[&str]) -> SolverResult {
    let mut ctx = Context::new();
    let mut last = SolverResult::Unknown;
    for cmd in commands {
        let out = ctx.execute_script(cmd).expect("execute_script");
        for line in out {
            match line.as_str() {
                "sat" => last = SolverResult::Sat,
                "unsat" => last = SolverResult::Unsat,
                "unknown" => last = SolverResult::Unknown,
                _ => {}
            }
        }
    }
    last
}

#[test]
fn uf_of_int_equated_to_two_distinct_literals_is_unsat() {
    // f(3)=3 ∧ f(3)=4 — f(3) cannot be both 3 and 4. (z3: unsat.)
    // Pre-fix: `sat`, because per-command parsing gave `f(3)` Bool sort.
    let r = solve_streamed(&[
        "(declare-fun f (Int) Int)",
        "(assert (= (f 3) 3))",
        "(assert (= (f 3) 4))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Unsat, "f(3)=3 ∧ f(3)=4 must be unsat");
}

#[test]
fn uf_of_int_single_equality_is_sat() {
    let r = solve_streamed(&[
        "(declare-fun f (Int) Int)",
        "(assert (= (f 3) 3))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat);
}

#[test]
fn nullary_int_function_equated_to_two_literals_is_unsat() {
    // g = 3 ∧ g = 4 with g : Int (nullary declare-fun → constant). (z3: unsat.)
    let r = solve_streamed(&[
        "(declare-fun g () Int)",
        "(assert (= g 3))",
        "(assert (= g 4))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Unsat);
}

#[test]
fn uf_of_int_two_distinct_args_is_sat() {
    let r = solve_streamed(&[
        "(declare-fun f (Int) Int)",
        "(assert (= (f 3) 3))",
        "(assert (= (f 4) 4))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat);
}

#[test]
fn ematching_pattern_axiom_produces_the_conflict() {
    // ∀a. f(a)=a [:pattern (f a)] ∧ f(3)=4 — the trigger instantiates
    // f(3)=3, contradicting f(3)=4. (z3: unsat.) Pre-fix: `sat`.
    let r = solve_streamed(&[
        "(declare-fun f (Int) Int)",
        "(assert (forall ((a Int)) (! (= (f a) a) :pattern ((f a)))))",
        "(assert (= (f 3) 4))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Unsat, "e-matching must derive f(3)=3");
}

#[test]
fn ematching_pattern_axiom_consistent_instance_is_sat() {
    // ∀a. f(a)=a ∧ f(3)=3 — consistent. (z3: sat.)
    let r = solve_streamed(&[
        "(declare-fun f (Int) Int)",
        "(assert (forall ((a Int)) (! (= (f a) a) :pattern ((f a)))))",
        "(assert (= (f 3) 3))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat);
}

#[test]
fn axiomatized_add_consistent_ground_fact_is_sat() {
    // ∀a b. Add(a,b)=a+b [:pattern (Add a b)] ∧ Add(2,3)=5 — the axiom forces
    // Add(2,3)=2+3=5, consistent with the assertion (z3: sat).
    //
    // Pre-fix this returned the UNSOUND `unsat` (a spurious conflict from the
    // quant+LIA path with `Add` mis-sorted as Bool). With the pattern-guided
    // e-matching path (Phase 1) running to a fixpoint and the model-based
    // enumeration skipping trigger-annotated axioms, it now converges to `sat`
    // the way z3 does — no enumeration blow-up.
    let r = solve_streamed(&[
        "(declare-fun Add (Int Int) Int)",
        "(assert (forall ((a Int) (b Int)) (! (= (Add a b) (+ a b)) :pattern ((Add a b)))))",
        "(assert (= (Add 2 3) 5))",
        "(check-sat)",
    ]);
    assert_eq!(
        r,
        SolverResult::Sat,
        "Add(2,3)=5 is consistent with the axiom"
    );
}

#[test]
fn axiomatized_add_genuine_contradiction_is_unsat() {
    // Add(2,3)=6 contradicts Add(2,3)=2+3=5. (z3: unsat.)
    let r = solve_streamed(&[
        "(declare-fun Add (Int Int) Int)",
        "(assert (forall ((a Int) (b Int)) (! (= (Add a b) (+ a b)) :pattern ((Add a b)))))",
        "(assert (= (Add 2 3) 6))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Unsat);
}

#[test]
fn axiomatized_add_entailment_with_precondition_is_unsat() {
    // The verus-fork repro: y>0 ∧ x≥0 ∧ ¬(Add(x,y)>0) — with Add(x,y)=x+y this
    // is x+y>0 under x≥0, y>0, so the negation is unsat (the goal is entailed).
    // (z3: unsat.) This is the per-subset entailment check the abductive
    // search delegates.
    let r = solve_streamed(&[
        "(declare-fun Add (Int Int) Int)",
        "(assert (forall ((a Int) (b Int)) (! (= (Add a b) (+ a b)) :pattern ((Add a b)))))",
        "(declare-const x Int)",
        "(declare-const y Int)",
        "(assert (> y 0))",
        "(assert (>= x 0))",
        "(assert (not (> (Add x y) 0)))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Unsat);
}

#[test]
fn axiomatized_add_satisfiable_countermodel_is_sat() {
    // y>0 ∧ ¬(Add(x,y)>0) is SAT — x can be ≪ 0, so x+y ≤ 0. This is the
    // abductive search's EMPTY-subset entailment probe (no extra hypothesis):
    // it must NOT report entailment. Pre-fix the model-based MBQI enumerated
    // `Add(v,w)` over the integers without converging (an infinite hang); the
    // pattern-guided path instantiates `Add(x,y)=x+y` once, saturates, and the
    // model is reported `sat` (matching z3) — terminating, and sound.
    let r = solve_streamed(&[
        "(declare-fun Add (Int Int) Int)",
        "(assert (forall ((a Int) (b Int)) (! (= (Add a b) (+ a b)) :pattern ((Add a b)))))",
        "(declare-const x Int)",
        "(declare-const y Int)",
        "(assert (> y 0))",
        "(assert (not (> (Add x y) 0)))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat, "a countermodel exists (x ≪ 0)");
}

// --- Conflict-Driven Quantifier Instantiation (CDQI) ---------------------
// A TRIGGER-FREE universal (no `:pattern`) is handled by the model-based
// path. CDQI instantiates it at terms that ALREADY exist and keeps the
// instance whose body is false under the model — a conflicting instance that
// prunes in one step, without fabricating synthetic domain values.

#[test]
fn existential_is_not_instantiated_as_universal() {
    // SOUNDNESS (#278): an existential must NOT be ground-instantiated like a
    // universal. `∃i.(0≤i≤1 ∧ a(i)=42) ∧ a(0)=42` is SAT (witness i=0), but the
    // engine used to register the `∃` as a `Quant` and emit `Q ⇒ φ[i↦t]` for
    // ground terms `t`; at `t:=42` the guard `0≤42≤1` is false so `Q ⇒ false`
    // = `¬Q` refuted the asserted existential → spurious `unsat`. The engine now
    // skips existentials (sound discharge needs host-side skolemization) and
    // reports the sound `Unknown` — the key invariant is NEVER the spurious
    // `Unsat`. (z3: sat.)
    let r = solve_streamed(&[
        "(declare-fun a (Int) Int)",
        "(assert (exists ((i Int)) (and (>= i 0) (<= i 1) (= (a i) 42))))",
        "(assert (= (a 0) 42))",
        "(check-sat)",
    ]);
    assert_ne!(
        r,
        SolverResult::Unsat,
        "a satisfiable bounded existential must NOT be a spurious Unsat (∃ ≠ ∀)"
    );
}

#[test]
fn bounded_existential_discharged_by_disjunction_is_sat() {
    // COMPLETENESS (#279): a BOUNDED existential is discharged by its exact
    // finite disjunction `Q ⇒ ⋁_{t∈D} φ[i↦t]` over the guard's domain. Here
    // `∃i.(0≤i≤1 ∧ a(i)=42) ∧ a(0)=42` ⇒ `(a(0)=42 ∨ a(1)=42)` is satisfied by
    // a(0)=42 → the witness exists → Sat (not just the sound Unknown). (z3: sat.)
    let r = solve_streamed(&[
        "(declare-fun a (Int) Int)",
        "(assert (exists ((i Int)) (and (>= i 0) (<= i 1) (= (a i) 42))))",
        "(assert (= (a 0) 42))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat, "bounded ∃ disjunction must recover the decisive Sat");
}

#[test]
fn bounded_existential_disjunction_is_complete_for_unsat() {
    // The disjunction is EXACT, so it is complete in BOTH directions: with
    // a(0)≠42 ∧ a(1)≠42 the witness disjunction `(a(0)=42 ∨ a(1)=42)` is
    // refuted → the existential has no witness → Unsat. (z3: unsat.)
    let r = solve_streamed(&[
        "(declare-fun a (Int) Int)",
        "(assert (exists ((i Int)) (and (>= i 0) (<= i 1) (= (a i) 42))))",
        "(assert (not (= (a 0) 42)))",
        "(assert (not (= (a 1) 42)))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Unsat, "the bounded ∃ disjunction must derive the genuine Unsat");
}

#[test]
fn unbounded_existential_stays_sound_unknown() {
    // An UNBOUNDED existential (no finite guard domain) has no finite
    // disjunction, so it emits nothing and stays the sound `Unknown` — never a
    // guessed verdict. `∃i.(a(i)=42) ∧ a(0)=42` is SAT (z3), but the clean
    // engine cannot decide it without skolemization; the invariant is only that
    // it is NOT the spurious Unsat.
    let r = solve_streamed(&[
        "(declare-fun a (Int) Int)",
        "(assert (exists ((i Int)) (= (a i) 42)))",
        "(assert (= (a 0) 42))",
        "(check-sat)",
    ]);
    assert_ne!(r, SolverResult::Unsat, "an unbounded ∃ must stay sound (Unknown), never spurious Unsat");
}

#[test]
fn congruence_axiom_is_recognized_not_instantiated() {
    // #276: the EXPLICIT congruence axiom `∀x,y.(= x y) ⇒ (= (f x) (f y))` is
    // VALID (a function maps equal inputs to equal outputs) and exactly
    // redundant with UF's built-in congruence closure. Instantiating it spirals
    // into an `f`-of-`f` matching loop that OOMs the EUF solver; recognising it
    // as a tautology (skip instantiation) terminates with the correct verdict.
    // Here a=b=c with f/g constrained consistently ⇒ Sat. (z3: sat.)
    let r = solve_streamed(&[
        "(declare-fun f (Int) Int)",
        "(declare-fun g (Int) Int)",
        "(assert (forall ((x Int) (y Int)) (=> (= x y) (= (f x) (f y)))))",
        "(assert (forall ((x Int) (y Int)) (=> (= x y) (= (g x) (g y)))))",
        "(declare-const a Int)",
        "(declare-const b Int)",
        "(assert (= a b))",
        "(assert (= (f a) 42))",
        "(assert (= (g b) 100))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat, "consistent congruence problem must be Sat (no OOM)");
}

#[test]
fn congruence_conflict_still_caught_by_builtin_closure() {
    // Soundness guard: recognising the congruence axiom as valid (and so NOT
    // instantiating it) must NOT hide a genuine congruence conflict — the EUF
    // solver's built-in congruence still forces `f(a)=f(b)` when `a=b`, so
    // `a=b ∧ f(a)=1 ∧ f(b)=2` is Unsat. (z3: unsat.)
    let r = solve_streamed(&[
        "(declare-fun f (Int) Int)",
        "(declare-const a Int)",
        "(declare-const b Int)",
        "(assert (forall ((x Int) (y Int)) (=> (= x y) (= (f x) (f y)))))",
        "(assert (= a b))",
        "(assert (= (f a) 1))",
        "(assert (= (f b) 2))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Unsat, "a=b ∧ f(a)=1 ∧ f(b)=2 is unsat by built-in congruence");
}

#[test]
fn order_transitivity_axiom_is_recognized() {
    // #281: `(f(x)≤f(y) ∧ f(y)≤f(z)) ⇒ f(x)≤f(z)` is VALID (≤ is transitive),
    // so it is recognized as a tautology and not instantiated — terminates with
    // the correct Sat. (z3: sat.)
    let r = solve_streamed(&[
        "(declare-fun f (Int) Int)",
        "(assert (forall ((x Int) (y Int) (z Int)) \
            (=> (and (<= (f x) (f y)) (<= (f y) (f z))) (<= (f x) (f z)))))",
        "(assert (= (f 0) 1))",
        "(assert (= (f 5) 10))",
        "(assert (<= (f 0) (f 5)))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat, "transitivity axiom is valid, must be Sat");
}

#[test]
fn symbolic_bound_guard_resolves_to_a_finite_domain() {
    // #281: a guard `(< i n)` with `(= n 3)` asserted is a bounded `∀` once `n`
    // is resolved — the host substitutes `n ↦ 3`, so `∀i.(0≤i<n ⇒ a(i)≥0)` is
    // instantiated over `[0,2]` and the solver-verified `Saturated` gives Sat.
    // (z3: sat.)
    let r = solve_streamed(&[
        "(declare-fun a (Int) Int)",
        "(declare-const n Int)",
        "(assert (= n 3))",
        "(assert (forall ((i Int)) (=> (and (>= i 0) (< i n)) (>= (a i) 0))))",
        "(assert (= (+ (a 0) (+ (a 1) (a 2))) 10))",
        "(assert (forall ((i Int)) (=> (and (>= i 0) (< i n)) (<= (a i) 5))))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat, "symbolic-bound ∀ (n=3) must resolve + be Sat");
}

#[test]
fn cdqi_finds_a_conflict_at_an_existing_ground_term() {
    // ∀a. f(a)>0 (NO pattern), with the existing ground term f(7) forced to
    // -3. CDQI instantiates at a=7 (an existing term), the body `f(7)>0` is
    // false → conflict → unsat. (z3: unsat.)
    let r = solve_streamed(&[
        "(declare-fun f (Int) Int)",
        "(declare-const c Int)",
        "(assert (forall ((a Int)) (> (f a) 0)))",
        "(assert (= c (f 7)))",
        "(assert (= c (- 3)))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Unsat, "CDQI must instantiate at a=7");
}

#[test]
fn cdqi_no_false_conflict_when_existing_terms_are_consistent() {
    // Same axiom, but f(7)=5 is consistent with ∀a. f(a)>0 — CDQI finds no
    // conflicting instance over the existing terms, so the model stands.
    // (z3: sat.)
    //
    // M3 arithmetic function completion (#260) discharges this: `∀a. f(a)>0` is
    // `f`'s sole universal constraint, the bound var feeds only `f`, the
    // arithmetic-aware oracle confirms the ONE existing ground point f(7)=5
    // satisfies `>0`, and `(> (f a) 0)` is satisfiable for some value — so `f`
    // is completed to a positive constant off that consistent point. The engine
    // skips enumerating it (avoiding the divergent `f`-tower); the completion's
    // witness never crosses into the engine. (z3: sat.)
    let r = solve_streamed(&[
        "(declare-fun f (Int) Int)",
        "(declare-const c Int)",
        "(assert (forall ((a Int)) (> (f a) 0)))",
        "(assert (= c (f 7)))",
        "(assert (= c 5))",
        "(check-sat)",
    ]);
    assert_eq!(
        r,
        SolverResult::Sat,
        "f(7)=5 is consistent with ∀a.f(a)>0 — M3 arithmetic function completion \
         (f ≡ positive constant, existing point verified) makes it Sat"
    );
}

// --- Uninterpreted sort cardinality (verus-fork P0 "Bug A") ---------------

#[test]
fn distinct_over_an_uninterpreted_sort_is_sat() {
    // (declare-sort S 0) has an UNBOUNDED domain, so `(distinct c1 … cN)` over
    // fresh constants is satisfiable for every N. Pre-fix `Context::parse_sort_name`
    // defaulted every unknown sort to `Bool` (a 2-element domain), so 3+ distinct
    // constants were unsat by pigeonhole — a soundness bug that made every Verus
    // prelude sort (FuelId, Height, Poly, …) finite. (z3: sat.)
    let mut cmds: Vec<String> = vec!["(declare-sort S 0)".into()];
    for i in 1..=60 {
        cmds.push(format!("(declare-const c{i} S)"));
    }
    let mut distinct = String::from("(assert (distinct");
    for i in 1..=60 {
        distinct.push_str(&format!(" c{i}"));
    }
    distinct.push_str("))");
    cmds.push(distinct);
    cmds.push("(check-sat)".into());
    let refs: Vec<&str> = cmds.iter().map(String::as_str).collect();
    assert_eq!(
        solve_streamed(&refs),
        SolverResult::Sat,
        "60 distinct constants of an uninterpreted sort are satisfiable"
    );
}

#[test]
fn uninterpreted_function_into_an_uninterpreted_sort_is_unbounded() {
    // `height : Poly -> Height` with three Poly arguments mapped to distinct
    // Height values — satisfiable (the Height domain is unbounded). Exercises
    // a declared sort used as a function RANGE, fed command-by-command.
    let r = solve_streamed(&[
        "(declare-sort Poly 0)",
        "(declare-sort Height 0)",
        "(declare-fun height (Poly) Height)",
        "(declare-const p1 Poly)",
        "(declare-const p2 Poly)",
        "(declare-const p3 Poly)",
        "(assert (distinct (height p1) (height p2) (height p3)))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat);
}

#[test]
fn trigger_free_partial_order_axioms_are_sat() {
    // verus-fork P0 "Bug C": reflexivity of a partial order plus the standard
    // strict-order biconditional, over an UNINTERPRETED sort, with NO
    // `:pattern`. Trivially satisfiable (z3: sat). A regression introduced
    // when pattern-guided e-matching (Phase 1) ran EAGERLY for trigger-free
    // quantifiers too: its auto-generated triggers fired against
    // model-completion witnesses and manufactured an unsound `unsat`. Phase-1
    // e-matching is now gated to EXPLICITLY-triggered quantifiers; trigger-free
    // ones are left to the model-based MBQI (Phase 2).
    let r = solve_streamed(&[
        "(declare-sort Height 0)",
        "(declare-fun height_lt (Height Height) Bool)",
        "(declare-fun partial-order (Height Height) Bool)",
        "(assert (forall ((x Height)) (partial-order x x)))",
        "(assert (forall ((x Height) (y Height)) \
            (= (height_lt x y) (and (partial-order x y) (not (= x y))))))",
        "(check-sat)",
    ]);
    // M3 model completion (#264) now reaches the full `Sat` verdict: `lt`
    // (height_lt) occurs only as the head of its defining biconditional, so it
    // is a conservative DEFINITION (`lt := λx y. po(x,y) ∧ x≠y`); `po`
    // (partial-order) occurs ONLY positively across the (non-definitional)
    // formula, so the model `po ≡ true` satisfies the reflexivity axiom. Both
    // model fragments are independent (distinct symbols), so they compose into
    // one satisfying model — built host-side, no witness crosses into the
    // engine. (z3: sat.)
    assert_eq!(
        r,
        SolverResult::Sat,
        "reflexivity (pure-positive po ≡ true) + strict-order definition (fresh \
         lt) over an uninterpreted sort — M3 model completion makes it Sat"
    );
}

#[test]
fn function_completion_respects_a_second_violating_ground_point() {
    // M3 #260 soundness: `∀a. f(a)>0` with f(7)=5 (ok) AND f(8)=-1 (violates).
    // The arithmetic function-completion recognizer scans EVERY existing
    // `f`-application in the model and arith-folds the body; f(8)=-1 fails `>0`,
    // so it must NOT certify the axiom — enumeration then asserts f(8)>0 and the
    // arithmetic theory refutes it. A spurious `Sat` would mean the verify only
    // checked some points (e.g. relied on CDQI's tuple budget).
    let r = solve_streamed(&[
        "(declare-fun f (Int) Int)",
        "(assert (forall ((a Int)) (> (f a) 0)))",
        "(assert (= (f 7) 5))",
        "(assert (= (f 8) (- 1)))",
        "(check-sat)",
    ]);
    assert_eq!(
        r,
        SolverResult::Unsat,
        "f(8)=-1 violates ∀a.f(a)>0 — the completion verify must scan ALL pinned \
         f-points, not skip the axiom"
    );
}

#[test]
fn function_completion_respects_an_inequality_constrained_ground_point() {
    // M3 #260 soundness REGRESSION (the masked corpus spurious-`sat`,
    // AUFLIRA/auflira_quantified): `∀x. f(x) ≥ 0` with `(< (f 5) 0)`. The
    // refuting point f(5) is constrained by an INEQUALITY, not an equality, so
    // the model's `assign` defaults its value to a poisoned `0` — the original
    // verify scanned `assign` and "confirmed" 0 ≥ 0, certifying the axiom and
    // hiding the conflict (spurious `sat`). The fix verifies against the
    // formula's top-level EQUALITY pins only (never the poisoned model value);
    // f(5) has none, so the axiom is NOT certified and enumeration refutes
    // f(5) ≥ 0 against f(5) < 0. (z3: unsat.)
    let r = solve_streamed(&[
        "(declare-fun f (Int) Int)",
        "(assert (forall ((x Int)) (>= (f x) 0)))",
        "(assert (< (f 5) 0))",
        "(check-sat)",
    ]);
    assert_eq!(
        r,
        SolverResult::Unsat,
        "f(5)<0 refutes ∀x.f(x)≥0 — an inequality-constrained ground point must \
         not be trusted from the poisoned model value"
    );
}

#[test]
fn function_completion_respects_a_chained_inequality_ground_point() {
    // Adversarial sharpening: f(5) is EQUALITY-pinned, but to a constant `d`
    // that is itself only INEQUALITY-constrained (`d < 0`). The pin chain
    // f(5)=d must resolve to a concrete via equalities ALONE — `d` has no
    // equality to a literal, so the value is not faithfully known and the axiom
    // is NOT certified (a model-based resolution of `d` would read the poisoned
    // default 0 and wrongly certify). (z3: unsat.)
    let r = solve_streamed(&[
        "(declare-fun f (Int) Int)",
        "(declare-const d Int)",
        "(assert (forall ((x Int)) (>= (f x) 0)))",
        "(assert (= (f 5) d))",
        "(assert (< d 0))",
        "(check-sat)",
    ]);
    assert_eq!(
        r,
        SolverResult::Unsat,
        "f(5)=d ∧ d<0 refutes ∀x.f(x)≥0 — the pin must resolve through equalities \
         to a literal, never the poisoned model value of d"
    );
}

#[test]
fn function_completion_certifies_through_an_equality_chain() {
    // Completeness companion (no regression): the SAME recognizer must still
    // certify the genuinely-satisfiable axiom when the ground point is pinned to
    // a SATISFYING concrete THROUGH an equality chain `f(7)=c`, `c=5`. Resolving
    // f(7) → c → 5 (≥ 0) lets the constant completion stand. (z3: sat.)
    let r = solve_streamed(&[
        "(declare-fun f (Int) Int)",
        "(declare-const c Int)",
        "(assert (forall ((x Int)) (>= (f x) 0)))",
        "(assert (= (f 7) c))",
        "(assert (= c 5))",
        "(check-sat)",
    ]);
    assert_eq!(
        r,
        SolverResult::Sat,
        "f(7)=c=5 (≥0) is consistent with ∀x.f(x)≥0 — the chained equality pin \
         must still resolve to certify the completion"
    );
}

#[test]
fn definitional_recognizer_does_not_mask_a_ground_contradiction() {
    // M3 soundness guard (#264): the definitional recognizer reports the
    // `height_lt` axiom `Some(true)` (it is a conservative definition), but the
    // ground facts `(po a b)` ∧ `(not (po a b))` are a contradiction INDEPENDENT
    // of that definition. Concluding `Sat` here would be a spurious sat: the
    // SAT/EUF solve must surface the ground `unsat` regardless of the M3
    // certificate for the definitional quantifier.
    let r = solve_streamed(&[
        "(declare-sort S 0)",
        "(declare-fun lt (S S) Bool)",
        "(declare-fun po (S S) Bool)",
        "(declare-const a S)",
        "(declare-const b S)",
        "(assert (forall ((x S) (y S)) (= (lt x y) (and (po x y) (not (= x y))))))",
        "(assert (po a b))",
        "(assert (not (po a b)))",
        "(check-sat)",
    ]);
    assert_eq!(
        r,
        SolverResult::Unsat,
        "a ground contradiction must NOT be masked by the definitional M3 \
         certificate for the (fresh) lt-definition axiom"
    );
}

#[test]
fn pure_polarity_guard_excludes_a_negatively_used_predicate() {
    // M3 soundness guard (#264): `∀x. (po x x)` alone would let the pure-polarity
    // recognizer set `po ≡ true`. But the ground `(not (po a a))` makes `po`
    // occur NEGATIVELY, so it is no longer pure-positive — the recognizer must
    // NOT fire, the reflexivity axiom is enumerated at `a`, and `po(a,a)` clashes
    // with `(not (po a a))` → the sound `Unsat`. A spurious `Sat` here would mean
    // the polarity guard ignored the negative occurrence.
    let r = solve_streamed(&[
        "(declare-sort S 0)",
        "(declare-fun po (S S) Bool)",
        "(declare-const a S)",
        "(assert (forall ((x S)) (po x x)))",
        "(assert (not (po a a)))",
        "(check-sat)",
    ]);
    assert_eq!(
        r,
        SolverResult::Unsat,
        "∀x.po(x,x) ∧ ¬po(a,a) is unsat — the pure-polarity recognizer must not \
         fire when po occurs negatively"
    );
}

#[test]
fn patterned_quantifier_does_not_self_match_its_own_body() {
    // verus-fork P0 "Bug B": the full `charClip`/`charInv`/`bitshr` Unicode-clamp
    // prelude fragment was spuriously `unsat` when fed ONE command at a time
    // (the in-process OxiZ delegation, and the streaming-stdin CLI), while the
    // one-shot batch parse was correctly `sat`.
    //
    // Root cause (engine, grouping-independent): e-matching scanned the WHOLE
    // term pool for trigger candidates — including the quantifier's OWN body
    // subterms. A trigger `(charClip i)` matched the in-body `(charClip i)`,
    // yielding the IDENTITY substitution `{i ↦ i}`; applying it returned the
    // body with `i` still free. Because two `:pattern` quantifiers that reuse
    // the bound-var name `i` hash-cons it to ONE `Var` term, those free vars
    // captured across the two axioms and manufactured a false `unsat`. The
    // verdict's dependence on assertion grouping was a downstream symptom.
    //
    // Fixed by rejecting any e-matching substitution whose range reintroduces a
    // bound variable of the quantifier being instantiated. (z3: does not
    // terminate in 60s — the only sound verdicts are sat/unknown, never unsat.)
    let r = solve_streamed(&[
        "(declare-sort Poly 0)",
        "(declare-fun %I (Poly) Int)",
        "(declare-fun iHi (Int) Int)",
        "(declare-fun charClip (Int) Int)",
        "(declare-fun charInv (Int) Bool)",
        "(declare-fun uClip (Int Int) Int)",
        "(declare-fun uInv (Int Int) Bool)",
        "(declare-fun bitshr (Poly Poly) Int)",
        "(declare-const c1 Int)",
        "(assert (= (iHi 128) 170141183460469231731687303715884105728))",
        "(assert (forall ((i Int)) (! (and \
            (or (and (<= 0 (charClip i)) (<= (charClip i) 55295)) \
                (and (<= 57344 (charClip i)) (<= (charClip i) 1114111))) \
            (=> (or (and (<= 0 i) (<= i 55295)) (and (<= 57344 i) (<= i 1114111))) \
                (= i (charClip i)))) :pattern ((charClip i)))))",
        "(assert (forall ((i Int)) (! (= (charInv i) \
            (or (and (<= 0 i) (<= i 55295)) (and (<= 57344 i) (<= i 1114111)))) \
            :pattern ((charInv i)))))",
        "(assert (forall ((x Poly) (y Poly) (bits Int)) (! \
            (=> (and (uInv bits (%I x)) (<= 0 (%I y))) (uInv bits (bitshr x y))) \
            :pattern ((uClip bits (bitshr x y))))))",
        "(check-sat)",
    ]);
    assert_ne!(
        r,
        SolverResult::Unsat,
        "the Unicode-clamp prelude fragment is satisfiable (z3 agrees it is not unsat)"
    );
}

#[test]
fn patterned_quantifier_still_instantiates_at_real_ground_terms() {
    // Companion to the self-match guard: it must NOT block legitimate ground
    // matches. A `:pattern`-guided `Add` axiom plus a GROUND application
    // `(Add x y)` (over declared constants — internally `Var` terms!) must still
    // e-match and entail the contradiction. Guards against an over-strict
    // `is_ground`-style fix that would drop `{a ↦ x, b ↦ y}`. (z3: unsat.)
    let r = solve_streamed(&[
        "(declare-fun Add (Int Int) Int)",
        "(declare-const x Int)",
        "(declare-const y Int)",
        "(assert (forall ((a Int) (b Int)) \
            (! (= (Add a b) (+ a b)) :pattern ((Add a b)))))",
        "(assert (= (Add x y) 7))",
        "(assert (= (+ x y) 9))",
        "(check-sat)",
    ]);
    assert_eq!(
        r,
        SolverResult::Unsat,
        "Add(x,y)=7 with the axiom Add(a,b)=a+b and x+y=9 is unsat"
    );
}

#[test]
fn trigger_free_quant_over_uninterpreted_sort_is_not_enumerated_into_unsat() {
    // verus-fork P0 "trigger D": a trigger-free definitional axiom over an
    // UNINTERPRETED sort — `∀x y:Height. height_lt(x,y) = (po(x,y) ∧ x≠y)` —
    // combined with two semantically-independent axioms over OTHER sorts (a
    // ground `fuel_bool_default` implication over `FuelId`, and `∀n:Int.
    // ens%false(n)=false`). All satisfiable (z3 does not terminate goal-free,
    // native: unknown — so the only sound verdicts are sat/unknown, never
    // unsat).
    //
    // Pre-fix: `unsat`.  Root cause: MBQI's enumerative instantiator built the
    // candidate domain for the `Height` variables from the model's FABRICATED
    // universe witnesses (`u!0`..`u!7`, minted by model completion), then
    // emitted the whole 8×8 grid of `body[x/u!i, y/u!j]` as hard SAT lemmas.
    // Though each is a sound universal instance, the fabricated grid accumulates
    // (non-monotonically in the count of unrelated ground facts) into a spurious
    // `unsat`.  Fixed by not enumerating over fabricated witnesses for
    // uninterpreted sorts — a genuine refutation still surfaces via the
    // counterexample generator.
    let r = solve_streamed(&[
        "(declare-sort Height 0)",
        "(declare-sort FuelId 0)",
        "(declare-fun height_lt (Height Height) Bool)",
        "(declare-fun partial-order (Height Height) Bool)",
        "(declare-fun fuel_bool_default (FuelId) Bool)",
        "(declare-const f0 FuelId) (declare-const f1 FuelId) (declare-const f2 FuelId)",
        "(declare-fun ens (Int) Bool)",
        "(assert (forall ((x Height) (y Height)) \
            (= (height_lt x y) (and (partial-order x y) (not (= x y))))))",
        "(assert (=> (fuel_bool_default f0) (and (fuel_bool_default f1) (fuel_bool_default f2))))",
        "(assert (forall ((n Int)) (! (= (ens n) false) :pattern ((ens n)))))",
        "(check-sat)",
    ]);
    assert_ne!(
        r,
        SolverResult::Unsat,
        "a trigger-free order definition over an uninterpreted sort must not be \
         enumerated over fabricated witnesses into a spurious unsat"
    );
}

#[test]
fn surjective_unbounded_existential_is_skolemized_to_sat() {
    // Surjectivity-style obligation: a top-level POSITIVE *unbounded* `∃`
    // (`∃y. f(y)=k`) plus a bounded `∀` on `f`'s range. The clean engine never
    // fabricates witnesses, so it would leave the existential `Unknown`;
    // assert-time skolemization replaces each `∃y. φ(y)` with `φ(sk)` for a
    // fresh constant `sk` (equisatisfiable), which IS satisfiable. (z3: sat.)
    let r = solve_streamed(&[
        "(set-logic UFLIA)",
        "(declare-fun f (Int) Int)",
        "(assert (exists ((y1 Int)) (= (f y1) 0)))",
        "(assert (exists ((y2 Int)) (= (f y2) 1)))",
        "(assert (exists ((y3 Int)) (= (f y3) 2)))",
        "(assert (forall ((x Int)) \
            (=> (and (>= x 0) (<= x 10)) (and (>= (f x) 0) (<= (f x) 5)))))",
        "(check-sat)",
    ]);
    assert_eq!(
        r,
        SolverResult::Sat,
        "an unbounded positive ∃ must be skolemized to a witnessable ground fact"
    );
}

#[test]
fn negated_valid_forall_folds_to_unsat() {
    // `(not (forall x. x = x))`. The matrix `x = x` is a reflexivity tautology,
    // so the `∀` is valid — and its negation is therefore unsat. Pre-fix this
    // returned a spurious `sat`: the validity recognizer only ran on the
    // POSITIVE path (the `eval_forall` verdict for an *active* quantifier), and
    // under the `not` the quantifier is asserted false → inactive → never
    // verified. Folding the valid quantifier to `true` up front makes this
    // `(not true)` → `false` → the sound `unsat`. (z3: unsat.)
    let r = solve_streamed(&[
        "(set-logic UFLIA)",
        "(assert (not (forall ((x Int)) (= x x))))",
        "(check-sat)",
    ]);
    assert_eq!(
        r,
        SolverResult::Unsat,
        "the negation of a valid (reflexive) ∀ must be unsat, not spurious sat"
    );
}

#[test]
fn negated_congruence_valid_forall_folds_to_unsat() {
    // `(not (forall x. f(x) = f(x)))` — the matrix is reflexivity over an
    // uninterpreted application, still a tautology, so the `∀` is valid and its
    // negation unsat. Exercises the fold through an uninterpreted-function term
    // (same polarity-independent path as the bare-variable case). (z3: unsat.)
    let r = solve_streamed(&[
        "(set-logic UFLIA)",
        "(declare-fun f (Int) Int)",
        "(assert (not (forall ((x Int)) (= (f x) (f x)))))",
        "(check-sat)",
    ]);
    assert_eq!(
        r,
        SolverResult::Unsat,
        "the negation of a valid ∀ over an uninterpreted application must be unsat"
    );
}

#[test]
fn negated_existential_with_ground_witness_is_unsat_via_nnf() {
    // `(not (exists y. (= (f y) 0)))` with `(= (f 5) 0)` asserted. The negated
    // existential is the CONTINGENT universal `forall y. f(y) != 0` — unsat only
    // via the ground fact f(5)=0, NOT a tautology, so no validity recognizer
    // catches it. Pre-fix it was a spurious `sat`: `collect_quants` recorded the
    // negated `exists` SYNTACTICALLY as an (inactive) existential and never
    // instantiated it. NNF (push the negation in: `not(exists) -> forall(not)`)
    // turns it into a positive universal the engine ENUMERATES at the ground
    // term 5 -> `f(5) != 0` -> conflict with `f(5)=0`. (z3: unsat.)
    let r = solve_streamed(&[
        "(set-logic UFLIA)",
        "(declare-fun f (Int) Int)",
        "(assert (not (exists ((y Int)) (= (f y) 0))))",
        "(assert (= (f 5) 0))",
        "(check-sat)",
    ]);
    assert_eq!(
        r,
        SolverResult::Unsat,
        "a negated existential refuted by a ground witness must be unsat, not spurious sat"
    );
}

#[test]
fn negated_existential_consistent_is_not_unsat() {
    // The soundness control for the case above: same shape but CONSISTENT
    // (`f(5)=1`, never 0). `forall y. f(y) != 0` together with `f(5)=1` is
    // satisfiable, so the verdict must be sat or the sound Unknown — NEVER a
    // spurious unsat from over-eager NNF instantiation. (z3: sat.)
    let r = solve_streamed(&[
        "(set-logic UFLIA)",
        "(declare-fun f (Int) Int)",
        "(assert (not (exists ((y Int)) (= (f y) 0))))",
        "(assert (= (f 5) 1))",
        "(check-sat)",
    ]);
    assert_ne!(
        r,
        SolverResult::Unsat,
        "a consistent negated existential must not be driven to a spurious unsat"
    );
}

#[test]
fn forall_exists_skolemized_to_a_function_is_sat() {
    // `∀x. ∃y. f(x,y) > 0` with ground anchors. Skolemization lowers the nested
    // `∃y` to a fresh unary Skolem FUNCTION of the enclosing universal x:
    // `∀x. f(x, sk(x)) > 0`. The engine instantiates that pure universal over
    // the ground anchors and the model completion verifies it satisfiable —
    // where the un-Skolemized `∀∃` was left Unknown (no witness to fabricate).
    // (z3: sat.)
    let r = solve_streamed(&[
        "(set-logic UFLIA)",
        "(declare-fun f (Int Int) Int)",
        "(assert (forall ((x Int)) (exists ((y Int)) (> (f x y) 0))))",
        "(assert (= (f 0 0) 1))",
        "(assert (= (f 1 1) 2))",
        "(check-sat)",
    ]);
    assert_eq!(
        r,
        SolverResult::Sat,
        "a ∀∃ with ground anchors must verify sat after Skolem-function lowering"
    );
}

#[test]
fn skolemized_forall_exists_unsat_is_never_spurious_sat() {
    // Soundness control: `∀x.∃y.f(x,y)>0` ∧ `∀x,y.f(x,y)≤0` is unsat, but with
    // NO ground constant to anchor enumeration the never-fabricate engine cannot
    // reach the conflict — the only sound verdicts are unsat or Unknown. The
    // Skolem-function lowering must never turn it into a spurious `sat`.
    let r = solve_streamed(&[
        "(set-logic UFLIA)",
        "(declare-fun f (Int Int) Int)",
        "(assert (forall ((x Int)) (exists ((y Int)) (> (f x y) 0))))",
        "(assert (forall ((x Int) (y Int)) (<= (f x y) 0)))",
        "(check-sat)",
    ]);
    assert_ne!(r, SolverResult::Sat, "an unsat ∀∃ must not be Skolemized into a spurious sat");
}

#[test]
fn monotone_affine_implication_is_valid_sat() {
    // `∀x,y. x≤y ⇒ (2x+1) ≤ (2y+1)` is VALID in every interpretation because
    // `2x+1` is monotone increasing — the monotonicity KB certifies the affine
    // form (scale by +2, add a constant), so the engine reports sat without any
    // model search. (z3: sat.)
    let r = solve_streamed(&[
        "(set-logic UFLRA)",
        "(assert (forall ((x Real) (y Real)) \
            (=> (<= x y) (<= (+ (* 2.0 x) 1.0) (+ (* 2.0 y) 1.0)))))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat, "an affine-monotone implication is a valid tautology → sat");
}

#[test]
fn anti_monotone_implication_is_not_certified_sat() {
    // Soundness: `∀x,y. x≤y ⇒ -x ≤ -y` is NOT valid (`-x` is DECREASING). The
    // certifier must NOT certify it — the only sound verdicts are unsat or
    // Unknown, never a spurious sat from a wrong-direction monotonicity claim.
    let r = solve_streamed(&[
        "(set-logic UFLIA)",
        "(assert (forall ((x Int) (y Int)) (=> (<= x y) (<= (- 0 x) (- 0 y)))))",
        "(check-sat)",
    ]);
    assert_ne!(r, SolverResult::Sat, "a wrong-direction monotonicity claim must not be certified sat");
}

#[test]
fn nonlinear_square_implication_is_not_certified_sat() {
    // Soundness: `∀x,y. x≤y ⇒ x² ≤ y²` is NOT valid (false for x=-2,y=1). The
    // certifier returns None for `x*x` (two var factors), so it is never
    // certified — sound Unknown/unsat, never spurious sat.
    let r = solve_streamed(&[
        "(set-logic UFLIA)",
        "(assert (forall ((x Int) (y Int)) (=> (<= x y) (<= (* x x) (* y y)))))",
        "(check-sat)",
    ]);
    assert_ne!(r, SolverResult::Sat, "a non-monotone square must not be certified sat");
}

#[test]
fn monotone_uninterpreted_with_consistent_points_is_sat() {
    // `∀x,y. x≤y ⇒ f(x)≤f(y)` over an UNINTERPRETED f, with ground points (and an
    // interval `30 ≤ f(5) ≤ 70`) that admit a monotone extension. The
    // order-extension recognizer checks the points are monotone-feasible (a
    // monotone total f exists), so the engine reports sat without a model search.
    // (z3: sat.)
    let r = solve_streamed(&[
        "(set-logic UFLIA)",
        "(declare-fun f (Int) Int)",
        "(assert (forall ((x Int) (y Int)) (=> (<= x y) (<= (f x) (f y)))))",
        "(assert (= (f 0) 0))",
        "(assert (= (f 10) 100))",
        "(assert (>= (f 5) 30))",
        "(assert (<= (f 5) 70))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat, "a monotone-feasible partial f extends to a monotone total f");
}

#[test]
fn monotone_violated_by_ground_points_is_unsat() {
    // Soundness: `∀x,y. x≤y ⇒ f(x)≤f(y)` with `f(0)=5`, `f(10)=3` — 0≤10 but 5>3,
    // so NO monotone extension exists. The recognizer must decline (the points
    // are infeasible); the engine then instantiates the axiom at 0,10 →
    // `f(0)≤f(10)` → `5≤3` → unsat. Never a spurious sat. (z3: unsat.)
    let r = solve_streamed(&[
        "(set-logic UFLIA)",
        "(declare-fun f (Int) Int)",
        "(assert (forall ((x Int) (y Int)) (=> (<= x y) (<= (f x) (f y)))))",
        "(assert (= (f 0) 5))",
        "(assert (= (f 10) 3))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Unsat, "monotone-violating ground points are unsat");
}

#[test]
fn monotone_with_unaccounted_constraint_is_not_certified_sat() {
    // Soundness (the accounting guard): the same monotone axiom, but `f(5)` is
    // ALSO constrained inside an arithmetic term `(* 2 (f 5)) = 60` the
    // order-extension cannot model. The guard (every f-application must be the
    // axiom or a handled bound) fails, so the recognizer declines → the sound
    // Unknown, never a guessed sat from an incompletely-modeled `f`.
    let r = solve_streamed(&[
        "(set-logic UFLIA)",
        "(declare-fun f (Int) Int)",
        "(assert (forall ((x Int) (y Int)) (=> (<= x y) (<= (f x) (f y)))))",
        "(assert (= (f 0) 0))",
        "(assert (= (* 2 (f 5)) 60))",
        "(check-sat)",
    ]);
    assert_ne!(r, SolverResult::Sat, "an unaccounted f-constraint must block the order-extension sat");
}

#[test]
fn idempotent_with_consistent_fixed_points_is_sat() {
    // `∀x. f(f(x)) = f(x)` with idempotency-consistent ground facts: every pinned
    // value is its own fixed point (`f(0)=5` and `f(5)=5`; `f(3)=3`). An
    // idempotent total model exists (identity off these points), so it is sat.
    // (z3: sat.)
    let r = solve_streamed(&[
        "(set-logic UFLIA)",
        "(declare-fun f (Int) Int)",
        "(assert (forall ((x Int)) (= (f (f x)) (f x))))",
        "(assert (= (f 0) 5))",
        "(assert (= (f 5) 5))",
        "(assert (= (f 3) 3))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat, "an idempotency-consistent partial f extends to an idempotent total f");
}

#[test]
fn idempotent_violated_is_unsat() {
    // Soundness: `f(0)=5` with `f(5)=7` violates idempotency
    // (`f(f(0)) = f(5) = 7 ≠ 5 = f(0)`). The recognizer must decline; the engine
    // instantiates the axiom at 0 → `f(5)=f(0)=5` → conflicts with `f(5)=7` →
    // unsat. Never a spurious sat. (z3: unsat.)
    let r = solve_streamed(&[
        "(set-logic UFLIA)",
        "(declare-fun f (Int) Int)",
        "(assert (forall ((x Int)) (= (f (f x)) (f x))))",
        "(assert (= (f 0) 5))",
        "(assert (= (f 5) 7))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Unsat, "an idempotency-violating ground point is unsat");
}

#[test]
fn array_extensionality_premise_with_equal_arrays_is_sat() {
    // `∀i. select(a,i) = select(b,i)` is a congruence consequence of `a = b`, so
    // asserting both is satisfiable (the universal is automatically satisfied).
    // (z3: sat.)
    let r = solve_streamed(&[
        "(set-logic AUFLIA)",
        "(declare-const a (Array Int Int))",
        "(declare-const b (Array Int Int))",
        "(assert (forall ((i Int)) (= (select a i) (select b i))))",
        "(assert (= a b))",
        "(assert (= (select a 0) 10))",
        "(assert (= (select b 0) 10))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat, "the extensionality premise is entailed by a=b");
}

#[test]
fn array_read_over_write_with_store_is_sat() {
    // `∀i. i≠k ⇒ select(b,i)=select(a,i)` is the read-over-write axiom, entailed
    // by `b = store(a,k,v)`. (z3: sat.)
    let r = solve_streamed(&[
        "(set-logic AUFLIA)",
        "(declare-const a (Array Int Int))",
        "(declare-const b (Array Int Int))",
        "(declare-const k Int)",
        "(declare-const v Int)",
        "(assert (= b (store a k v)))",
        "(assert (= k 3))",
        "(assert (= v 99))",
        "(assert (forall ((i Int)) (=> (not (= i k)) (= (select b i) (select a i)))))",
        "(assert (= (select b k) v))",
        "(assert (= (select a 0) 10))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat, "read-over-write is entailed by b=store(a,k,v)");
}

#[test]
fn array_extensionality_without_array_equality_is_not_spurious_sat() {
    // Soundness: `∀i. select(a,i)=select(b,i)` WITHOUT `a=b`, where `a` and `b`
    // disagree at index 0 — the recognizer must decline (no array equality), and
    // the engine instantiates at 0 → `10 = 20` → unsat. Never a spurious sat.
    let r = solve_streamed(&[
        "(set-logic AUFLIA)",
        "(declare-const a (Array Int Int))",
        "(declare-const b (Array Int Int))",
        "(assert (forall ((i Int)) (= (select a i) (select b i))))",
        "(assert (= (select a 0) 10))",
        "(assert (= (select b 0) 20))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Unsat, "extensionality with disagreeing arrays and no a=b is unsat");
}

#[test]
fn skolem_existential_inside_universal_eq_is_sat() {
    // `∀x. ∃y. g(x)=f(y)` skolemizes to `∀x. g(x)=f(sk(x))`. With ground
    // g(0)=10, g(1)=20, f(5)=10, f(7)=20, a witness exists (sk(0)=5, sk(1)=7),
    // and for any other x a fresh preimage can be minted. The fresh-Skolem
    // equality-witness recognizer certifies it. (z3: sat.)
    let r = solve_streamed(&[
        "(set-logic UFLIA)",
        "(declare-fun f (Int) Int)",
        "(declare-fun g (Int) Int)",
        "(assert (forall ((x Int)) (exists ((y Int)) (= (g x) (f y)))))",
        "(assert (= (g 0) 10))",
        "(assert (= (g 1) 20))",
        "(assert (= (f 5) 10))",
        "(assert (= (f 7) 20))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat, "skolemized ∀x.∃y.g(x)=f(y) is sat");
}

#[test]
fn skolem_witness_blocked_by_universal_f_bound_is_not_spurious_sat() {
    // Soundness control: the SAME `∀x.∃y.g(x)=f(y)` but now `f` is ALSO bounded
    // universally (`∀y. f(y) ≤ 5`) while `g(0)=10`. The witness needs f(·)=10 > 5
    // — UNSAT. `f` then appears in TWO quantifiers, so the recognizer's
    // `quant_count[f]==1` gate DECLINES (the universal bound could forbid the
    // witness it would otherwise assume free). The clean engine must NOT report
    // a spurious `sat`. (z3: unsat → clean engine: sound `unknown`/`unsat`.)
    let r = solve_streamed(&[
        "(set-logic UFLIA)",
        "(declare-fun f (Int) Int)",
        "(declare-fun g (Int) Int)",
        "(assert (forall ((x Int)) (exists ((y Int)) (= (g x) (f y)))))",
        "(assert (forall ((y Int)) (<= (f y) 5)))",
        "(assert (= (g 0) 10))",
        "(check-sat)",
    ]);
    assert_ne!(r, SolverResult::Sat, "f universally bounded below the witness must not be spurious sat");
}

#[test]
fn real_bounded_function_unit_interval_is_sat() {
    // `∀x. 0 ≤ f(x) ≤ 1` with ground points all inside [0,1]. The constant
    // range-completion recognizer completes `f` to a constant in [0,1] off the
    // ground points. (z3: sat; corpus `real_bounds.smt2`.)
    let r = solve_streamed(&[
        "(set-logic UFLRA)",
        "(declare-fun f (Real) Real)",
        "(assert (forall ((x Real)) (and (>= (f x) 0.0) (<= (f x) 1.0))))",
        "(assert (= (f 0.0) 0.5))",
        "(assert (= (f 1.0) 0.75))",
        "(assert (= (f (- 1.0)) 0.25))",
        "(assert (<= (+ (f 0.0) (+ (f 1.0) (f (- 1.0)))) 3.0))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat, "∀x.0≤f(x)≤1 with in-range ground points is sat");
}

#[test]
fn real_range_completion_with_out_of_range_ground_point_is_not_spurious_sat() {
    // Soundness control: `∀x. 0 ≤ f(x) ≤ 1` but `f(0)=5` — the universal at x=0
    // demands 5 ≤ 1, UNSAT. The recognizer VERIFIES the ground point (5 ∉ [0,1])
    // and declines; the engine instantiates at 0 and refutes. Never spurious sat.
    let r = solve_streamed(&[
        "(set-logic UFLRA)",
        "(declare-fun f (Real) Real)",
        "(assert (forall ((x Real)) (and (>= (f x) 0.0) (<= (f x) 1.0))))",
        "(assert (= (f 0.0) 5.0))",
        "(check-sat)",
    ]);
    assert_ne!(r, SolverResult::Sat, "an out-of-range ground point must not be spurious sat");
}

#[test]
fn int_range_completion_two_sided_bound_is_sat() {
    // The same range completion over Int: `∀x. 1 ≤ f(x) ≤ 3`, in-range ground.
    let r = solve_streamed(&[
        "(set-logic UFLIA)",
        "(declare-fun f (Int) Int)",
        "(assert (forall ((x Int)) (and (>= (f x) 1) (<= (f x) 3))))",
        "(assert (= (f 0) 2))",
        "(assert (= (f 7) 3))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat, "∀x.1≤f(x)≤3 with in-range ground points is sat");
}

#[test]
fn int_function_completion_with_symbolic_point_is_not_spurious_sat() {
    // Soundness control (the Int analog of `real_unsat`): `∀x. f(x) ≤ 1` with a
    // SYMBOLIC application `f(c) > 1` for a free constant `c`. The universal at
    // x=c forces f(c) ≤ 1, contradicting f(c) > 1 — UNSAT. `f(c)` is not a
    // literal ground point, so the single-function completion's accounting guard
    // (body f(x̄) + literal points ≠ all occurrences) DECLINES. Never spurious sat.
    let r = solve_streamed(&[
        "(set-logic UFLIA)",
        "(declare-fun f (Int) Int)",
        "(declare-const c Int)",
        "(assert (forall ((x Int)) (<= (f x) 1)))",
        "(assert (> (f c) 1))",
        "(check-sat)",
    ]);
    assert_ne!(r, SolverResult::Sat, "a symbolic out-of-bound f-application must not be spurious sat");
}

#[test]
fn bounded_oscillation_lipschitz_is_sat() {
    // `∀x,y∈[0,5]. |f(x)-f(y)| ≤ 10` with pinned f(0)=0, f(1)=1.5, f(3)=4
    // (spread 4 ≤ 10). The constant default δ=min satisfies it. (z3: sat;
    // corpus `real_lipschitz.smt2`.)
    let r = solve_streamed(&[
        "(set-logic UFLRA)",
        "(declare-fun f (Real) Real)",
        "(assert (forall ((x Real) (y Real))
           (=> (and (>= x 0.0) (<= x 5.0) (>= y 0.0) (<= y 5.0))
               (and (<= (- (f x) (f y)) 10.0) (<= (- (f y) (f x)) 10.0)))))",
        "(assert (= (f 0.0) 0.0))",
        "(assert (= (f 1.0) 1.5))",
        "(assert (= (f 3.0) 4.0))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat, "Lipschitz with in-window pinned values is sat");
}

#[test]
fn bounded_oscillation_violated_spread_is_not_spurious_sat() {
    // Soundness control: the same shape but pinned f(0)=0, f(1)=100 — spread
    // 100 > 10, so the universal at (0,1) forces 100 ≤ 10, UNSAT. The recognizer
    // sees max-min=100 > 10 and DECLINES; the engine instantiates and refutes.
    let r = solve_streamed(&[
        "(set-logic UFLRA)",
        "(declare-fun f (Real) Real)",
        "(assert (forall ((x Real) (y Real))
           (=> (and (>= x 0.0) (<= x 5.0) (>= y 0.0) (<= y 5.0))
               (and (<= (- (f x) (f y)) 10.0) (<= (- (f y) (f x)) 10.0)))))",
        "(assert (= (f 0.0) 0.0))",
        "(assert (= (f 1.0) 100.0))",
        "(check-sat)",
    ]);
    assert_ne!(r, SolverResult::Sat, "an oscillation-violating pinned pair must not be spurious sat");
}

#[test]
fn archimedean_var_relative_bound_is_sat() {
    // `∀r∈[0,10]. ceil(r) ≥ r` with ceil(3.7)=4, ceil(0)=0. The identity default
    // ceil(r):=r satisfies r≥r; pinned points verified (4≥3.7, 0≥0). (z3: sat;
    // corpus `real_archimedean.smt2`.)
    let r = solve_streamed(&[
        "(set-logic UFLRA)",
        "(declare-fun ceil (Real) Real)",
        "(assert (forall ((r Real))
           (=> (and (>= r 0.0) (<= r 10.0)) (>= (ceil r) r))))",
        "(assert (= (ceil 3.7) 4.0))",
        "(assert (= (ceil 0.0) 0.0))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat, "∀r∈[0,10].ceil(r)≥r with consistent pins is sat");
}

#[test]
fn var_relative_bound_violated_pin_is_not_spurious_sat() {
    // Soundness control: `∀r∈[0,10]. f(r) ≥ r` but f(5)=3 — at r=5, 3≥5 is false,
    // UNSAT. The recognizer verifies the pin (3≥5 fails) and DECLINES; the engine
    // instantiates at 5 and refutes. Never spurious sat.
    let r = solve_streamed(&[
        "(set-logic UFLRA)",
        "(declare-fun f (Real) Real)",
        "(assert (forall ((r Real))
           (=> (and (>= r 0.0) (<= r 10.0)) (>= (f r) r))))",
        "(assert (= (f 5.0) 3.0))",
        "(check-sat)",
    ]);
    assert_ne!(r, SolverResult::Sat, "a pin below the identity bound must not be spurious sat");
}

#[test]
fn commuting_functions_identity_collapse_is_sat() {
    // `∀x∈[0,5]. f(g(x))=g(f(x))` with f,g pinned-agreeing on 0,1,2. The g≡f
    // collapse satisfies commutativity structurally. (z3: sat; corpus
    // `real_composition.smt2`.)
    let r = solve_streamed(&[
        "(set-logic UFLRA)",
        "(declare-fun f (Real) Real)",
        "(declare-fun g (Real) Real)",
        "(assert (forall ((x Real))
           (=> (and (>= x 0.0) (<= x 5.0)) (= (f (g x)) (g (f x))))))",
        "(assert (= (f 0.0) 0.0))",
        "(assert (= (g 0.0) 0.0))",
        "(assert (= (f 1.0) 1.0))",
        "(assert (= (g 1.0) 1.0))",
        "(assert (= (f 2.0) 2.0))",
        "(assert (= (g 2.0) 2.0))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat, "commuting functions with agreeing pins is sat");
}

#[test]
fn commuting_functions_contradictory_pins_is_not_spurious_sat() {
    // Soundness control: `∀x∈[0,5]. f(g(x))=g(f(x))` with f(0)=1, g(0)=0, g(1)=2.
    // At x=0: f(g(0))=f(0)=1, g(f(0))=g(1)=2 → 1=2, UNSAT. f and g disagree at 0
    // (f(0)=1, g(0)=0) so the collapse DECLINES; the engine instantiates and
    // refutes. Never spurious sat.
    let r = solve_streamed(&[
        "(set-logic UFLRA)",
        "(declare-fun f (Real) Real)",
        "(declare-fun g (Real) Real)",
        "(assert (forall ((x Real))
           (=> (and (>= x 0.0) (<= x 5.0)) (= (f (g x)) (g (f x))))))",
        "(assert (= (f 0.0) 1.0))",
        "(assert (= (g 0.0) 0.0))",
        "(assert (= (g 1.0) 2.0))",
        "(check-sat)",
    ]);
    assert_ne!(r, SolverResult::Sat, "contradictory commuting-function pins must not be spurious sat");
}

#[test]
fn layered_bounds_interp_is_sat() {
    // §3.5 multi-axiom: f sign-bounded (≥0 on x≥0), f ≤ g on [0,10], g=2x+1 on
    // [0,10]. The layered model f≡0, g≡2x+1 is feasible (0 ≤ 2x+1 on [0,10]).
    // (z3: sat; corpus `real_interp.smt2`.)
    let r = solve_streamed(&[
        "(set-logic UFLRA)",
        "(declare-fun f (Real) Real)",
        "(declare-fun g (Real) Real)",
        "(assert (forall ((x Real)) (=> (>= x 0.0) (>= (f x) 0.0))))",
        "(assert (forall ((x Real)) (=> (and (>= x 0.0) (<= x 10.0)) (<= (f x) (g x)))))",
        "(assert (forall ((x Real)) (=> (and (>= x 0.0) (<= x 10.0)) (= (g x) (+ (* 2.0 x) 1.0)))))",
        "(assert (= (f 0.0) 0.5))",
        "(assert (= (f 5.0) 8.0))",
        "(assert (= (g 0.0) 1.0))",
        "(assert (= (g 5.0) 11.0))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat, "layered f≤g=2x+1, f≥0 is sat");
}

#[test]
fn layered_bounds_infeasible_negative_affine_is_not_spurious_sat() {
    // Soundness control: same layering but g=2x-15 on [0,10] — at x=0, g(0)=-15,
    // so 0 ≤ f(0) ≤ -15 is impossible, UNSAT. The recognizer computes the affine
    // min (-15) < L (0) and DECLINES; the engine instantiates and refutes.
    let r = solve_streamed(&[
        "(set-logic UFLRA)",
        "(declare-fun f (Real) Real)",
        "(declare-fun g (Real) Real)",
        "(assert (forall ((x Real)) (=> (>= x 0.0) (>= (f x) 0.0))))",
        "(assert (forall ((x Real)) (=> (and (>= x 0.0) (<= x 10.0)) (<= (f x) (g x)))))",
        "(assert (forall ((x Real)) (=> (and (>= x 0.0) (<= x 10.0)) (= (g x) (- (* 2.0 x) 15.0)))))",
        "(check-sat)",
    ]);
    assert_ne!(r, SolverResult::Sat, "infeasible negative-affine layering must not be spurious sat");
}

#[test]
fn real_fixed_point_skolem_witness_is_sat() {
    // `∀x∈[0,1]. 0≤f(x)≤1` (guarded range) + `∃x∈[0,1]. f(x)=x` + f(0.5)=0.5.
    // The ∃ skolemizes to f(sk)=sk, sk∈[0,1] — an IN-RANGE fixed-point point that
    // the guard-aware range completion now tolerates. (z3: sat; corpus
    // `real_fixed_point.smt2`.)
    let r = solve_streamed(&[
        "(set-logic UFLRA)",
        "(declare-fun f (Real) Real)",
        "(assert (forall ((x Real)) (=> (and (>= x 0.0) (<= x 1.0)) (and (>= (f x) 0.0) (<= (f x) 1.0)))))",
        "(assert (exists ((x Real)) (and (>= x 0.0) (<= x 1.0) (= (f x) x))))",
        "(assert (= (f 0.5) 0.5))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat, "bounded range + in-range fixed-point ∃ is sat");
}

#[test]
fn skolem_fixed_point_out_of_range_is_not_spurious_sat() {
    // Soundness control: UNGUARDED `∀x. 0≤f(x)≤1` so f maps ALL reals into [0,1],
    // plus `∃x≥2. f(x)=x` → f(sk)=sk≥2 but f(sk)≤1 — UNSAT. The fixed-point fold
    // [0,1]∩[2,∞)=∅ makes range completion DECLINE; the engine refutes.
    let r = solve_streamed(&[
        "(set-logic UFLRA)",
        "(declare-fun f (Real) Real)",
        "(assert (forall ((x Real)) (and (>= (f x) 0.0) (<= (f x) 1.0))))",
        "(assert (exists ((x Real)) (and (>= x 2.0) (= (f x) x))))",
        "(check-sat)",
    ]);
    assert_ne!(r, SolverResult::Sat, "an out-of-range fixed-point witness must not be spurious sat");
}

#[test]
fn nested_forall_exists_forall_threshold_is_sat() {
    // `∀x.∃y.∀z. (z≥y ⇒ f(x,z)≥0)` (triple-nested). Skolemizes the ∃y to a fresh
    // threshold sk(x), leaving `∀x,z. (z≥sk(x) ⇒ f(x,z)≥0)`. The fresh threshold
    // can be pushed above all ground points (incl. f(0,0)=-1), so the axiom is
    // vacuous there and free above. (z3: sat; corpus `nested_quantifiers.smt2`.)
    let r = solve_streamed(&[
        "(set-logic UFLIA)",
        "(declare-fun f (Int Int) Int)",
        "(assert (forall ((x Int)) (exists ((y Int)) (forall ((z Int))
           (=> (>= z y) (>= (f x z) 0))))))",
        "(assert (= (f 0 0) (- 1)))",
        "(assert (= (f 0 5) 10))",
        "(assert (= (f 0 6) 12))",
        "(assert (= (f 1 3) 7))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat, "nested ∀∃∀ threshold guard with a negative low point is sat");
}

#[test]
fn nested_threshold_infeasible_consequent_is_not_spurious_sat() {
    // Soundness control: the consequent `f(x,z)≥0 ∧ f(x,z)≤-1` is infeasible, so
    // `z≥y ⇒ ψ` collapses to `z<y` and `∀z. z<y` is false — UNSAT. The recognizer
    // sees the empty ψ-interval and DECLINES (never spurious sat).
    let r = solve_streamed(&[
        "(set-logic UFLIA)",
        "(declare-fun f (Int Int) Int)",
        "(assert (forall ((x Int)) (exists ((y Int)) (forall ((z Int))
           (=> (>= z y) (and (>= (f x z) 0) (<= (f x z) (- 1))))))))",
        "(check-sat)",
    ]);
    assert_ne!(r, SolverResult::Sat, "an infeasible threshold consequent must not be spurious sat");
}
