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
