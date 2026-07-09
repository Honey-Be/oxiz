#!/usr/bin/env python3
"""Pure-SAT differential fuzz harness — extended.

Differences from sat_diff_fuzz.py:
  * Drives the PURE oxiz-sat engine directly via the `pure_sat_runner` example
    (env OXIZ_PURE), NOT `oxiz --dimacs` (which routes CNF through the SMT/theory
    CDCL layer). This is what actually audits the 38k-line oxiz-sat core.
  * Adds CNF families that stress the advanced/soundness-risky features:
      - XOR / parity constraints (Tseitin-expanded), to exercise XOR reasoning
        and produce resolution-hard learning.
      - graph k-colouring (resolution-hard; learning + inprocessing).
      - larger pigeonhole.
      - randomised-XOR-over-3SAT mixes.
  * Sweeps a SolverConfig preset (env OXIZ_SAT_PRESET) so inprocessing / LRB /
    CHB branching code paths get exercised.
  * On SAT, the runner self-validates the model; a `s MODEL-INVALID` line is an
    unsound-SAT detected without any oracle.

Env: OXIZ_PURE (path to pure_sat_runner), SATFUZZ_N, SATFUZZ_SEED,
     OXIZ_SAT_PRESET (passed through to the runner).
"""
import os, random, subprocess, sys, tempfile

OXIZ_PURE = os.environ.get("OXIZ_PURE", "./target/debug/examples/pure_sat_runner")
N = int(os.environ.get("SATFUZZ_N", "2000"))
_seed_raw = os.environ.get("SATFUZZ_SEED", "12648430")
SEED = int(_seed_raw, 0) if _seed_raw.startswith("0x") else int(_seed_raw)


def cnf_text(nv, clauses):
    out = [f"p cnf {nv} {len(clauses)}"]
    for c in clauses:
        out.append(" ".join(str(l) for l in c) + " 0")
    return "\n".join(out) + "\n"


def run(cmd, text, timeout=15, env=None):
    try:
        with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as f:
            f.write(text)
            path = f.name
        e = dict(os.environ)
        if env:
            e.update(env)
        r = subprocess.run(cmd + [path], capture_output=True, text=True,
                           timeout=timeout, env=e)
        os.unlink(path)
        return r.stdout + "\n" + r.stderr
    except Exception:
        return ""


def verdict(out):
    for ln in out.splitlines():
        s = ln.strip()
        if s == "s MODEL-INVALID":
            return "model-invalid"
        if s == "sat" or s.startswith("s SATISFIABLE"):
            return "sat"
        if s == "unsat" or s.startswith("s UNSATISFIABLE"):
            return "unsat"
    return "unknown"


def solve_oxiz(text, preset=None):
    env = {"OXIZ_SAT_PRESET": preset} if preset else None
    return verdict(run([OXIZ_PURE], text, env=env))


def solve_cadical(text):
    return verdict(run(["cadical", "-q"], text))


def solve_z3(text):
    return verdict(run(["z3", "-dimacs", "-T:12"], text))


def solve_cms(text):
    return verdict(run(["cryptominisat5", "--verb=0"], text))


# ----------------------------------------------------------------------------
# generators
# ----------------------------------------------------------------------------
def gen_3sat(rng, nv, ratio):
    m = int(nv * ratio)
    clauses = []
    for _ in range(m):
        c = set()
        while len(c) < 3:
            v = rng.randint(1, nv)
            c.add(v if rng.random() < 0.5 else -v)
        clauses.append(list(c))
    return nv, clauses


def gen_ksat(rng, nv, ratio, k):
    m = int(nv * ratio)
    clauses = []
    for _ in range(m):
        c = set()
        kk = min(k, nv)
        while len(c) < kk:
            v = rng.randint(1, nv)
            c.add(v if rng.random() < 0.5 else -v)
        clauses.append(list(c))
    return nv, clauses


def gen_php(n):
    pigeons, holes = n + 1, n

    def var(p, h):
        return p * holes + h + 1

    nv = pigeons * holes
    clauses = []
    for p in range(pigeons):
        clauses.append([var(p, h) for h in range(holes)])
    for h in range(holes):
        for p1 in range(pigeons):
            for p2 in range(p1 + 1, pigeons):
                clauses.append([-var(p1, h), -var(p2, h)])
    return nv, clauses


def xor_clauses(lits, rhs):
    """CNF for (l1 XOR l2 XOR ... XOR lk) == rhs.  lits are signed ints (vars).
    Expands to 2^(k-1) clauses — keep k small (<=5)."""
    k = len(lits)
    clauses = []
    for mask in range(1 << k):
        # parity of mask = number of literals set NEGATED
        neg = bin(mask).count("1")
        # a clause forbids the assignment that makes the XOR equal to (rhs XOR ...).
        # Standard CNF of XOR==rhs: include all assignments whose parity != rhs.
        parity = neg & 1
        if parity == (0 if rhs else 1):
            # this assignment violates XOR==rhs -> add a clause ruling it out
            cl = []
            for i, lit in enumerate(lits):
                if (mask >> i) & 1:
                    cl.append(-lit)
                else:
                    cl.append(lit)
            clauses.append(cl)
    return clauses


def gen_xor_system(rng, nvars, neqs, width, force_unsat):
    """Random parity (XOR) constraint system over GF(2). Solvable by Gaussian
    elimination; resolution-hard for plain CDCL. If force_unsat, append a
    contradicting parity row so the whole system is UNSAT."""
    clauses = []
    rows = []
    for _ in range(neqs):
        vs = rng.sample(range(1, nvars + 1), min(width, nvars))
        rhs = rng.randint(0, 1)
        rows.append((vs, rhs))
        clauses += xor_clauses(vs, rhs == 1)
    if force_unsat and rows:
        # XOR-sum two existing rows but flip the rhs -> contradiction
        (vs1, r1) = rows[0]
        sset = set(vs1)
        for (vs2, r2) in rows[1:3]:
            sset ^= set(vs2)
        contradict_rhs = (r1 ^ (rows[1][1] if len(rows) > 1 else 0)) ^ 1
        vs = sorted(sset)
        if len(vs) == 0:
            # degenerate: empty XOR == 1 is directly false -> add a unit-pair
            clauses.append([1])
            clauses.append([-1])
        elif len(vs) <= 6:
            clauses += xor_clauses(vs, contradict_rhs == 1)
    return nvars, clauses


def gen_parity_chain(rng, n, force_unsat):
    """A chain of 3-var XOR gates v_{i} XOR v_{i+1} XOR a_i = 0 — Tseitin-style,
    exercises XOR detection (k=3 clauses are the classic XOR pattern)."""
    clauses = []
    nv = n
    for i in range(1, n - 1):
        clauses += xor_clauses([i, i + 1, i + 2], rng.randint(0, 1) == 1)
    if force_unsat:
        # pin all to a parity that the chain can't satisfy: add unit + contradiction
        clauses += xor_clauses([1, 2, 3], True)
        clauses += xor_clauses([1, 2, 3], False)
    return nv, clauses


def gen_color(rng, nverts, ncolors, edge_p):
    """Graph k-colouring CNF. var(v,c) = vertex v has colour c.
    Resolution-hard, stresses learning + inprocessing."""
    def var(v, c):
        return v * ncolors + c + 1

    nv = nverts * ncolors
    clauses = []
    # each vertex has at least one colour
    for v in range(nverts):
        clauses.append([var(v, c) for c in range(ncolors)])
    # each vertex at most one colour
    for v in range(nverts):
        for c1 in range(ncolors):
            for c2 in range(c1 + 1, ncolors):
                clauses.append([-var(v, c1), -var(v, c2)])
    # adjacent vertices differ
    edges = []
    for a in range(nverts):
        for b in range(a + 1, nverts):
            if rng.random() < edge_p:
                edges.append((a, b))
                for c in range(ncolors):
                    clauses.append([-var(a, c), -var(b, c)])
    return nv, clauses


def gen_clique_color_unsat(ncolors):
    """K_{ncolors+1} needs ncolors+1 colours -> UNSAT with ncolors. Guaranteed
    UNSAT, resolution-hard, exercises the learning core."""
    nverts = ncolors + 1

    def var(v, c):
        return v * ncolors + c + 1

    nv = nverts * ncolors
    clauses = []
    for v in range(nverts):
        clauses.append([var(v, c) for c in range(ncolors)])
    for v in range(nverts):
        for c1 in range(ncolors):
            for c2 in range(c1 + 1, ncolors):
                clauses.append([-var(v, c1), -var(v, c2)])
    for a in range(nverts):
        for b in range(a + 1, nverts):
            for c in range(ncolors):
                clauses.append([-var(a, c), -var(b, c)])
    return nv, clauses


def minimize(nv, clauses, bad):
    changed = True
    while changed and len(clauses) > 1:
        changed = False
        for i in range(len(clauses)):
            cand = clauses[:i] + clauses[i + 1:]
            if bad(nv, cand):
                clauses = cand
                changed = True
                break
    return nv, clauses


def gen_instance(rng):
    kind = rng.randint(0, 11)
    if kind == 0:
        return gen_3sat(rng, rng.randint(5, 40), rng.uniform(3.8, 4.6))
    if kind == 1:
        return gen_3sat(rng, rng.randint(10, 60), rng.uniform(4.0, 4.3))
    if kind == 2:
        return gen_ksat(rng, rng.randint(5, 30), rng.uniform(1.5, 8.0), rng.randint(2, 5))
    if kind == 3:
        return gen_ksat(rng, rng.randint(4, 20), rng.uniform(6.0, 20.0), 2)
    if kind == 4:
        # Range widened 2..6 -> 2..9 (2026-07-09): the recycled-clause-id
        # stale-watcher bug (reduce_clause_database not scrubbing self.watches
        # before freeing a slot, mirroring the forget_learned_since fix) only
        # manifests once clause_deletion_threshold conflicts accumulate, which
        # PHP(n<=6) never reaches — PHP(9) was the smallest instance in
        # ad hoc testing that actually triggered it (deterministic, all
        # presets, self-detected MODEL-INVALID). n=9 still solves within the
        # harness's 15s per-instance timeout under every preset measured;
        # n=10 is left out of routine fuzzing (it can take 10s of seconds even
        # for cadical/minisat) but is the fixed regression's manual repro.
        return gen_php(rng.randint(2, 9))
    if kind == 5:
        return gen_3sat(rng, rng.randint(3, 15), rng.uniform(2.0, 9.0))
    if kind == 6:
        return gen_xor_system(rng, rng.randint(6, 22), rng.randint(3, 12),
                              rng.randint(3, 5), rng.random() < 0.5)
    if kind == 7:
        return gen_parity_chain(rng, rng.randint(6, 30), rng.random() < 0.5)
    if kind == 8:
        return gen_color(rng, rng.randint(5, 14), rng.randint(2, 4), rng.uniform(0.3, 0.8))
    if kind == 9:
        return gen_clique_color_unsat(rng.randint(2, 5))
    if kind == 10:
        # XOR mixed into a 3SAT body
        nv, cl = gen_3sat(rng, rng.randint(8, 20), rng.uniform(3.0, 4.0))
        nv2, xcl = gen_xor_system(rng, nv, rng.randint(2, 6), 3, False)
        return nv, cl + xcl
    # dense 2-SAT, large
    return gen_ksat(rng, rng.randint(10, 40), rng.uniform(8.0, 25.0), 2)


def main():
    if subprocess.run(["which", "cadical"], capture_output=True).returncode != 0:
        print("[sat-fuzz] cadical not on PATH", file=sys.stderr)
        return 2
    if not os.path.exists(OXIZ_PURE):
        print(f"[sat-fuzz] runner not found: {OXIZ_PURE}", file=sys.stderr)
        return 2
    preset = os.environ.get("OXIZ_SAT_PRESET")
    rng = random.Random(SEED)
    checked = agree = ox_unknown = ref_unknown = model_invalid = 0
    unsound = []
    for _ in range(N):
        nv, cl = gen_instance(rng)
        text = cnf_text(nv, cl)
        ox = solve_oxiz(text, preset)
        if ox == "model-invalid":
            model_invalid += 1
            unsound.append((nv, cl, "sat(model-invalid)", "?"))
            print("[sat-fuzz] MODEL-INVALID (self-detected unsound SAT)!", file=sys.stderr)
            if len(unsound) >= 3:
                break
            continue
        ref = solve_cadical(text)
        if ref == "unknown":
            ref_unknown += 1
            continue
        checked += 1
        if ox == "unknown":
            ox_unknown += 1
            continue
        if ox != ref:
            z = solve_z3(text)
            cms = solve_cms(text)
            ref_votes = [v for v in (ref, z, cms) if v in ("sat", "unsat")]
            truth = max(set(ref_votes), key=ref_votes.count) if ref_votes else ref
            if ox != truth:
                unsound.append((nv, cl, ox, truth))
                print(f"[sat-fuzz] UNSOUND oxiz={ox} truth={truth} "
                      f"(cadical={ref} z3={z} cms={cms})", file=sys.stderr)
                if len(unsound) >= 3:
                    break
        else:
            agree += 1
    print(f"[sat-fuzz] preset={preset or 'default'} checked={checked} agree={agree} "
          f"ox_unknown={ox_unknown} ref_unknown={ref_unknown} "
          f"model_invalid={model_invalid} unsound={len(unsound)}")
    if unsound:
        nv, cl, ox, truth = unsound[0]
        print(f"[sat-fuzz] UNSOUND: oxiz={ox} truth={truth} ({len(cl)} clauses) — minimizing…")

        def bad(nv2, cl2):
            t = cnf_text(nv2, cl2)
            o = solve_oxiz(t, preset)
            if o == "model-invalid":
                return True
            r = solve_cadical(t)
            return o != "unknown" and r != "unknown" and o != r and o == ox.split("(")[0]
        nv, cl = minimize(nv, cl, bad)
        print(f"[sat-fuzz] MINIMAL ({len(cl)} clauses):")
        print(cnf_text(nv, cl))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
