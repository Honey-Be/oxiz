#!/usr/bin/env python3
"""Pure-SAT differential fuzz harness for oxiz-sat vs reference CDCL solvers.

Generates random CNF (k-SAT, ratios around the 3-SAT phase transition where the
hardest sat/unsat-boundary instances cluster) plus a few structured families,
solves each with oxiz (--dimacs) and cadical (gold standard), and flags every
UNSOUND disagreement:
  * unsound SAT   — oxiz s SATISFIABLE,   cadical s UNSATISFIABLE
  * unsound UNSAT — oxiz s UNSATISFIABLE, cadical s SATISFIABLE
On a disagreement it cross-checks z3 + cryptominisat5 (to exonerate cadical),
delta-debugs the CNF to a minimal reproducer, and prints it.

Env: OXIZ (path to oxiz cli), SATFUZZ_N (#instances), SATFUZZ_SEED.
"""
import os, random, subprocess, sys, tempfile

OXIZ = os.environ.get("OXIZ", "./target/debug/oxiz")
N = int(os.environ.get("SATFUZZ_N", "2000"))
SEED = int(os.environ.get("SATFUZZ_SEED", "0xC0FFEE"), 0) if isinstance(os.environ.get("SATFUZZ_SEED"), str) and os.environ.get("SATFUZZ_SEED", "").startswith("0x") else int(os.environ.get("SATFUZZ_SEED", "12648430"))


def cnf_text(nv, clauses):
    out = [f"p cnf {nv} {len(clauses)}"]
    for c in clauses:
        out.append(" ".join(str(l) for l in c) + " 0")
    return "\n".join(out) + "\n"


def run(cmd, text, timeout=10):
    try:
        with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as f:
            f.write(text)
            path = f.name
        r = subprocess.run(cmd + [path], capture_output=True, text=True, timeout=timeout)
        os.unlink(path)
        return r.stdout
    except Exception:
        return ""


def verdict(out):
    for ln in out.splitlines():
        s = ln.strip()
        if s == "sat" or s.startswith("s SATISFIABLE"):
            return "sat"
        if s == "unsat" or s.startswith("s UNSATISFIABLE"):
            return "unsat"
    return "unknown"


def solve_oxiz(text):
    return verdict(run([OXIZ, "--dimacs"], text))


def solve_cadical(text):
    return verdict(run(["cadical", "-q"], text))


def solve_z3(text):
    return verdict(run(["z3", "-dimacs", "-T:10"], text))


def solve_cms(text):
    return verdict(run(["cryptominisat5", "--verb=0"], text))


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
    # pigeonhole PHP(n+1, n): n+1 pigeons in n holes — always UNSAT, exercises
    # the resolution/learning core hard.
    pigeons, holes = n + 1, n

    def var(p, h):
        return p * holes + h + 1

    nv = pigeons * holes
    clauses = []
    for p in range(pigeons):
        clauses.append([var(p, h) for h in range(holes)])  # each pigeon in some hole
    for h in range(holes):
        for p1 in range(pigeons):
            for p2 in range(p1 + 1, pigeons):
                clauses.append([-var(p1, h), -var(p2, h)])  # no two pigeons share a hole
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


def main():
    for tool in ("cadical",):
        if subprocess.run(["which", tool], capture_output=True).returncode != 0:
            print(f"[sat-fuzz] {tool} not on PATH", file=sys.stderr)
            return 2
    rng = random.Random(SEED)
    checked = agree = ox_unknown = ref_unknown = 0
    unsound = []
    for _ in range(N):
        kind = rng.randint(0, 5)
        if kind == 0:
            nv, cl = gen_3sat(rng, rng.randint(5, 40), rng.uniform(3.8, 4.6))
        elif kind == 1:
            nv, cl = gen_3sat(rng, rng.randint(10, 60), rng.uniform(4.0, 4.3))
        elif kind == 2:
            nv, cl = gen_ksat(rng, rng.randint(5, 30), rng.uniform(1.5, 8.0), rng.randint(2, 5))
        elif kind == 3:
            nv, cl = gen_ksat(rng, rng.randint(4, 20), rng.uniform(6.0, 20.0), 2)  # 2-SAT-ish, dense
        elif kind == 4:
            nv, cl = gen_php(rng.randint(2, 5))  # small UNSAT pigeonhole
        else:
            nv, cl = gen_3sat(rng, rng.randint(3, 15), rng.uniform(2.0, 9.0))
        text = cnf_text(nv, cl)
        ox = solve_oxiz(text)
        ref = solve_cadical(text)
        if ref == "unknown":
            ref_unknown += 1
            continue
        checked += 1
        if ox == "unknown":
            ox_unknown += 1
            continue
        if ox != ref:
            # cross-check to exonerate cadical
            z = solve_z3(text)
            cms = solve_cms(text)
            ref_votes = [v for v in (ref, z, cms) if v in ("sat", "unsat")]
            truth = max(set(ref_votes), key=ref_votes.count) if ref_votes else ref
            if ox != truth:
                unsound.append((nv, cl, ox, truth))
                if len(unsound) >= 3:
                    break
        else:
            agree += 1
    print(f"[sat-fuzz] checked={checked} agree={agree} ox_unknown={ox_unknown} ref_unknown={ref_unknown} unsound={len(unsound)}")
    if unsound:
        nv, cl, ox, truth = unsound[0]
        print(f"[sat-fuzz] UNSOUND: oxiz={ox} truth={truth} ({len(cl)} clauses) — minimizing…")

        def bad(nv2, cl2):
            t = cnf_text(nv2, cl2)
            o = solve_oxiz(t)
            r = solve_cadical(t)
            return o != "unknown" and r != "unknown" and o != r and o == ox
        nv, cl = minimize(nv, cl, bad)
        print(f"[sat-fuzz] MINIMAL ({len(cl)} clauses):")
        print(cnf_text(nv, cl))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
