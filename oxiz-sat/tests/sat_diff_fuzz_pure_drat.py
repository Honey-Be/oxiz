#!/usr/bin/env python3
"""Pure-SAT differential fuzz harness — DRAT-verify mode.

This is `sat_diff_fuzz_pure.py` extended with an independent UNSAT-proof check:
whenever the pure oxiz-sat engine returns UNSAT, the runner emits a DRAT proof
(env OXIZ_DRAT) and this harness runs `drat-trim <cnf> <proof>`. A proof that
fails to verify (`s NOT VERIFIED`, a non-zero exit, or a missing `s VERIFIED`
line) is treated as a SOUNDNESS FAILURE — it means the engine concluded UNSAT
without a checkable resolution proof, i.e. a (potentially spurious) UNSAT the
DRAT certificate cannot back up.

This catches a broader class of bug than the cross-solver oracle alone: even if
oxiz and cadical happen to AGREE on UNSAT, a non-verifying DRAT proof reveals
that oxiz's *reasoning* (clause learning / deletion / inprocessing mutation) is
not sound, so the agreement was luck.

It keeps the original cross-solver differential check too (oxiz vs
cadical/z3/cryptominisat5), so SAT-side unsoundness is still caught.

Env:
  OXIZ_PURE        path to the pure_sat_runner example binary
  SATFUZZ_N        number of instances (default 2000)
  SATFUZZ_SEED     PRNG seed (default 12648430; 0x-prefixed hex accepted)
  OXIZ_SAT_PRESET  SolverConfig preset, passed through to the runner
  OXIZ_INPROC      "1" to force-enable inprocessing (vivify/strengthen paths)
  DRAT_TRIM        path to drat-trim (default: "drat-trim" on PATH)
  DRAT_ONLY        "1" to skip the cross-solver oracle and ONLY DRAT-check UNSATs
                   (faster; pure proof-soundness sweep)
"""
import os, random, subprocess, sys, tempfile

OXIZ_PURE = os.environ.get("OXIZ_PURE", "./target/debug/examples/pure_sat_runner")
DRAT_TRIM = os.environ.get("DRAT_TRIM", "drat-trim")
N = int(os.environ.get("SATFUZZ_N", "2000"))
DRAT_ONLY = os.environ.get("DRAT_ONLY", "0") == "1"
_seed_raw = os.environ.get("SATFUZZ_SEED", "12648430")
SEED = int(_seed_raw, 0) if _seed_raw.startswith("0x") else int(_seed_raw)


def cnf_text(nv, clauses):
    out = [f"p cnf {nv} {len(clauses)}"]
    for c in clauses:
        out.append(" ".join(str(l) for l in c) + " 0")
    return "\n".join(out) + "\n"


def _write_cnf(text):
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as f:
        f.write(text)
        return f.name


def run_oxiz(text, preset=None, drat_path=None, timeout=20):
    """Run the pure runner. Returns (verdict, stdout+stderr, cnf_path).
    The cnf file is NOT unlinked so a DRAT proof over it can be checked; the
    caller cleans up."""
    path = _write_cnf(text)
    e = dict(os.environ)
    if preset:
        e["OXIZ_SAT_PRESET"] = preset
    if drat_path:
        e["OXIZ_DRAT"] = drat_path
    try:
        r = subprocess.run([OXIZ_PURE, path], capture_output=True, text=True,
                           timeout=timeout, env=e)
        out = r.stdout + "\n" + r.stderr
    except Exception:
        out = ""
    return verdict(out), out, path


def run_ref(cmd, text, timeout=15):
    path = _write_cnf(text)
    try:
        r = subprocess.run(cmd + [path], capture_output=True, text=True,
                           timeout=timeout)
        out = r.stdout + "\n" + r.stderr
    except Exception:
        out = ""
    finally:
        try:
            os.unlink(path)
        except OSError:
            pass
    return verdict(out)


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


def drat_path_from(out):
    """The runner prints `c DRAT <path>`; return that path, or None."""
    for ln in out.splitlines():
        s = ln.strip()
        if s.startswith("c DRAT "):
            return s[len("c DRAT "):].strip()
    return None


def drat_verify(cnf_path, proof_path, timeout=60):
    """Returns (ok, detail). ok is True iff drat-trim prints 's VERIFIED' and
    exits zero. Anything else (NOT VERIFIED, non-zero exit, crash, missing
    line) is a failure."""
    try:
        r = subprocess.run([DRAT_TRIM, cnf_path, proof_path],
                           capture_output=True, text=True, timeout=timeout)
    except Exception as ex:
        return False, f"drat-trim crashed/timeout: {ex}"
    out = r.stdout + "\n" + r.stderr
    verified = any(ln.strip() == "s VERIFIED" for ln in out.splitlines())
    not_verified = any("NOT VERIFIED" in ln for ln in out.splitlines())
    if not_verified or not verified or r.returncode != 0:
        tail = "\n".join(out.splitlines()[-8:])
        return False, f"rc={r.returncode} verified={verified} not_verified={not_verified}\n{tail}"
    return True, "verified"


def solve_cadical(text):
    return run_ref(["cadical", "-q"], text)


def solve_z3(text):
    return run_ref(["z3", "-dimacs", "-T:12"], text)


def solve_cms(text):
    return run_ref(["cryptominisat5", "--verb=0"], text)


# ----------------------------------------------------------------------------
# generators (identical to sat_diff_fuzz_pure.py)
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
    k = len(lits)
    clauses = []
    for mask in range(1 << k):
        neg = bin(mask).count("1")
        parity = neg & 1
        if parity == (0 if rhs else 1):
            cl = []
            for i, lit in enumerate(lits):
                if (mask >> i) & 1:
                    cl.append(-lit)
                else:
                    cl.append(lit)
            clauses.append(cl)
    return clauses


def gen_xor_system(rng, nvars, neqs, width, force_unsat):
    clauses = []
    rows = []
    for _ in range(neqs):
        vs = rng.sample(range(1, nvars + 1), min(width, nvars))
        rhs = rng.randint(0, 1)
        rows.append((vs, rhs))
        clauses += xor_clauses(vs, rhs == 1)
    if force_unsat and rows:
        (vs1, r1) = rows[0]
        sset = set(vs1)
        for (vs2, r2) in rows[1:3]:
            sset ^= set(vs2)
        contradict_rhs = (r1 ^ (rows[1][1] if len(rows) > 1 else 0)) ^ 1
        vs = sorted(sset)
        if len(vs) == 0:
            clauses.append([1])
            clauses.append([-1])
        elif len(vs) <= 6:
            clauses += xor_clauses(vs, contradict_rhs == 1)
    return nvars, clauses


def gen_parity_chain(rng, n, force_unsat):
    clauses = []
    nv = n
    for i in range(1, n - 1):
        clauses += xor_clauses([i, i + 1, i + 2], rng.randint(0, 1) == 1)
    if force_unsat:
        clauses += xor_clauses([1, 2, 3], True)
        clauses += xor_clauses([1, 2, 3], False)
    return nv, clauses


def gen_color(rng, nverts, ncolors, edge_p):
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
            if rng.random() < edge_p:
                for c in range(ncolors):
                    clauses.append([-var(a, c), -var(b, c)])
    return nv, clauses


def gen_clique_color_unsat(ncolors):
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
        return gen_php(rng.randint(2, 6))
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
        nv, cl = gen_3sat(rng, rng.randint(8, 20), rng.uniform(3.0, 4.0))
        nv2, xcl = gen_xor_system(rng, nv, rng.randint(2, 6), 3, False)
        return nv, cl + xcl
    return gen_ksat(rng, rng.randint(10, 40), rng.uniform(8.0, 25.0), 2)


def main():
    if subprocess.run(["which", DRAT_TRIM], capture_output=True).returncode != 0:
        print(f"[sat-fuzz-drat] drat-trim not on PATH ({DRAT_TRIM})", file=sys.stderr)
        return 2
    if not DRAT_ONLY and subprocess.run(["which", "cadical"], capture_output=True).returncode != 0:
        print("[sat-fuzz-drat] cadical not on PATH", file=sys.stderr)
        return 2
    if not os.path.exists(OXIZ_PURE):
        print(f"[sat-fuzz-drat] runner not found: {OXIZ_PURE}", file=sys.stderr)
        return 2

    preset = os.environ.get("OXIZ_SAT_PRESET")
    rng = random.Random(SEED)
    checked = agree = ox_unknown = ref_unknown = model_invalid = 0
    unsat_count = drat_verified = 0
    unsound = []          # cross-solver disagreement (truth differs)
    drat_failures = []    # UNSAT whose DRAT proof did NOT verify

    for _ in range(N):
        nv, cl = gen_instance(rng)
        text = cnf_text(nv, cl)

        # Use a per-instance DRAT path so concurrent reuse never clashes.
        drat_fd, drat_file = tempfile.mkstemp(suffix=".drat")
        os.close(drat_fd)

        ox, ox_out, cnf_path = run_oxiz(text, preset, drat_path=drat_file)

        try:
            if ox == "model-invalid":
                model_invalid += 1
                unsound.append((nv, cl, "sat(model-invalid)", "?"))
                print("[sat-fuzz-drat] MODEL-INVALID (self-detected unsound SAT)!",
                      file=sys.stderr)
                if len(unsound) + len(drat_failures) >= 3:
                    break
                continue

            # DRAT check on every UNSAT.
            if ox == "unsat":
                unsat_count += 1
                proof = drat_path_from(ox_out) or drat_file
                ok, detail = drat_verify(cnf_path, proof)
                if ok:
                    drat_verified += 1
                else:
                    drat_failures.append((nv, cl, detail))
                    print(f"[sat-fuzz-drat] DRAT-UNVERIFIED UNSAT proof!\n{detail}",
                          file=sys.stderr)
                    if len(unsound) + len(drat_failures) >= 3:
                        break

            if DRAT_ONLY:
                if ox == "unknown":
                    ox_unknown += 1
                continue

            # Cross-solver oracle (catches SAT-side unsoundness).
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
                    print(f"[sat-fuzz-drat] UNSOUND oxiz={ox} truth={truth} "
                          f"(cadical={ref} z3={z} cms={cms})", file=sys.stderr)
                    if len(unsound) + len(drat_failures) >= 3:
                        break
            else:
                agree += 1
        finally:
            for p in (cnf_path, drat_file):
                try:
                    os.unlink(p)
                except OSError:
                    pass

    print(f"[sat-fuzz-drat] preset={preset or 'default'} drat_only={DRAT_ONLY} "
          f"checked={checked} agree={agree} ox_unknown={ox_unknown} "
          f"ref_unknown={ref_unknown} model_invalid={model_invalid} "
          f"unsat={unsat_count} drat_verified={drat_verified} "
          f"drat_failures={len(drat_failures)} unsound={len(unsound)}")

    if drat_failures:
        nv, cl, detail = drat_failures[0]
        print(f"[sat-fuzz-drat] FIRST DRAT FAILURE ({len(cl)} clauses):\n{detail}")
        print(cnf_text(nv, cl))
        return 1
    if unsound:
        nv, cl, ox, truth = unsound[0]
        print(f"[sat-fuzz-drat] CROSS-SOLVER UNSOUND oxiz={ox} truth={truth} "
              f"({len(cl)} clauses):")
        print(cnf_text(nv, cl))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
