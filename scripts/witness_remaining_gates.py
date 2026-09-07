#!/usr/bin/env python3
"""The remaining mechanism gates on the section-54 witness A* -- hclose and the block engine.

WHY THIS EXISTS (the analysis it is bound to)
---------------------------------------------
`CertificateSocketCollapse.md` section 54 (cross-index T33) produced

    A* = (N \\ {2^i}) xor {4p : p prime}

as the first set with BOTH exhaustion-map OPEN-class membership (aperiodic,
reciprocal-divergent, nullity `0,0,0`) and a DEAD socket route (`Odd_{A*}` syndetic with
gap exactly 4, by the T33b containment lemma).  Two catalogued mechanisms were left
untested on it: `hclose`, and the section-45 shifted-block / transplant engine.  Section 50
corrected exactly the overreach of naming a hard core before every gate was closed, so
these are run before any such claim.

THE ALGEBRA, DERIVED BEFORE THE RUN
-----------------------------------
`{4p}` meets `{2^i}` only at `4*2 = 8`, so with
`E = ({2^i : i>=1} u {4p : p odd prime})` we have `A* = N \\ E` and

    tau_{A*}(m) = d(m) - #{a | m : a in E}.

`1` is in `A*` (neither a power of two nor `4p`); `8` is in `A*` (it lies in BOTH
ingredient sets, so the xor returns it).

**(a) `hclose`.**  `a = N+1` lies in `A*` unless `N+1` is in `E`, and `E` has DENSITY ZERO.
When it does, `delta_{N+1}(N) = 1` and the term is `1/2`, so `excess(N) >= 1/2` for almost
every `N`.  Predict `hclose` FAILS -- min excess bounded away from zero.  **Residual (l)
applies: my ">= 1/2" claim for the previous set held only for `N >= 4`, so small `N` are
checked explicitly rather than assumed.**

**(b) The block engine.**  The shift clause is `tau_{A*}(N+j) = tau_{A*}(j) + 1`.  Head
values: `tau_{A*}(1) = 1`, `tau_{A*}(2) = 1` (2 is excluded), `tau_{A*}(3) = 2`.  So `j=1`
demands `tau(N+1) = 2`, `j=2` demands `tau(N+2) = 2`, `j=3` demands `tau(N+3) = 3`.
**These differ from `A = N`, so the section-45 kill (`d(N+2)=3`, `d(N+3)=3` forcing
consecutive prime squares) does NOT transfer verbatim.**  It must be measured.

PREDICTIONS, RECORDED BEFORE THE RUN
------------------------------------
  CALIBRATOR `A = N`   max block `K = 2`, attained at `N = 2` ONLY -- PROVEN in section 45.
                       Any other reading means the census is misbuilt and nothing may be
                       concluded.
  `A*` hclose          min excess bounded away from 0; predict `>= 0.3`; `hclose` FAILS,
                       so the witness SURVIVES this gate.
  `A*` block           predict a small cap, `K <= 4`, since `A*` is `N` minus a
                       density-zero set.  The engine needs `K -> infinity` (section 47),
                       so any fixed cap kills it IN RANGE.
  CONTROL              marginal-preserving shuffle of `tau_{A*}`; report its max block so a
                       coincidence count is never mistaken for structure (T27a/T25 rule).

FALSIFIER, stated before the run: the `A = N` calibrator failing to give max `K = 2` at
`N = 2`; or `A*`'s min excess reaching `0`, which would mean `hclose` DECIDES `A*` and the
witness dies exactly as the geometric sets did in section 50.

VERDICT LABELS -- every conclusion carries one:
  PROVEN            follows from an argument here or in a cited section
  MEASURED-IN-RANGE holds over the computed window only (T12: finite search never refutes
                    existence)
  BOX-ONLY          the nullity readings, which rule out `(d=2, D=5)` at `k=2,3,4` (T31c)

Bound directions, per the standing infrastructure rule:
  analysis -> here : CertificateSocketCollapse.md 45, 46, 47, 50, 54; T25, T27a, T31c,
                     T33b; exhaustion map section AO
  here -> analysis : CertificateSocketCollapse.md section 55, cross-index trap,
                     receipt under state/formal_math/erdos257_period_noncollapse/
"""

from __future__ import annotations

import argparse, hashlib, json, random
from math import gcd
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]


def sieve(M):
    s = bytearray([1]) * (M + 1); s[0:2] = b"\x00\x00"
    i = 2
    while i * i <= M:
        if s[i]:
            for m in range(i * i, M + 1, i): s[m] = 0
        i += 1
    return s


def build(M):
    pr = sieve(M)
    pow2 = {2 ** i for i in range(1, 40) if 2 ** i <= M}
    fourp = {4 * p for p in range(2, M + 1) if pr[p] and 4 * p <= M}
    Astar = (set(range(1, M + 1)) - pow2) ^ fourp
    return Astar, pr


def tau_of(S, M):
    t = [0] * (M + 1)
    for a in S:
        if a >= 1:
            for m in range(a, M + 1, a): t[m] += 1
    return t


def max_block(tau, M, nmax, cap=40):
    best, at = 0, None
    for N in range(1, nmax + 1):
        K = 0
        while K < cap and N + K + 1 <= M:
            j = K + 1
            if tau[N + j] != tau[j] + 1: break
            K += 1
        if K > best: best, at = K, N
    return best, at


def atom_exact(N: int, a: int) -> float:
    """EXACT excess term at support element `a`, per `shiftedMersenneAtom`:

        (2^(N mod a) - 1) / (2^a - 1),      zero exactly when a | N.

    Evaluated as `2^-(a-r) * (1 - 2^-r) / (1 - 2^-a)` so that huge `a` never
    overflows a float; the factored form is algebraically identical.
    """
    r = N % a
    if r == 0:
        return 0.0                        # T29d: divisibility by %, never by a zero term
    if a - r > 1000:
        return 0.0                        # genuinely negligible, skipped EXPLICITLY
    return 2.0 ** -(a - r) * (1.0 - 2.0 ** -r) / (1.0 - 2.0 ** -a)


def atom_approx(N: int, a: int) -> float:
    """The APPROXIMATION this programme used before section 57: `2^-(a - N mod a)`.

    Retained only so the guard below can demonstrate the defect.  **Never sum this.**
    """
    r = N % a
    if r == 0:
        return 0.0
    if a - r > 1000:
        return 0.0
    return 2.0 ** -(a - r)


def _guard() -> None:
    """Pin the section-57 defect, and the section-58 correction to how it behaves.

    `atom_exact / atom_approx = (2^a - 2^(a-r)) / (2^a - 1) -> 1 - 2^-r`, so the
    approximation's error is governed by `r = N mod a` and NOT by `delta = a - r`.
    Section 57 said "agree at large delta"; that is FALSE -- at `r = 1` the two differ
    by a factor of two however large `delta` is.  This guard fails if either the defect
    disappears (which would make it vacuous) or the `r`-law breaks.
    """
    # r = 1, within the evaluated regime: must DISAGREE, ratio approaching 1/2
    for a in (2, 200, 1000):
        e, ap = atom_exact(1, a), atom_approx(1, a)
        assert ap > 0.0, f"guard vacuous: approx skipped at a={a}"
        assert e < ap, f"exact must be strictly smaller (a={a})"
        assert abs(e / ap - 0.5) < 0.2, f"r=1 ratio must approach 1/2 (a={a})"
    # beyond the skip threshold BOTH must vanish together, or the comparison is
    # meaningless -- the first run of this guard failed exactly here (see s58)
    assert atom_exact(1, 5000) == 0.0 and atom_approx(1, 5000) == 0.0, \
        "skip must be symmetric across both terms"
    # large r: must AGREE to within 2^-r
    e, ap = atom_exact(64, 128), atom_approx(64, 128)
    assert abs(e / ap - 1.0) < 2.0 ** -60, "large r must agree (this is the s50 case)"
    # the a | N convention
    assert atom_exact(12, 4) == 0.0 and atom_approx(12, 4) == 0.0, "a | N must give 0"


_guard()


def excess(S, N, cap=1400):
    """Exact excess `sum_{a in A} (2^(N mod a) - 1)/(2^a - 1)`."""
    tot = 0.0
    for a in S:
        if a < 1 or a > N + cap:
            continue
        tot += atom_exact(N, a)
    return tot


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max", type=int, default=120000)
    ap.add_argument("--nmax", type=int, default=60000)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    M, nmax = args.max, args.nmax
    Astar, pr = build(M)
    tA = tau_of(Astar, M)
    tN = tau_of(set(range(1, M + 1)), M)

    calK, calN = max_block(tN, M, min(nmax, 20000))
    aK, aN = max_block(tA, M, nmax)
    rng = random.Random(20260823)
    shuf = [0] + rng.sample(tA[1:M + 1], M)
    cK, cN = max_block(shuf, M, nmax)

    tests = list(range(1, 60)) + [2 ** i - 1 for i in range(2, 12)]
    L = 1
    for k in range(2, 13):
        L = L * k // gcd(L, k)
        if L <= nmax: tests.append(L)
    tests = sorted({t for t in tests if 1 <= t})
    ex = [(N, excess(Astar, N)) for N in tests]
    mn = min(ex, key=lambda t: t[1])

    report = {
        "max_n": M, "nmax": nmax,
        "calibrator_A_eq_N": {"max_block_K": calK, "at_N": calN,
                              "expected": "K=2 at N=2 (PROVEN s45)"},
        "Astar_block": {"max_block_K": aK, "at_N": aN},
        "control_shuffled_block": {"max_block_K": cK, "at_N": cN},
        "Astar_hclose": {"min_excess": mn[1], "argmin_N": mn[0],
                         "tested_N_count": len(tests),
                         "rows_small_N": [(N, round(e, 6)) for N, e in ex[:8]],
                         "rows_2pow_minus_1": [(N, round(e, 6)) for N, e in ex
                                               if (N + 1) & N == 0 and N > 1][:6]},
    }
    ok = (calK == 2 and calN == 2) and mn[1] > 0.0
    report["falsifier_survived"] = ok
    print(f"CALIBRATOR A=N block: K={calK} at N={calN}   (must be K=2 at N=2)")
    print(f"A* block:             K={aK} at N={aN}")
    print(f"CONTROL (shuffled):   K={cK} at N={cN}")
    print(f"A* hclose min excess: {mn[1]:.6f} at N={mn[0]}  over {len(tests)} tested N")
    print(f"  small-N rows: {report['Astar_hclose']['rows_small_N']}")
    print(f"  N=2^i-1 rows: {report['Astar_hclose']['rows_2pow_minus_1']}")
    print(f"FALSIFIER: {'SURVIVED' if ok else 'BROKEN'}")

    out = args.out or str(REPO / "state/formal_math/erdos257_period_noncollapse/witness_remaining_gates_receipt.json")
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    blob = json.dumps(report, indent=2, sort_keys=True)
    Path(out).write_text(blob)
    print(f"wrote {out} sha256={hashlib.sha256(blob.encode()).hexdigest()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
