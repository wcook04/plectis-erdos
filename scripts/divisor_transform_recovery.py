#!/usr/bin/env python3
"""Which functionals of 1_A survive the Dirichlet transform tau_A = 1 * 1_A.

WHY THIS EXISTS
---------------
`docs/formal_math/erdos257_computational_exhaustion_map_2026_08_22.md` section AJ
states the unifying law: the transform PRESERVES periodicity and boundedness
(`sum_{d in A} 1/d < infty`) and DESTROYS complexity entirely.  Its section AK
asks the open question this script answers one case of:

    "which statistics of A are invariants of tau_A beyond density and
     periodicity"

This script exhibits a family that IS recoverable and is neither.  Fix any
modulus `ell`.  The residue-class means of `tau_A` mod `ell` satisfy

    fbar_j := lim (ell/x) * sum_{N <= x, N = j mod ell} tau_A(N)
            = sum_{g | ell, g | j}  g * H_g(A),     H_g = sum_{a in A, gcd(a,ell)=g} 1/a

so `fbar_j` depends on `j` only through `d = gcd(j, ell)`.  Writing `F_d` for that
common value, the system is triangular over the divisor lattice and inverts:

    d * H_d(A) = sum_{g | d} mu(d/g) * F_g                       (RECOVERY)

i.e. the mod-`ell` residue means of `tau_A` recover the harmonic weights of `A`
refined by `gcd(a, ell)`.  For `A` of positive density these are the densities of
`A` along the `gcd`-with-`ell` decomposition -- a refinement of density selected
by the modulus, not raw density and not periodicity.

WHERE ell COMES FROM, and the lane this closes
----------------------------------------------
For a RATIONAL target `y = p/q` the natural modulus is `ell = ord_q(2)`, because
`{2^N y}` is purely periodic with that period.  I had hoped the resulting
cycle-averaged identity

    Dbar_j (2^ell - 1) = sum_{i=1..ell} 2^(ell-i) (fbar_{j+i} - t_{j+i})

would collide bounded `t` against divergent `fbar`.  It does not: it is exactly
the geometric resummation of `R_N = sum_k tau_A(N+k) 2^-k` under `ell`-periodicity
together with `theta_j = sum_k t_{j+k} 2^-k`, so it is a tautology and both sides
diverge at the same rate.  That lane is CLOSED.  Only the RECOVERY statement above
survives, and it is offered to section AK, not claimed as progress on 257.

Bound directions:
  analysis -> here : exhaustion map sections AJ, AK (the transform's invariants)
  here -> analysis : Erdos257/DivisorTransformRecovery.md, receipt under state/
"""

from __future__ import annotations

import argparse
import hashlib
import json
from math import gcd
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]


def mobius(n: int) -> int:
    if n == 1:
        return 1
    res, d, m = 1, 2, n
    while d * d <= m:
        if m % d == 0:
            m //= d
            if m % d == 0:
                return 0
            res = -res
        d += 1
    if m > 1:
        res = -res
    return res


def divisors(n: int):
    return [d for d in range(1, n + 1) if n % d == 0]


def tau_A(A: set, X: int):
    """tau_A(N) = #{a in A : a | N}, for N = 1..X."""
    t = [0] * (X + 1)
    for a in A:
        if a == 0:
            continue
        for N in range(a, X + 1, a):
            t[N] += 1
    return t


def measure(A: set, ell: int, X: int):
    """Empirical F_d (residue means of tau_A) and direct H_g, both truncated at X."""
    t = tau_A(A, X)
    # empirical: mean of tau_A over each residue class, grouped by d = gcd(j, ell)
    tot = {}
    cnt = {}
    for N in range(1, X + 1):
        d = gcd(N % ell, ell) if N % ell else ell
        tot[d] = tot.get(d, 0) + t[N]
        cnt[d] = cnt.get(d, 0) + 1
    F_emp = {d: tot[d] / cnt[d] for d in tot}
    # direct: H_g over a in A, a <= X
    H = {g: 0.0 for g in divisors(ell)}
    for a in A:
        if 1 <= a <= X:  # a is already capped by amax at construction
            H[gcd(a, ell)] += 1.0 / a
    # predicted F_d = sum_{g | d} g H_g
    F_pred = {d: sum(g * H[g] for g in divisors(ell) if d % g == 0) for d in divisors(ell)}
    # RECOVERY: d H_d = sum_{g | d} mu(d/g) F_g, using the EMPIRICAL F
    H_rec = {}
    for d in divisors(ell):
        H_rec[d] = sum(mobius(d // g) * F_emp.get(g, 0.0) for g in divisors(d)) / d
    return F_emp, F_pred, H, H_rec


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--X", type=int, default=400000)
    ap.add_argument("--amax", type=int, default=0,
                    help="cap on elements of A; must be << X or the residue means "
                         "under-credit large a and the inversion fails by truncation")
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    X = args.X
    amax = args.amax or max(1, X // 500)

    # supports chosen to span the law's two preserved properties and neither:
    families = {
        "all_naturals":      (set(range(1, amax + 1)), 12),
        "evens":             (set(range(2, amax + 1, 2)), 12),
        "coprime_to_12":     ({a for a in range(1, amax + 1) if gcd(a, 12) == 1}, 12),
        "arith_prog_5_mod_12": (set(range(5, amax + 1, 12)), 12),
        "squares_lacunary":  ({k * k for k in range(1, int(amax ** 0.5) + 1)}, 12),
        "density_half_mixed": ({a for a in range(1, amax + 1) if (a * a + 3 * a) % 4 < 2}, 12),
        "ell_16_naturals":   (set(range(1, amax + 1)), 16),
        "ell_16_odd":        (set(range(1, amax + 1, 2)), 16),
    }

    report = {"X": X, "amax": amax, "families": {}}
    worst = 0.0
    for name, (A, ell) in families.items():
        F_emp, F_pred, H, H_rec = measure(A, ell, X)
        errs = []
        for d in divisors(ell):
            direct = d * H[d]
            rec = d * H_rec[d]
            denom = max(1e-12, abs(direct))
            errs.append(abs(direct - rec) / denom if direct else abs(rec))
        rel = max(errs)
        worst = max(worst, rel)
        report["families"][name] = {
            "ell": ell,
            "F_empirical": {str(k): v for k, v in sorted(F_emp.items())},
            "F_predicted": {str(k): v for k, v in sorted(F_pred.items())},
            "gH_direct": {str(d): d * H[d] for d in divisors(ell)},
            "gH_recovered": {str(d): d * H_rec[d] for d in divisors(ell)},
            "max_relative_recovery_error": rel,
        }
        print(f"{name:>22} ell={ell:>3}  max_rel_recovery_err={rel:.3e}")

    report["worst_relative_recovery_error"] = worst
    report["verdict"] = (
        "RECOVERY verified" if worst < 5e-2 else "RECOVERY FAILED"
    )
    out = args.out or str(
        REPO / "state/formal_math/erdos257_period_noncollapse/divisor_transform_recovery_receipt.json"
    )
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    blob = json.dumps(report, indent=2, sort_keys=True)
    Path(out).write_text(blob)
    print(f"worst={worst:.3e}  verdict={report['verdict']}")
    print(f"wrote {out} sha256={hashlib.sha256(blob.encode()).hexdigest()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
