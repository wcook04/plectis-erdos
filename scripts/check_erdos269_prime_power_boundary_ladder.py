#!/usr/bin/env python3
"""Erdos 269 / support {2,3,5}: prime-power boundary ladder checker.

Verifies, against exact substrate, the claims that arrived from the parallel
Type B lane on 2026-08-23.  Nothing here is an irrationality proof.

  (J)  Jump identity.       Sigma = sum_{p in {2,3,5}} sum_{m>=1} (p-1) A(p^m)/H(p^m),
       with A(x) = #{s smooth : 2 <= s < x}.  Exact finite form at a boundary R:
           sum_{2<=s<R} 1/H(s) = sum_{p^m<=R} (p-1)A(p^m)/H(p^m) + A(R)/H(R).
  (C)  Boundary clearing.   Every smooth s < p^m has p*H(s) | H(p^m); i.e. the whole
       rational prefix clears against H(p^m)/p at EVERY prime-power boundary, not
       only at powers of two.
  (R)  Boundary recurrence. On the merged ordered boundary ladder r_1<r_2<...,
       U_{j+1} = p_j U_j - C_j, with U_j = (H(r_j)/p_j) T(r_j) and
       C_j = #{s smooth : r_j <= s < r_{j+1}}.  At r_j = 2^a this must reproduce
       the dyadic state X_a.
  (B)  Two-sided state bounds.
           lower: X_a >= (1/60)(floor(a/(2 log2 3))+1)(floor(a/(2 log2 5))+1)
           upper: X_a <= a^2 + 6a + 11
  (A)  Residue annulus.     For an integral start X_a and a window L with
       Q_{a,L} > upper(a+L), the residue rho = (-E_{a,L}) mod Q_{a,L} must equal
       X_{a+L}, hence must lie in [lower(a+L), upper(a+L)].  Reports how many
       starts the two-sided annulus excludes versus the one-sided test.
       This branch is denominator one only.
"""
from __future__ import annotations

problem_id = "erdos_269"

import argparse
import json
import math
import pathlib
import sys
from fractions import Fraction

import numpy as np
from mpmath import mp

L3 = math.log2(3.0)
L5 = math.log2(5.0)
PRIMES = (2, 3, 5)


def smooth_log_grid(nmax: float) -> np.ndarray:
    jj = np.arange(int(nmax / L3) + 2, dtype=np.float64)[:, None]
    kk = np.arange(int(nmax / L5) + 2, dtype=np.float64)[None, :]
    mu = (jj * L3 + kk * L5).ravel()
    return np.sort(mu[mu <= nmax + 2.0])


class Counter:
    """#{smooth s : log2 s < X}, and counts on half-open log2 intervals."""

    def __init__(self, nmax: float) -> None:
        self.mu = smooth_log_grid(nmax)
        self.min_slack = 1.0

    def below(self, x: float) -> int:
        mu = self.mu[: np.searchsorted(self.mu, x)]
        r = x - mu
        gap = np.abs(r - np.rint(r))
        nz = gap[gap > 0.0]
        if nz.size:
            self.min_slack = min(self.min_slack, float(nz.min()))
        return int(np.sum(np.ceil(r)))

    def between(self, lo: float, hi: float) -> int:
        return self.below(hi) - self.below(lo)


def height(x: int) -> int:
    """H(x) by exact integer arithmetic."""
    out = 1
    for p in PRIMES:
        q = 1
        while q * p <= x:
            q *= p
        out *= q
    return out


def smooth_below(bound: int) -> list[int]:
    vals = []
    a2 = 1
    while a2 < bound:
        a3 = a2
        while a3 < bound:
            a5 = a3
            while a5 < bound:
                vals.append(a5)
                a5 *= 5
            a3 *= 3
        a2 *= 2
    return sorted(vals)


def check_jump_identity_exact(limit: int) -> dict:
    """(J) exact finite jump identity at every prime-power boundary R <= limit."""
    smooth = smooth_below(limit + 1)
    boundaries = sorted({p ** m for p in PRIMES for m in range(1, 64) if p ** m <= limit})
    failures = []
    for R in boundaries:
        left = sum((Fraction(1, height(s)) for s in smooth if 2 <= s < R), Fraction())
        right = Fraction()
        for p in PRIMES:
            r = p
            while r <= R:
                cnt = sum(1 for s in smooth if 2 <= s < r)
                right += Fraction((p - 1) * cnt, height(r))
                r *= p
        right += Fraction(sum(1 for s in smooth if 2 <= s < R), height(R))
        if left != right:
            failures.append({"R": R, "left": str(left), "right": str(right)})
    return {"boundaries_checked": len(boundaries), "limit": limit, "failures": failures}


def check_boundary_clearing_exact(mmax: int) -> dict:
    """(C) p*H(s) | H(p^m) for every smooth s < p^m."""
    failures = []
    tested = 0
    for p in PRIMES:
        for m in range(1, mmax + 1):
            bound = p ** m
            hb = height(bound)
            for s in smooth_below(bound):
                if s < 1:
                    continue
                tested += 1
                if hb % (p * height(s)) != 0:
                    failures.append({"p": p, "m": m, "s": s})
    return {"pairs_tested": tested, "failures": failures}


def boundary_ladder(nmax: int) -> list[tuple[float, int, int]]:
    """Merged ordered prime-power boundaries below 2^nmax, as (log2 r, prime, exponent)."""
    rows = []
    for p, lg in ((2, 1.0), (3, L3), (5, L5)):
        m = 1
        while m * lg <= nmax:
            rows.append((m * lg, p, m))
            m += 1
    rows.sort()
    return rows


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--nmax", type=int, default=320, help="ladder depth in log2 units")
    ap.add_argument("--identity-limit", type=int, default=100_000)
    ap.add_argument("--clearing-mmax", type=int, default=9)
    ap.add_argument("--annulus-starts", type=int, default=400)
    ap.add_argument("--receipt", type=str, default=None)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    mp.dps = 60
    counter = Counter(args.nmax + 4.0)

    identity = check_jump_identity_exact(args.identity_limit)
    clearing = check_boundary_clearing_exact(args.clearing_mmax)

    # ---- (R) boundary ladder, digits C_j, tails U_j -------------------------
    ladder = boundary_ladder(args.nmax)
    logs = [row[0] for row in ladder]
    primes = [row[1] for row in ladder]
    counts = [counter.between(logs[j], logs[j + 1]) for j in range(len(ladder) - 1)]

    # U_j = sum_{k>=j} C_k / (p_j ... p_k)
    def boundary_state(j: int) -> mp.mpf:
        total, den = mp.mpf(0), mp.mpf(1)
        for k in range(j, len(counts)):
            den *= primes[k]
            total += mp.mpf(counts[k]) / den
            if den > mp.mpf(10) ** 45:
                break
        return total

    rec_failures = []
    for j in range(0, min(len(counts) - 60, 200)):
        lhs = boundary_state(j + 1)
        rhs = primes[j] * boundary_state(j) - counts[j]
        if abs(lhs - rhs) > mp.mpf(10) ** (-30):
            rec_failures.append({"j": j, "defect": mp.nstr(abs(lhs - rhs), 6)})

    # cross-check against the dyadic states X_a computed on the dyadic ladder
    dy_index = {row[2]: j for j, row in enumerate(ladder) if row[1] == 2}
    cross = []
    for a in (5, 20, 60, 120, 200):
        if a in dy_index and dy_index[a] < len(counts) - 80:
            cross.append({"a": a, "U_at_2^a": mp.nstr(boundary_state(dy_index[a]), 15)})

    # ---- (B) two-sided bounds on the dyadic states --------------------------
    def lower_bound(a: int) -> float:
        return (math.floor(a / (2 * L3)) + 1) * (math.floor(a / (2 * L5)) + 1) / 60.0

    def upper_bound(a: int) -> int:
        return a * a + 6 * a + 11

    bound_rows, bound_failures = [], []
    for a in (10, 50, 100, 200, 300):
        if a not in dy_index or dy_index[a] >= len(counts) - 80:
            continue
        xa = float(boundary_state(dy_index[a]))
        lo, hi = lower_bound(a), upper_bound(a)
        ok = lo <= xa <= hi
        bound_rows.append({"a": a, "lower": lo, "X_a": xa, "upper": hi, "ok": ok})
        if not ok:
            bound_failures.append(a)

    # ---- (A) residue annulus on the denominator-one branch ------------------
    # dyadic digits and radices, exact integers
    def dyadic_blocks(nmax: int):
        bs, ds = [0] * (nmax + 2), [0] * (nmax + 2)
        for n in range(1, nmax + 1):
            u3 = (math.floor(n / L3) + 1) * L3
            u5 = (math.floor(n / L5) + 1) * L5
            d3 = 1 if u3 < n + 1 else 0
            d5 = 1 if u5 < n + 1 else 0
            cuts = sorted([float(n)] + ([u3] if d3 else []) + ([u5] if d5 else []) + [float(n + 1)])
            digit = 0
            for lo, hi in zip(cuts[:-1], cuts[1:]):
                if hi <= lo:
                    continue
                w = 1
                if d3 and hi <= u3:
                    w *= 3
                if d5 and hi <= u5:
                    w *= 5
                digit += w * counter.between(lo, hi)
            bs[n], ds[n] = 2 * 3 ** d3 * 5 ** d5, digit
        return bs, ds

    win_max = 8 * (max(args.annulus_starts, 2) - 1).bit_length() + 24
    bs, ds = dyadic_blocks(args.annulus_starts + win_max + 2)
    one_sided = two_sided_only = inconclusive = 0
    annulus_examples = []
    for a in range(1, args.annulus_starts + 1):
        Q, E, L = 1, 0, 0
        while L < win_max and Q <= upper_bound(a + L):
            Q *= bs[a + L]
            E = bs[a + L] * E + ds[a + L] if L else ds[a]
            L += 1
        # rebuild E consistently: E_{a,L} = sum_j d_{a+j} prod_{r>j} b_{a+r}
        Q, E = 1, 0
        for r in range(L):
            E = E * bs[a + r] + ds[a + r]
            Q *= bs[a + r]
        rho = (-E) % Q
        lo, hi = lower_bound(a + L), upper_bound(a + L)
        if rho == 0 or rho > hi:
            one_sided += 1
        elif rho < lo:
            two_sided_only += 1
            if len(annulus_examples) < 5:
                annulus_examples.append({"a": a, "window": L, "rho": rho,
                                         "lower": lo, "upper": hi})
        else:
            inconclusive += 1

    receipt = {
        "problem_id": "erdos_269",
        "checker": "check_erdos269_prime_power_boundary_ladder",
        "parameters": {"nmax": args.nmax, "identity_limit": args.identity_limit,
                       "clearing_mmax": args.clearing_mmax,
                       "annulus_starts": args.annulus_starts},
        "J_jump_identity_exact": identity,
        "C_boundary_clearing_exact": clearing,
        "R_boundary_recurrence": {"ladder_length": len(ladder),
                                  "steps_checked": min(len(counts) - 60, 200),
                                  "failures": rec_failures,
                                  "dyadic_cross_check": cross},
        "B_two_sided_state_bounds": {"rows": bound_rows, "failures": bound_failures},
        "A_residue_annulus_denominator_one": {
            "starts": args.annulus_starts,
            "excluded_one_sided": one_sided,
            "excluded_only_by_lower_bound": two_sided_only,
            "inconclusive": inconclusive,
            "examples_gained_by_lower_bound": annulus_examples,
            "boundary": "denominator-one branch only; not an irrationality proof",
        },
        "min_float_slack": counter.min_slack,
    }
    ok = (not identity["failures"] and not clearing["failures"]
          and not rec_failures and not bound_failures)
    receipt["status"] = "pass" if ok else "fail"

    if args.receipt:
        path = pathlib.Path(args.receipt)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    if args.json:
        print(json.dumps(receipt, indent=2, sort_keys=True))
    else:
        print(f"(J) jump identity   : {identity['boundaries_checked']} exact boundaries <= "
              f"{args.identity_limit}, failures {len(identity['failures'])}")
        print(f"(C) boundary clear  : {clearing['pairs_tested']} exact (p,m,s) pairs, "
              f"failures {len(clearing['failures'])}")
        print(f"(R) ladder recurr.  : {min(len(counts)-60,200)} steps, failures {len(rec_failures)}")
        for row in cross:
            print(f"      U at 2^{row['a']:<4} = {row['U_at_2^a']}")
        print("(B) state bounds    :")
        for row in bound_rows:
            print(f"      a={row['a']:>4}  {row['lower']:>10.2f} <= {row['X_a']:>12.4f} "
                  f"<= {row['upper']:<10}  {'ok' if row['ok'] else 'FAIL'}")
        ann = receipt["A_residue_annulus_denominator_one"]
        print(f"(A) residue annulus : starts {ann['starts']}; excluded one-sided "
              f"{ann['excluded_one_sided']}; gained by lower bound "
              f"{ann['excluded_only_by_lower_bound']}; inconclusive {ann['inconclusive']}")
        print(f"status              : {receipt['status']}  (min float slack "
              f"{counter.min_slack:.2e})")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
