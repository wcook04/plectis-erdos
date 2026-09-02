"""Erdős #1049: is (14,12,14;27) the best direction for the rational-base contour?

For a direction (alpha0, alpha1, alpha2; beta) on Zudilin's cone
    alpha1 <= alpha2,  alpha1 + alpha2 < beta <= alpha0 + alpha2,
the rational-base threshold of the homogenised forms is theta*(dir) = C_0/C_1 with
    C_1 = (a0+a1+a2) b - (a1^2 + a2^2 + b^2)/2,
    C_0 = a1^2/2 + a0 a1 + (b-a2)(a2-a1) - (3/pi^2) (m^2 - J),
    J   = int_0^1 omega(x) d(-psi'(x)),
    omega(x) = max{0, [c21 x]+[c22 x]-[c11 x]-[c12 x], [c01 x]+[c21 x]-[c00 x]-[c12 x]},
    c = (a0+a1+a2-b, a0, a1, a2, b-a1, b-a2),  m = max c,
exactly Zudilin's (25), (26).  theta* is invariant under scaling the direction, so we
enumerate primitive directions with max entry <= BOUND and report the best few.
The same enumeration is the one Zudilin performed for mu = C_1/C_0; here it is
re-run because a different objective would not change the answer (theta* = 1/mu),
but a larger box might.
"""
from __future__ import annotations

import json
import math
import os
import sys
from fractions import Fraction as Fr
from functools import lru_cache

from mpmath import mp, mpf, pi, polygamma

mp.dps = 30
BOUND = int(sys.argv[1]) if len(sys.argv) > 1 else 22
THREE_OVER_PI2 = 3 / pi ** 2


@lru_cache(maxsize=None)
def psi1(num: int, den: int):
    return polygamma(1, mpf(num) / den)


def theta_of(a0: int, a1: int, a2: int, b: int):
    c00, c01, c11, c21, c12, c22 = a0 + a1 + a2 - b, a0, a1, a2, b - a1, b - a2
    if c00 <= 0:
        return None
    m = max(c00, c01, c11, c21, c12, c22)
    C1 = Fr((a0 + a1 + a2) * b) - Fr(a1 * a1 + a2 * a2 + b * b, 2)
    C0p = Fr(a1 * a1, 2) + a0 * a1 + (b - a2) * (a2 - a1)
    cs = (c00, c01, c11, c21, c12, c22)
    bps = sorted({Fr(k, c) for c in cs for k in range(c + 1)})

    def omega(x: Fr) -> int:
        fl = lambda c: (c * x).numerator // (c * x).denominator
        return max(0, fl(c21) + fl(c22) - fl(c11) - fl(c12), fl(c01) + fl(c21) - fl(c00) - fl(c12))

    J = mpf(0)
    for u, v in zip(bps, bps[1:]):
        w = omega((u + v) / 2)
        if w:
            J += w * (psi1(u.numerator, u.denominator) - psi1(v.numerator, v.denominator))
    C0 = mpf(C0p.numerator) / C0p.denominator - THREE_OVER_PI2 * (m * m - J)
    if C0 <= 0:
        return None
    return C0 / (mpf(C1.numerator) / C1.denominator)


def main() -> int:
    best = []
    seen = 0
    for a1 in range(1, BOUND + 1):
        for a2 in range(a1, BOUND + 1):
            for b in range(a1 + a2 + 1, BOUND + 1):
                for a0 in range(b - a2, BOUND + 1):
                    if math.gcd(math.gcd(a0, a1), math.gcd(a2, b)) != 1:
                        continue
                    th = theta_of(a0, a1, a2, b)
                    seen += 1
                    if th is None:
                        continue
                    best.append((float(th), (a0, a1, a2, b)))
    best.sort(reverse=True)
    print(f"primitive directions with entries <= {BOUND}: {seen}; best ten by theta* = C0/C1:")
    for th, d in best[:10]:
        print(f"   {d}: theta* = {th:.12f}   mu = {1/th:.10f}")
    ref = theta_of(14, 12, 14, 27)
    print("reference (14,12,14;27): theta* =", float(ref), " mu =", float(1 / ref))
    receipt_dir = os.path.normpath(os.path.join(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "..", "state", "formal_math",
        "erdos257_period_noncollapse", "erdos1049_zudilin_region"))
    os.makedirs(receipt_dir, exist_ok=True)
    with open(os.path.join(receipt_dir, f"direction_search_bound{BOUND}.json"), "w", encoding="utf-8") as fh:
        json.dump({"bound": BOUND, "directions_scanned": seen,
                   "best": [{"direction": d, "theta_star": th, "mu": 1 / th} for th, d in best[:25]],
                   "reference_14_12_14_27": float(ref)}, fh, ensure_ascii=False, indent=1)
    return 0


if __name__ == "__main__":
    sys.exit(main())
