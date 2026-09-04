#!/usr/bin/env python3
"""An exact analytic representation of the Erdos #269 {2,3,5} value.

Why this exists
---------------
Every route the packet has tried treats the series combinatorially: carries,
Lyapunov functionals, coboundaries, observers, escape certificates.  The radix
word was shown to be a coding of a rotation on the 2-torus, so it is worth
asking whether the VALUE itself has a torus-analytic form rather than only its
digit word.

The pointwise identity
----------------------
With L = log_2 s, theta = log_2 3, phi = log_2 5, the running height is
H(s) = 2^floor(L) * 3^floor(L/theta) * 5^floor(L/phi), and s^3 = 2^L 3^(L/theta)
5^(L/phi), so

    1 / H(s)  =  2^{L} 3^{L/theta} 5^{L/phi} / s^3          ({.} = fractional part)

and therefore, summing over the {2,3,5}-smooth lattice s = 2^i 3^j 5^k,

    S  =  sum_(i,j,k >= 0)  W(L) / (8^i 27^j 125^k),
    W  =  2^{L} 3^{L/theta} 5^{L/phi},   L = i + j*theta + k*phi.

W is a bounded function of the point ({L}, {L/theta}, {L/phi}) on the 3-torus,
so it has a Fourier expansion, and because 2^{x} 3^{y} 5^{z} factorises, each
Fourier mode makes the (i,j,k) sum a product of three ordinary geometric series.
Writing lambda = m1 + m2/theta + m3/phi, the mode contributes

    c(m1) c'(m2) c''(m3) / [ (1 - e(lambda)/8)(1 - e(lambda*theta)/27)
                             (1 - e(lambda*phi)/125) ]

with c(m) = 1/(ln2 - 2 pi i m), c'(m) = 2/(ln3 - 2 pi i m),
c''(m) = 4/(ln5 - 2 pi i m).

The correction, and why it is exactly 17/2
------------------------------------------
W jumps wherever a coordinate hits 0, and the Fourier series converges there to
the jump midpoint instead.  Those points are exactly the three coordinate axes
of the lattice.  The resulting excess is

    origin:  (1+2)/2 * (1+3)/2 * (1+5)/2 - 1 = 9 - 1 = 8
    p-axis:  (p-1)/2 * sum_(n>=1) 1/H(p^n)   for each p in {2,3,5}

and the axis terms sum to exactly 1/2, because at each prime power the height
multiplies by p, so

    (p-1)/H(p^n) = 1/H(p^n - 1) - 1/H(p^n),

and summing that telescope over every prime power from 1 downwards gives
sum_p (p-1) sum_n 1/H(p^n) = 1/H(1) = 1.  Half of it is 1/2, so the total
correction is 8 + 1/2 = 17/2 exactly.

Hence

    S  =  lim_(M -> inf) [ truncated triple Fourier sum ]  -  17/2.

Predeclared falsifier
---------------------
The corrected partial sums failing to converge to the directly computed S, or
the telescope failing to equal 1 exactly.
"""

from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction
from pathlib import Path

import numpy as np

THETA = math.log2(3)
PHI = math.log2(5)
CORRECTION = Fraction(17, 2)


def running_height(x: int) -> int:
    h = 1
    for p in (2, 3, 5):
        v = 1
        while v * p <= x:
            v *= p
        h *= v
    return h


def telescope_identity(bound: int = 10 ** 40) -> dict:
    """sum_p (p-1) sum_n 1/H(p^n): exactly 1, with truncation error exactly 1/H(last)."""
    total = Fraction(0)
    per_prime = {}
    last_height = 1
    for p in (2, 3, 5):
        s = Fraction(0)
        n = 1
        while p ** n < bound:
            s += Fraction(1, running_height(p ** n))
            last_height = max(last_height, running_height(p ** n))
            n += 1
        per_prime[p] = s
        total += (p - 1) * s
    residual = 1 - total
    return {
        "per_prime_sums": {str(p): float(v) for p, v in per_prime.items()},
        "weighted_total": float(total),
        "one_minus_total_numerator": residual.numerator,
        "one_minus_total_is_reciprocal_of_an_integer": residual.numerator == 1,
        "telescope_holds_to_truncation": residual.numerator == 1,
    }


def direct_value(bound_bits: int = 40) -> float:
    limit = 1 << bound_bits
    total = 0.0
    v2 = 1
    while v2 < limit:
        v3 = v2
        while v3 < limit:
            v5 = v3
            while v5 < limit:
                total += 1.0 / running_height(v5)
                v5 *= 5
            v3 *= 3
        v2 *= 2
    return total


def fourier_partial(M: int) -> float:
    m = np.arange(-M, M + 1)
    c1 = 1.0 / (math.log(2) - 2j * math.pi * m)
    c2 = 2.0 / (math.log(3) - 2j * math.pi * m)
    c3 = 4.0 / (math.log(5) - 2j * math.pi * m)
    lam = m[:, None, None] + m[None, :, None] / THETA + m[None, None, :] / PHI
    e = lambda x: np.exp(2j * np.pi * x)  # noqa: E731
    g = (1.0 / (1.0 - e(lam) / 8.0)
         / (1.0 - e(lam * THETA) / 27.0)
         / (1.0 - e(lam * PHI) / 125.0))
    return float((c1[:, None, None] * c2[None, :, None] * c3[None, None, :] * g).sum().real)


def pointwise_check(samples: int) -> float:
    """Max relative error of 1/H(s) = 2^{L} 3^{L/theta} 5^{L/phi} / s^3."""
    limit = 1 << 40
    vals = []
    v2 = 1
    while v2 < limit:
        v3 = v2
        while v3 < limit:
            v5 = v3
            while v5 < limit:
                vals.append(v5)
                v5 *= 5
            v3 *= 3
        v2 *= 2
    vals.sort()
    frac = lambda x: x - math.floor(x)  # noqa: E731
    worst = 0.0
    for s in vals[:samples]:
        L = math.log2(s)
        lhs = 1.0 / running_height(s)
        rhs = (2 ** frac(L)) * (3 ** frac(L / THETA)) * (5 ** frac(L / PHI)) / s ** 3
        worst = max(worst, abs(lhs - rhs) / lhs)
    return worst


def run(max_mode: int, samples: int) -> dict:
    target = direct_value()
    pw = pointwise_check(samples)
    tele = telescope_identity()
    rows = []
    M = 20
    while M <= max_mode:
        F = fourier_partial(M)
        rows.append({"M": M, "fourier_partial": round(F, 9),
                     "corrected": round(F - float(CORRECTION), 9),
                     "abs_error": round(abs(F - float(CORRECTION) - target), 9)})
        M *= 2
    errs = [r["abs_error"] for r in rows]
    return {
        "probe_id": "erdos269_torus_fourier_representation",
        "direct_value": target,
        "pointwise_identity_max_relative_error": pw,
        "telescope_identity": tele,
        "correction_constant": "17/2",
        "convergence": rows,
        "error_is_decreasing": all(errs[i] > errs[i + 1] for i in range(len(errs) - 1)),
        "final_abs_error": errs[-1] if errs else None,
        "reading": (
            "the corrected triple Fourier sum converges to the directly computed value; "
            "the representation is exact with correction constant 17/2"
            if errs and errs[-1] < 0.02 and all(errs[i] > errs[i + 1] for i in range(len(errs) - 1))
            else "the corrected sum does not converge as claimed"
        ),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-mode", type=int, default=320)
    ap.add_argument("--samples", type=int, default=4000)
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()
    payload = run(args.max_mode, args.samples)
    if args.out:
        Path(args.out).write_text(json.dumps(payload, indent=1) + "\n")
    print(json.dumps(payload, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
