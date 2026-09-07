#!/usr/bin/env python3
"""Reproduce the computational evidence for the collinear-root theorem.

This script is a falsifier and exact-arithmetic companion, not proof authority.
The proof is the Chebyshev--Hadamard/resultant/interlacing argument in
``../CollinearRootCase.md`` and its formal kernels are in
``../SharpCollinearAlternation.lean`` and ``../CollinearRootCase.lean``.

Checks performed:

* the sharp constrained-Chebyshev gap constant
  ``1 / (2^(n-1) cos(pi/(2n))^n)`` survives deterministic random stress and
  is attained by the scaled Chebyshev root configuration;
* the Chebyshev leading-coefficient product is exactly
  ``2^((n-1)(n-2)/2)``;
* deterministic random points in ``[-1,1]`` satisfy the corresponding
  squared Vandermonde bound;
* the exact Legendre--Lobatto Fekete configurations satisfy both the clean
  bound and the closed all-degree discriminant formula;
* the rational cubic unsafe-gap value is exactly ``5471893/5400000 > 1``.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import math
import random

import numpy as np
import sympy as sp


def squared_vandermonde(points: list[float]) -> float:
    value = 1.0
    for i, left in enumerate(points):
        for right in points[i + 1 :]:
            value *= (right - left) ** 2
    return value


def clean_bound(n: int) -> Fraction:
    return Fraction(n**n, 2 ** ((n - 1) * (n - 2)))


def sharp_gap_height(n: int) -> float:
    r = math.cos(math.pi / (2 * n))
    return 1.0 / (2 ** (n - 1) * r**n)


def minimum_gap_peak(points: list[float]) -> float:
    """Return the smallest critical height between adjacent simple roots."""

    coefficients = np.poly(np.asarray(points, dtype=float))
    critical = np.roots(np.polyder(coefficients))
    real_critical = sorted(
        float(z.real) for z in critical if abs(float(z.imag)) <= 1e-8
    )
    if len(real_critical) != len(points) - 1:
        raise AssertionError("real-rooted derivative lost a numerical root")
    return min(abs(float(np.polyval(coefficients, c))) for c in real_critical)


def exact_lobatto_squared_vandermonde(n: int) -> sp.Rational:
    x = sp.symbols("x")
    legendre = sp.legendre(n - 1, x)
    lobatto = sp.Poly((x**2 - 1) * sp.diff(legendre, x), x)
    monic = lobatto.monic().as_expr()
    return abs(sp.discriminant(monic, x))


def exact_interval_fekete_formula(n: int) -> sp.Rational:
    """Squared Vandermonde maximum for ``n`` points in ``[-1, 1]``.

    The recurrence

        Lambda_(k+1) / Lambda_k
          = (k+1)^(k+1) (k-1)^(k-1) / (2k-1)^(2k-1)

    starts from ``Lambda_2 = 4``.  Its maximizers are the roots of
    ``(x^2-1) P'_(n-1)(x)``.
    """

    value = sp.Rational(4)
    for k in range(2, n):
        value *= sp.Rational(
            (k + 1) ** (k + 1) * (k - 1) ** (k - 1),
            (2 * k - 1) ** (2 * k - 1),
        )
    return sp.factor(value)


def run(max_n: int, samples: int, seed: int) -> bool:
    rng = random.Random(seed)
    ok = True
    print(f"seed={seed} samples_per_degree={samples}")

    for n in range(2, max_n + 1):
        exponent_sum = sum(max(j - 1, 0) for j in range(n))
        expected_exponent = (n - 1) * (n - 2) // 2
        scale_ok = exponent_sum == expected_exponent

        clean = clean_bound(n)
        bound_q = sp.Rational(clean.numerator, clean.denominator)
        bound = float(clean)
        worst_ratio = 0.0
        sharp_random_ratio = 0.0
        for sample_index in range(samples):
            points = sorted(rng.uniform(-1.0, 1.0) for _ in range(n))
            worst_ratio = max(worst_ratio, squared_vandermonde(points) / bound)
            diameter = points[-1] - points[0]
            normalized = [2 * (x - points[0]) / diameter - 1 for x in points]
            sharp_random_ratio = max(
                sharp_random_ratio,
                minimum_gap_peak(normalized) / sharp_gap_height(n),
            )

        r = math.cos(math.pi / (2 * n))
        chebyshev_roots = sorted(
            math.cos((2 * k - 1) * math.pi / (2 * n)) / r
            for k in range(1, n + 1)
        )
        sharp_equality_ratio = minimum_gap_peak(chebyshev_roots) / sharp_gap_height(n)
        sharp_ok = (
            sharp_random_ratio <= 1.0 + 2e-8
            and abs(sharp_equality_ratio - 1.0) <= 2e-8
        )

        lobatto = exact_lobatto_squared_vandermonde(n)
        fekete_formula = exact_interval_fekete_formula(n)
        formula_ok = lobatto == fekete_formula
        exact_ok = lobatto <= bound_q
        random_ok = worst_ratio <= 1.0 + 1e-12
        ok = ok and scale_ok and formula_ok and exact_ok and random_ok and sharp_ok
        print(
            f"n={n:2d} scale={scale_ok} "
            f"fekete_formula={formula_ok} "
            f"max_random_ratio={worst_ratio:.12g} "
            f"sharp_gap_random={sharp_random_ratio:.12g} "
            f"sharp_gap_equality={sharp_equality_ratio:.12g} "
            f"lobatto_ratio={float(lobatto / bound_q):.12g} "
            f"status={'PASS' if scale_ok and formula_ok and exact_ok and random_ok and sharp_ok else 'FAIL'}"
        )

    t = sp.symbols("t", real=True)
    cubic_vandermonde = ((t + 1) * 2 * (1 - t)) ** 2
    cubic_identity_ok = sp.expand(cubic_vandermonde - 4 * (1 - t**2) ** 2) == 0
    ok = ok and cubic_identity_ok
    print(
        "cubic_vandermonde=4(1-t^2)^2 "
        f"status={'PASS' if cubic_identity_ok else 'FAIL'}"
    )

    x = Fraction(-1, 3)
    unsafe = (x + Fraction(19, 20)) * (x - Fraction(9, 10)) * (
        x - Fraction(999, 1000)
    )
    unsafe_ok = unsafe == Fraction(5_471_893, 5_400_000) and unsafe > 1
    ok = ok and unsafe_ok
    print(f"unsafe_gap_value={unsafe} status={'PASS' if unsafe_ok else 'FAIL'}")
    print("PASS" if ok else "FAIL")
    return ok


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n", type=int, default=10)
    parser.add_argument("--samples", type=int, default=20_000)
    parser.add_argument("--seed", type=int, default=1041)
    args = parser.parse_args()
    if args.max_n < 2 or args.samples < 1:
        parser.error("--max-n must be at least 2 and --samples must be positive")
    return 0 if run(args.max_n, args.samples, args.seed) else 1


if __name__ == "__main__":
    raise SystemExit(main())
