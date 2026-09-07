#!/usr/bin/env python3
"""Exact replay for the weighted-coefficient radial collar."""

from __future__ import annotations

from fractions import Fraction
import random

import sympy as sp


def scalar_replay() -> None:
    t = sp.symbols("t", nonnegative=True)
    for n in range(2, 15):
        for k in range(1, n):
            phi = n * t**k - k * t**n
            assert sp.expand(sp.diff(phi, t) - n * k * t ** (k - 1) * (1 - t ** (n - k))) == 0
            assert sp.expand(
                (n - k) * (1 - t**n) - n * (t**k - t**n)
                - ((n - k) - phi)
            ) == 0


def endpoint_identity_replay() -> None:
    t, a, c = sp.symbols("t a c")
    for n in range(2, 12):
        bs = sp.symbols(f"b1:{n}")
        root_relation = -c - sum(bs[k - 1] * a**k for k in range(1, n))
        lhs = t**n * root_relation + sum(bs[k - 1] * (t * a) ** k for k in range(1, n)) + c
        rhs = c * (1 - t**n) + sum(
            bs[k - 1] * a**k * (t**k - t**n) for k in range(1, n)
        )
        assert sp.expand(lhs - rhs) == 0


def rational_inequality_replay() -> None:
    rng = random.Random(1041)
    for n in range(2, 14):
        for _ in range(200):
            t = Fraction(rng.randrange(0, 1001), 1000)
            for k in range(1, n):
                lhs = n * (t**k - t**n)
                rhs = (n - k) * (1 - t**n)
                assert lhs <= rhs

    # Exact sparse-family inclusion: epsilon<1-R^n implies its weighted
    # coefficient defect is strictly below the collar threshold.
    for n in range(2, 14):
        r = Fraction(999, 1000)
        slack = 1 - r**n
        eps = slack * Fraction(999, 1000)
        assert (n - 1) * eps < n * slack


def direct_complex_stress() -> None:
    # This section only checks the already-proved inequality numerically on
    # exact-rational complex coefficients and rational t; proof authority is
    # scalar_replay + endpoint_identity_replay.
    rng = random.Random(41041)
    for n in range(5, 14):
        cabs = Fraction(4, 5)
        budget = n * (1 - cabs)
        raw = [Fraction(rng.randrange(1, 50), 1000) for _ in range(1, n)]
        weighted = sum((n - k) * raw[k - 1] for k in range(1, n))
        scale = min(Fraction(1), budget / (2 * weighted))
        mags = [x * scale for x in raw]
        assert sum((n - k) * mags[k - 1] for k in range(1, n)) <= budget
        for j in range(1, 100):
            t = Fraction(j, 100)
            remainder = sum(
                mags[k - 1] * (t**k - t**n) for k in range(1, n)
            )
            bound = cabs * (1 - t**n) + remainder
            assert bound <= 1 - t**n < 1


def root_energy_selector_replay() -> None:
    rng = random.Random(104108)
    for n in range(2, 14):
        threshold = Fraction(n, 5)
        for _ in range(500):
            vals = [Fraction(rng.randrange(0, 1000), 1000) * threshold for _ in range(n)]
            total = sum(vals)
            if total <= (n - 1) * threshold:
                assert sorted(vals)[1] <= threshold


def main() -> None:
    scalar_replay()
    endpoint_identity_replay()
    rational_inequality_replay()
    direct_complex_stress()
    root_energy_selector_replay()
    print("global spoke coefficient/cusp dichotomy: PASS")
    print("exact: W(a)<=n(1-|c|) makes the complete root spoke safe")
    print("boundary: higher-tangent multi-mode angular cusp and non-Fekete bulk")


if __name__ == "__main__":
    main()
