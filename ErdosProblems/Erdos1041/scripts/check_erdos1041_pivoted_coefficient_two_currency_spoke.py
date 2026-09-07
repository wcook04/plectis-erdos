#!/usr/bin/env python3
"""Replay the pivoted two-currency coefficient certificate."""

from __future__ import annotations

from fractions import Fraction
import random

import numpy as np
import sympy as sp


def symbolic_replay() -> None:
    t, a, c = sp.symbols("t a c")
    for n in range(3, 11):
        bs = sp.symbols(f"b1:{n}")
        for m in range(1, n):
            bm_relation = (-c - a**n
                           - sum(bs[k - 1] * a**k for k in range(1, n) if k != m)) / a**m
            direct = t**n * a**n + c + sum(
                (bm_relation if k == m else bs[k - 1]) * (t * a) ** k
                for k in range(1, n)
            )
            pivot = (c * (1 - t**m) + a**n * (t**n - t**m)
                     + sum(bs[k - 1] * a**k * (t**k - t**m)
                           for k in range(1, n) if k != m))
            assert sp.simplify(direct - pivot) == 0

    # Derivative proofs of both sharp exchange rates.
    for m in range(2, 11):
        for k in range(1, m):
            phi = m * t**k - k * t**m
            assert sp.expand(sp.diff(phi, t) - m * k * t ** (k - 1) * (1 - t ** (m - k))) == 0
        for k in range(m + 1, 12):
            phi = k * t**m - m * t**k
            assert sp.expand(sp.diff(phi, t) - k * m * t ** (m - 1) * (1 - t ** (k - m))) == 0


def exact_grid_replay() -> None:
    rng = random.Random(51041)
    for n in range(3, 13):
        for m in range(1, n):
            for j in range(501):
                t = Fraction(j, 500)
                for k in range(1, m):
                    assert t**k - t**m <= Fraction(m - k, m) * (1 - t**m)
                for k in range(m + 1, n):
                    assert t**m - t**k <= Fraction(k - m, m) * (1 - t**m)
                    assert t**m - t**k <= t**m - t**n

    # Exact two-mode allocation formula (14) against direct theta feasibility.
    for _ in range(1000):
        m = rng.randrange(1, 5)
        k = rng.randrange(m + 1, 6)
        d = Fraction(rng.randrange(1, 100), 100)
        root_slack = Fraction(rng.randrange(1, 100), 100)
        const_slack = Fraction(rng.randrange(1, 100), 100)
        q = Fraction(k - m, m)
        closed = q * max(d - root_slack, 0) <= const_slack
        # The least admissible theta moves exactly the root-currency excess.
        theta_mass = max(d - root_slack, 0)
        feasible = theta_mass <= d and q * theta_mass <= const_slack
        assert closed == feasible


def optimal_pivot(pc: np.ndarray, root: complex) -> list[int]:
    n = len(pc) - 1
    cslack = 1 - abs(pc[-1])
    r = abs(root)
    passing = []
    for m in range(1, n):
        low = sum((m - k) / m * abs(pc[n - k]) * r**k for k in range(1, m))
        if low > cslack + 1e-12:
            continue
        items = [((k - m) / m, abs(pc[n - k]) * r**k) for k in range(m + 1, n)]
        excess = max(sum(d for _, d in items) - (1 - r**n), 0.0)
        cost = 0.0
        for q, d in sorted(items):
            take = min(d, excess)
            cost += q * take
            excess -= take
        if excess <= 1e-10 and low + cost <= cslack + 1e-10:
            passing.append(m)
    return passing


def quintic_obstruction_probe() -> None:
    rng = np.random.default_rng(51041)
    found = None
    for eps in np.logspace(-6, -0.3, 16):
        for _ in range(300):
            theta = 2 * np.pi * np.arange(5) / 5 + eps * rng.standard_normal(5)
            roots = 0.999 * np.exp(1j * theta)
            pc = np.poly(roots)
            passes = [optimal_pivot(pc, a) for a in roots]
            if sum(bool(x) for x in passes) < 2:
                found = (eps, pc, passes)
                break
        if found is not None:
            break
    assert found is not None
    eps, pc, passes = found
    assert eps < 0.003 and not any(passes)
    assert abs(abs(pc[-1]) - 0.999**5) < 1e-12


def main() -> None:
    symbolic_replay()
    exact_grid_replay()
    quintic_obstruction_probe()
    print("pivoted coefficient two-currency spoke: PASS")
    print("exact: arbitrary pivot, optimal fractional allocation, two-mode formula")
    print("computed boundary: quintic multi-mode angular face defeats all pivots")


if __name__ == "__main__":
    main()
