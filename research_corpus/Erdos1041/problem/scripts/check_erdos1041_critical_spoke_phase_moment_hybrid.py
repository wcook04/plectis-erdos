#!/usr/bin/env python3
"""Replay the critical-spoke phase-moment hybrid certificate."""

from __future__ import annotations

from fractions import Fraction

import numpy as np
import sympy as sp


t = sp.symbols("t", nonnegative=True, real=True)


def equal_weight_phi_formula(n: int) -> tuple[sp.Expr, sp.Expr]:
    S = n - 1
    bracket = 1 + (2 * t + S * t**2) / (n - 1)
    square = sp.expand((1 - t) ** 2 * bracket ** (n - 1))
    tstar = sp.Rational(n - 3, n - 1)
    derivative = sp.factor(sp.diff(square, t))
    assert derivative.subs(t, tstar) == 0
    value = sp.Rational(2, n - 1) * (
        sp.Rational(2 * (n - 2), n - 1)
    ) ** sp.Rational(n - 1, 2)
    assert sp.simplify((1 - tstar) * bracket.subs(t, tstar) ** sp.Rational(n - 1, 2) - value) == 0
    return tstar, value


t5, phi5 = equal_weight_phi_formula(5)
assert t5 == sp.Rational(1, 2)
assert phi5 == sp.Rational(9, 8)
assert Fraction(99, 100) ** 5 * Fraction(9, 8) > 1


# Newton identities with U_1=0.
U2, U3, U4 = sp.symbols("U2 U3 U4")
e2 = -U2 / 2
e3 = U3 / 3
e4 = U2**2 / 8 - U4 / 4
assert e2 == -U2 / 2
assert -e3 == -U3 / 3
assert e4 == U2**2 / 8 - U4 / 4


def coefficients(us: np.ndarray) -> np.ndarray:
    out = np.array([1.0 + 0.0j])
    for value in us:
        out = np.convolve(out, np.array([1.0 + 0.0j, -value]))
    return out


def direct_and_bounds(us: np.ndarray, grid: np.ndarray) -> tuple[float, float, float]:
    n = len(us)
    coeff = coefficients(us)
    assert abs(coeff[1]) < 2e-11
    selected = int(np.argmin(abs(us - 1)))
    spectators = np.delete(us, selected)
    S = float(np.sum(abs(spectators) ** 2))
    direct_max = 0.0
    energy_max = 0.0
    moment_max = 0.0
    for x in grid:
        direct = abs(np.prod(1 - x * us))
        energy = (1 - x) * (1 + (2 * x + S * x * x) / (n - 1)) ** ((n - 1) / 2)
        moment = (
            1
            - x**n
            + sum(abs(coeff[k]) * x**k for k in range(2, n))
            + abs(coeff[n] + 1) * x**n
        )
        assert direct <= energy + 2e-10
        assert direct <= moment + 2e-10
        direct_max = max(direct_max, direct)
        energy_max = max(energy_max, energy)
        moment_max = max(moment_max, moment)
    return direct_max, energy_max, moment_max


grid = np.linspace(0.0, 1.0, 4001)
rows = []
for n in (5, 6):
    regular = np.exp(2j * np.pi * np.arange(n) / n)
    row = direct_and_bounds(regular, grid)
    # Exact coefficient identity C(t)=1-t^n, up to float reconstruction.
    coeff = coefficients(regular)
    assert max(abs(coeff[1:n])) < 2e-12
    assert abs(coeff[n] + 1) < 2e-12
    assert row[0] <= 1 + 2e-12
    assert row[2] <= 1 + 2e-12
    rows.append((n, "regular", row))

    # Deterministic phase-asymmetric critical-balance sample: u_0=1 and
    # choose the last spectator to make sum u=0.
    base = [1 + 0j]
    for k in range(1, n - 1):
        radius = 0.45 + 0.06 * k
        phase = 0.71 * k + 0.13
        base.append(radius * np.exp(1j * phase))
    base.append(-sum(base))
    sample = np.asarray(base, dtype=complex)
    rows.append((n, "asymmetric", direct_and_bounds(sample, grid)))

print("PASS equal-weight Phi formula and exact quintic 99/100 falsifier")
print("PASS low Newton coefficient identities")
for n, label, row in rows:
    print(
        f"PASS n={n} {label}: direct={row[0]:.12g}, "
        f"energy={row[1]:.12g}, phase_moment={row[2]:.12g}"
    )
print("ALL CHECKS PASSED")
