#!/usr/bin/env python3
"""Replay algebra/scalar checks for ExteriorFibreDefectCriticalStability.md.

This checker is deliberately modest: it verifies the exact algebraic
translations and deterministic high-precision instances of the localization
inequalities.  Rouche, spectral factorization, Clark's identity, and the
Kovalev--Yang theorem and the attachment lemma remain ordinary mathematical
inputs of the note.
"""

from fractions import Fraction
from mpmath import mp


mp.dps = 100


def qmp(x: Fraction) -> mp.mpf:
    return mp.mpf(x.numerator) / x.denominator


def audit(n: int, m: int, p: Fraction) -> dict[str, mp.mpf]:
    d = n - m
    p0 = Fraction(d, n + m)
    assert 0 < p < p0

    # Exact capacity/Clark-defect translations, equation (4).
    delta = Fraction(1, 1) - p
    delta /= 1 + p
    delta -= Fraction(m, n)
    delta_a = Fraction((n + m), n) * (p0 - p) / (1 + p)
    delta_b = 2 * (p0 - p) / ((1 + p) * (1 + p0))
    assert delta == delta_a == delta_b

    # Exact solution of the Jensen inequality in equation (11).
    sum_h_ceiling = Fraction(n * n, 1) * delta / (
        1 + Fraction(n, m) * delta
    )
    assert (
        delta * n * (n - sum_h_ceiling / m) == sum_h_ceiling
    )

    # Exact expression (13).
    e2 = (
        Fraction(n * (d + 1) ** 2, m * m)
        * (1 + p) ** 2
        * delta
        / (p * (1 + Fraction(n, m) * delta))
    )
    assert e2 > 0

    E = mp.sqrt(qmp(e2))
    sigma = 2 * mp.sin(mp.pi / n)
    threshold = min(
        mp.mpf(1) / (2 * (n + 2)),
        sigma / (2 * (1 + mp.sqrt(m - 1))),
    )
    assert E < threshold

    rho = 2 * E
    # The squared Cauchy--Schwarz bound from (16) is strictly below one.
    rouche_bound_sq = E**2 * (
        rho ** -2 + (m - 1) * (sigma - rho) ** -2
    )
    assert rouche_bound_sq < 1

    R0 = rho / (1 - rho)
    assert R0 < mp.mpf(1) / (n + 1)
    D0 = mp.mpf(2) / (n + 1) - R0
    assert D0 > 0
    Gamma0 = mp.mpf(n) / (1 - R0) ** 2 + mp.mpf(2 * m) / D0**2
    value_ceiling = mp.exp(Gamma0 * R0**2 / 2)
    assert value_ceiling > 1

    # Saturation itself has exactly zero defect.
    saturation_delta = (1 - p0) / (1 + p0) - Fraction(m, n)
    assert saturation_delta == 0

    return {
        "delta": qmp(delta),
        "E": E,
        "threshold": threshold,
        "R0": R0,
        "value_ceiling": value_ceiling,
    }


def main() -> None:
    # The theorem is local near saturation.  These exact rational inputs are
    # deliberately close enough to p0 that the explicit sufficient condition
    # (17), rather than a floating-point accident, has a comfortable margin.
    cases = [
        (5, 3, Fraction(1, 4) - Fraction(1, 10**8)),
        (6, 3, Fraction(1, 3) - Fraction(1, 10**8)),
        (7, 5, Fraction(1, 6) - Fraction(1, 10**9)),
    ]
    for n, m, p in cases:
        out = audit(n, m, p)
        print(
            f"n={n} m={m} delta={mp.nstr(out['delta'], 8)} "
            f"E={mp.nstr(out['E'], 8)} "
            f"threshold={mp.nstr(out['threshold'], 8)} "
            f"R0={mp.nstr(out['R0'], 8)} "
            f"critical_value_ceiling={mp.nstr(out['value_ceiling'], 10)}"
        )
    print("PASS exterior fibre-defect critical stability audit")


if __name__ == "__main__":
    main()
