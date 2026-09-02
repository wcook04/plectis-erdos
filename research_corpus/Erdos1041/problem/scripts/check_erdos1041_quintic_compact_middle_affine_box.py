#!/usr/bin/env python3
"""Exact arithmetic replay for QuinticCompactMiddleAffineBoxReduction.md."""

from fractions import Fraction

import sympy as sp


def positive_a_plus_b_sqrt(a: Fraction, b: Fraction, radicand: int) -> bool:
    """Decide a+b*sqrt(radicand)>0 using rational arithmetic."""
    if b == 0:
        return a > 0
    if b > 0:
        if a >= 0:
            return True
        return b * b * radicand > a * a
    if a <= 0:
        return False
    return a * a > b * b * radicand


def main() -> None:
    q = sp.sqrt(105)
    t = sp.Rational(5, 16) + 3 * q / 80
    phi_squared = sp.expand(
        (1 - t) ** 2 * (1 + t) ** 6 * (16 * t**2 - 4 * t + 1)
    )
    asserted = (
        sp.Rational(2963137215087, 419430400000)
        + sp.Rational(49597072497, 83886080000) * q
    )
    assert sp.simplify(phi_squared - asserted) == 0

    # The maximizer is the positive root of 40t^2-25t-2.
    assert sp.simplify(40 * t**2 - 25 * t - 2) == 0
    assert 0 < t < 1

    # Exact proof of sqrt(105)<41/4.
    assert 16 * 105 < 41**2
    upper_phi_squared = (
        Fraction(2963137215087, 419430400000)
        + Fraction(49597072497, 83886080000) * Fraction(41, 4)
    )
    radius_square_target = Fraction(13, 10) ** 10
    assert upper_phi_squared < radius_square_target

    # Vieta bounds from |u_j|<13/5.
    root_bound = Fraction(13, 5)
    a4_bound = 5 * root_bound
    a3_bound = 10 * root_bound**2
    a2_bound = 10 * root_bound**3
    assert a4_bound == 13
    assert a3_bound < 68
    assert a2_bound < 176

    # The derivative-root coordinates give a much tighter coefficient box.
    critical_bound = root_bound
    critical_a4_bound = Fraction(5, 4) * 3 * critical_bound
    critical_a3_bound = Fraction(5, 3) * 3 * critical_bound**2
    critical_a2_bound = Fraction(5, 2) * critical_bound**3
    assert critical_a4_bound == Fraction(39, 4) < 10
    assert critical_a3_bound == Fraction(169, 5) < 34
    assert critical_a2_bound == Fraction(2197, 50) < 44

    u, k1, k2, k3 = sp.symbols("u k1 k2 k3")
    derivative = sp.expand(5 * u * (u - k1) * (u - k2) * (u - k3))
    reconstructed = sp.integrate(derivative, (u, 0, u)) + 1
    assert sp.expand(sp.diff(reconstructed, u) - derivative) == 0
    assert sp.expand(reconstructed.subs(u, 0)) == 1

    # The exact gap is positive even before decimal rendering.
    gap_a = radius_square_target - Fraction(2963137215087, 419430400000)
    gap_b = -Fraction(49597072497, 83886080000)
    assert positive_a_plus_b_sqrt(gap_a, gap_b, 105)

    print("QUINTIC COMPACT-MIDDLE AFFINE BOX: PASS")
    print(f"t*={sp.N(t, 16)}")
    print(f"M5={sp.N(sp.sqrt(phi_squared), 16)}")
    print(f"M5^(1/5)={sp.N(phi_squared ** sp.Rational(1, 10), 16)}")
    print("exact outer radius: M5^(1/5) < 13/10")
    print("root-Vieta box: |a2|<176, |a3|<68, |a4|<13")
    print("preferred critical cube: |kappa_j|<13/5")
    print("critical-Vieta box: |a2|<44, |a3|<34, |a4|<10")


if __name__ == "__main__":
    main()
