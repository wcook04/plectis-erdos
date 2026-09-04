#!/usr/bin/env python3
"""Exact rational-ball no-go for the quintic Bernstein-or-J2 selector."""

from __future__ import annotations

from math import comb, isqrt

import sympy as sp


def sqrt_bounds(x: sp.Rational, digits: int = 40) -> tuple[sp.Rational, sp.Rational]:
    assert x >= 0
    scale = 10**digits
    num, den = int(sp.numer(x)), int(sp.denom(x))
    lo_int = isqrt((num * scale * scale) // den)
    while (lo_int + 1) ** 2 * den <= num * scale * scale:
        lo_int += 1
    while lo_int**2 * den > num * scale * scale:
        lo_int -= 1
    return sp.Rational(lo_int, scale), sp.Rational(lo_int + 1, scale)


def norm_bounds(z: sp.Expr) -> tuple[sp.Rational, sp.Rational]:
    return sqrt_bounds(sp.factor(sp.re(z * sp.conjugate(z))))


def ascending_coefficients(poly: sp.Poly) -> list[sp.Expr]:
    return list(reversed(poly.all_coeffs()))


def bernstein_controls(poly: sp.Poly, a: sp.Expr) -> list[sp.Expr]:
    coeff = ascending_coefficients(poly)
    q = [coeff[k] * a**k for k in range(6)]
    return [
        sp.factor(
            sum(q[k] * sp.Rational(comb(j, k), comb(5, k)) for k in range(j + 1))
        )
        for j in range(6)
    ]


def shifted_coefficients(expr: sp.Expr, w: sp.Symbol) -> list[sp.Expr]:
    return ascending_coefficients(sp.Poly(sp.expand(expr), w))


def taylor_modulus_bounds(
    poly: sp.Poly, z: sp.Symbol, w: sp.Symbol, center: sp.Expr, radius: sp.Rational
) -> tuple[sp.Rational, sp.Rational]:
    coeff = shifted_coefficients(poly.as_expr().subs(z, center + w), w)
    lower = norm_bounds(coeff[0])[0] - sum(
        norm_bounds(a)[1] * radius**k for k, a in enumerate(coeff) if k
    )
    upper = sum(norm_bounds(a)[1] * radius**k for k, a in enumerate(coeff))
    return lower, upper


def phase_row_lower(
    poly: sp.Poly,
    roots: list[sp.Expr],
    z: sp.Symbol,
    w: sp.Symbol,
    center: sp.Expr,
    radius: sp.Rational,
    root_index: int,
    distance_lower: sp.Rational,
    mu_upper: sp.Rational,
    t: sp.Rational,
) -> sp.Rational:
    """Lower-bound the exact endpoint-absorbed row H_i at one rational t."""

    coefficient_lower: list[sp.Rational] = []
    for k in range(2, 5):
        nk = sp.diff(poly.as_expr(), z, k) / sp.factorial(k)
        shifted = shifted_coefficients(nk.subs(z, center + w), w)
        nk_lower = norm_bounds(shifted[0])[0] - sum(
            norm_bounds(a)[1] * radius**ell
            for ell, a in enumerate(shifted)
            if ell
        )
        assert nk_lower > 0
        coefficient_lower.append(nk_lower * distance_lower**k / mu_upper)

    # The terminal endpoint-absorbed coefficient is
    # |1+(a_i-c)^5/P(c)|.  Bound its numerator directly on the disk.
    terminal = sp.expand(
        (roots[root_index] - (center + w)) ** 5
        + poly.as_expr().subs(z, center + w)
    )
    shifted_terminal = shifted_coefficients(terminal, w)
    terminal_lower = norm_bounds(shifted_terminal[0])[0] - sum(
        norm_bounds(a)[1] * radius**ell
        for ell, a in enumerate(shifted_terminal)
        if ell
    )
    assert terminal_lower > 0
    terminal_lower /= mu_upper

    return (
        1
        - t**5
        + sum(coefficient_lower[k - 2] * t**k for k in range(2, 5))
        + terminal_lower * t**5
    )


def main() -> None:
    # Decimal strings are exact rationals.  This is the rationalization of the
    # mixed first/second-mode torus witness found by the adversarial probe.
    raw = [
        ("0.9976274963", "-0.0688286176"),
        ("0.2336442603", "0.9723211196"),
        ("-0.8077935542", "0.5894638019"),
        ("-0.8347956985", "-0.5505580276"),
        ("0.3448410498", "-0.9386600292"),
    ]
    roots = [sp.Rational(x) + sp.I * sp.Rational(y) for x, y in raw]
    assert all(sp.sign(1 - sp.re(a * sp.conjugate(a))) == 1 for a in roots)

    z, w = sp.symbols("z w")
    poly = sp.Poly(sp.prod(z - a for a in roots), z)
    coeff = ascending_coefficients(poly)

    # Both low modes are genuinely present, and the second is dominant.
    b1_sq = sp.factor(sp.re(coeff[1] * sp.conjugate(coeff[1])))
    b2_sq = sp.factor(sp.re(coeff[2] * sp.conjugate(coeff[2])))
    assert b1_sq > sp.Rational(1, 500)
    assert b2_sq > 4 * b1_sq

    # The normalized Vandermonde is in the finite near-gon band, not at the
    # regular equality itself.
    disc_abs = norm_bounds(poly.discriminant())[0]
    discriminant_ratio_lower = disc_abs / 5**5
    disc_abs_upper = norm_bounds(poly.discriminant())[1]
    discriminant_ratio_upper = disc_abs_upper / 5**5
    assert sp.Rational(9597, 10000) < discriminant_ratio_lower
    assert discriminant_ratio_upper < sp.Rational(9599, 10000)

    # Exactly one root passes every Bernstein control.  The other four have
    # the displayed exact failing controls.
    failing_indices: list[int | None] = [1, 1, None, 3, 1]
    safe: list[bool] = []
    for a, failed in zip(roots, failing_indices, strict=True):
        controls = bernstein_controls(poly, a)
        gaps = [sp.factor(sp.re(b * sp.conjugate(b)) - 1) for b in controls]
        if failed is None:
            assert all(sp.sign(gap) == -1 for gap in gaps)
            safe.append(True)
        else:
            assert sp.sign(gaps[failed]) == 1
            safe.append(False)
    assert safe == [False, False, True, False, False]

    # (center, nearest root, second-nearest root, rational witness t).
    # The first three critical disks lie in {|P|<1}; the fourth lies outside.
    critical_data: list[tuple[sp.Expr, int, int, sp.Rational | None]] = [
        (
            sp.Rational("-0.08110254623302735637")
            + sp.I * sp.Rational("0.45420358003252453847"),
            1,
            2,
            sp.Rational(3143, 10000),
        ),
        (
            sp.Rational("-0.39725974112619382945")
            + sp.I * sp.Rational("-0.06141457026133894437"),
            3,
            2,
            sp.Rational(326, 1000),
        ),
        (
            sp.Rational("0.38081381182063186505")
            + sp.I * sp.Rational("-0.23575517147048456797"),
            0,
            4,
            sp.Rational(2281, 10000),
        ),
        (
            sp.Rational("0.04436731849858932077")
            + sp.I * sp.Rational("-0.15404324062070102613"),
            4,
            0,
            None,
        ),
    ]
    radius = sp.Rational(1, 10**10)
    centers = [row[0] for row in critical_data]
    for i in range(4):
        for j in range(i):
            assert norm_bounds(centers[i] - centers[j])[0] > 2 * radius

    margins: list[tuple[sp.Rational, sp.Rational]] = []
    derivative = poly.diff()
    for row_index, (center, nearest, second, t) in enumerate(critical_data):
        # Rouche: on |w|=radius the linear Taylor term of P' dominates.
        shifted_derivative = shifted_coefficients(
            derivative.as_expr().subs(z, center + w), w
        )
        linear_lower = norm_bounds(shifted_derivative[1])[0]
        remainder_upper = sum(
            norm_bounds(a)[1] * radius**k
            for k, a in enumerate(shifted_derivative)
            if k != 1
        )
        assert linear_lower * radius > remainder_upper

        mu_lower, mu_upper = taylor_modulus_bounds(poly, z, w, center, radius)

        distance_bounds: list[tuple[sp.Rational, sp.Rational]] = []
        for a in roots:
            lower, upper = norm_bounds(a - center)
            distance_bounds.append((lower - radius, upper + radius))
        assert distance_bounds[nearest][1] < distance_bounds[second][0]
        assert distance_bounds[second][1] < min(
            distance_bounds[j][0] for j in range(5) if j not in (nearest, second)
        )

        if t is None:
            assert row_index == 3
            assert mu_lower > 1
            continue

        assert mu_upper < 1
        second_lower, second_upper = distance_bounds[second]
        s_lower = second_lower**2 * sum(
            1 / distance_bounds[j][1] ** 2 for j in range(5) if j != second
        )
        energy_lower = (1 - t) * (1 + (2 * t + s_lower * t**2) / 4) ** 2
        phase_lower = phase_row_lower(
            poly,
            roots,
            z,
            w,
            center,
            radius,
            second,
            second_lower,
            mu_upper,
            t,
        )
        energy_margin = sp.factor(mu_lower * energy_lower - 1)
        phase_margin = sp.factor(mu_lower * phase_lower - 1)
        assert energy_margin > sp.Rational(2, 100000)
        assert phase_margin > sp.Rational(1, 100)
        margins.append((energy_margin, phase_margin))

    # Four disjoint one-zero disks exhaust the degree-four derivative.  Every
    # admissible critical point therefore fails mu*J2<=1, since at the stated
    # t both exact rows exceed 1/mu; the remaining critical point has mu>1.
    assert len(margins) == 3 and derivative.degree() == 4

    print("quintic Bernstein-or-J2 mixed-mode no-go: PASS")
    print("exact Bernstein-safe root count: 1")
    print(
        "normalized Vandermonde interval: "
        f"[{float(discriminant_ratio_lower):.12f}, "
        f"{float(discriminant_ratio_upper):.12f}]"
    )
    for i, (energy_margin, phase_margin) in enumerate(margins):
        print(
            f"admissible critical disk {i}: "
            f"mu*F-1>{float(energy_margin):.9g}, "
            f"mu*H-1>{float(phase_margin):.9g}"
        )
    print("fourth critical disk: |P|>1")
    print("boundary: certificate no-go only; not a counterexample to Erdos 1041")


if __name__ == "__main__":
    main()
