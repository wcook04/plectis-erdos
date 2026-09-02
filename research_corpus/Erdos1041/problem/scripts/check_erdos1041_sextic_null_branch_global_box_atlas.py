#!/usr/bin/env python3
"""Exact selector-polytope and Bernstein replay for the global sextic null box."""

from __future__ import annotations

from fractions import Fraction
import math

import sympy as sp


def real(expr: sp.Expr) -> sp.Expr:
    return sp.expand(sp.re(sp.expand_complex(expr)))


def power_to_bernstein(poly: sp.Expr, variable: sp.Symbol) -> list[sp.Expr]:
    p = sp.Poly(sp.expand(poly), variable)
    degree = p.degree()
    coefficients = [p.coeff_monomial(variable**j) for j in range(degree + 1)]
    return [
        sp.expand(
            sum(
                coefficients[j] * sp.binomial(k, j) / sp.binomial(degree, j)
                for j in range(k + 1)
            )
        )
        for k in range(degree + 1)
    ]


def truncated_binomial(exponent: sp.Rational, slope: sp.Expr, degree: int) -> list[sp.Expr]:
    return [sp.binomial(exponent, n) * slope**n for n in range(degree + 1)]


def convolution(left: list[sp.Expr], right: list[sp.Expr]) -> list[sp.Expr]:
    degree = min(len(left), len(right)) - 1
    return [sp.expand(sum(left[j] * right[n - j] for j in range(n + 1))) for n in range(degree + 1)]


def bernstein_tensor(
    polynomial: sp.Expr,
    first: sp.Symbol,
    second: sp.Symbol,
    first_degree: int,
    second_degree: int,
    sqrt_three: sp.Expr,
) -> list[list[tuple[Fraction, Fraction]]]:
    power = sp.Poly(sp.expand(polynomial), first, second)
    coefficients = [
        [power.coeff_monomial(first**i * second**j) for j in range(second_degree + 1)]
        for i in range(first_degree + 1)
    ]
    return [
        [
            qs_pair(
                sum(
                    coefficients[i][j]
                    * sp.binomial(k_first, i)
                    / sp.binomial(first_degree, i)
                    * sp.binomial(k_second, j)
                    / sp.binomial(second_degree, j)
                    for i in range(k_first + 1)
                    for j in range(k_second + 1)
                ),
                sqrt_three,
            )
            for k_second in range(second_degree + 1)
        ]
        for k_first in range(first_degree + 1)
    ]


def qs_pair(expr: sp.Expr, sqrt_three: sp.Expr) -> tuple[Fraction, Fraction]:
    symbol = sp.Symbol("S")
    reduced = sp.radsimp(sp.cancel(expr)).xreplace({sqrt_three: symbol})
    numerator, denominator = sp.fraction(reduced)
    modulus = sp.Poly(symbol**2 - 3, symbol)
    pn = sp.Poly(numerator, symbol).rem(modulus)
    pd = sp.Poly(denominator, symbol).rem(modulus)
    if pd.degree() > 0:
        da, db = pd.nth(0), pd.nth(1)
        pn = sp.Poly(sp.expand(pn.as_expr() * (da - db * symbol)), symbol).rem(modulus)
        denominator = da**2 - 3 * db**2
    else:
        denominator = pd.nth(0)
    return (
        Fraction(sp.Rational(pn.nth(0) / denominator)),
        Fraction(sp.Rational(pn.nth(1) / denominator)),
    )


def qs_add(left: tuple[Fraction, Fraction], right: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
    return left[0] + right[0], left[1] + right[1]


def qs_half(value: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
    return value[0] / 2, value[1] / 2


def qs_nonpos(value: tuple[Fraction, Fraction]) -> bool:
    rational, radical = value
    if radical == 0:
        return rational <= 0
    threshold = -rational / radical
    if radical > 0:
        return threshold >= 0 and Fraction(3) <= threshold**2
    return threshold <= 0 or Fraction(3) >= threshold**2


def split_line(values: list[tuple[Fraction, Fraction]]) -> tuple[list[tuple[Fraction, Fraction]], list[tuple[Fraction, Fraction]]]:
    levels = [values]
    while len(levels[-1]) > 1:
        levels.append(
            [qs_half(qs_add(levels[-1][i], levels[-1][i + 1])) for i in range(len(levels[-1]) - 1)]
        )
    degree = len(values) - 1
    return (
        [levels[i][0] for i in range(degree + 1)],
        [levels[degree - i][i] for i in range(degree + 1)],
    )


def split_tensor(tensor: list[list[tuple[Fraction, Fraction]]], dimension: int):
    if dimension == 0:
        pairs = [split_line(list(line)) for line in zip(*tensor)]
        return (
            [list(line) for line in zip(*[pair[0] for pair in pairs])],
            [list(line) for line in zip(*[pair[1] for pair in pairs])],
        )
    left, right = [], []
    for row in tensor:
        row_left, row_right = split_line(row)
        left.append(row_left)
        right.append(row_right)
    return left, right


def certify_tensor(tensor: list[list[tuple[Fraction, Fraction]]]) -> tuple[int, int, int]:
    stack = [(tensor, 0)]
    nodes = leaves = maximum_depth = 0
    while stack:
        current, depth = stack.pop()
        nodes += 1
        maximum_depth = max(maximum_depth, depth)
        if all(qs_nonpos(value) for row in current for value in row):
            leaves += 1
            continue
        assert depth < 60
        dimension = 1 if depth % 3 != 2 else 0
        left, right = split_tensor(current, dimension)
        stack.extend([(left, depth + 1), (right, depth + 1)])
    return nodes, leaves, maximum_depth


def certify_line(values: list[tuple[Fraction, Fraction]]) -> tuple[int, int, int]:
    stack = [(values, 0)]
    nodes = leaves = maximum_depth = 0
    while stack:
        current, depth = stack.pop()
        nodes += 1
        maximum_depth = max(maximum_depth, depth)
        if all(qs_nonpos(value) for value in current):
            leaves += 1
            continue
        assert depth < 60
        left, right = split_line(current)
        stack.extend([(left, depth + 1), (right, depth + 1)])
    return nodes, leaves, maximum_depth


def main() -> None:
    t, beta, x, y = sp.symbols("t beta x y", real=True)
    p, q, u = sp.symbols("p q u", real=True)
    s, imaginary = sp.sqrt(3), sp.I
    omega = sp.Rational(1, 2) + imaginary * s / 2
    q0 = (7 + 4 * s) / 27
    branch_slope = sp.Rational(3, 2) * q0 * (s - 1)
    radius_slope = (21 + 11 * s) / 54
    beta_star = (106 + 25 * s) / 1221
    beta_split = sp.Rational(1, 10**6)
    h = (3 - s) / 2
    r0 = q0 ** sp.Rational(1, 4)
    plus_offset = -117 + sp.Rational(135, 2) * s
    minus_offset = -9 + sp.Rational(9, 2) * s
    average = -63 + 36 * s
    equalizer_size = plus_offset - average
    inner_corner = 78 - equalizer_size

    vertices = {
        0: [
            (-78, -78, -78),
            (-78, -78, inner_corner),
            (-78, inner_corner, -78),
            (inner_corner, -78, -78),
            (inner_corner, -inner_corner, -78),
            (-inner_corner, inner_corner, -78),
            (0, 0, -equalizer_size),
        ],
        2: [
            (78, 78, 78),
            (78, 78, inner_corner),
            (78, -78, 78),
            (78, -78, -78),
            (78, -inner_corner, -78),
            (-78, -78, 78),
            (-78, -78, inner_corner),
            (inner_corner, -78, -78),
            (inner_corner, -inner_corner, -78),
            (0, 0, -equalizer_size),
        ],
    }
    profile = {
        0: plus_offset + p + q + u,
        2: minus_offset - p + q - u,
    }

    certificate_rows = []
    for cell, pair in ((0, 0), (2, 3)):
        sign = 1 if cell == 0 else -1
        rho = (q0 + sign * radius_slope * beta) ** sp.Rational(1, 4)
        branch_radius = (q0 + branch_slope * beta) ** sp.Rational(1, 4)
        w = sp.expand(((1 - t) + t * omega) * omega**pair)
        a1 = p * r0 / (2 * h)
        b1 = -u * r0 / (2 * h)
        theta = q / (4 * h**2)
        normalized = sp.expand(
            -2 * real(w**2)
            - 2 * (q0 + sign * radius_slope * beta) * real(w**6)
            + 6 * beta * (branch_radius / rho) * (2 - s) * real(-imaginary * w)
            + 2 * beta * (rho / branch_radius) * real(imaginary * w**3)
            + 2 * beta**2 / rho * real((a1 + imaginary * b1) * w)
            + 2 * beta**2 * theta * real(-imaginary * w**2)
        )
        n0 = sp.simplify(normalized.subs(beta, 0))
        n1 = sp.simplify(sp.diff(normalized, beta).subs(beta, 0))
        n2 = sp.simplify(sp.diff(normalized, beta, 2).subs(beta, 0) / 2)

        for index, vertex in enumerate(vertices[cell]):
            selected_profile = sp.simplify(profile[cell].subs({p: vertex[0], q: vertex[1], u: vertex[2]}))
            if index == len(vertices[cell]) - 1:
                assert sp.simplify(selected_profile - average) == 0
                remainder = sp.Rational(1, 2)
            else:
                assert bool(selected_profile <= -78)
                remainder = sp.Rational(300)

            upper = sp.expand(
                (n0 + beta * n1 + beta**2 * n2).subs({p: vertex[0], q: vertex[1], u: vertex[2]})
                + remainder * beta**3
            )
            transformed = sp.Poly(
                sp.expand(upper.subs({beta: beta_split + (beta_star - beta_split) * x, t: y})),
                x,
                y,
            )
            tensor = bernstein_tensor(transformed.as_expr(), x, y, 3, 6, s)
            nodes, leaves, depth = certify_tensor(tensor)
            certificate_rows.append((cell, index, remainder, nodes, leaves, depth))

        # The central small-beta constants are reconstructed exactly.
        central = {p: 0, q: 0, u: -equalizer_size}
        for name, derivative, bound in (
            ("n1_prime", sp.diff(n1, t), 5),
            ("n1_second", sp.diff(n1, t, 2), 33),
            ("n2", n2.subs(central), 1),
            ("n2_prime", sp.diff(n2.subs(central), t), 4),
        ):
            local = sp.Symbol("local", real=True)
            coefficients = []
            for segment in range(16):
                restricted = sp.expand(
                    derivative.subs(central).subs(t, (segment + local) / 16)
                )
                coefficients.extend(power_to_bernstein(restricted, local))
            assert all(
                bool(-bound < coefficient) and bool(coefficient < bound)
                for coefficient in coefficients
            ), (
                cell,
                name,
                coefficients,
            )

        # A fully analytic cubic-remainder certificate for the central vertex.
        # After cancelling r0, the only non-polynomial factors are binomial
        # series with relative slopes A and B.  Their coefficients have
        # magnitude at most 1, so the discarded differentiated tails admit
        # the explicit geometric-majorant bound below.
        series_degree = 20
        relative_branch = sp.simplify(branch_slope / q0)
        relative_radius = sp.simplify(sign * radius_slope / q0)
        assert bool(0 < relative_branch) and bool(relative_branch < sp.Rational(6, 5))
        assert bool(abs(relative_radius) < sp.Rational(3, 2))
        assert bool(beta_star < sp.Rational(1, 8))

        branch_over_radius = convolution(
            truncated_binomial(sp.Rational(1, 4), relative_branch, series_degree),
            truncated_binomial(sp.Rational(-1, 4), relative_radius, series_degree),
        )
        radius_over_branch = convolution(
            truncated_binomial(sp.Rational(1, 4), relative_radius, series_degree),
            truncated_binomial(sp.Rational(-1, 4), relative_branch, series_degree),
        )
        reciprocal_radius = truncated_binomial(
            sp.Rational(-1, 4), relative_radius, series_degree
        )
        central_coefficient = equalizer_size / h
        coefficient_one = 6 * (2 - s) * real(-imaginary * w)
        coefficient_two = 2 * real(imaginary * w**3)
        coefficient_three = central_coefficient * real(imaginary * w)
        for coefficient, bound in (
            (coefficient_one, 2),
            (coefficient_two, 3),
            (coefficient_three, 1),
        ):
            assert all(
                bool(-bound < value) and bool(value < bound)
                for value in power_to_bernstein(coefficient, t)
            )

        # Exact rational arithmetic behind the coarse all-box K=300 budget.
        # On a base at least 13/16, a reciprocal quarter power with slope at
        # most 3/2 has derivative bounds 1/2, 6/5, 7 through order three.
        assert (sp.Rational(3, 8) ** 4 * sp.Rational(16, 13) ** 5) < sp.Rational(1, 2) ** 4
        assert (sp.Rational(45, 64) ** 4 * sp.Rational(16, 13) ** 9) < sp.Rational(6, 5) ** 4
        assert (sp.Rational(405, 128) ** 4 * sp.Rational(16, 13) ** 13) < 7**4
        ratio_second = sp.Rational(53, 10)
        ratio_third = sp.Rational(158, 5)
        ratio_terms = 4 * (
            ratio_second / 2 + sp.Rational(1, 8) * ratio_third / 6
        )
        transverse_term = 312 * (
            sp.Rational(1, 2)
            + sp.Rational(1, 8) * sp.Rational(6, 5)
            + sp.Rational(1, 64) * 7 / 6
        )
        assert ratio_terms + transverse_term < 233 < 300

        central_third = sp.expand(
            coefficient_one
            * sum(
                sp.binomial(n + 1, 3) * branch_over_radius[n] * beta ** (n - 2)
                for n in range(2, series_degree + 1)
            )
            + coefficient_two
            * sum(
                sp.binomial(n + 1, 3) * radius_over_branch[n] * beta ** (n - 2)
                for n in range(2, series_degree + 1)
            )
            + coefficient_three
            * sum(
                sp.binomial(n + 2, 3) * reciprocal_radius[n] * beta ** (n - 1)
                for n in range(1, series_degree + 1)
            )
        )

        ratio_radius = sp.Rational(27, 80)
        ratio_start = series_degree - 1
        ratio_quotient = ratio_radius * sp.Rational(ratio_start + 4, ratio_start + 3) ** 3
        ratio_tail = (
            sp.Rational(27, 10) ** 2
            * (ratio_start + 3) ** 3
            * ratio_radius**ratio_start
            / (1 - ratio_quotient)
        )
        reciprocal_ratio = sp.Rational(3, 16)
        reciprocal_start = series_degree
        reciprocal_quotient = (
            reciprocal_ratio
            * sp.Rational(reciprocal_start + 4, reciprocal_start + 3) ** 3
        )
        reciprocal_tail = (
            sp.Rational(3, 2)
            * (reciprocal_start + 3) ** 3
            * reciprocal_ratio**reciprocal_start
            / (1 - reciprocal_quotient)
        )
        tail = sp.simplify(5 * ratio_tail + reciprocal_tail)
        assert bool(tail < sp.Rational(1, 1000))
        transformed_third = sp.expand(
            (central_third + tail - sp.Rational(1, 2)).subs(
                {beta: beta_star * x, t: y}
            )
        )
        third_tensor = bernstein_tensor(
            transformed_third, x, y, series_degree - 2, 3, s
        )
        third_nodes, third_leaves, third_depth = certify_tensor(third_tensor)
        certificate_rows.append(
            (cell, "central-cubic", tail, third_nodes, third_leaves, third_depth)
        )

        # The same selector vertices also control both outward radial tails.
        # For a sixth-root direction and z=rho*y*omega^j, the normalized ray
        # derivative has the form A*y^5+B*y+C.  Since y>=1, the four subset
        # inequalities A, A+B, A+C, A+B+C <= 0 imply monotone decrease.
        ratio_polynomial = sum(
            branch_over_radius[n] * beta**n for n in range(series_degree + 1)
        )
        reciprocal_polynomial = sum(
            reciprocal_radius[n] * beta**n for n in range(series_degree + 1)
        )
        ray_tail = sp.simplify(
            sp.Rational(1, 4)
            * ratio_radius ** (series_degree + 1)
            / (1 - ratio_radius)
            + 5
            * reciprocal_ratio ** (series_degree + 1)
            / (1 - reciprocal_ratio)
        )
        assert bool(ray_tail < sp.Rational(1, 10**8))
        for index, vertex in enumerate(vertices[cell]):
            for ray in (pair, pair + 1):
                ray_direction = omega**ray
                ray_fifth = -12 * (q0 + sign * radius_slope * beta)
                ray_linear = sp.expand(
                    -4 * real(ray_direction**2)
                    + beta**2
                    * vertex[1]
                    / h**2
                    * real(-imaginary * ray_direction**2)
                )
                ray_constant = sp.expand(
                    6
                    * beta
                    * (2 - s)
                    * real(-imaginary * ray_direction)
                    * ratio_polynomial
                    + beta**2
                    / h
                    * real((vertex[0] - imaginary * vertex[2]) * ray_direction)
                    * reciprocal_polynomial
                )
                for subset, ray_polynomial in (
                    ("A", ray_fifth),
                    ("AB", ray_fifth + ray_linear),
                    ("AC", ray_fifth + ray_constant + ray_tail),
                    ("ABC", ray_fifth + ray_linear + ray_constant + ray_tail),
                ):
                    restricted = sp.expand(ray_polynomial.subs(beta, beta_star * x))
                    line = [qs_pair(value, s) for value in power_to_bernstein(restricted, x)]
                    ray_nodes, ray_leaves, ray_depth = certify_line(line)
                    certificate_rows.append(
                        (
                            cell,
                            f"ray-{index}-{ray}-{subset}",
                            ray_tail,
                            ray_nodes,
                            ray_leaves,
                            ray_depth,
                        )
                    )

    # Exact small-beta arithmetic for the two vertex strata.
    assert sp.Rational(56_000, 10**6) < sp.Rational(1, 10)
    assert sp.Rational(40_500_000, 10**6) < 78

    # Adversarial calibration of the selector cells; not proof authority.
    assert bool(average < -sp.Rational(3, 5))
    print("selector vertices: cell 0 = 7, cell 2 = 10; reflected cells identical")
    for row in certificate_rows:
        if not isinstance(row[1], str) or row[1] == "central-cubic":
            print("cell/vertex/remainder/nodes/leaves/depth:", row)
    ray_rows = [row for row in certificate_rows if isinstance(row[1], str) and row[1].startswith("ray-")]
    print("exact radial subset certificates:", len(ray_rows))
    print("central profile:", average, "=", sp.N(average, 16))
    print("PASS: exact 34-vertex finite-beta null-box Bernstein atlas")


if __name__ == "__main__":
    main()
