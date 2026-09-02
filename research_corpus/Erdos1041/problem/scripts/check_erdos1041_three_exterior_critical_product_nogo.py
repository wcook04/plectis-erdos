#!/usr/bin/env python3
"""Exact replay for ThreeExteriorCriticalProductNoGo.md."""

from fractions import Fraction as F
from math import comb

import sympy as sp


Interval = tuple[F, F]


def iadd(a: Interval, b: Interval) -> Interval:
    return a[0] + b[0], a[1] + b[1]


def imul(a: Interval, b: Interval) -> Interval:
    values = [a[i] * b[j] for i in (0, 1) for j in (0, 1)]
    return min(values), max(values)


def idiv(a: Interval, b: Interval) -> Interval:
    assert not (b[0] <= 0 <= b[1])
    return imul(a, (1 / b[1], 1 / b[0]))


def ihorner(coefficients: list[F], x: Interval) -> Interval:
    value = (coefficients[0], coefficients[0])
    for coefficient in coefficients[1:]:
        value = iadd(imul(value, x), (coefficient, coefficient))
    return value


def absolute_lower(a: Interval) -> F:
    assert not (a[0] <= 0 <= a[1])
    return min(abs(a[0]), abs(a[1]))


def speed_certificate() -> None:
    u, t = sp.symbols("u t", real=True)
    cubic = sp.Poly(
        25920000 * u**3 + 162872928 * u**2 - 28889659 * u - 165922849,
        u,
    )
    transformed = sp.Poly(sp.expand(cubic.as_expr().subs(u, 2 * t - 1)), t)
    power = [F(int(transformed.nth(i))) for i in range(4)]
    bernstein = [
        sum(power[i] * F(comb(k, i), comb(3, i)) for i in range(k + 1))
        for k in range(4)
    ]
    assert bernstein == [F(-80262), F(-553991816, 3), F(-767291134, 3), F(-6019580)]
    assert all(value < 0 for value in bernstein)

    # D=-(45u-53)(288u+337)(2000u+15689) is positive on [-1,1].
    assert 45 * 1 - 53 < 0
    assert 288 * (-1) + 337 > 0
    assert 2000 * (-1) + 15689 > 0


def critical_intervals_and_values() -> None:
    z = sp.symbols("z", real=True)
    critical = sp.Poly(
        6480000 * z**6
        + 81436464 * z**5
        - 9449659 * z**4
        - 168972770 * z**3
        - 9449659 * z**2
        + 81436464 * z
        + 6480000,
        z,
    )
    intervals = (
        (F(-12519, 1000), F(-12518, 1000)),
        (F(-1025, 1000), F(-1024, 1000)),
        (F(-977, 1000), F(-976, 1000)),
        (F(-80, 1000), F(-79, 1000)),
        (F(836, 1000), F(837, 1000)),
        (F(1194, 1000), F(1195, 1000)),
    )
    assert sum(sp.polys.polytools.count_roots(critical, a, b) for a, b in intervals) == 6
    assert all(sp.polys.polytools.count_roots(critical, a, b) == 1 for a, b in intervals)

    p_coeff = [F(1), F(1277, 18000), F(-5617, 18000), F(-1, 50)]
    q_coeff = [F(-1, 50), F(-5617, 18000), F(1277, 18000), F(1)]
    inside = intervals[2:5]
    lower_bounds = []
    for root_interval in inside:
        p_value = ihorner(p_coeff, root_interval)
        q_value = ihorner(q_coeff, root_interval)
        square = imul(root_interval, root_interval)
        fourth = imul(square, square)
        fifth = imul(fourth, root_interval)
        r_value = idiv(p_value, imul(q_value, fifth))
        lower_bounds.append(absolute_lower(r_value))

    assert lower_bounds[0] > F(99, 100)
    assert lower_bounds[1] > 1400
    assert lower_bounds[2] > 1
    assert lower_bounds[0] * lower_bounds[1] * lower_bounds[2] > 1386


def symmetric_upper_bound() -> None:
    y = sp.symbols("y", real=True)
    equation = y**2 - sp.Rational(2504, 125) * y + 1
    assert equation.subs(y, sp.Rational(39, 2)) == sp.Rational(-4687, 500)
    assert equation.subs(y, 20) == sp.Rational(9, 25)

    upper = F(20) ** 5 * (1 - F(39, 2) / 50) ** 3 / (F(39, 2) - F(1, 50)) ** 3
    assert upper < 100


def main() -> None:
    assert F(9, 16) * F(8, 125) * F(5, 9) == F(1, 50)
    speed_certificate()
    critical_intervals_and_values()
    symmetric_upper_bound()
    print("three-exterior critical-product no-go: exact replay PASS")
    print("checked: strict speed, six Sturm roots, saddle intervals, symmetric upper bound")


if __name__ == "__main__":
    main()
