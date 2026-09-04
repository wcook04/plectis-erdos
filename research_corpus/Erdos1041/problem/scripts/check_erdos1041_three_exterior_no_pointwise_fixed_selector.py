#!/usr/bin/env python3
"""Exact replay for ThreeExteriorNoPointwiseFixedSelector.md."""

from fractions import Fraction as F

import sympy as sp


RADII = (F(3, 50), F(9, 160), F(125, 1728))
UNITS = ((F(1), F(0)), (F(7, 25), F(24, 25)), (F(-117, 125), F(-44, 125)))
S = F(1, 16)


def dot(u: tuple[F, F], v: tuple[F, F]) -> F:
    return u[0] * v[0] + u[1] * v[1]


def qfactor(r: F, x: F, c: F) -> F:
    return (1 - 2 * r * x * c + r * r * x * x) / (x * x - 2 * r * x * c + r * r)


def selected_sq(r: F, x: F) -> F:
    return (1 - r * x) ** 2 / (x - r) ** 2


def squared_ratio(j: int, x: F, cosines: list[list[F]]) -> F:
    numerator = selected_sq(RADII[j], x)
    for k in range(3):
        if k != j:
            numerator *= qfactor(RADII[k], x, cosines[j][k])
    denominator = selected_sq(S, x) * qfactor(S, x, F(-1, 2)) ** 2
    return numerator / denominator


def pointwise_obstruction() -> None:
    assert all(dot(u, u) == 1 for u in UNITS)
    cosines = [[dot(UNITS[i], UNITS[j]) for j in range(3)] for i in range(3)]
    assert (cosines[0][1], cosines[0][2], cosines[1][2]) == (F(7, 25), F(-117, 125), F(-3, 5))
    assert RADII[0] * RADII[1] * RADII[2] == S**3 == F(1, 4096)

    xs = (F(15), F(15), F(3))
    expected = (
        F(172787754918790708715041, 102525497999369526069153),
        F(367494798077462739999625, 102233383454364535848969),
        F(7940052051703231440629, 7665730371986326402005),
    )
    for j, x in enumerate(xs):
        assert 1 < x < min(1 / RADII[j], 1 / S)
        value = squared_ratio(j, x, cosines)
        assert value == expected[j]
        assert value > 1


def boundary_speed_certificate() -> None:
    t = sp.symbols("t", real=True)
    X = (1 - t**2) / (1 + t**2)
    Y = 2 * t / (1 + t**2)

    speed = 0
    for r0, (cx0, sy0) in zip(RADII, UNITS, strict=True):
        r = sp.Rational(r0.numerator, r0.denominator)
        cx = sp.Rational(cx0.numerator, cx0.denominator)
        sy = sp.Rational(sy0.numerator, sy0.denominator)
        speed += (1 - r**2) / (1 + r**2 - 2 * r * (X * cx + Y * sy))

    numerator, denominator = sp.together(5 - speed).as_numer_denom()
    P = sp.Poly(
        484587325002401 * t**6
        - 60656800485888 * t**5
        + 1473437332595025 * t**4
        - 175831243637760 * t**3
        + 1452136601119935 * t**2
        - 96565790863872 * t
        + 461871237111311,
        t,
    )
    D = sp.Poly(
        (2809 * t**2 + 2209)
        * (132437 * t**2 - 27648 * t + 124373)
        * (2597257 * t**2 + 304128 * t + 3405961),
        t,
    )
    assert sp.Poly(numerator, t) == 4 * P
    assert sp.Poly(denominator, t) == D

    quadratics = (
        2809 * t**2 + 2209,
        132437 * t**2 - 27648 * t + 124373,
        2597257 * t**2 + 304128 * t + 3405961,
    )
    expected_discriminants = (-24820324, -65121936100, -35292130355524)
    for quadratic, expected in zip(quadratics, expected_discriminants, strict=True):
        poly = sp.Poly(quadratic, t)
        assert poly.LC() > 0
        assert sp.discriminant(poly.as_expr(), t) == expected < 0

    assert sp.polys.polytools.count_roots(P, -sp.oo, sp.oo) == 0
    assert P.eval(0) > 0
    assert P.LC() > 0


def main() -> None:
    pointwise_obstruction()
    boundary_speed_certificate()
    print("three-exterior no-pointwise-fixed-selector: exact replay PASS")
    print("checked: rational rays, three strict profile gaps, global strict quintic speed")


if __name__ == "__main__":
    main()
