#!/usr/bin/env python3
"""Exact replay for ThreeExteriorLowCapacityAngularSwitchCertificate.md."""

from fractions import Fraction as F

import sympy as sp


U = [
    (F(1), F(0)),
    (F(21, 221), F(-220, 221)),
    (F(-91, 109), F(60, 109)),
]
B = [F(1), F(24, 25), F(51, 50)]
P = F(612, 625)
EPS0 = F(1, 600)
J = 1


def dot(u: tuple[F, F], v: tuple[F, F]) -> F:
    return u[0] * v[0] + u[1] * v[1]


def angular_moments() -> tuple[list[F], list[F]]:
    moments = [
        sum((B[k] * dot(U[j], U[k]) for k in range(3)), F(0))
        for j in range(3)
    ]
    charges = [B[j] * (moments[j] - B[j]) for j in range(3)]
    return moments, charges


def distance_polynomial(y: sp.Symbol) -> sp.Expr:
    out = sp.Integer(1)
    for k in range(3):
        bk = sp.Rational(B[k].numerator, B[k].denominator)
        c = dot(U[J], U[k])
        cc = sp.Rational(c.numerator, c.denominator)
        out *= y * y + bk * bk - 2 * y * bk * cc
    return sp.expand(out)


def sturm_bound(n: int, bound: F, expected_at_left: F) -> None:
    y = sp.symbols("y")
    numerator = distance_polynomial(y)
    uu = sp.Rational(bound.numerator, bound.denominator)
    q = sp.Poly(uu * uu * y ** (2 * n) - numerator, y, domain=sp.QQ)
    left = sp.Rational(B[J].numerator, B[J].denominator)
    assert q.count_roots(left, sp.oo) == 0
    value = q.eval(left)
    assert value == sp.Rational(expected_at_left.numerator, expected_at_left.denominator)
    assert value > 0


def comparator_check(n: int, bound: F, y0: F, expected_l: F) -> F:
    lval = (y0**3 - P) / y0**n
    assert lval == expected_l
    corrected = bound / (1 - EPS0 * B[2]) ** 3
    assert corrected < lval
    return lval - corrected


def main() -> None:
    for u in U:
        assert dot(u, u) == 1
    assert B[J] == min(B)

    moments, charges = angular_moments()
    assert moments == [F(288661, 1204450), F(500061, 1204450), F(-502339, 1204450)]
    assert charges == [F(-915789, 1204450), F(-7874532, 15055625), F(-2596317, 1771250)]
    assert moments[J] == max(moments)
    assert charges[J] == max(charges)

    sturm_bound(5, F(31, 100), F(3808165569232896, 59604644775390625))
    sturm_bound(6, F(6, 25), F(1314732507698036736, 37252902984619140625))

    gap5 = comparator_check(5, F(31, 100), F(27, 20), F(526640, 1594323))
    gap6 = comparator_check(6, F(6, 25), F(5, 4), F(2493248, 9765625))
    assert gap5 == F(29718569381417680, 1586205767647501101)
    assert gap6 == F(136804039410832576, 9715904932490234375)

    print(f"selected_index={J} moments={moments} charges={charges}")
    print(f"n=5 corrected_comparator_gap={float(gap5):.12f}")
    print(f"n=6 corrected_comparator_gap={float(gap6):.12f}")
    print("PASS exact low-capacity angular selector switch")


if __name__ == "__main__":
    main()
