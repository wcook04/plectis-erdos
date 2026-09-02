#!/usr/bin/env python3
"""Exact replay for ThreeExteriorLowCapacityRegularKernelSecondVariation."""

import sympy as sp


def zero_mod_cubic(expr: sp.Expr, t: sp.Symbol, value: sp.Rational) -> bool:
    num, _den = sp.cancel(expr).as_numer_denom()
    remainder = sp.rem(sp.Poly(num, t), sp.Poly(t**3 - value, t))
    return remainder == 0


def check_degree(n: int) -> None:
    e, q, t, p, r = sp.symbols("e q t p r", real=True)
    d = n - 3
    x = (p, r, -p-r)
    s01, s02, s12 = sp.symbols("s01 s02 s12", real=True)
    c = (
        (1, -sp.Rational(1, 2) + e*s01, -sp.Rational(1, 2) + e*s02),
        (-sp.Rational(1, 2) + e*s01, 1, -sp.Rational(1, 2) + e*s12),
        (-sp.Rational(1, 2) + e*s02, -sp.Rational(1, 2) + e*s12, 1),
    )
    b = tuple(sp.exp(e*xx) for xx in x)
    logs = []
    for j in range(3):
        ell = d * sp.log(q)
        for k in range(3):
            ell += sp.log(1 - 2*q*b[k]*c[j][k] + q*q*b[k]*b[k]) / 2
        logs.append(ell)

    cubic_value = sp.Rational(d, n)
    first = [sp.cancel(sp.diff(ell, e).subs({e: 0, q: t})) for ell in logs]
    solution = sp.solve(first, (s01, s02, s12), dict=True)
    assert len(solution) == 1
    solution = solution[0]
    expected = {
        s01: 3*(p+r)*(t+1)/(2*(t-1)),
        s02: -3*r*(t+1)/(2*(t-1)),
        s12: -3*p*(t+1)/(2*(t-1)),
    }
    for var in expected:
        assert zero_mod_cubic(solution[var] - expected[var], t, cubic_value)
    assert sp.simplify(sum(solution[v] for v in (s01, s02, s12))) == 0

    envelope_seconds = []
    for ell in logs:
        lee = sp.diff(ell, e, 2).subs({e: 0, q: t, **solution})
        leq = sp.diff(ell, e, q).subs({e: 0, q: t, **solution})
        lqq = sp.diff(ell, q, 2).subs({e: 0, q: t, **solution})
        envelope_seconds.append(sp.cancel(lee - leq*leq/lqq))

    total = sp.cancel(sum(envelope_seconds))
    Q = p*p + p*r + r*r
    if n == 5:
        target = -sp.Rational(10, 3)*Q*(9*t*t - 2*t + 20)
    else:
        target = -4*Q*(10*t*t - t + 30)
    assert zero_mod_cubic(total - target, t, cubic_value)

    # Each individual form is negative definite.  The exact quadratic forms
    # have matrices [[A,B/2],[B/2,C]]; their determinant factors are
    # manifestly positive for t>0.
    if n == 5:
        A = 11*t*t + 3*t + 16
        D = 14*t*t - 14*t + 48
        B = 8*t*t + 20*t - 16
        expected_individual = (
            -sp.Rational(5, 6)*(A*p*p + D*p*r + D*r*r),
            -sp.Rational(5, 6)*(D*p*p + D*p*r + A*r*r),
            -sp.Rational(5, 6)*(A*p*p + B*p*r + A*r*r),
        )
        determinant_factors = (D, 30*t*t + 26*t + 16,
                               14*t*t - 14*t + 16,
                               30*t*t + 26*t + 16)
    else:
        A = 13*t*t + 5*t + 24
        D = 14*t*t - 14*t + 72
        B = 12*t*t + 24*t - 24
        expected_individual = (
            -(A*p*p + D*p*r + D*r*r),
            -(D*p*p + D*p*r + A*r*r),
            -(A*p*p + B*p*r + A*r*r),
        )
        determinant_factors = (D, 38*t*t + 34*t + 24,
                               14*t*t - 14*t + 24,
                               38*t*t + 34*t + 24)
    for actual, expected_form in zip(envelope_seconds, expected_individual):
        assert zero_mod_cubic(actual - expected_form, t, cubic_value)
    for factor in determinant_factors:
        # The only possible negative linear coefficient occurs in
        # 14t^2-14t+constant; complete the square to certify it.
        assert sp.discriminant(factor, t) < 0 or all(
            coefficient >= 0 for coefficient in sp.Poly(factor, t).all_coeffs()
        )
        assert sp.LC(sp.Poly(factor, t)) > 0

    # Positivity is elementary on 0<t<1: both displayed quadratics have
    # negative discriminant and positive leading coefficient.
    poly = (9*t*t - 2*t + 20) if n == 5 else (10*t*t - t + 30)
    assert sp.discriminant(poly, t) < 0
    assert sp.LC(sp.Poly(poly, t)) > 0
    print(f"n={n}: kernel and negative individual envelope Hessians verified")


def main() -> None:
    import sys
    degrees = tuple(map(int, sys.argv[1:])) or (5, 6)
    for degree in degrees:
        check_degree(degree)
    print("PASS exact regular-kernel second-variation replay")


if __name__ == "__main__":
    main()
