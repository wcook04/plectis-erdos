#!/usr/bin/env python3
"""Exact collapsed-radius-face certificate for the stationary GP3 surplus.

On the scale-free face u=0, symmetry lets us order 0<v<=w and write v=s*w.
After a positive denominator is cleared, the numerator has an exact factor
w^3.  This checker converts the quotient to the tensor Bernstein basis on
[0,1]^3 in (t,s,w); every coefficient is nonnegative.
"""

from __future__ import annotations

import sympy as sp
import hashlib
import json
from fractions import Fraction
from math import comb


def bernstein_coefficients(poly: sp.Poly, variables: tuple[sp.Symbol, ...]):
    degrees = [poly.degree(variable) for variable in variables]
    arr = {tuple(ex): Fraction(coefficient) for ex, coefficient in poly.as_dict().items()}
    for axis, degree in enumerate(degrees):
        groups = {}
        for exponent, coefficient in arr.items():
            other = exponent[:axis] + exponent[axis + 1 :]
            groups.setdefault(other, {})[exponent[axis]] = coefficient
        converted = {}
        for other, column in groups.items():
            for k in range(degree + 1):
                value = sum(
                    column.get(i, Fraction(0)) * Fraction(comb(k, i), comb(degree, i))
                    for i in range(k + 1)
                )
                converted[other[:axis] + (k,) + other[axis:]] = value
        arr = converted
    return degrees, arr


def main() -> int:
    t, u, v, w = sp.symbols("t u v w", nonnegative=True, real=True)

    def A(x):
        return 1 + x + x**2

    def D(x):
        return 1 + t * x + t**2 * x**2

    def L(x):
        return (1 - x**2) / A(x) ** 2 + t * (1 - t**2 * x**2) / D(x) ** 2

    def self_term(x):
        return x / (1 - x) + t * x**2 / (1 - t * x)

    def pair_term(a, b):
        return a * (1 + b / 2) / A(b) - t * a * b * (t * b + sp.Rational(1, 2)) / D(b)

    def l_fraction(x):
        qx = sp.expand(A(x) ** 2 * D(x) ** 2)
        nx = sp.expand((1 - x**2) * D(x) ** 2 + t * (1 - t**2 * x**2) * A(x) ** 2)
        return nx, qx

    nv, qv = l_fraction(v)
    nw, qw = l_fraction(w)
    l0 = 1 + t
    kv = sp.expand(l0 * qv + nv)
    kw = sp.expand(l0 * qw + nw)
    mvw = sp.expand(nv * qw + nw * qv)
    alpha_vw = v * w * mvw / (qv * qw)
    collapsed_penalty = sp.Rational(1, 2) * (
        v**2 * kv * mvw / (qv**2 * kw)
        + w**2 * kw * mvw / (qw**2 * kv)
    )
    # At u=0 the raw (pre-tangent-correction) residual collapses before any
    # expansion: the two zero-radius cross pairs contribute v+w and the
    # regular comparator contributes -3(v+w).
    # A deliberately unreduced positive common denominator.  Every factor is
    # positive on 0<t,v,w<1.  Clearing term by term is much cheaper and more
    # auditable than asking a CAS to factor one giant rational expression.
    sign_factors = (1 - v) * (1 - t * v) * (1 - w) * (1 - t * w)
    def P(expr):
        return sp.Poly(expr, t, v, w, domain=sp.QQ)

    def mul(*factors):
        answer = P(1)
        for factor in factors:
            answer *= factor if isinstance(factor, sp.Poly) else P(factor)
        return answer

    qvp, qwp, kvp, kwp, mvwp = map(P, (qv, qw, kv, kw, mvw))
    avp, awp, dvp, dwp = map(P, (A(v), A(w), D(v), D(w)))
    sf = [P(1 - v), P(1 - t * v), P(1 - w), P(1 - t * w)]
    common_tail = mul(qvp**2, qwp**2, kvp, kwp)
    cleared_terms = [
        mul(v, sf[1], sf[2], sf[3], common_tail),
        mul(t * v**2, sf[0], sf[2], sf[3], common_tail),
        mul(w, sf[3], sf[0], sf[1], common_tail),
        mul(t * w**2, sf[2], sf[0], sf[1], common_tail),
        mul(v * (1 + w / 2), *sf, qvp**2, awp**3, dwp**4, kvp, kwp),
        mul(-t * v * w * (t * w + sp.Rational(1, 2)), *sf, qvp**2, awp**4, dwp**3, kvp, kwp),
        mul(w * (1 + v / 2), *sf, qwp**2, avp**3, dvp**4, kvp, kwp),
        mul(-t * w * v * (t * v + sp.Rational(1, 2)), *sf, qwp**2, avp**4, dvp**3, kvp, kwp),
        mul(-2 * (v + w), *sf, common_tail),
        mul(v * w / 2, mvwp, *sf, qvp, qwp, kvp, kwp),
        mul(-v**2 / 2, kvp, mvwp, *sf, qwp**2, kvp),
        mul(-w**2 / 2, kwp, mvwp, *sf, qvp**2, kwp),
    ]
    numerator = sp.Poly(0, t, v, w)
    for index, term in enumerate(cleared_terms):
        numerator += term
    degrees = [numerator.degree(variable) for variable in (t, v, w)]
    min_total_vw = min(exponent[1] + exponent[2] for exponent in numerator.as_dict())
    leading_vw = sp.Poly(
        sum(
            coefficient * t ** exponent[0] * v ** exponent[1] * w ** exponent[2]
            for exponent, coefficient in numerator.as_dict().items()
            if exponent[1] + exponent[2] == min_total_vw
        ),
        t,
        v,
        w,
    )
    expected_leading = 6 * (t + 1) ** 2 * (t**2 + 1) * (v + w) * (
        2 * v**2 - 3 * v * w + 2 * w**2
    )
    leading_identity = sp.Poly(leading_vw.as_expr() - expected_leading, t, v, w).is_zero
    numerator_dict = numerator.as_dict()
    symmetric = all(
        numerator_dict.get((i, k, j), 0) == coefficient
        for (i, j, k), coefficient in numerator_dict.items()
    )
    ordered_dict = {}
    for (i, j, k), coefficient in numerator_dict.items():
        assert j + k >= 3
        exponent = (i, j, j + k - 3)
        ordered_dict[exponent] = ordered_dict.get(exponent, 0) + coefficient
    s = sp.symbols("s", nonnegative=True, real=True)
    ordered = sp.Poly.from_dict(ordered_dict, (t, s, w), domain=sp.QQ)
    ordered_degrees, ordered_table = bernstein_coefficients(ordered, (t, s, w))
    ordered_coefficients = list(ordered_table.values())
    nonnegative = all(value >= 0 for value in ordered_coefficients)
    positive_count = sum(value > 0 for value in ordered_coefficients)
    zero_count = sum(value == 0 for value in ordered_coefficients)
    s_one_values = [
        value for (it, js, kw_index), value in ordered_table.items() if js == ordered_degrees[1]
    ]
    s_one_positive = any(value > 0 for value in s_one_values) and all(
        value >= 0 for value in s_one_values
    )

    # Verify the hand-cleared numerator against the original rational limit at
    # several exact points.  This is independent of the Bernstein transform.
    raw_terms = [
        self_term(v),
        self_term(w),
        pair_term(v, w),
        pair_term(w, v),
        -2 * (v + w),
    ]
    direct_terms = raw_terms + [alpha_vw / 2, -collapsed_penalty]
    common_denominator = sign_factors * qv**2 * qw**2 * kv * kw
    point_checks = []
    for point in (
        {t: sp.Rational(1, 5), v: sp.Rational(2, 7), w: sp.Rational(3, 8)},
        {t: sp.Rational(4, 9), v: sp.Rational(1, 11), w: sp.Rational(5, 13)},
        {t: sp.Rational(7, 8), v: sp.Rational(3, 10), w: sp.Rational(4, 5)},
    ):
        direct_value = sum(term.subs(point) for term in direct_terms)
        cleared_value = numerator.eval(point) / common_denominator.subs(point)
        point_checks.append(sp.factor(direct_value - cleared_value) == 0)

    # Exact reciprocal-variance identity behind the correction.
    a, b, c = sp.symbols("a b c", positive=True, real=True)
    tangent = (a + b + c - a * b / c - a * c / b - b * c / a) / 2
    reciprocal_variance = -sp.Rational(1, 4) * (
        c * (a - b) ** 2 / (a * b)
        + b * (a - c) ** 2 / (a * c)
        + a * (b - c) ** 2 / (b * c)
    )
    reciprocal_variance_identity = sp.factor(tangent - reciprocal_variance) == 0

    # L_t(x)=f(x)+t f(tx) is positive and strictly decreasing on the open
    # square.  The displayed derivative formula makes the sign elementary.
    x = sp.symbols("x", positive=True, real=True)
    f = (1 - x**2) / (1 + x + x**2) ** 2
    f_derivative_expected = 2 * (x**3 - 3 * x - 1) / (1 + x + x**2) ** 3
    f_derivative_identity = sp.factor(sp.diff(f, x) - f_derivative_expected) == 0

    # Independent exact Bernstein expansion checks.
    expansion_checks = []
    dt, ds, dw = ordered_degrees
    for t0, s0, w0 in (
        (sp.Rational(2, 7), sp.Rational(3, 5), sp.Rational(4, 9)),
        (sp.Rational(5, 6), sp.Rational(7, 8), sp.Rational(1, 3)),
    ):
        expansion = sum(
            value
            * sp.binomial(dt, i) * t0**i * (1 - t0) ** (dt - i)
            * sp.binomial(ds, j) * s0**j * (1 - s0) ** (ds - j)
            * sp.binomial(dw, k) * w0**k * (1 - w0) ** (dw - k)
            for (i, j, k), value in ordered_table.items()
        )
        expansion_checks.append(
            sp.Rational(expansion.numerator, expansion.denominator)
            == ordered.eval({t: t0, s: s0, w: w0})
        )

    coefficient_digest = hashlib.sha256(
        "\n".join(
            f"{index}:{value.numerator}/{value.denominator}"
            for index, value in sorted(ordered_table.items())
        ).encode()
    ).hexdigest()

    passed = all(
        (
            symmetric,
            min_total_vw == 3,
            leading_identity,
            degrees == [28, 28, 28],
            ordered_degrees == [28, 28, 50],
            len(ordered_coefficients) == 42891,
            nonnegative,
            positive_count == 42829,
            zero_count == 62,
            s_one_positive,
            all(point_checks),
            reciprocal_variance_identity,
            f_derivative_identity,
            all(expansion_checks),
        )
    )
    result = {
        "schema": "erdos1041_three_exterior_stationary_collapsed_face_receipt_v1",
        "reciprocal_variance_identity_exact": reciprocal_variance_identity,
        "kernel_f_derivative_identity_exact": f_derivative_identity,
        "cleared_numerator_symmetric": symmetric,
        "cleared_numerator_degree": degrees,
        "cleared_numerator_term_count": len(numerator.terms()),
        "minimum_total_vw_degree": min_total_vw,
        "leading_cubic_identity_exact": leading_identity,
        "exact_rational_point_checks": point_checks,
        "ordered_chart": "v=s*w on 0<=v<=w",
        "ordered_quotient_degree": ordered_degrees,
        "ordered_quotient_term_count": len(ordered.terms()),
        "bernstein_coefficient_count": len(ordered_coefficients),
        "bernstein_all_nonnegative": nonnegative,
        "bernstein_strictly_positive_count": positive_count,
        "bernstein_zero_count": zero_count,
        "bernstein_s_equals_one_face_positive": s_one_positive,
        "bernstein_expansion_checks": expansion_checks,
        "bernstein_sha256": coefficient_digest,
        "collapsed_face_stationary_surplus_strictly_positive": passed,
        "claim_boundary": (
            "Proves the continuous u=0 stationary-residual face is strictly "
            "positive for 0<t<1 and 0<v,w<1. It does not prove a collar "
            "u>0, the fully distinct positive-radius interior, GP3, or Erdos 1041."
        ),
        "pass": passed,
    }
    print(json.dumps(result, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
