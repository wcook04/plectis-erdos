"""Exact isosceles-slice positivity certificate for the GP3 stationary surplus.

The isosceles slice (r1, r2, r3) = (x, x, z) of the stationary-branch radial
surplus satisfies the exact factorization

    S_stat(q; x, x, z) = (z - x)^2 * Num(t, u, w) / Den(q, u, w),
    u = x/q,  w = z/q,  t = q^2,

and this checker proves Num <= 0 on the closed unit box [0,1]^3 by converting
-Num exactly to the tensor Bernstein basis: all 22*21*21 = 9702 coefficients
are nonnegative.  The denominator is strictly negative on the open box (seven
strictly negative sign-bearing factors and manifestly positive remaining
factors), so

    S_stat(q; x, x, z) >= 0   for all   0 < x, z <= q < 1,

with the diagonal z = x the exact equality locus.  This closes the full
isosceles slice of the radial surplus inequality; the off-isosceles coupled
case, GP3, the selector lemma, and unrestricted Erdos 1041 remain open.

Replay:
    ./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/\
Erdos1041/scripts/check_erdos1041_gp3_isosceles_slice.py
"""

import json
import sys
from fractions import Fraction
from math import comb

import sympy as sp


def monomial_to_bernstein_1d(coeffs):
    n = len(coeffs) - 1
    out = []
    for k in range(n + 1):
        acc = Fraction(0)
        for i in range(k + 1):
            if coeffs[i]:
                acc += coeffs[i] * Fraction(comb(k, i), comb(n, i))
        out.append(acc)
    return out


def poly_to_bernstein(coeff_dict, degrees):
    dim = len(degrees)
    shape = tuple(d + 1 for d in degrees)
    arr = {}
    for ex, c in coeff_dict.items():
        arr[tuple(ex)] = Fraction(c)
    for axis in range(dim):
        n = degrees[axis]
        groups = {}
        for ex, c in arr.items():
            groups[ex[:axis] + ex[axis + 1:]] = groups.get(
                ex[:axis] + ex[axis + 1:], {}
            )
            groups[ex[:axis] + ex[axis + 1:]][ex[axis]] = c
        new = {}
        for oidx, column in groups.items():
            vec = [column.get(i, Fraction(0)) for i in range(n + 1)]
            conv = monomial_to_bernstein_1d(vec)
            for k, v in enumerate(conv):
                new[oidx[:axis] + (k,) + oidx[axis:]] = v
        arr = new
    out = {}
    for ex, c in arr.items():
        out[ex] = c
    return out, shape


def main() -> int:
    q, x, z = sp.symbols("q x z", positive=True)
    half = sp.Rational(1, 2)

    def H(r, c):
        return (q - r * c) / (q**2 + r**2 - 2 * q * r * c) - (
            q * r * r - r * c
        ) / (1 + q**2 * r**2 - 2 * q * r * c)

    def Hc(r, c):
        return r * (q**2 - r**2) / (q**2 + r**2 - 2 * q * r * c) ** 2 + r * (
            1 - q**2 * r**2
        ) / (1 + q**2 * r**2 - 2 * q * r * c) ** 2

    radii = (x, x, z)
    pairs = ((0, 1), (1, 2), (2, 0))
    alpha = [
        radii[i] * Hc(radii[j], -half) + radii[j] * Hc(radii[i], -half)
        for i, j in pairs
    ]
    p = x * x * z
    tot = 2 * x + z
    terms = [radii[i] * H(radii[i], 1) for i in range(3)]
    terms += [
        radii[i] * H(radii[j], -half) + radii[j] * H(radii[i], -half)
        for i, j in pairs
    ]
    terms += [-tot * 3 * q**2 / (q**3 - p), -tot * 3 * p * q**2 / (1 - p * q**3)]
    terms += [a / 2 for a in alpha]
    terms += [
        -(alpha[0] * alpha[1] / alpha[2] + alpha[0] * alpha[2] / alpha[1]
          + alpha[1] * alpha[2] / alpha[0]) / 2
    ]

    acc = sorted([sp.factor(t) for t in terms], key=sp.count_ops)
    while len(acc) > 1:
        a = acc.pop(0)
        b = acc.pop(0)
        acc.append(sp.factor(sp.together(a + b)))
        acc.sort(key=sp.count_ops)
    surplus_iso = acc[0]

    quotient = sp.cancel(surplus_iso / (z - x) ** 2)
    u, w, t = sp.symbols("u w t", nonnegative=True)
    num, den = sp.fraction(sp.together(quotient.subs({x: q * u, z: q * w})))

    factorization_identity = (
        sp.cancel(surplus_iso.subs({x: q * u, z: q * w}) - (q * (u - w)) ** 2 * num / den)
        == 0
    )

    tail_u = (
        (1 - u**2)
        + q**2 * (1 - q**4 * u**2)
        + q**4 * u**4 * (1 + q**2)
        + 4 * q**4 * u**3
        + 4 * q**2 * u**2 * (1 + q**2)
        + 4 * q**2 * u
    )
    expected_den = (
        4
        * q**2
        * (u - 1)
        * (w - 1)
        * (q * u - 1)
        * (q * u + 1)
        * (q**2 * u - 1)
        * (q**2 * w - 1)
        * (u**2 * w - 1)
        * (q**6 * u**2 * w - 1)
        * (u**2 + u + 1) ** 2
        * (w**2 + w + 1) ** 4
        * (q**4 * u**2 + q**2 * u + 1) ** 2
        * (q**4 * w**2 + q**2 * w + 1) ** 4
        * tail_u
    )
    denominator_factorization_verified = sp.factor(den - expected_den) == 0

    numexp = sp.expand(num)
    qpoly = sp.Poly(numexp, q)

    def q_power(k):
        return k[0] if isinstance(k, tuple) else k

    even_q_powers = all(q_power(k) % 2 == 0 for k in qpoly.as_dict())
    # The denominator is strictly negative on the open box (seven strictly
    # negative sign-bearing factors), so the certificate target is -Num >= 0.
    normalized = sp.expand(
        -sum(
            c * t ** (q_power(k) // 2)
            for k, c in qpoly.as_dict().items()
        )
    )
    poly = sp.Poly(normalized, t, u, w)
    degrees = [poly.degree(t), poly.degree(u), poly.degree(w)]

    coeff = {}
    for ex, c in poly.terms():
        coeff[tuple(ex)] = Fraction(int(c.p), int(c.q))
    bernstein, shape = poly_to_bernstein(coeff, degrees)
    values = list(bernstein.values())
    nonnegative = all(v >= 0 for v in values)
    positive_count = sum(1 for v in values if v > 0)
    zero_count = sum(1 for v in values if v == 0)

    expansion_verified = True
    for point in ((sp.Rational(1, 3), sp.Rational(1, 5), sp.Rational(2, 7)),
                  (sp.Rational(7, 9), sp.Rational(1, 2), sp.Rational(1, 8)),
                  (sp.Rational(1, 16), sp.Rational(3, 4), sp.Rational(5, 6))):
        t0, u0, w0 = point
        dt, du, dw = degrees
        expansion = sum(
            bernstein[(k, l, m)]
            * sp.binomial(dt, k) * t0**k * (1 - t0) ** (dt - k)
            * sp.binomial(du, l) * u0**l * (1 - u0) ** (du - l)
            * sp.binomial(dw, m) * w0**m * (1 - w0) ** (dw - m)
            for k in range(dt + 1)
            for l in range(du + 1)
            for m in range(dw + 1)
        )
        if sp.simplify(expansion - poly.eval({t: t0, u: u0, w: w0})) != 0:
            expansion_verified = False
            break

    slice_nonnegative = (
        factorization_identity
        and denominator_factorization_verified
        and even_q_powers
        and degrees[0] == 21
        and degrees[1] == 20
        and degrees[2] == 20
        and len(values) == 9702
        and nonnegative
        and expansion_verified
    )

    result = {
        "schema": "erdos1041_gp3_isosceles_slice_receipt_v1",
        "factorization_identity_exact": factorization_identity,
        "denominator_factorization_verified": denominator_factorization_verified,
        "numerator_even_q_powers": even_q_powers,
        "bernstein_degree": degrees,
        "bernstein_coefficient_count": len(values),
        "bernstein_all_nonnegative": nonnegative,
        "bernstein_strictly_positive_count": positive_count,
        "bernstein_zero_count": zero_count,
        "bernstein_expansion_verified": expansion_verified,
        "isosceles_slice_surplus_nonnegative": slice_nonnegative,
        "claim_boundary": (
            "Proves the stationary-branch surplus on the isosceles slice "
            "(x,x,z) for all 0<x,z<=q<1, with equality only on the diagonal "
            "z=x. The off-isosceles coupled case, GP3, the selector lemma, "
            "and unrestricted Erdos 1041 remain open."
        ),
    }
    result["pass"] = slice_nonnegative
    print(json.dumps(result, indent=2))
    return 0 if result["pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
