#!/usr/bin/env python3
"""Exact Bernstein certificate for the GP3 isosceles surplus slice.

On the isosceles slice (r1, r2, r3) = (x, x, z) of the coupled three-exterior
inequality, the stationary residual factors exactly as

    S(q; x, x, z) = q^2 (u-w)^2 Num(t,u,w) / Den(q,u,w),   u=x/q, w=z/q, t=q^2,

with Den strictly negative on the open unit box.  This replay proves
Num <= 0 on [0,1]^3 by converting -Num to the tensor Bernstein basis: all
22*21*21 = 9702 coefficients are nonnegative.  Hence S >= 0 on the whole
isosceles slice, with equality only on the diagonal z = x.

This optional research replay requires SymPy.  It proves a slice theorem only;
the fully coupled case, GP3, the selector lemma, and unrestricted Erdos 1041
remain open.
"""
import json
from fractions import Fraction
from math import comb
import sympy as s


def mono_to_bern_1d(coeffs):
    n = len(coeffs) - 1
    out = []
    for k in range(n + 1):
        acc = Fraction(0)
        for i in range(k + 1):
            if coeffs[i]:
                acc += coeffs[i] * Fraction(comb(k, i), comb(n, i))
        out.append(acc)
    return out


def poly_to_bernstein(coeff, degrees):
    arr = {tuple(ex): Fraction(c) for ex, c in coeff.items()}
    for axis in range(3):
        n = degrees[axis]
        groups = {}
        for ex, c in arr.items():
            key = ex[:axis] + ex[axis + 1:]
            groups.setdefault(key, {})[ex[axis]] = c
        new = {}
        for key, column in groups.items():
            vec = [column.get(i, Fraction(0)) for i in range(n + 1)]
            conv = mono_to_bern_1d(vec)
            for k, v in enumerate(conv):
                new[key[:axis] + (k,) + key[axis:]] = v
        arr = new
    return arr


def main():
    q, x, z = s.symbols("q x z", positive=True)
    c = -s.Rational(1, 2)
    radii = (x, x, z)
    pairs = ((0, 1), (1, 2), (2, 0))

    def H(r, c):
        return (q - r*c)/(q*q + r*r - 2*q*r*c) - (q*r*r - r*c)/(1 + q*q*r*r - 2*q*r*c)

    def Hc(r, c):
        return r*(q*q - r*r)/(q*q + r*r - 2*q*r*c)**2 + r*(1 - q*q*r*r)/(1 + q*q*r*r - 2*q*r*c)**2

    alpha = [radii[i]*Hc(radii[j], c) + radii[j]*Hc(radii[i], c) for i, j in pairs]
    product = x*x*z
    total = 2*x + z
    terms = [radii[i]*H(radii[i], 1) for i in range(3)]
    terms += [radii[i]*H(radii[j], c) + radii[j]*H(radii[i], c) for i, j in pairs]
    terms += [-total*3*q*q/(q**3 - product), -total*3*product*q*q/(1 - product*q**3)]
    terms += [a/2 for a in alpha]
    terms += [-alpha[0]*alpha[1]/alpha[2]/2, -alpha[0]*alpha[2]/alpha[1]/2,
              -alpha[1]*alpha[2]/alpha[0]/2]
    values = sorted([s.factor(t) for t in terms], key=s.count_ops)
    while len(values) > 1:
        a = values.pop(0); b = values.pop(0)
        values.append(s.factor(s.together(a + b)))
        values.sort(key=s.count_ops)
    surplus = values[0]

    quotient = s.cancel(surplus / (z - x)**2)
    u, w, t = s.symbols("u w t", nonnegative=True)
    num, den = s.fraction(s.together(quotient.subs({x: q*u, z: q*w})))
    identity_ok = s.cancel(surplus.subs({x: q*u, z: q*w}) - (q*(u - w))**2*num/den) == 0

    tail = ((1 - u**2) + q**2*(1 - q**4*u**2) + q**4*u**4*(1 + q**2)
            + 4*q**4*u**3 + 4*q**2*u**2*(1 + q**2) + 4*q**2*u)
    expected_den = (4*q**2*(u - 1)*(w - 1)*(q*u - 1)*(q*u + 1)*(q**2*u - 1)
                    *(q**2*w - 1)*(u**2*w - 1)*(q**6*u**2*w - 1)
                    *(u**2 + u + 1)**2*(w**2 + w + 1)**4
                    *(q**4*u**2 + q**2*u + 1)**2*(q**4*w**2 + q**2*w + 1)**4*tail)
    den_ok = s.factor(den - expected_den) == 0

    numexp = s.expand(num)
    qpoly = s.Poly(numexp, q)
    normalized = s.expand(
        -sum(coef*t**((k[0] if isinstance(k, tuple) else k)//2)
             for k, coef in qpoly.as_dict().items()))
    poly = s.Poly(normalized, t, u, w)
    dt, du, dw = poly.degree(t), poly.degree(u), poly.degree(w)
    coeff = {ex: Fraction(int(c.p), int(c.q)) for ex, c in poly.terms()}
    bern = poly_to_bernstein(coeff, [dt, du, dw])
    vals = list(bern.values())
    nonneg = all(v >= 0 for v in vals)
    strict = sum(1 for v in vals if v > 0)

    expansion_ok = True
    for pt in ((s.Rational(1, 3), s.Rational(1, 5), s.Rational(2, 7)),
               (s.Rational(7, 9), s.Rational(1, 2), s.Rational(1, 8))):
        t0, u0, w0 = pt
        ev = sum(bern[(k, l, m)]
                 * s.binomial(dt, k)*t0**k*(1 - t0)**(dt - k)
                 * s.binomial(du, l)*u0**l*(1 - u0)**(du - l)
                 * s.binomial(dw, m)*w0**m*(1 - w0)**(dw - m)
                 for k in range(dt + 1) for l in range(du + 1) for m in range(dw + 1))
        if s.simplify(ev - poly.eval({t: t0, u: u0, w: w0})) != 0:
            expansion_ok = False

    passed = (identity_ok and den_ok and (dt, du, dw) == (21, 20, 20)
              and len(vals) == 9702 and nonneg and expansion_ok)
    print(json.dumps({
        "schema": "erdos1041-gp3-isosceles-slice/1",
        "factorization_identity_exact": identity_ok,
        "denominator_factorization_verified": den_ok,
        "bernstein_degree": [dt, du, dw],
        "coefficient_count": len(vals),
        "strictly_positive_coefficient_count": strict,
        "all_coefficients_nonnegative": nonneg,
        "bernstein_expansion_verified": expansion_ok,
        "isosceles_slice_surplus_nonnegative": passed,
        "claim_boundary": "Slice theorem only; the fully coupled case, GP3, the selector lemma, and unrestricted Erdos 1041 remain unproved."
    }, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
