#!/usr/bin/env python3
"""Exact interval/Bernstein certificate for the sextic chord recession lemma.

All acceptance arithmetic is integer or Fraction arithmetic. No sampled
maximum, floating-point optimizer, or external CAS enters the certificate.
See ../SexticChordRecessionClosure.md for the continuous-domain argument.
"""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from math import comb, isqrt, lcm
import hashlib
import json
import time

Q = 1 << 40
SQ = isqrt(3 * Q * Q)


def interval(x):
    x = F(x) * Q
    return x.numerator // x.denominator, -((-x.numerator) // x.denominator)


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def scale(a, k):
    return (a[0] * k, a[1] * k) if k >= 0 else (a[1] * k, a[0] * k)


def mul(a, b):
    p = [x * y for x in a for y in b]
    return min(p) // Q, -((-max(p)) // Q)


def half(a):
    return a[0] // 2, -((-a[1]) // 2)


def circle(t, quadrant=0):
    a = interval((1-t*t)/(1+t*t))
    b = interval(2*t/(1+t*t))
    for _ in range(quadrant):
        a, b = scale(b, -1), a
    return a, b


def coefficients(ta, tb, quadrant):
    """Enclose exact coefficients of L_j and N_j with C removed, |A|=1."""
    a, b = circle(ta)
    c, d = circle(tb, quadrant)
    sb, sd = mul((SQ, SQ+1), b), mul((SQ, SQ+1), d)
    # sqrt(3) Re(A exp(i theta_j)), Im(A exp(i theta_j)).
    us = [half(add(scale(a, 3), scale(sb, -1))), scale(sb, -1),
          half(add(scale(a, -3), scale(sb, -1)))]
    vs = [half(add(a, sb)), a, half(add(a, scale(sb, -1)))]
    us += [scale(v, -1) for v in us]
    vs += [scale(v, -1) for v in vs]
    ps = [half(add(c, scale(sd, -1))), scale(c, -1), half(add(c, sd))]
    rs = [half(add(scale(c, 3), sd)), scale(sd, -1),
          half(add(scale(c, -3), sd))]
    zero = (0, 0)
    out = []
    for j in range(6):
        linear = [scale(us[j], 50), scale(vs[j], 58),
                  scale(us[j], -10), scale(vs[j], -2)]
        base = [add(interval(91), scale(ps[j % 3], 84)),
                scale(rs[j % 3], 16),
                add(interval(-44), scale(ps[j % 3], -4)), zero, interval(1)]
        n = [add(base[k], linear[k] if k < 4 else zero) for k in range(5)]
        out.append((linear, n))
    return out


@lru_cache(None)
def matrices(degree, pieces):
    """Exact power-to-Bernstein matrices on a partition of [-1,1]."""
    rows = []
    for s in range(pieces):
        left, width = F(2*s-pieces, pieces), F(2, pieces)
        for i in range(degree+1):
            weights = [sum((F(comb(i, k), comb(degree, k)) * comb(j, k)
                            * left**(j-k) * width**k
                            for k in range(min(i, j)+1)), F(0))
                       for j in range(degree+1)]
            den = lcm(*(w.denominator for w in weights))
            ints = [int(w*den) for w in weights]
            rows.append((ints, den))
    return rows


def upper_dot(coeffs, weights):
    return sum(w*(a[1] if w >= 0 else a[0]) for w, a in zip(weights, coeffs))


def ceil_ratio(a, b):
    assert b > 0
    return -((-a)//b)


def bounds(ta, tb, quadrant, pieces):
    slopes, thresholds = [], []
    for linear, n in coefficients(ta, tb, quadrant):
        slopes.append(max(ceil_ratio(upper_dot(linear, w), den*Q)
                          for w, den in matrices(3, pieces)))
        # P = (1-x^2) N - 255/4. P - T(1-x^2) <= 0
        # certifies H <= -1/256 at cubic threshold T.
        p = [(0, 0) for _ in range(7)]
        for k in range(5):
            p[k] = add(p[k], n[k])
            p[k+2] = add(p[k+2], scale(n[k], -1))
        p[0] = add(p[0], interval(F(-255, 4)))
        candidates = []
        for w, den in matrices(6, pieces):
            numerator = upper_dot(p, w)
            divisor = Q*(w[0]-w[2])
            assert divisor >= 0
            if divisor == 0:
                assert numerator <= 0
            else:
                candidates.append(ceil_ratio(numerator, divisor))
        thresholds.append(max(candidates))
    return slopes, thresholds


def certify_box(a0, a1, b0, b1, quadrant, pieces):
    slopes, thresholds = bounds((a0+a1)/2, (b0+b1)/2, quadrant, pieces)
    # |du/dt| <= 2; chord kernels have Euclidean norms <=90 and <=85.
    drift_l = 90*(a1-a0)
    drift_w = drift_l+85*(b1-b0)
    choices = []
    for j in (0, 2, 4):
        for k in (1, 3, 5):
            sm = -(slopes[j]+slopes[k]+2*drift_l)
            tm = -(thresholds[j]+thresholds[k]+2*drift_w)
            if sm >= 0 and tm >= 0:
                choices.append((min(sm, tm), j, k, sm, tm))
    return max(choices) if choices else None


def run(pieces=16, max_depth=8):
    start = time.monotonic()
    stack = [(F(i, 48), F(i+1, 48), F(j, 32), F(j+1, 32), q, 0)
             for q in range(4) for i in range(16) for j in range(32)]
    accepted = subdivisions = 0
    deepest = 0
    slack_s = slack_t = None
    digest = hashlib.sha256()
    while stack:
        a0, a1, b0, b1, q, depth = stack.pop()
        got = certify_box(a0, a1, b0, b1, q, pieces)
        if got is not None:
            _, j, k, sm, tm = got
            accepted += 1
            deepest = max(deepest, depth)
            slack_s = sm if slack_s is None else min(slack_s, sm)
            slack_t = tm if slack_t is None else min(slack_t, tm)
            digest.update((str((a0, a1, b0, b1, q, j, k, sm, tm))+'\n').encode())
            continue
        if depth == max_depth:
            return {'status': 'unresolved_box', 'box': list(map(str, (a0,a1,b0,b1,q))),
                    'accepted_boxes': accepted, 'evidence_class': 'incomplete_exact_certificate'}
        subdivisions += 1
        # Split the larger of the two contributions to the Lipschitz radius.
        if 90*(a1-a0) >= 85*(b1-b0):
            mid = (a0+a1)/2
            stack += [(a0,mid,b0,b1,q,depth+1),(mid,a1,b0,b1,q,depth+1)]
        else:
            mid = (b0+b1)/2
            stack += [(a0,a1,b0,mid,q,depth+1),(a0,a1,mid,b1,q,depth+1)]
    return {'status': 'proved', 'evidence_class': 'exact_integer_interval_bernstein_certificate',
            'statement': 'For |A|>=1, |B|=1, every real C admits an adjacent unit chord with H<=-1/256.',
            'accepted_boxes': accepted, 'subdivisions': subdivisions, 'max_depth': deepest,
            'minimum_recession_slack': str(slack_s), 'minimum_threshold_slack': str(slack_t),
            'certificate_sha256': digest.hexdigest(), 'bernstein_pieces': pieces,
            'elapsed_seconds': round(time.monotonic()-start, 3),
            'boundary': 'Homogeneous sextic model only; not unrestricted Erdos 1041; not Lean checked.'}


def audit():
    """Independent symbolic reconstruction; SymPy is optional for this audit."""
    import sympy as s
    x, a, b, c, d, cubic = s.symbols('x a b c d cubic', real=True)
    root = s.sqrt(3)
    cosines = [root/2, 0, -root/2, -root/2, 0, root/2]
    sines = [s.Rational(1, 2), 1, s.Rational(1, 2),
             -s.Rational(1, 2), -1, -s.Rational(1, 2)]
    checks = 0
    for j in range(6):
        rotation = cosines[j]+s.I*sines[j]
        z = rotation*(root+s.I*x)/2
        first, second = a+s.I*b, c+s.I*d
        original = s.expand(s.re(first*z+second*z**2+s.I*cubic*z**3
                                -s.conjugate(second)*z**4
                                -s.conjugate(first)*z**5-z**6))
        alpha, beta = s.expand(first*rotation), s.expand(second*rotation**2)
        linear = 10*root*s.re(alpha)*(5-x*x)+2*s.im(alpha)*x*(29-x*x)
        base = x**4-44*x*x+91+4*s.re(beta)*(21-x*x)+16*root*s.im(beta)*x
        assert s.expand(64*original+64-(1-x*x)*(base+linear-24*root*(-1)**j*cubic)) == 0
        checks += 1
        for ta, tb, quadrant in [(F(0),F(1),0),(F(1,7),F(2,5),1),
                                 (F(1,3),F(0),2),(F(1,5),F(3,7),3)]:
            ac = ((1-ta*ta)+2*s.I*ta)/(1+ta*ta)
            bc = s.I**quadrant*((1-tb*tb)+2*s.I*tb)/(1+tb*tb)
            substitutions = {a:s.re(ac),b:s.im(ac),c:s.re(bc),d:s.im(bc)}
            enclosed = coefficients(ta,tb,quadrant)[j]
            for polynomial, intervals in [(linear,enclosed[0]),(linear+base,enclosed[1])]:
                poly = s.Poly(s.expand(polynomial.subs(substitutions)), x)
                for k,(lo,hi) in enumerate(intervals):
                    exact = s.expand(poly.nth(k))
                    rational, radical = exact.coeff(root,0), exact.coeff(root,1)
                    assert s.expand(exact-rational-radical*root)==0
                    ends = [F(rational)+F(radical)*F(v,Q) for v in (SQ,SQ+1)]
                    assert F(lo,Q)<=min(ends)<=max(ends)<=F(hi,Q)
                    checks += 1
    # Reconstruct every monomial from its controls at independent rational
    # local coordinates, rather than reusing the transform to evaluate it.
    for degree in (3,6):
        mats = matrices(degree,16)
        for piece in range(16):
            block = mats[piece*(degree+1):(piece+1)*(degree+1)]
            for t in (F(0),F(1,3),F(2,5),F(1)):
                location = F(2*piece-16,16)+F(2,16)*t
                for k in range(degree+1):
                    value = sum(F(w[k],den)*comb(degree,i)*t**i*(1-t)**(degree-i)
                                for i,(w,den) in enumerate(block))
                    assert value==location**k
                    checks += 1
    return {'status':'pass','exact_identity_and_enclosure_checks':checks,
            'method':'independent SymPy expansion plus rational Bernstein reconstruction'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pieces', type=int, default=16)
    parser.add_argument('--max-depth', type=int, default=8)
    parser.add_argument('--audit', action='store_true', help='also reconstruct formulas independently with SymPy')
    args = parser.parse_args()
    assert args.pieces > 0 and args.max_depth >= 0
    result = run(args.pieces, args.max_depth)
    if args.audit:
        result['independent_formula_audit'] = audit()
    print(json.dumps(result, sort_keys=True))
    raise SystemExit(result['status'] != 'proved')
