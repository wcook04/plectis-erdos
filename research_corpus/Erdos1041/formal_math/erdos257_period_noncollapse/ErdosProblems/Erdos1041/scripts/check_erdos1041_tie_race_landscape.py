#!/usr/bin/env python3
"""Exact certificate for TieRaceLandscape.md, Erdős #1041.

Certified statement (negative result).  For the monic octic with the Gaussian-rational roots below (all strictly inside the open unit disc), let c* be the least critical point and
nu_max = max_j |f(c_j)| the largest critical-value modulus.  Then at least n-1 of the n straight spokes
[c*, a_k] carry a point where |f| > nu_max, so the second-smallest spoke maximum at c* exceeds nu_max:
the statement "spoke maxima at the least critical point are bounded by the largest critical value" is FALSE.

Method (all in Fraction arithmetic):
  * critical points: float approximations c_j, then a Kantorovich-style disc D(c_j, r) is certified to contain a
    zero of f' by the bound |f'(c_j)| / min_{D} |f''| < r with |f''| bounded below on the disc through its value
    at c_j minus r * max|f'''|; the n-1 discs are pairwise disjoint, so each holds exactly one critical point;
  * nu_max <= max_j ( |f(c_j)| + r * M1 ) with M1 an upper bound for |f'| on the disc (crude: sum of |coeff| (1+r)^k);
  * the least critical point lies in the disc whose centre has the smallest |f|, provided that disc's upper bound
    is below every other disc's lower bound |f(c_j)| - r M1 (certified);
  * for each root a (except one), a rational s in (0,1) with |f(h + s(a - h))| - r M1' > nu_max_upper for EVERY h
    in the c* disc, where M1' bounds |f'| on the segment's r-neighbourhood; squares are compared exactly.
Output: one JSON line with status/evidence_class; exit 0 on pass."""
from __future__ import annotations
import json, math, sys
from fractions import Fraction as F

ROOTS = {
    "octic": [(F(9728, 10000), F(-635, 100000)), (F(71258, 100000), F(67082, 100000)), (F(1356, 100000), F(96, 100)),
              (F(-66936, 100000), F(65707, 100000)), (F(-98758, 100000), F(587, 100000)), (F(-67722, 100000), F(-66973, 100000)),
              (F(2632, 100000), F(-98418, 100000)), (F(68875, 100000), F(-71365, 100000))],
}


class G:  # exact Gaussian rational
    __slots__ = ("re", "im")
    def __init__(self, re, im=F(0)): self.re, self.im = F(re), F(im)
    def __add__(self, o): return G(self.re + o.re, self.im + o.im)
    def __sub__(self, o): return G(self.re - o.re, self.im - o.im)
    def __mul__(self, o): return G(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)
    def scale(self, k): return G(self.re * k, self.im * k)
    def n2(self): return self.re * self.re + self.im * self.im


def poly_from_roots(rs):
    co = [G(1)]
    for r in rs:
        nc = [G(0)] * (len(co) + 1)
        for i, c in enumerate(co):
            nc[i] = nc[i] + c
            nc[i + 1] = nc[i + 1] - c * r
        co = nc
    return co  # highest degree first


def polyval(co, z):
    acc = G(0)
    for c in co: acc = acc * z + c
    return acc


def polyder(co):
    n = len(co) - 1
    return [co[i].scale(n - i) for i in range(n)]


DEN = 10**15


def ceil_q(q: F) -> F: return F(-((-q.numerator * DEN) // q.denominator), DEN)


def floor_q(q: F) -> F: return F((q.numerator * DEN) // q.denominator, DEN)


def sqrt_upper(q: F) -> F:
    """rational upper bound for sqrt(q), q >= 0, by integer square root on a fixed grid"""
    if q <= 0: return F(0)
    m = -((-q.numerator * DEN * DEN) // q.denominator)   # ceil(q * DEN^2)
    r = math.isqrt(m)
    if r * r < m: r += 1
    return F(r, DEN)


def abs_upper(z: G) -> F: return sqrt_upper(z.n2())


def abs_lower(z: G) -> F:
    """rational lower bound for |z| via floor of the integer square root"""
    q = z.n2()
    if q <= 0: return F(0)
    m = (q.numerator * DEN * DEN) // q.denominator
    return F(math.isqrt(m), DEN)


def sup_abs_disc(co, c: G, r: F) -> F:
    """upper bound for |p| on D(c, r): sum |p^(k)(c)|/k! r^k via Taylor shift, crude but exact"""
    # Taylor shift: coefficients of p(c + w)
    n = len(co) - 1
    sh = [G(0)] * (n + 1)
    # Horner-based synthetic shift
    cur = list(co)
    for k in range(n + 1):
        # divide cur by (w) after substituting: compute p(c) repeatedly
        acc = G(0); rem = []
        for cc in cur:
            acc = acc * c + cc
            rem.append(acc)
        sh[k] = rem[-1]
        cur = rem[:-1]
        if not cur: break
    # sh[k] is coefficient of w^k of p(c+w) in order k=0..n
    tot = F(0); rk = F(1)
    for k in range(n + 1):
        tot += abs_upper(sh[k]) * rk; rk *= r
    return ceil_q(tot)


def certify(name, roots_q):
    rs = [G(a, b) for a, b in roots_q]
    n = len(rs)
    for z in rs:
        assert z.n2() < 1, "root not in the open disc"
    f = poly_from_roots(rs); f1 = polyder(f); f2 = polyder(f1); f3 = polyder(f2)
    # float critical points
    import numpy as np
    cf = [complex(float(c.re), float(c.im)) for c in f1]
    crit = np.roots(cf)
    r = F(1, 10**6)
    discs = []
    for c in crit:
        cq = G(F(round(c.real * 10**12), 10**12), F(round(c.imag * 10**12), 10**12))
        f1c = abs_upper(polyval(f1, cq))
        f2c = abs_lower(polyval(f2, cq)) - r * sup_abs_disc(f3, cq, r)
        assert f2c > 0 and f1c / f2c < r, f"Kantorovich disc failed for {name}"
        discs.append(cq)
    # disjointness
    for i in range(len(discs)):
        for j in range(i + 1, len(discs)):
            assert (discs[i] - discs[j]).n2() > (2 * r) ** 2, "discs overlap"
    ups, lows = [], []
    for cq in discs:
        M1 = sup_abs_disc(f1, cq, r)
        v = polyval(f, cq)
        ups.append(abs_upper(v) + r * M1); lows.append(abs_lower(v) - r * M1)
    numax_upper = max(ups)
    istar = min(range(len(discs)), key=lambda i: ups[i])
    assert all(ups[istar] < lows[j] for j in range(len(discs)) if j != istar), "least critical point not separated"
    cstar = discs[istar]
    mu_lower, mu_upper = lows[istar], ups[istar]
    # spokes: for each root find a rational s with certified |f| > numax_upper for every h in D(cstar, r)
    exceeding = 0; witnesses = []
    for a in rs:
        best = None
        for num in range(1, 400):
            s = F(num, 400)
            z = cstar + (a - cstar).scale(s)
            # h varies in D(cstar,r): z(h) = h + s(a-h) moves within r(1-s) <= r of z
            M1s = sup_abs_disc(f1, z, r)
            val = abs_lower(polyval(f, z)) - r * M1s
            if val > numax_upper:
                best = (s, val); break
        if best:
            exceeding += 1; witnesses.append({"root": [str(a.re), str(a.im)], "s": str(best[0]), "certified_abs_f_lower": float(best[1])})
    ok = exceeding >= n - 1
    return {"name": name, "n": n, "mu_bounds": [float(mu_lower), float(mu_upper)], "nu_max_upper": float(numax_upper),
            "disc_radius": str(r), "spokes_exceeding_nu_max": exceeding, "required": n - 1, "pass": ok,
            "witnesses": witnesses}


def main():
    rep = {"check": "erdos1041_tie_race_landscape", "source": "ErdosProblems/Erdos1041/TieRaceLandscape.md",
           "evidence_class": "exact_rational_certificate", "cases": []}
    ok = True
    for name, rq in ROOTS.items():
        c = certify(name, rq); rep["cases"].append(c); ok = ok and c["pass"]
    rep["status"] = "pass" if ok else "FAIL"
    rep["certified_negative"] = ("at the least critical point c*, at least n-1 straight spokes carry a point with |f| > nu_max; "
                                 "so the second-smallest spoke maximum at c* exceeds the largest critical value")
    print(json.dumps(rep))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
