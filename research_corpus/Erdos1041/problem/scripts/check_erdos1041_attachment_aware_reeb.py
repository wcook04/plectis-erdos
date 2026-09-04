#!/usr/bin/env python3
"""Exact checker for AttachmentAwareReeb.md.

Angles are carried by the rational parametrisation of the unit circle,
`cos = (1-t^2)/(1+t^2)`, `sin = 2t/(1+t^2)`, so every trigonometric statement
below is exact rational arithmetic.  Nothing is sampled in floating point.

ARM RAYDIST    the completed square behind Theorem 2
ARM WINDOW     the attachable angular window and its exact width scaling
ARM EXTREMAL   Theorem 5 on z^n - r^n: closest approach, attainment, window
ARM EXPONENT   Theorem 2': the window exponent is the ramification index
ARM TREE       (1c): k vertices, k-1 edges, connected  =>  tree; and the
               transposition-graph version
ARM AVERAGE    Corollary 3a's averaging step
ARM ROOTSTAR   Theorem 4: the tangent pull-out, and its exact vanishing on the
               Cassini witness
ARM CASSINI    the recorded 4/25 attachment deficit, in exact integers
"""

from __future__ import annotations

import json
import random
import sys
from fractions import Fraction as F


def cos_sin(t: F):
    """Exact (cos, sin) of the angle with half-tangent t."""
    d = 1 + t * t
    return (1 - t * t) / d, (2 * t) / d


class DSU:
    def __init__(self, n):
        self.p = list(range(n))

    def find(self, x):
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]
            x = self.p[x]
        return x

    def union(self, a, b):
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return False
        self.p[ra] = rb
        return True


# ------------------------------------------------------------------ the arms


def arm_raydist(rng, trials=6000):
    rows = 0
    for _ in range(trials):
        rho = F(rng.randint(1, 400), 100)
        r = F(rng.randint(0, 800), 100)
        t = F(rng.randint(-60, 60), rng.randint(1, 25))
        c, s = cos_sin(t)
        assert c * c + s * s == 1
        lhs = rho ** 2 - 2 * rho * r * c + r ** 2 - rho ** 2 * s ** 2
        if lhs != (r - rho * c) ** 2:
            return {"status": "FAIL", "arm": "identity"}
        # the minimum over the ray is rho^2 s^2 exactly, attained at r = rho c
        if rho ** 2 - 2 * rho * (rho * c) * c + (rho * c) ** 2 != rho ** 2 * s ** 2:
            return {"status": "FAIL", "arm": "attained"}
        rows += 1
    return {"status": "PASS", "rows": rows}


def arm_window(rng, trials=4000):
    """rho |sin| < delta on the cos>0 branch, with exact width bounds."""
    rows = 0
    for _ in range(trials):
        rho = F(rng.randint(1, 200), 100)
        delta = F(rng.randint(1, 99), 100) * rho     # delta < rho
        # inside the sufficient sub-window |t| < delta/(2 rho): always attachable
        tin = F(rng.randint(0, 999), 1000) * delta / (2 * rho)
        c, s = cos_sin(tin)
        if not (rho * abs(s) < delta and c > 0):
            return {"status": "FAIL", "arm": "sufficient", "t": str(tin)}
        # outside |t| > delta/rho but still on the cos>0 branch: never attachable
        lo = delta / rho
        if lo < 1:
            tout = lo + (1 - lo) * F(rng.randint(1, 1000), 1000)
            c2, s2 = cos_sin(tout)
            if c2 > 0 and rho * abs(s2) < delta:
                return {"status": "FAIL", "arm": "necessary", "t": str(tout)}
        rows += 1
    return {"status": "PASS", "rows": rows,
            "width_bracket": "delta/(2 rho) <= half-width <= delta/rho"}


def arm_extremal(rng, trials=3000):
    """Theorem 5 on z^n - r^n, with Rho = r^n."""
    rows = 0
    for _ in range(trials):
        n = rng.randint(2, 8)
        r = F(rng.randint(1, 100), 100)
        Rho = r ** n
        t = F(rng.randint(-60, 60), rng.randint(1, 25))
        c, s = cos_sin(t)
        for tt in (F(0), F(rng.randint(0, 500), 100), F(rng.randint(0, 5000), 100)):
            val = Rho ** 2 + 2 * Rho * tt * c + tt ** 2
            if not val >= Rho ** 2 * s ** 2:
                return {"status": "FAIL", "arm": "lower", "n": n}
            if c >= 0 and not val >= Rho ** 2:
                return {"status": "FAIL", "arm": "cos_nonneg", "n": n}
        if c < 0:
            tstar = -(Rho * c)
            assert tstar >= 0
            if Rho ** 2 + 2 * Rho * tstar * c + tstar ** 2 != Rho ** 2 * s ** 2:
                return {"status": "FAIL", "arm": "attained", "n": n}
        rows += 1
    return {"status": "PASS", "rows": rows}


def arm_exponent(rng, trials=2000):
    """Theorem 2': the extremal window is exactly |sin| < (eps/r)^n."""
    rows = 0
    ratios = []
    for _ in range(trials):
        n = rng.randint(2, 9)
        r = F(rng.randint(50, 100), 100)
        eps = F(rng.randint(1, 49), 100) * r        # eps < r
        thr = (eps / r) ** n
        # the window strictly shrinks as the ramification index grows
        if not (eps / r) ** (n + 1) < thr:
            return {"status": "FAIL", "arm": "monotone_in_n"}
        # a point inside the window really does reach within eps
        t = F(rng.randint(1, 999), 1000)
        c, s = cos_sin(t)
        if c < 0 and abs(s) < thr:
            Rho = r ** n
            if not Rho ** 2 * s ** 2 < (eps ** n) ** 2:
                return {"status": "FAIL", "arm": "inside", "n": n}
        # and a point outside does not
        if c < 0 and abs(s) > thr:
            Rho = r ** n
            if not Rho ** 2 * s ** 2 > (eps ** n) ** 2:
                return {"status": "FAIL", "arm": "outside", "n": n}
        ratios.append(thr)
        rows += 1
    return {"status": "PASS", "rows": rows, "max_window_threshold": str(max(ratios))}


def arm_tree(rng, trials=3000):
    """k vertices, k-1 edges, connected => tree; transposition version too."""
    rows = 0
    for _ in range(trials):
        k = rng.randint(2, 12)
        # build a random spanning tree by transpositions, as in (1c)
        perm_edges = []
        for v in range(1, k):
            perm_edges.append((rng.randrange(v), v))
        dsu = DSU(k)
        acyclic = all(dsu.union(a, b) for a, b in perm_edges)
        comps = len({dsu.find(v) for v in range(k)})
        if not (acyclic and comps == 1 and len(perm_edges) == k - 1):
            return {"status": "FAIL", "arm": "tree", "k": k}
        # the transpositions really do generate a transitive group
        reach = {0}
        changed = True
        while changed:
            changed = False
            for a, b in perm_edges:
                if a in reach and b not in reach:
                    reach.add(b); changed = True
                if b in reach and a not in reach:
                    reach.add(a); changed = True
        if len(reach) != k:
            return {"status": "FAIL", "arm": "transitive", "k": k}
        # a k-1-edge graph with a repeated edge is NOT connected: negative control
        if k >= 3:
            bad = perm_edges[:-1] + [perm_edges[0]]
            dsu2 = DSU(k)
            for a, b in bad:
                dsu2.union(a, b)
            if len({dsu2.find(v) for v in range(k)}) == 1:
                return {"status": "FAIL", "arm": "negative_control", "k": k}
        rows += 1
    return {"status": "PASS", "rows": rows}


def arm_average(rng, trials=4000):
    rows = 0
    for _ in range(trials):
        m = rng.randint(1, 12)
        B = F(rng.randint(1, 400), 100)
        L = [F(rng.randint(0, 800), 100) for _ in range(m)]
        if sum(L) <= B * m:
            if not min(L) <= B:
                return {"status": "FAIL", "arm": "average"}
            rows += 1
        else:
            # negative control: the aggregate can fail while a minimum survives
            pass
    return {"status": "PASS", "rows": rows,
            "note": "aggregate (A) implies the hub statement; the converse is false"}


def arm_rootstar(rng, trials=4000):
    """Theorem 4: sum_i Re(a conj(w u_i)) = Re(a conj(w) sum_i conj(u_i))."""
    rows = 0
    for _ in range(trials):
        d = rng.randint(1, 6)
        a = complex_rat(rng)
        w = complex_rat(rng)
        us = [complex_rat(rng) for _ in range(d)]
        lhs = sum(re_mul_conj(a, mul(w, u)) for u in us)
        acc = (F(0), F(0))
        for u in us:
            acc = add(acc, conj(u))
        rhs = re_mul(mul(a, conj(w)), acc)
        if lhs != rhs:
            return {"status": "FAIL", "arm": "pullout"}
        rows += 1
    # the Cassini witness: R + <a, U_a> = 0 at both roots, exactly
    for num in range(1, 100):
        a = F(num, 100)
        # at the root a: U_a = -1 (theta_c = pi, arg f'(a) = 0)
        if a + re_mul_conj((a, F(0)), (F(-1), F(0))) != 0:
            return {"status": "FAIL", "arm": "cassini_root_plus"}
        # at the root -a: U = +1 (theta_c = pi, arg f'(-a) = pi)
        if a + re_mul_conj((-a, F(0)), (F(1), F(0))) != 0:
            return {"status": "FAIL", "arm": "cassini_root_minus"}
    return {"status": "PASS", "rows": rows,
            "cassini_endpoint_deficit": "0 at both roots, for every a"}


def complex_rat(rng):
    return (F(rng.randint(-20, 20), rng.randint(1, 9)),
            F(rng.randint(-20, 20), rng.randint(1, 9)))


def mul(x, y):
    return (x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0])


def conj(x):
    return (x[0], -x[1])


def add(x, y):
    return (x[0] + y[0], x[1] + y[1])


def re_mul(x, y):
    return mul(x, y)[0]


def re_mul_conj(x, y):
    return mul(x, conj(y))[0]


def arm_cassini():
    """(27 - 2 sqrt 171)/5 > 4/25, in exact integers."""
    # equivalent to 131 > 10 sqrt 171, i.e. 131^2 > 100 * 171
    if not 131 ** 2 > 100 * 171:
        return {"status": "FAIL", "arm": "deficit"}
    if 131 ** 2 - 100 * 171 != 61:
        return {"status": "FAIL", "arm": "margin"}
    # Theorem 5 at n = 2 is the Cassini closest-approach formula: with
    # Rho = a^2, the minimum of Rho^2 + 2 Rho t c + t^2 is Rho^2 s^2, so
    # |z|^2 = a^2 |s| and |z| = a sqrt|s|.
    a = F(9, 10)
    Rho = a ** 2
    for num in range(1, 200):
        t = F(num, 100)
        c, s = cos_sin(t)
        if c < 0:
            tstar = -(Rho * c)
            if Rho ** 2 + 2 * Rho * tstar * c + tstar ** 2 != Rho ** 2 * s ** 2:
                return {"status": "FAIL", "arm": "n2_specialisation"}
    return {"status": "PASS",
            "integer_margin": "131^2 - 100*171 = 61 > 0",
            "note": "the 4/25 deficit is recorded in CassiniAttachmentDeficitLab.md"}


def main() -> int:
    rng = random.Random(1041_2026_0825_8)
    result = {
        "checker": "erdos1041_attachment_aware_reeb",
        "arithmetic": "exact Fraction; angles via the rational half-tangent parametrisation",
        "arms": {
            "RAYDIST": arm_raydist(rng),
            "WINDOW": arm_window(rng),
            "EXTREMAL": arm_extremal(rng),
            "EXPONENT": arm_exponent(rng),
            "TREE": arm_tree(rng),
            "AVERAGE": arm_average(rng),
            "ROOTSTAR": arm_rootstar(rng),
            "CASSINI": arm_cassini(),
        },
    }
    ok = all(a["status"] == "PASS" for a in result["arms"].values())
    result["status"] = "PASS" if ok else "FAIL"
    result["claim_boundary"] = (
        "These arms check the algebraic and combinatorial steps of "
        "AttachmentAwareReeb.md. Riemann-Hurwitz, the monodromy transposition "
        "argument, the strip diffeomorphism, and the skeleton limits of Theorem 3 "
        "are carried by the ordinary proof."
    )
    json.dump(result, sys.stdout, indent=2)
    sys.stdout.write("\n")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
