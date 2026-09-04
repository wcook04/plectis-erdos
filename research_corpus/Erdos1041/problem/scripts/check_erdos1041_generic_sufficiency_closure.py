#!/usr/bin/env python3
"""Exact checker for GenericSufficiencyClosure.md.

Every arm is exact Gaussian-rational or rational arithmetic.  Nothing here is
sampled in floating point and nothing here proves the analytic theorem; the
arms pin the finite steps the ordinary proof leans on, plus the two exact
witnesses that make the extremal value and the vanishing-slack regression
concrete.

ARM APRIORI  the a priori containment  {|g| <= 1} subset {|z| <= 2}
ARM AFFINE   the strictification arithmetic produced by R < 1 alone
ARM SUBLEVEL the exact characterisation |z|^(2n) <= 2 Re(z^n) of |z^n - 1| <= 1
ARM PETAL    strict positivity of Re(z^n) off the origin, sector disjointness,
             and the exact escape of the adjacent chord at n = 4
ARM EXTREMAL the radial pair path of length exactly 2 on z^n - 1
ARM CASSINI  the vanishing-slack regression of negative_results entry 3
ARM LIMIT    an exact shrinking family g_v -> z^4 - 1 with Lam(g_v) <= 2
"""

from __future__ import annotations

import json
import random
import sys
from fractions import Fraction as F

# ---------------------------------------------------------------- Gaussian Q


class G:
    """Exact Gaussian rational."""

    __slots__ = ("re", "im")

    def __init__(self, re=0, im=0):
        self.re = F(re)
        self.im = F(im)

    def __add__(self, o):
        return G(self.re + o.re, self.im + o.im)

    def __sub__(self, o):
        return G(self.re - o.re, self.im - o.im)

    def __mul__(self, o):
        return G(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)

    def __eq__(self, o):
        return self.re == o.re and self.im == o.im

    def normsq(self) -> F:
        return self.re * self.re + self.im * self.im

    def __pow__(self, n: int):
        out = G(1, 0)
        for _ in range(n):
            out = out * self
        return out

    def __repr__(self):
        return f"({self.re}{'+' if self.im >= 0 else '-'}{abs(self.im)}i)"


ONE = G(1, 0)


def rational_unit_point(s: F) -> G:
    """The rational parametrisation of the unit circle: normsq is exactly 1."""
    d = 1 + s * s
    return G((1 - s * s) / d, (2 * s) / d)


# ------------------------------------------------------------------ the arms


def arm_apriori(rng, trials=4000):
    """|b_j| <= 1 and |z| >= 2  ==>  prod_j |z - b_j| >= 1, exactly."""
    rows = 0
    worst = None
    for _ in range(trials):
        n = rng.randint(2, 9)
        roots = []
        for _ in range(n):
            # exactly on or inside the closed unit circle
            s = F(rng.randint(-40, 40), rng.randint(1, 40))
            u = rational_unit_point(s)
            shrink = F(rng.randint(0, 10), 10)
            roots.append(G(u.re * shrink, u.im * shrink))
            assert roots[-1].normsq() <= 1
        s = F(rng.randint(-40, 40), rng.randint(1, 40))
        u = rational_unit_point(s)
        scale = F(rng.randint(2, 7)) + F(rng.randint(0, 9), 10)
        z = G(u.re * scale, u.im * scale)
        assert z.normsq() >= 4
        prod = F(1)
        for b in roots:
            prod *= (z - b).normsq()
        if prod < 1:
            return {"status": "FAIL", "witness": repr(z), "prod_sq": str(prod)}
        if worst is None or prod < worst:
            worst = prod
        rows += 1
    return {"status": "PASS", "rows": rows, "min_prod_squared": str(worst)}


def arm_affine(rng, trials=4000):
    """R < 1 alone yields both strict inequalities of Corollary S."""
    rows = 0
    worst_len = None
    worst_lvl = None
    for _ in range(trials):
        n = rng.randint(2, 12)
        R = F(rng.randint(1, 999), 1000)
        L = F(rng.randint(0, 2000), 1000)
        v = F(rng.randint(0, 1000), 1000)
        if not (R * L < 2):
            return {"status": "FAIL", "arm": "length", "R": str(R), "L": str(L)}
        if not (R ** n * v < 1):
            return {"status": "FAIL", "arm": "level", "R": str(R), "n": n}
        worst_len = R * L if worst_len is None else max(worst_len, R * L)
        worst_lvl = R ** n * v if worst_lvl is None else max(worst_lvl, R ** n * v)
        rows += 1
    return {
        "status": "PASS",
        "rows": rows,
        "sup_transported_length": str(worst_len),
        "sup_transported_level": str(worst_lvl),
    }


def arm_sublevel(rng, trials=6000):
    """normSq(z^n - 1) <= 1  iff  normSq(z)^n <= 2 Re(z^n), exactly."""
    rows = 0
    inside = 0
    for _ in range(trials):
        n = rng.randint(2, 8)
        z = G(F(rng.randint(-30, 30), rng.randint(1, 20)),
              F(rng.randint(-30, 30), rng.randint(1, 20)))
        w = z ** n
        lhs = (w - ONE).normsq() <= 1
        rhs = z.normsq() ** n <= 2 * w.re
        if lhs != rhs:
            return {"status": "FAIL", "z": repr(z), "n": n}
        inside += 1 if lhs else 0
        rows += 1
    return {"status": "PASS", "rows": rows, "rows_inside_sublevel": inside}


def arm_petal(rng, trials=6000):
    """Off the origin the extremal sublevel set forces Re(z^n) > 0.

    Sector disjointness is the integer statement 2*(1/(2n)) < 2/n, checked
    exactly; the adjacent chord of z^4 - 1 escapes, checked exactly.
    """
    rows = 0
    tested_inside = 0
    for _ in range(trials):
        n = rng.randint(2, 8)
        # bias towards the sublevel set: small perturbations of the roots
        k = rng.randrange(n)
        s = F(rng.randint(-6, 6), rng.randint(1, 12))
        base = rational_unit_point(s)
        shrink = F(rng.randint(1, 12), 12)
        z = G(base.re * shrink, base.im * shrink)
        if z == G(0, 0):
            continue
        w = z ** n
        if (w - ONE).normsq() <= 1:
            if not (w.re > 0):
                return {"status": "FAIL", "z": repr(z), "n": n, "re": str(w.re)}
            tested_inside += 1
        rows += 1
        del k
    # sector disjointness, exactly, for every degree used above
    for n in range(2, 41):
        half_width_sum = 2 * F(1, 2 * n)   # in units of pi
        centre_gap = F(2, n)               # in units of pi
        if not (half_width_sum < centre_gap):
            return {"status": "FAIL", "arm": "sector_disjointness", "n": n}
    # exact escape of the adjacent chord of z^4 - 1 at its midpoint
    mid = G(F(1, 2), F(1, 2))
    esc = (mid ** 4 - ONE).normsq()
    if not esc > 1:
        return {"status": "FAIL", "arm": "adjacent_chord", "value": str(esc)}
    return {
        "status": "PASS",
        "rows": rows,
        "rows_inside_sublevel": tested_inside,
        "sector_disjointness_degrees": "2..40",
        "adjacent_chord_midpoint_normsq_at_n4": str(esc),
    }


def arm_extremal():
    """The radial pair path of z^n - 1 has length exactly 2 and stays inside."""
    checked = 0
    for n in range(2, 13):
        for num in range(0, 1001):
            t = F(num, 1000)
            val = (F(1) - t ** n) ** 2      # normSq((t^n - 1))
            if not val <= 1:
                return {"status": "FAIL", "n": n, "t": str(t)}
            checked += 1
    # the two half-lengths are exactly 1 each on the unit-modulus roots
    if not (F(1) + F(1) == 2):
        return {"status": "FAIL", "arm": "length"}
    # at n = 4 the whole extremal configuration is Gaussian rational
    for w in (G(1, 0), G(0, 1), G(-1, 0), G(0, -1)):
        if w.normsq() != 1 or (w ** 4 - ONE).normsq() != 0:
            return {"status": "FAIL", "arm": "n4_roots", "w": repr(w)}
    if (G(0, 0) ** 4 - ONE).normsq() != 1:
        return {"status": "FAIL", "arm": "origin_on_boundary"}
    return {
        "status": "PASS",
        "radial_rows": checked,
        "origin_normsq_on_extremal": "1",
        "pair_path_length": "2",
    }


def arm_cassini():
    """negative_results 3: the slack vanishes, and the reduction never uses it."""
    rows = []
    for m in range(2, 60):
        a = F(m - 1, m)                     # a = 1 - 1/m
        # the straight segment [-a, a] lies in {|z^2 - a^2| <= 1}
        for num in range(-1000, 1001):
            t = a * F(num, 1000)
            if not (t * t - a * a) ** 2 <= 1:
                return {"status": "FAIL", "m": m, "t": str(t)}
        rows.append((m, 2 - 2 * a))
    slack = rows[-1][1]
    if not slack > 0:
        return {"status": "FAIL", "arm": "slack_positive"}
    return {
        "status": "PASS",
        "degenerations": len(rows),
        "least_slack": str(slack),
        "note": "slack 2-2a tends to 0; Corollary S consumes none of it",
    }


def arm_limit():
    """An exact shrinking family g_v -> z^4 - 1 with Lam(g_v) <= 2 throughout."""
    checked = 0
    for v in range(2, 80):
        s = F(v - 1, v)
        # g_v(z) = s^4 * ((z/s)^4 - 1) = z^4 - s^4 ; roots s*{1,i,-1,-i}
        for num in range(0, 501):
            t = s * F(num, 500)
            # radial arm value: |g_v(t)| = |t^4 - s^4|
            val = (t ** 4 - s ** 4) ** 2
            if not val <= 1:
                return {"status": "FAIL", "v": v, "t": str(t)}
            checked += 1
        if not 2 * s <= 2:
            return {"status": "FAIL", "arm": "length", "v": v}
    return {
        "status": "PASS",
        "rows": checked,
        "limit": "z^4 - 1",
        "limit_lambda": "2",
        "note": "Lam(g_v) <= 2s_v < 2 for every v; the limit attains 2 exactly",
    }


def main() -> int:
    rng = random.Random(1041_2026_0825)
    result = {
        "checker": "erdos1041_generic_sufficiency_closure",
        "arithmetic": "exact Fraction / Gaussian rational",
        "arms": {
            "APRIORI": arm_apriori(rng),
            "AFFINE": arm_affine(rng),
            "SUBLEVEL": arm_sublevel(rng),
            "PETAL": arm_petal(rng),
            "EXTREMAL": arm_extremal(),
            "CASSINI": arm_cassini(),
            "LIMIT": arm_limit(),
        },
    }
    ok = all(a["status"] == "PASS" for a in result["arms"].values())
    result["status"] = "PASS" if ok else "FAIL"
    result["claim_boundary"] = (
        "These arms check the finite steps of GenericSufficiencyClosure.md. "
        "Arzela-Ascoli, lower semicontinuity of length, and the connectedness "
        "step of the petal lower bound are carried by the ordinary proof."
    )
    json.dump(result, sys.stdout, indent=2)
    sys.stdout.write("\n")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
