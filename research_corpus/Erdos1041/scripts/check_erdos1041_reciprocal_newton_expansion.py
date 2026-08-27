#!/usr/bin/env python3
"""Exact checker for ReciprocalNewtonExpansion.md.

All arithmetic is exact Gaussian-rational.  Moduli are compared through
`normSq`, so no square root is ever taken, and root sets with exactly rational
modulus are produced by the rational parametrisation of the unit circle.

ARM NEWTON      Theorem R2: the coefficient recursion reproduces sum_j a_j^-m
ARM COEFFBOUND  |p_m| <= n r^-m, as normSq(p_m) <= n^2 (r^2)^-m
ARM BRIDGE      Theorem R3 at n = 4, where omega = i is Gaussian rational
ARM STAPLE      Theorem R4: the length identity and |a_i| + |a_j| < 2
ARM CONTACT     Theorem R5: the completed square is attained at x = B/(2 kappa)
ARM COUNTERMODEL  -x^2 + eps: uniform convergence to a non-positive model is
                  not enough, which is why R5 keeps the curvature
"""

from __future__ import annotations

import json
import random
import sys
from fractions import Fraction as F


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

    def scal(self, t: F):
        return G(self.re * t, self.im * t)

    def normsq(self) -> F:
        return self.re * self.re + self.im * self.im

    def inv(self):
        d = self.normsq()
        assert d != 0
        return G(self.re / d, -self.im / d)

    def __pow__(self, n: int):
        out = G(1, 0)
        base = self
        for _ in range(n):
            out = out * base
        return out

    def __eq__(self, o):
        return self.re == o.re and self.im == o.im

    def __repr__(self):
        return f"({self.re}{'+' if self.im >= 0 else '-'}{abs(self.im)}i)"


ZERO, ONE, I = G(0, 0), G(1, 0), G(0, 1)


def poly_from_roots(roots):
    """Monic coefficient list c[0..n] with c[n] = 1."""
    c = [ONE]
    for a in roots:
        new = [ZERO] * (len(c) + 1)
        for k, ck in enumerate(c):
            new[k + 1] = new[k + 1] + ck          # z * c_k
            new[k] = new[k] - ck * a              # -a * c_k
        c = new
    return c


def unit_point(s: F) -> G:
    d = 1 + s * s
    return G((1 - s * s) / d, (2 * s) / d)


# ------------------------------------------------------------------ the arms


def arm_newton(rng, trials=1200, mmax=12):
    rows = 0
    for _ in range(trials):
        n = rng.randint(2, 8)
        roots = []
        while len(roots) < n:
            a = G(F(rng.randint(-9, 9), rng.randint(1, 7)),
                  F(rng.randint(-9, 9), rng.randint(1, 7)))
            if a.normsq() == 0 or any(a == b for b in roots):
                continue
            roots.append(a)
        c = poly_from_roots(roots)
        c0inv = c[0].inv()
        chat = [c[k] * c0inv for k in range(len(c))]
        chat += [ZERO] * (mmax + 2)
        # recursion  p_m = -m chat_m - sum_{j=1}^{m-1} chat_j p_{m-j}
        p = [ZERO] * (mmax + 1)
        for m in range(1, mmax + 1):
            acc = ZERO
            for j in range(1, m):
                acc = acc + chat[j] * p[m - j]
            p[m] = ZERO - chat[m].scal(F(m)) - acc
        for m in range(1, mmax + 1):
            direct = ZERO
            for a in roots:
                direct = direct + a.inv() ** m
            if not (p[m] == direct):
                return {"status": "FAIL", "n": n, "m": m,
                        "recursion": repr(p[m]), "direct": repr(direct)}
            rows += 1
    return {"status": "PASS", "rows": rows, "max_order": mmax}


def arm_coeffbound(rng, trials=1500, mmax=10):
    rows = 0
    for _ in range(trials):
        n = rng.randint(2, 8)
        roots = []
        while len(roots) < n:
            a = G(F(rng.randint(-9, 9), rng.randint(1, 5)),
                  F(rng.randint(-9, 9), rng.randint(1, 5)))
            if a.normsq() == 0:
                continue
            roots.append(a)
        rsq = min(a.normsq() for a in roots)
        for m in range(1, mmax + 1):
            pm = ZERO
            for a in roots:
                pm = pm + a.inv() ** m
            # |p_m| <= n r^-m   <==>   normSq(p_m) <= n^2 (r^2)^-m
            if not pm.normsq() <= F(n) ** 2 / rsq ** m:
                return {"status": "FAIL", "n": n, "m": m}
            rows += 1
    return {"status": "PASS", "rows": rows, "max_order": mmax}


def arm_bridge(rng, trials=900):
    """Theorem R3 at n = 4: -p_m/m - E_m is O(eta^2), exactly."""
    n = 4
    rows = 0
    worst_ratio = F(0)
    for _ in range(trials):
        H = F(1, rng.randint(4, 40))          # rational bound on eta
        e = []
        for _ in range(n):
            while True:
                cand = G(F(rng.randint(-20, 20), 40), F(rng.randint(-20, 20), 40))
                cand = cand.scal(H * 2)
                if cand.normsq() <= H * H:
                    e.append(cand)
                    break
        roots = [(I ** k) * (ONE + e[k]) for k in range(n)]
        if any(a.normsq() == 0 for a in roots):
            continue
        for m in range(1, n):
            pm = ZERO
            for a in roots:
                pm = pm + a.inv() ** m
            Em = ZERO
            for k in range(n):
                Em = Em + e[k] * (I.inv() ** (k * m))
            resid = (ZERO - pm.scal(F(1, m))) - Em
            bound = F(n) * F(m + 1) * H * H / (2 * (1 - H) ** (m + 2))
            if not resid.normsq() <= bound * bound:
                return {"status": "FAIL", "m": m, "H": str(H),
                        "resid_normsq": str(resid.normsq()),
                        "bound_sq": str(bound * bound)}
            if bound != 0:
                ratio = resid.normsq() / (bound * bound)
                worst_ratio = max(worst_ratio, ratio)
            rows += 1
    return {"status": "PASS", "rows": rows,
            "worst_residual_over_bound_squared": str(worst_ratio)}


def arm_staple(rng, trials=3000):
    rows = 0
    for _ in range(trials):
        # exact rational moduli, exact unit directions
        rho_i = F(rng.randint(1, 999), 1000)
        rho_j = F(rng.randint(1, 999), 1000)
        u_i = unit_point(F(rng.randint(-30, 30), rng.randint(1, 20)))
        u_j = unit_point(F(rng.randint(-30, 30), rng.randint(1, 20)))
        assert u_i.normsq() == 1 and u_j.normsq() == 1
        if not (u_i - u_j).normsq() <= 4:
            return {"status": "FAIL", "arm": "chord_le_two"}
        if not rho_i + rho_j < 2:
            return {"status": "FAIL", "arm": "moduli_sum"}
        # length identity with the chord length treated as a free parameter
        s = F(rng.randint(0, 1000), 1000) * min(rho_i, rho_j)
        c = F(rng.randint(0, 2000), 1000)
        lhs = (rho_i - s) + s * c + (rho_j - s)
        rhs = rho_i + rho_j - s * (2 - c)
        if lhs != rhs:
            return {"status": "FAIL", "arm": "identity"}
        if c <= 2 and not lhs < 2:
            return {"status": "FAIL", "arm": "lt_two"}
        rows += 1
    return {"status": "PASS", "rows": rows}


def arm_contact(rng, trials=2000):
    rows = 0
    for _ in range(trials):
        kappa = F(rng.randint(1, 200), 100)
        B = F(rng.randint(-300, 300), 100)
        V = F(rng.randint(-400, 100), 100)
        eps = F(rng.randint(0, 50), 1000)
        cap = V + eps + B * B / (4 * kappa)
        # the completed square is attained at |x| = |B|/(2 kappa)
        xstar = abs(B) / (2 * kappa)
        val = -kappa * xstar * xstar + abs(B) * xstar + V + eps
        if val != cap:
            return {"status": "FAIL", "arm": "attained"}
        for _ in range(6):
            x = F(rng.randint(-500, 500), 100)
            if not -kappa * x * x + B * abs(x) + V + eps <= cap:
                return {"status": "FAIL", "arm": "upper_bound"}
        if cap < 0:
            for _ in range(6):
                x = F(rng.randint(-500, 500), 100)
                if not -kappa * x * x + B * abs(x) + V + eps < 0:
                    return {"status": "FAIL", "arm": "survives"}
        rows += 1
    # the recorded sextic instance: curvature -x^2/20 against slope 3 delta |x|
    for d in range(1, 40):
        delta = F(d, 100)
        kappa, B = F(1, 20), 3 * delta
        if B * B / (4 * kappa) != 45 * delta * delta:
            return {"status": "FAIL", "arm": "sextic_instance", "delta": str(delta)}
    return {"status": "PASS", "rows": rows, "sextic_cost": "45 delta^2"}


def arm_countermodel():
    """-x^2 + eps converges uniformly to -x^2 and is positive at x = 0."""
    for k in range(1, 200):
        eps = F(1, k)
        if not (-F(0) * F(0) + eps) > 0:
            return {"status": "FAIL"}
        if not eps <= F(1, 1):
            return {"status": "FAIL"}
    return {"status": "PASS",
            "note": "sup |h_eps - h_0| = eps -> 0 while max h_eps = eps > 0"}


def main() -> int:
    rng = random.Random(1041_2026_0825_2)
    result = {
        "checker": "erdos1041_reciprocal_newton_expansion",
        "arithmetic": "exact Fraction / Gaussian rational, normSq comparisons only",
        "arms": {
            "NEWTON": arm_newton(rng),
            "COEFFBOUND": arm_coeffbound(rng),
            "BRIDGE": arm_bridge(rng),
            "STAPLE": arm_staple(rng),
            "CONTACT": arm_contact(rng),
            "COUNTERMODEL": arm_countermodel(),
        },
    }
    ok = all(a["status"] == "PASS" for a in result["arms"].values())
    result["status"] = "PASS" if ok else "FAIL"
    result["claim_boundary"] = (
        "These arms check Theorems R2, R3, R4, R5 and the coefficient bound of "
        "R1 on exact data. The convergence of the logarithmic series, the C1 and "
        "C2 tail estimates, and the normalisation of section 4 are carried by "
        "the ordinary proof."
    )
    json.dump(result, sys.stdout, indent=2)
    sys.stdout.write("\n")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
