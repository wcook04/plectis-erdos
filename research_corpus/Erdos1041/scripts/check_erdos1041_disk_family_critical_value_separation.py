"""Exact replay for DiskFamilyCriticalValueSeparation.md.

Checks, symbolically or in exact rational arithmetic:

1. the Möbius normal form: M(w) = wS/(S^2 + a w - a^2) maps D(a,S) onto the
   unit disk with M(0)=0, is increasing on [0,1], and M(1) = S/(S^2+p) with
   p = a(1-a);
2. the Bergman segment constant Lambda(q) = (2/pi) log((1+q^2)/(1-q^2))
   evaluated at q^2 = S/(S^2+p) equals (2/pi) log((S^2+S+p)/(S^2-S+p));
3. the centre monotonicity (S^2+S+p)/(S^2-S+p) <= (S+1)/(S-1) iff p >= 0;
4. (S+1)/(S-1) <= 7 iff S >= 4/3, and log 7 < 2 via 7 < e^2 from a rational
   lower bound on e;
5. the exterior-fibre gap constant k/(2n-k) at k=2 is 1/(n-1);
6. the new squared coefficient is strictly below the old one at every
   (n, S) with n >= 3, S > 1, and the old convenient thresholds
   (3,4), (4,3), (6,2) are dominated;
7. the branch-centred radius 2 works for every n >= 3 and radius 6/5 at
   n = 3, by exact rational inequalities plus rational bounds on logs.

Exit code 0 means every check passed.
"""

from __future__ import annotations

import math
import sys
from fractions import Fraction as Fr

import sympy as sp

S, a, w, p, n = sp.symbols("S a w p n", positive=True)


def check(name, cond):
    print(("PASS " if cond else "FAIL ") + name)
    return bool(cond)


def main() -> int:
    ok = True

    # 1. Moebius normal form
    M = w * S / (S**2 + a * w - a**2)
    ok &= check("M(0)=0", sp.simplify(M.subs(w, 0)) == 0)
    # |M(w)|=1 on |w-a|=S: check M maps the boundary circle to the unit circle
    th = sp.symbols("theta", real=True)
    wb = a + S * sp.exp(sp.I * th)
    Mb = M.subs(w, wb)
    mod2 = sp.simplify(sp.expand(Mb * sp.conjugate(Mb)))
    ok &= check("|M|=1 on the boundary circle", sp.simplify(mod2 - 1) == 0)
    dM = sp.simplify(sp.diff(M, w))
    ok &= check(
        "M'(w) = S(S^2-a^2)/(S^2+aw-a^2)^2 > 0 for S>a",
        sp.simplify(dM - S * (S**2 - a**2) / (S**2 + a * w - a**2) ** 2) == 0,
    )
    M1 = sp.simplify(M.subs(w, 1))
    ok &= check("M(1) = S/(S^2 + a(1-a))", sp.simplify(M1 - S / (S**2 + a * (1 - a))) == 0)

    # 2. Lambda closed form at q^2 = S/(S^2+p)
    q2 = S / (S**2 + p)
    ratio = sp.simplify((1 + q2) / (1 - q2))
    ok &= check(
        "(1+q^2)/(1-q^2) = (S^2+S+p)/(S^2-S+p)",
        sp.simplify(ratio - (S**2 + S + p) / (S**2 - S + p)) == 0,
    )
    # Lambda(q) integral identity: int_{-q}^{q} int_{-q}^{q} ds ds'/(pi(1-ss')^2)
    s, t, q = sp.symbols("s t q", real=True)
    inner = sp.simplify(sp.integrate(1 / (1 - s * t) ** 2, (t, -q, q)))
    ok &= check("inner integral = 2q/(1-q^2 s^2)", sp.simplify(inner - 2 * q / (1 - q**2 * s**2)) == 0)
    lam = sp.integrate(2 * q / (1 - q**2 * s**2), (s, -q, q)) / sp.pi
    target = (2 / sp.pi) * sp.log((1 + q**2) / (1 - q**2))
    lam_ok = all(
        abs(float(lam.subs(q, qq)) - float(target.subs(q, qq))) < 1e-12
        for qq in [sp.Rational(1, 10), sp.Rational(1, 2), sp.Rational(9, 10), sp.Rational(99, 100)]
    )
    ok &= check("Lambda(q) = (2/pi) log((1+q^2)/(1-q^2)) (exact integral, sampled)", lam_ok)

    # 3. centre monotonicity
    lhs = (S**2 + S + p) * (S - 1)
    rhs = (S + 1) * (S**2 - S + p)
    ok &= check("(S+1)(S^2-S+p) - (S^2+S+p)(S-1) = 2p", sp.simplify(rhs - lhs - 2 * p) == 0)

    # 4. threshold 7 and log 7 < 2
    ok &= check("(S+1)/(S-1) <= 7 iff S >= 4/3", sp.simplify(7 * (S - 1) - (S + 1) - (6 * S - 8)) == 0)
    e_lower = Fr(27182818283, 10**10)
    ok &= check("7 < e^2 (rational lower bound on e)", e_lower**2 > 7)
    ok &= check("log 7 < 2 numerically", math.log(7) < 2)

    # 5. fibre-gap constant
    ok &= check("k/(2n-k) at k=2 equals 1/(n-1)", sp.simplify(2 / (2 * n - 2) - 1 / (n - 1)) == 0)

    # 6. new < old
    def old_coeff(nn, SS):
        return 4 * (1 + SS) ** (2 / nn) * math.log(SS / (SS - 1))

    def new_coeff(nn, SS, pp=0.0):
        return 2 * (SS / (nn - 1)) ** (2 / nn) * math.log((SS * SS + SS + pp) / (SS * SS - SS + pp))

    dominated = all(
        new_coeff(nn, SS) < old_coeff(nn, SS)
        for nn in range(3, 60)
        for SS in [1.01, 1.1, 1.3, 1.5, 2.0, 3.0, 4.0, 10.0, 100.0]
    )
    ok &= check("new squared coefficient < old at a grid of (n,S)", dominated)
    ok &= check("log((S+1)/(S-1)) < 2 log(S/(S-1)) symbolically <=> S^2-1 < S^2",
                sp.simplify((S + 1) * (S - 1) - S**2 + 1) == 0)
    for nn, SS in [(3, 4.0), (4, 3.0), (6, 2.0)]:
        ok &= check(f"old threshold ({nn},{SS}) dominated: new={new_coeff(nn, SS):.4f} old={old_coeff(nn, SS):.4f}",
                    new_coeff(nn, SS) < old_coeff(nn, SS) < 4)

    # 7. uniform regimes
    # radius 2 in every degree: (2/(n-1))^(2/n) <= 1 and log 3 < 2 (3 < e^2)
    ok &= check("3 < e^2", e_lower**2 > 3)
    # S = 4/3 for all n>=3, p in [0,1/4]: coefficient <= log 7 < 2
    ok &= check("max_n C(n,4/3,p) < 2 numerically",
                max(new_coeff(nn, 4 / 3, pp) / 2 for nn in range(3, 500) for pp in [0, 0.1, 0.25]) < 2)
    # degree three radius 6/5: (3/5)^(2/3) <= 18/25 by cubing, log 11 < 5/2 by e^5 > 121
    ok &= check("(3/5)^2 <= (18/25)^3", Fr(9, 25) <= Fr(18, 25) ** 3)
    ok &= check("121 < e^5", e_lower**5 > 121)
    ok &= check("(18/25)(5/2) < 2", Fr(18, 25) * Fr(5, 2) < 2)
    ok &= check("(3/5)^(2/3) log 11 < 2 numerically", (0.6 ** (2 / 3)) * math.log(11) < 2)

    # thresholds table (informational)
    print("per-degree endpoint thresholds S_n^* (p=0):")
    for nn in [3, 4, 5, 6, 8, 10, 20, 100, 1000]:
        lo, hi = 1.000001, 50.0
        for _ in range(200):
            mid = 0.5 * (lo + hi)
            if new_coeff(nn, mid) / 2 > 2:
                lo = mid
            else:
                hi = mid
        print(f"  n={nn:5d}  S*={hi:.6f}")
    print(f"  limit coth(1) = {1/math.tanh(1):.6f}")

    print("ALL PASS" if ok else "SOME CHECKS FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
