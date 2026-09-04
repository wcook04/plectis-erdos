#!/usr/bin/env python3
"""Replay the one-row phase/energy splice and its computed route boundary."""

from __future__ import annotations

from fractions import Fraction
import math

import numpy as np
import sympy as sp


def exact_reciprocal_replay() -> None:
    # Reciprocal roots v_j=1/d_j with sum zero make c=0 critical.
    v = [sp.Rational(10), sp.Rational(8), sp.Rational(4),
         sp.Rational(-7), sp.Rational(-15)]
    assert sum(v) == 0
    w, t = sp.symbols("w t")
    q = sp.expand(sp.prod(1 - w * z for z in v))
    coeff = [sp.expand(q).coeff(w, k) for k in range(6)]
    assert coeff[0] == 1 and coeff[1] == 0

    for z in v:
        d = 1 / z
        direct = sp.expand(sp.prod(1 - t * d * y for y in v))
        common = sp.expand(q.subs(w, t * d))
        assert sp.expand(direct - common) == 0
        assert sp.expand(common.subs(t, 1)) == 0
        endpoint = coeff[5] * d**5 + 1
        assert sp.expand(endpoint + sum(coeff[k] * d**k for k in range(2, 5))) == 0

    # The two nearest roots correspond to |v|=15 and |v|=10.
    d1, d2 = sp.Rational(1, 15), sp.Rational(1, 10)
    x1 = [abs(coeff[k]) * d1**k for k in range(2, 5)]
    x2 = [abs(coeff[k]) * d2**k for k in range(2, 5)]
    assert all(a <= b for a, b in zip(x1, x2))
    k1 = 1 - t**5 + sum(x1[k - 2] * (t**k + t**5) for k in range(2, 5))
    k2 = 1 - t**5 + sum(x2[k - 2] * (t**k + t**5) for k in range(2, 5))
    # Coefficients of K_2-K_1 are nonnegative.
    assert all(sp.expand(k2 - k1).coeff(t, k) >= 0 for k in range(6))

    # S_i=sum_{j!=i}|d_i/d_j|^2; it is monotone for this exact ordered pair.
    s1 = sum((d1 * z) ** 2 for z in v if z != -15)
    s2 = sum((d2 * z) ** 2 for z in v if z != 10)
    assert s1 <= s2


def exact_head_and_young_replay() -> None:
    # Exact rational head inequality in a representative n=5 row.
    n = 5
    xs = [sp.Rational(1, 20), sp.Rational(1, 25), sp.Rational(1, 50)]
    dsum = sum(xs)
    t, tau = sp.symbols("t tau", nonnegative=True)
    krow = 1 - t**n + sum(xs[k - 2] * (t**k + t**n) for k in range(2, n))
    head = 1 + sum(xs[k - 2] * tau**k for k in range(2, n))
    # D<1, so K(t)-1 <= sum x_k t^k <= sum x_k tau^k on 0<=t<=tau.
    assert dsum < 1
    assert sp.expand(krow - 1 - sum(xs[k - 2] * t**k for k in range(2, n))) == (dsum - 1) * t**n

    # Allocate q=1-D exactly, and verify the stationary-value algebra in (17).
    q = 1 - dsum
    alphas = [q / 3] * 3
    assert sum(alphas) == q
    for k, d, alpha in zip(range(2, n), xs, alphas):
        ystar = sp.Rational(k) * d / (sp.Rational(n) * alpha)
        # At x^(n-k)=ystar, the derivative vanishes and the value factors.
        assert sp.simplify(k * d - n * alpha * ystar) == 0
        factor = sp.simplify(d - alpha * ystar)
        assert factor == sp.Rational(n - k, n) * d
        yval = (sp.Rational(n - k, n) * d
                * ystar ** sp.Rational(k, n - k))
        stated = (sp.Rational(n - k, n) * d
                  * (sp.Rational(k) * d / (sp.Rational(n) * alpha))
                  ** sp.Rational(k, n - k))
        assert sp.simplify(yval - stated) == 0

    # Rational-grid replay of the summed Young domination.
    def kval(x: Fraction) -> float:
        z = float(x)
        return 1 - z**n + sum(float(xs[k - 2]) * (z**k + z**n) for k in range(2, n))

    young = 1.0
    for k, d, alpha in zip(range(2, n), xs, alphas):
        young += float(sp.Rational(n - k, n) * d
                       * (sp.Rational(k) * d / (sp.Rational(n) * alpha))
                       ** sp.Rational(k, n - k))
    assert max(kval(Fraction(j, 2000)) for j in range(2001)) <= young + 1e-13


def max_poly(coeff_ascending: np.ndarray) -> float:
    deriv = np.array([k * coeff_ascending[k] for k in range(1, len(coeff_ascending))])
    cand = [0.0, 1.0]
    if np.max(abs(deriv)):
        for z in np.roots(deriv[::-1]):
            if abs(z.imag) < 1e-7 and 0 <= z.real <= 1:
                cand.append(float(z.real))
    return max(float(np.polyval(coeff_ascending[::-1], x)) for x in cand)


def sharp_joint_row(roots: np.ndarray, c: complex, i: int) -> float:
    n = len(roots)
    u = (roots[i] - c) / (roots - c)
    coeff = np.array([1.0 + 0j])
    for z in u:
        coeff = np.convolve(coeff, [1.0, -z])
    s = float(sum(abs(np.delete(u, i)) ** 2))
    grid = np.linspace(0, 1, 2401)
    f = (1 - grid) * (1 + (2 * grid + s * grid**2) / (n - 1)) ** ((n - 1) / 2)
    h = 1 - grid**n
    for k in range(2, n):
        h += abs(coeff[k]) * grid**k
    h += abs(coeff[n] + 1) * grid**n
    return float(np.max(np.minimum(f, h)))


def obstruction_probe() -> dict[int, float]:
    # Fixed epsilon fractions from an independent sweep.  This is deliberately
    # float evidence only; the note makes no interval-certified counterexample claim.
    fractions = {
        5: 0.5202258388860467,
        6: 0.141441143102754,
        7: 0.03845560036973857,
        8: 0.007549868614353118,
        9: 0.0011813153675177739,
        10: 0.0005087876785805565,
        11: 0.00009437958183192068,
        12: 0.000007540328105173989,
        13: 0.0000013987229710971092,
    }
    out = {}
    r = 0.999
    for n, frac in fractions.items():
        eps = (1 - r**n) * frac
        pc = np.zeros(n + 1)
        pc[0], pc[-2], pc[-1] = 1, eps, -(r**n)
        roots = np.roots(pc)
        assert max(abs(roots)) < 1 - 1e-8
        scores = []
        for c in np.roots(np.polyder(pc)):
            ids = np.argsort(abs(roots - c))[:2]
            mu = abs(np.polyval(pc, c))
            scores.append(mu * max(sharp_joint_row(roots, c, int(i)) for i in ids))
        out[n] = float(min(scores))
        assert out[n] > 1.005
    return out


def main() -> None:
    exact_reciprocal_replay()
    exact_head_and_young_replay()
    values = obstruction_probe()
    print("critical-spoke hybrid low-mode dichotomy: PASS")
    print("computed sharp-hybrid obstruction signals:")
    for n, value in values.items():
        print(f"  n={n}: {value:.9f}")
    print("boundary: float signals are not interval-certified counterexamples")


if __name__ == "__main__":
    main()
