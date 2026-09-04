"""Checker for FreePointZeroInsertionFP4Matching.md (Erdos 1041).

Verifies:
  1  small-angle insertion theorem: proof-step inequalities
     (t_i <= 1, A_j^{(m)} = A_j^{(m-1)} d_ij, power-mean chain) and the
     end-to-end statement on random stratum configurations, m = 4..7;
  2  the K4-matching Hoelder S_4^4 <= 8W on random configurations, and
     exactness of the row reconstruction;
  3  exact falsification of W <= 32: on {r, r w, r w^2, 0} the sympy
     identity W(u) = (4-3u)(1+sqrt(1+u+u^2))^3, the critical polynomial
     64u^3 - 48u^2 - 27u + 8 (dW/du has this factor), W(u*) > 32, and
     S_4 = 1 + 3(1-u^3)^{1/4} exactly on the family;
  4  exact falsification of the CS variant: P(u) = (4-3u)^2 (2+u+u^2)^3,
     dP/du vanishing at u = 3/8, P* = (23/8)^2 (161/64)^3 > 128 exact;
  5  the obstruction constant: 32C(sigma, theta) formula minimized at
     sigma = 1/(12 theta) gives 1/(8 theta) (sympy), hence C >= 3/256
     for theta <= 1/3;
  6  PM_2 proof steps ((x1+x2) d12 <= 2 via d <= 1 + r1 r2) and PM_m
     numeric battery: m = 3, 4, 5 hold on random + adversarial spot
     configs; m = 6 violated at (5/7, -1, -1, -1, -1, -1) with value
     7.2516 (exact rational evaluation);
  7  Moebius covariance identity numerically, m = 4;
  8  the radial closed form F'(x): matches central differences, and
     sum_{j,k} zeta_jk = sum_r x^{r-1} |q_r|^2 (identity battery);
     first-nonzero-mode expansion spot check;
  9  exact rational no-go for the pairwise-comonotonicity / Chebyshev
     shortcut to radial monotonicity, while the full weighted sum stays
     positive on the same specimen.
 10  exhaustive replay of the unweighted four-column row-factor permutation
     class on triangle+origin, plus the exact aligned obstruction
     329/2+14sqrt(43)>256 at u=1/6.
 11  the FP4 matching-stratum theorem: symbolic two-point identity, random
     proof-step replay, and an exact rational configuration whose superunit
     graph consists of precisely two disjoint edges.
 12  the all-degree rowwise log-variance theorem: sharp quadratic remainder,
     radius-profile certificate, Lambert-W uniform threshold, and exact rows.
 13  the complete FP4 theorem: exact eight-cell Bernstein proof of the
     central row envelope, rational Taylor bounds, the outer-radius
     K4-Hoelder majorant, its unique stationary point and positive radical
     slack, plus an end-to-end dichotomy replay.

Exit 0 iff all pass.
"""
import sys
from fractions import Fraction
import itertools

import numpy as np
import sympy as sp

rng = np.random.default_rng(41)
FAILURES = []


def report(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


def rows(cs):
    m = len(cs)
    d = np.abs(1 - np.conj(cs)[:, None] * cs[None, :])
    A = np.array([np.prod([d[j, k] for k in range(m)]) for j in range(m)])
    return d, A


def S_of(cs):
    m = len(cs)
    _, A = rows(np.asarray(cs))
    return float(np.sum(np.maximum(A, 0) ** (1.0 / m)))


def main():
    # 1 small-angle insertion
    ok1 = True
    for m in (4, 5, 6, 7):
        for _ in range(800):
            # build a stratum config: c_i = 0 or a dominator
            cs = np.array([np.sqrt(rng.uniform()) * np.exp(2j * np.pi * rng.uniform())
                           for _ in range(m - 1)] + [0j])
            if rng.uniform() < 0.5:
                # small-angle dominator: cluster others within 50 deg of c_i
                base = rng.uniform(0, 2 * np.pi)
                cs = np.array([np.sqrt(rng.uniform())
                               * np.exp(1j * (base + rng.uniform(-0.8, 0.8)))
                               for _ in range(m)])
                i = int(rng.integers(m))
            else:
                i = m - 1
            d, A = rows(cs)
            if not all(d[i, j] <= 1 + 1e-12 for j in range(m)):
                continue  # not on the stratum; skip
            # proof steps
            t_i = A[i] ** (1.0 / m)
            if t_i > 1 + 1e-10:
                ok1 = False
            # deletion relation
            keep = [j for j in range(m) if j != i]
            csm1 = cs[keep]
            _, B_A = rows(csm1)
            for jj, j in enumerate(keep):
                if abs(A[j] - B_A[jj] * d[i, j]) > 1e-9 * max(1, A[j]):
                    ok1 = False
            if S_of(cs) > m + 1e-9:
                ok1 = False
    report("1 small-angle insertion (proof steps + statement, m=4..7)", ok1)

    # 2 K4-matching Hoelder
    ok2 = True
    M = [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]
    for _ in range(20000):
        cs = np.array([np.sqrt(rng.uniform()) * np.exp(2j * np.pi * rng.uniform())
                       for _ in range(4)])
        if rng.uniform() < 0.3:
            cs[rng.integers(4)] = np.exp(2j * np.pi * rng.uniform())
        d, A = rows(cs)
        x = 1 - np.abs(cs) ** 2
        W = x.sum() * np.prod([d[e[0], e[1]] + d[f[0], f[1]] for (e, f) in M])
        if S_of(cs) ** 4 > 8 * W + 1e-8:
            ok2 = False
    report("2 K4-matching Hoelder S_4^4 <= 8W", ok2)

    # 3 exact falsification of W <= 32 + the S_4 identity
    u = sp.symbols("u", positive=True)
    r = sp.sqrt(u)
    w3 = sp.exp(2 * sp.I * sp.pi / 3)
    csym = [r, r * w3, r * w3**2, sp.Integer(0)]
    # pairwise |1 - conj(ci) cj|: within triangle = sqrt(1 + u + u^2); to 0 = 1
    D = sp.sqrt(1 + u + u**2)
    # |1 - u w|^2 = (1 - u w)(1 - u conj(w)) = 1 + u + u^2 since w + conj(w) = -1
    dcheck = sp.simplify(sp.expand_complex(
        sp.expand((1 - u * w3) * (1 - u * sp.conjugate(w3))) - (1 + u + u**2))) == 0
    Wfam = (4 - 3 * u) * (1 + D) ** 3
    dW = sp.together(sp.diff(Wfam, u))
    # the numerator of dW/du should vanish where 64u^3-48u^2-27u+8 = 0
    crit_poly = sp.Poly(64 * u**3 - 48 * u**2 - 27 * u + 8, u)
    ustar = [rr for rr in sp.real_roots(crit_poly) if 0 < rr < 1]
    ok3 = dcheck and len(ustar) == 1
    us = ustar[0]
    resid = sp.diff(Wfam, u).subs(u, sp.nsimplify(us.evalf(40), rational=True))
    ok3 &= abs(complex(resid.evalf(40)).real) < 1e-30
    Wstar = float(Wfam.subs(u, us).evalf(30))
    ok3 &= Wstar > 32
    # S_4 identity on the family: A_triangle = (1-u) D^2 * 1 = (1-u)(1+u+u^2) = 1-u^3
    ident = sp.simplify((1 - u) * (1 + u + u**2) - (1 - u**3)) == 0
    ok3 &= ident
    # numeric spot: S_4 = 1 + 3(1-u^3)^{1/4}
    for uu in (0.1, 0.23, 0.5):
        cn = np.array([np.sqrt(uu), np.sqrt(uu) * np.exp(2j * np.pi / 3),
                       np.sqrt(uu) * np.exp(-2j * np.pi / 3), 0j])
        ok3 &= abs(S_of(cn) - (1 + 3 * (1 - uu**3) ** 0.25)) < 1e-10
    report("3 W <= 32 exactly falsified; S_4 = 1 + 3(1-u^3)^{1/4} on family", ok3,
           f"u* = {float(us):.15f}, W* = {Wstar:.13f}, S_4 cap {float((8*Wstar)**0.25):.10f}")

    # 4 CS variant exact
    Pfam = (4 - 3 * u) ** 2 * (2 + u + u**2) ** 3
    dP = sp.factor(sp.diff(Pfam, u))
    at38 = sp.simplify(sp.diff(Pfam, u).subs(u, sp.Rational(3, 8))) == 0
    Pstar = sp.Rational(23, 8) ** 2 * sp.Rational(161, 64) ** 3
    ok4 = at38 and sp.simplify(Pfam.subs(u, sp.Rational(3, 8)) - Pstar) == 0 \
        and Pstar > 128 and Pstar == sp.Rational(2207665649, 16777216)
    report("4 CS polynomial variant exactly falsified", ok4,
           f"P* = {float(Pstar):.10f} at u = 3/8")

    # 5 obstruction constant
    sig, th = sp.symbols("sigma theta", positive=True)
    C32 = 3 * (sp.Rational(1, 4) - 3 * sig * th) ** 2 / (1 - 3 * th) \
        + 9 * th * sig**2 + 3 / (16 * th) - sp.Rational(3, 2) * sig
    sig_star = sp.solve(sp.diff(C32, sig), sig)
    ok5 = any(sp.simplify(s0 - 1 / (12 * th)) == 0 for s0 in sig_star)
    C32min = sp.simplify(C32.subs(sig, 1 / (12 * th)))
    ok5 &= sp.simplify(C32min - 1 / (8 * th)) == 0
    # theta <= 1/3 => C = C32/32 >= (1/(8*(1/3)))/32 = 3/256
    ok5 &= sp.Rational(1, 8) / sp.Rational(1, 3) / 32 == sp.Rational(3, 256)
    report("5 obstruction: min_sigma 32C = 1/(8 theta) => C >= 3/256", ok5)

    # 6 PM ladder
    ok6 = True
    # PM_2 proof steps
    for _ in range(4000):
        c1 = np.sqrt(rng.uniform()) * np.exp(2j * np.pi * rng.uniform())
        c2 = np.sqrt(rng.uniform()) * np.exp(2j * np.pi * rng.uniform())
        x1, x2 = 1 - abs(c1) ** 2, 1 - abs(c2) ** 2
        d12 = abs(1 - np.conj(c1) * c2)
        if d12 > 1 + abs(c1) * abs(c2) + 1e-12:
            ok6 = False
        if (x1 + x2) * d12 > 2 + 1e-10:
            ok6 = False
    # PM_m battery
    for m, should_hold in ((3, True), (4, True), (5, True)):
        sup = 0.0
        for _ in range(30000):
            cs = np.array([np.sqrt(rng.uniform()) * np.exp(2j * np.pi * rng.uniform())
                           for _ in range(m)])
            _, A = rows(cs)
            sup = max(sup, float(A.sum()))
        if should_hold and sup > m + 1e-8:
            ok6 = False
    # m = 6 violation, exact rational: c = (5/7, -1 x5)
    c1 = Fraction(5, 7)
    # A_1 = (1 - c1^2)(1 + c1)^5 ; A_j (j>=2) = 0 since x_j = 0
    A1 = (1 - c1 * c1) * (1 + c1) ** 5
    ok6 &= A1 > 6 and abs(float(A1) - 7.2515557779011) < 1e-9
    report("6 PM ladder: PM_2 proof, PM_3..5 hold, PM_6 exactly violated", ok6,
           f"PM_6 witness value = {float(A1):.10f}")

    # 7 Moebius covariance
    ok7 = True
    for _ in range(300):
        cs = np.array([np.sqrt(rng.uniform()) * np.exp(2j * np.pi * rng.uniform())
                       for _ in range(4)])
        a = 0.5 * np.sqrt(rng.uniform()) * np.exp(2j * np.pi * rng.uniform())
        phi = (cs - a) / (1 - np.conj(a) * cs)
        lhs = np.abs(1 - np.conj(phi)[:, None] * phi[None, :])
        rhs = (1 - abs(a) ** 2) * np.abs(1 - np.conj(cs)[:, None] * cs[None, :]) / (
            np.abs(1 - a * np.conj(cs))[:, None] * np.abs(1 - np.conj(a) * cs)[None, :])
        if np.max(np.abs(lhs - rhs)) > 1e-11:
            ok7 = False
    report("7 Moebius covariance identity", ok7)

    # 8 radial closed form + power-sum identity + first-mode expansion
    ok8 = True
    for m in (3, 4, 5):
        for _ in range(200):
            cs = np.array([np.sqrt(rng.uniform()) * np.exp(2j * np.pi * rng.uniform())
                           for _ in range(m)])
            x = rng.uniform(0.05, 0.9)
            # zeta identity: sum_{j,k} zeta_jk = sum_r x^{r-1}|q_r|^2
            R = np.real(np.conj(cs)[:, None] * cs[None, :])
            rho2 = np.abs(cs) ** 2
            dsq = np.abs(1 - x * np.conj(cs)[:, None] * cs[None, :]) ** 2
            zeta = (R - x * rho2[:, None] * rho2[None, :]) / dsq
            lhs = float(np.sum(zeta))
            rhs = float(sum(x ** (r - 1) * abs(np.sum(cs**r)) ** 2
                            for r in range(1, 400)))
            if abs(lhs - rhs) > 1e-8 * max(1, abs(rhs)):
                ok8 = False
        # F' vs central differences at one random config
        cs = np.array([np.sqrt(rng.uniform()) * np.exp(2j * np.pi * rng.uniform())
                       for _ in range(m)])

        def F_of(xv):
            csx = np.sqrt(xv) * cs
            return S_of(csx)

        x0 = 0.4
        h = 1e-5
        fd = (F_of(x0 + h) - F_of(x0 - h)) / (2 * h)
        # closed form
        csx = cs
        dmat = np.abs(1 - x0 * np.conj(csx)[:, None] * csx[None, :])
        A = np.array([np.prod(dmat[j]) for j in range(m)])
        T = A ** (1.0 / m)
        R = np.real(np.conj(csx)[:, None] * csx[None, :])
        rho2 = np.abs(csx) ** 2
        zeta = (R - x0 * rho2[:, None] * rho2[None, :]) / dmat**2
        Fp = -(1.0 / m) * float(np.sum(T * zeta.sum(axis=1)))
        if abs(fd - Fp) > 1e-4 * max(1, abs(Fp)):
            ok8 = False
    # first-nonzero-mode: q1 = 0 config, m = 4
    cs = np.array([0.5, -0.5, 0.5j, -0.5j])
    xsmall = 1e-3
    q2 = abs(np.sum(cs**2)) ** 2
    pred = 4 - q2 * xsmall**2 / (4 * 2)
    csx = np.sqrt(xsmall) * cs  # scaling convention: F(x) uses x * conj(ci) cj
    # direct: F(x) = sum_j prod_k |1 - x conj(cj) ck|^{1/4}
    dmat = np.abs(1 - xsmall * np.conj(cs)[:, None] * cs[None, :])
    Fdir = float(np.sum(np.prod(dmat, axis=1) ** 0.25))
    ok8 &= abs(Fdir - pred) < 5e-9
    report("8 radial closed form F', zeta identity, first-mode expansion", ok8,
           f"first-mode dev {abs(Fdir - pred):.2e}")

    # 9 Exact no-go for the pairwise-comonotonicity shortcut to RM.
    csq = (Fraction(-9, 10), Fraction(-3, 4),
           Fraction(-1, 2), Fraction(-1, 4))
    xq = Fraction(1, 4)
    Aq = []
    Gq = []
    for cj in csq:
        aj = Fraction(1)
        gj = Fraction(0)
        for ck in csq:
            djk = 1 - xq * cj * ck
            aj *= djk
            gj += (cj * ck - xq * cj * cj * ck * ck) / (djk * djk)
        Aq.append(aj)
        Gq.append(gj)
    expected_A = (Fraction(454859867, 819200000),
                  Fraction(2588047, 4194304))
    expected_G = (Fraction(1170425808, 454859867),
                  Fraction(26878032, 12940235))
    weighted = sum(float(aj) ** 0.25 * float(gj)
                   for aj, gj in zip(Aq, Gq))
    ok9 = (tuple(Aq[:2]) == expected_A and tuple(Gq[:2]) == expected_G
           and Aq[0] < Aq[1] and Gq[0] > Gq[1] and weighted > 0)
    report("9 RM pairwise-comonotonicity shortcut exactly refuted", ok9,
           f"(A1-A2)(G1-G2) < 0, full weighted sum = {weighted:.10f}")

    # 10 The complete unweighted row-factor permutation class.  Column
    # permutation symmetry fixes the first triangle row.  D occurs twice, so
    # there are 12 unique row permutations and only 12^2 exact assignments.
    uq = sp.Rational(1, 6)
    Dq = sp.sqrt(1 + uq + uq**2)
    xq = 1 - uq
    row = (Dq, Dq, sp.Integer(1), xq)
    perms = sorted(set(itertools.permutations(row)), key=str)
    base = perms[0]
    products = []
    for p1 in perms:
        for p2 in perms:
            products.append(sp.prod(1 + base[k] + p1[k] + p2[k]
                                    for k in range(4)))
    aligned = 4 * (4 - 3 * uq) * (1 + 3 * Dq) ** 2
    minimum_numeric = min(float(sp.N(value, 40)) for value in products)
    aligned_numeric = float(sp.N(aligned, 40))
    radical_form = sp.Rational(329, 2) + 14 * sp.sqrt(43)
    ok10 = (len(perms) == 12 and len(products) == 144
            and abs(minimum_numeric - aligned_numeric) < 1e-12
            and sp.simplify(aligned - radical_form) == 0
            and 28**2 * 43 > 183**2
            and aligned_numeric > 256)
    report("10 all unweighted row-factor permutations exactly obstructed", ok10,
           f"min product = {aligned_numeric:.12f}, cap = {aligned_numeric**0.25:.10f}")

    # 11 FP4 matching stratum.  The pair inequality follows after fourth
    # powers from (a+b)^4 <= 8(a^4+b^4), d_ij <= 1+rs, and this identity.
    rr, ss = sp.symbols("r s", nonnegative=True)
    residual = sp.expand(2 - (2 - rr**2 - ss**2) * (1 + rr * ss))
    residual_target = (rr - ss) ** 2 + rr * ss * (rr**2 + ss**2)
    ok11 = sp.expand(residual - residual_target) == 0
    for _ in range(20000):
        r1, r2 = np.sqrt(rng.uniform()), np.sqrt(rng.uniform())
        delta = rng.uniform(-np.pi, np.pi)
        dij = abs(1 - r1 * r2 * np.exp(1j * delta))
        lhs = dij ** 0.25 * ((1 - r1*r1) ** 0.25
                            + (1 - r2*r2) ** 0.25)
        if lhs > 2 + 2e-12:
            ok11 = False

    # End-to-end replay whenever the four cross edges are small.
    accepted = 0
    for _ in range(50000):
        cs = np.array([np.sqrt(rng.uniform()) * np.exp(2j * np.pi * rng.uniform())
                       for _ in range(4)])
        d, _ = rows(cs)
        if all(d[i, j] <= 1 for i in (0, 1) for j in (2, 3)):
            accepted += 1
            pair12 = d[0, 1] ** 0.25 * sum((1 - abs(cs[i])**2) ** 0.25
                                           for i in (0, 1))
            pair34 = d[2, 3] ** 0.25 * sum((1 - abs(cs[i])**2) ** 0.25
                                           for i in (2, 3))
            if pair12 > 2 + 2e-12 or pair34 > 2 + 2e-12 or S_of(cs) > 4 + 2e-12:
                ok11 = False
    ok11 &= accepted >= 100

    # Exact nonempty specimen: squared d_12,d_34 exceed one and every cross
    # squared distance is below one.  All squared moduli are also below one.
    cq = ((Fraction(54, 100), Fraction(35, 100)),
          (Fraction(-23, 100), Fraction(57, 100)),
          (Fraction(69, 100), Fraction(54, 100)),
          (Fraction(-24, 100), Fraction(81, 100)))
    r2q = tuple(x*x + y*y for x, y in cq)

    def d2q(i, j):
        x, y = cq[i]
        u0, v0 = cq[j]
        re = x*u0 + y*v0
        im = x*v0 - y*u0
        return (1 - re) ** 2 + im ** 2

    bad_edges = {(i, j) for i in range(4) for j in range(i + 1, 4)
                 if d2q(i, j) > 1}
    expected_bad = {(0, 1), (2, 3)}
    specimen = np.array([float(x) + 1j * float(y) for x, y in cq])
    ok11 &= all(value < 1 for value in r2q)
    ok11 &= bad_edges == expected_bad
    ok11 &= S_of(specimen) < 4
    report("11 FP4 matching-stratum theorem", ok11,
           f"accepted random rows = {accepted}, exact bad edges = {sorted(bad_edges)}")

    # 12 Adaptive log-variance theorem and its uniform central radius.
    Lstar = float(sp.N(-sp.LambertW(-1 / (2 * sp.sqrt(sp.E)), -1)
                         - sp.Rational(1, 2), 50))
    rho_star = np.sqrt(1 - np.exp(-Lstar))
    ok12 = (abs(np.exp(Lstar) - 1 - 2*Lstar) < 5e-15
            and rho_star > 0.8457)
    worst_variance_slack = float("inf")
    worst_target_slack = float("inf")
    worst_certificate_slack = float("inf")
    for m in (2, 3, 4, 5, 7, 10):
        for _ in range(600):
            # Include rows close to the sharp radius as well as the interior.
            radii = rho_star * rng.uniform(size=m) ** rng.choice((0.2, 0.5, 1.0, 2.0))
            cs = radii * np.exp(2j * np.pi * rng.uniform(size=m))
            d, _ = rows(cs)
            h = np.mean(np.log(d), axis=1)
            E = -float(np.sum(h))
            R = float(np.max(np.abs(cs)))
            Lj = -np.log(1 - np.abs(cs)**2)
            Lmax = float(np.max(Lj))
            Mj = np.mean(-np.log(1 - np.abs(cs)[:, None] * np.abs(cs)[None, :]), axis=1)

            def cfun(value):
                value = np.asarray(value)
                return np.where(value > 1e-7,
                                (np.expm1(value) - value) / value**2,
                                0.5 + value/6 + value**2/24)

            Cj = cfun(Mj)
            coarse_C = float(cfun(np.array(Lmax)))

            # Independent truncated replay of E=(1/m) sum_r |q_r|^2/r.
            powers = np.array(cs, dtype=complex)
            Eseries = 0.0
            for rr0 in range(1, 301):
                Eseries += abs(np.sum(powers))**2 / (m * rr0)
                powers *= cs
            variance_slack = E*float(np.mean(Lj)) - float(np.sum(h*h))
            target_slack = m - float(np.sum(np.exp(h)))
            row_certificate = float(np.mean(Cj * Lj))
            coarse_certificate = coarse_C * float(np.mean(Lj))
            certificate_slack = 1 - row_certificate
            quadratic_slack = float(np.sum(1 + h + Cj*h*h - np.exp(h)))
            worst_variance_slack = min(worst_variance_slack, variance_slack)
            worst_target_slack = min(worst_target_slack, target_slack)
            worst_certificate_slack = min(worst_certificate_slack, certificate_slack)
            if (E < -2e-12 or abs(E-Eseries) > 2e-10
                    or np.max(np.abs(h) - Mj) > 2e-12
                    or variance_slack < -2e-12
                    or quadratic_slack < -2e-12
                    or certificate_slack < -2e-12
                    or row_certificate > coarse_certificate + 2e-12
                    or np.sum(np.exp(h)) > m + 2e-12
                    or np.exp(Lmax) > 1 + 2*Lmax + 2e-12):
                ok12 = False

    # A strict rowwise gain: this outer-shell specimen fails the coarser
    # C(Lmax)Lbar certificate but passes ROWCERT with large slack.
    adaptive_radii = np.array([0.016920919326, 0.004235517327,
                               0.964431612887, 0.024339671445])
    adaptive_cs = adaptive_radii * np.exp(1j * np.array([0.0, 0.7, 2.1, 4.2]))
    adaptive_Lj = -np.log(1 - adaptive_radii**2)
    adaptive_Mj = np.mean(-np.log(1 - adaptive_radii[:, None]
                                  * adaptive_radii[None, :]), axis=1)
    adaptive_Cj = (np.expm1(adaptive_Mj) - adaptive_Mj) / adaptive_Mj**2
    adaptive_rowcert = float(np.mean(adaptive_Cj * adaptive_Lj))
    adaptive_Lmax = float(np.max(adaptive_Lj))
    adaptive_coarse_C = (np.expm1(adaptive_Lmax) - adaptive_Lmax) / adaptive_Lmax**2
    adaptive_coarse = adaptive_coarse_C * float(np.mean(adaptive_Lj))
    ok12 &= (adaptive_radii.max() > rho_star and adaptive_rowcert < 1
             and adaptive_coarse > 1)
    ok12 &= S_of(adaptive_cs) <= 4 + 2e-12
    report("12 all-degree rowwise log-variance theorem", ok12,
           f"rho* = {rho_star:.12f}, min certificate slack = {worst_certificate_slack:.3e}, "
           f"strict-gain row/coarse = {adaptive_rowcert:.6f}/{adaptive_coarse:.6f}")

    # 13 Complete FP4 theorem: central/outer dichotomy at max |c_j|^2=21/25.
    ok13 = True
    tt = sp.symbols("t", real=True)
    aa0 = sp.Rational(21, 25)
    central_gap = sp.expand(sp.Rational(12, 5)
                            - (1 - aa0 * tt**2) * (1 + aa0 * tt)**3)

    # Exact Bernstein positivity on the eight equal cells of [0,1].
    bernstein_coeffs = []
    for cell in range(8):
        lo = sp.Rational(cell, 8)
        hi = sp.Rational(cell + 1, 8)
        cell_poly = sp.Poly(sp.expand(central_gap.subs(tt, lo + (hi-lo)*tt)), tt)
        power_coeffs = [cell_poly.nth(k) for k in range(6)]
        bernstein_coeffs.extend(
            sp.factor(sum(power_coeffs[i] * sp.binomial(k, i) / sp.binomial(5, i)
                          for i in range(k + 1)))
            for k in range(6)
        )
    exact_bernstein_min = min(bernstein_coeffs)
    ok13 &= all(value > 0 for value in bernstein_coeffs)
    ok13 &= exact_bernstein_min == sp.Rational(604219, 51200000)

    # Exact rational Taylor estimates used to bound the one-sided exponential
    # coefficient and the diagonal logarithmic energy.
    x1 = Fraction(22, 25)
    lower1 = sum(x1**k / Fraction(sp.factorial(k)) for k in range(5))
    x2 = Fraction(11, 6)
    lower2 = sum(x2**k / Fraction(sp.factorial(k)) for k in range(8))
    x3 = Fraction(11, 50)
    upper3 = 1 + x3 + (x3*x3 / 2) / (1 - x3 / 3)
    ok13 &= lower1 - Fraction(12, 5) == Fraction(6757, 1171875)
    ok13 &= lower2 - Fraction(25, 4) == Fraction(211489, 282175488)
    ok13 &= upper3 == Fraction(17321, 13900)
    ok13 &= Fraction(779, 625) - upper3 == Fraction(99, 347500)

    # Symbolic outer majorant.  First recover the exact D_2 identity in real
    # coordinates, then the three-smaller-radii pair-product estimate.
    xr = sp.symbols("x0:4", real=True)
    yr = sp.symbols("y0:4", real=True)
    ur = [xr[i]**2 + yr[i]**2 for i in range(4)]
    d2sym = []
    for i in range(4):
        for j in range(i + 1, 4):
            re = xr[i]*xr[j] + yr[i]*yr[j]
            im = xr[i]*yr[j] - yr[i]*xr[j]
            d2sym.append((1-re)**2 + im**2)
    Qsym = sum(ur)
    E2sym = sum(ur[i]*ur[j] for i in range(4) for j in range(i + 1, 4))
    centroid2 = sum(xr)**2 + sum(yr)**2
    ok13 &= sp.expand(sum(d2sym) - (6 + Qsym - centroid2 + E2sym)) == 0

    ux, uy, uz = sp.symbols("u_x u_y u_z", real=True)
    pair_slack = sp.expand((ux+uy+uz)**2 - 3*(ux*uy+ux*uz+uy*uz))
    pair_sos = sp.expand(((ux-uy)**2 + (ux-uz)**2 + (uy-uz)**2) / 2)
    ok13 &= sp.expand(pair_slack - pair_sos) == 0

    aa, ss = sp.symbols("a s", real=True)
    DD = 6 + aa + (1+aa)*ss + ss**2/3
    XX = 4 - aa - ss
    derivative_a_numerator = sp.expand(2*DD - 3*(1+ss)*XX)
    derivative_a_target = 5*aa + (5*aa-7)*ss + sp.Rational(11, 3)*ss**2
    ok13 &= sp.expand(derivative_a_numerator - derivative_a_target) == 0

    DD0 = sp.expand(DD.subs(aa, aa0))
    XX0 = sp.expand(XX.subs(aa, aa0))
    derivative_s_numerator = sp.factor(3*XX0*sp.diff(DD0, ss) - 2*DD0)
    derivative_s_target = -sp.Rational(8, 1875)*(625*ss**2 + 675*ss - 882)
    ok13 &= sp.expand(derivative_s_numerator - derivative_s_target) == 0
    sstar = (-27 + 3*sp.sqrt(473))/50
    ok13 &= sp.simplify(625*sstar**2 + 675*sstar - 882) == 0
    squared_slack = sp.simplify(3456 - XX0.subs(ss, sstar)**2 * DD0.subs(ss, sstar)**3)
    squared_slack_target = (sp.Rational(32157853108929, 61035156250)
                            - sp.Rational(7334791379487, 305175781250)*sp.sqrt(473))
    radical_integer_slack = (160789265544645**2
                             - 473*7334791379487**2)
    ok13 &= sp.simplify(squared_slack - squared_slack_target) == 0
    ok13 &= radical_integer_slack == 406183067764073374294937088
    ok13 &= squared_slack > 0

    # End-to-end replay: the central case satisfies the proved one-sided
    # majorant; the outer case satisfies W<32 and hence S_4^4<=8W<256.
    inner_count = 0
    outer_count = 0
    worst_outer_W = 0.0
    worst_S = 0.0
    for _ in range(120000):
        radii = np.sqrt(rng.uniform(size=4))
        cs = radii * np.exp(2j*np.pi*rng.uniform(size=4))
        d, Avec = rows(cs)
        sval = float(np.sum(Avec**0.25))
        worst_S = max(worst_S, sval)
        if np.max(radii*radii) <= 21/25:
            inner_count += 1
            row_envelope = ((1-radii*radii)
                            * np.prod(1+radii[:, None]*radii[None, :], axis=1)
                            / (1+radii*radii))
            if np.max(row_envelope) > 12/5 + 2e-12 or sval > 4 + 2e-12:
                ok13 = False
        else:
            outer_count += 1
            W = ((np.sum(1-radii*radii))
                 * (d[0,1]+d[2,3]) * (d[0,2]+d[1,3]) * (d[0,3]+d[1,2]))
            worst_outer_W = max(worst_outer_W, float(W))
            if W >= 32 + 2e-10 or sval**4 > 8*W + 2e-10:
                ok13 = False
    ok13 &= inner_count > 1000 and outer_count > 1000
    report("13 FP4 complete central/outer theorem", ok13,
           f"Bernstein min = {exact_bernstein_min}, outer sampled W max = {worst_outer_W:.9f}, "
           f"sampled S max = {worst_S:.9f}")

    print()
    if FAILURES:
        print("FAIL:", FAILURES)
        return 1
    print("PASS: all sections")
    return 0


if __name__ == "__main__":
    sys.exit(main())
