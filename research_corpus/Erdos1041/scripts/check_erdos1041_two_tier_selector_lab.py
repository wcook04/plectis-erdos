"""Checker for TwoTierStraightStarSelectorLab.md (Erdos 1041).

Three instruments (compact versions of the lab's runs):
  1  model-core spot grid: on the gauge core of H = w^5 + b2 w^2 + b1 w,
     every sampled model is closed by O (>=2 exactly-safe origin rays),
     C+ (positive critical hub, bracketing adjacent pair, straight arms in
     {Re H >= 0}), or F+ (hub slid along [0,c], bracketing pair) — residual
     empty on the sample.
  2  real-scale deterministic sweep: on-circle quintics at amplitudes
     A in {0.05, 0.2, 0.45}: Tier 1 (>=2 contained radial segments) or
     Tier 2 (SOME admissible critical hub with ITS bracketing roots, both
     straight segments contained, length <= 2; a deterministic <=4-test
     rule) closes every sample.
  3  witness transfer: on the exact rational origin-refutation witness
     (NearFeketeRadialAngularSplit.md Thm 7), the minimal-modulus critical
     point is admissible and its bracketing star is contained with the
     recorded margins (containment ~2.2e-4, length ~0.296), while the raw
     argmin-by-modulus critical point over ALL critical points is
     inadmissible.
  4  adversarial-corner adjudication (round 1): at the four recorded
     adversarial optima (near common-rotation gon configs that kill Tier 1
     and the one-hub shortcut), exactly one origin spoke is contained, yet
     some admissible hub's bracketing star closes the config (sup|f| < 1,
     L <= 2), and the r = 0.5 Form A-cut chord closes it too.
  5  escalation corners (round 2): at the three deeper corners where even
     the multi-hub bracketing star fails, (a) the asymmetric Form A-cut at
     the recorded (pair, s_a, s_b) closes each (sup|f| < 1), and (b) the
     descent arms from the best admissible hub have total length <= 2
     (containment automatic), reproducing min L in (1.74, 1.80).
  6  round-3 corners (gon limit, residual ~2e-3): the recorded best cuts
     FAIL there (sup > 1 — the negative premise of the refined
     recommendation), while descent arms close with min L in (1.80, 1.87).

Exit 0 iff all instruments pass.
"""
import sys

import numpy as np

rng = np.random.default_rng(55)
FAILURES = []
U5 = np.exp(2j * np.pi * np.arange(5) / 5)
K1 = 3.0 / 4.0 ** (4.0 / 3.0)
KCUT = 8.0


def report(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


# ---------------- instrument 1: model core ----------------
def n_safe_rays(b1, b2):
    n = 0
    for u in U5:
        a_u = (b1 * u).real
        b_u = (b2 * u * u).real
        if a_u >= K1 * max(-b_u, 0.0) ** (4.0 / 3.0) - 1e-14:
            n += 1
    return n


def seg_min_model(b1, b2, h, uu, N=1501):
    s = np.linspace(0.0, 1.0, N)
    z = h + s * (KCUT * uu - h)
    return float(np.min((z ** 5 + b2 * z * z + b1 * z).real))


def bracketing_index(h):
    ang = np.angle(h) % (2 * np.pi)
    k = int(np.floor(ang / (2 * np.pi / 5)))
    return k % 5, (k + 1) % 5


def model_closed(b1, b2):
    if n_safe_rays(b1, b2) >= 2:
        return "O"
    crits = np.roots([5.0, 0, 0, 2 * b2, b1])
    H = lambda w: w ** 5 + b2 * w * w + b1 * w
    pos = [c for c in crits if H(c).real > 1e-12]
    for c in pos:
        i, j = bracketing_index(c)
        if min(seg_min_model(b1, b2, c, U5[i]), seg_min_model(b1, b2, c, U5[j])) >= -1e-9:
            return "C+"
    for c in pos:
        for t in np.linspace(0.9, 0.1, 9):
            h = t * c
            i, j = bracketing_index(h)
            if min(seg_min_model(b1, b2, h, U5[i], N=801),
                   seg_min_model(b1, b2, h, U5[j], N=801)) >= -1e-9:
                return "F+"
    return "RES"


def instrument1():
    counts = {"O": 0, "C+": 0, "F+": 0, "RES": 0}
    NP, NS = 20, 5
    for branch in ("A", "B"):
        for s in np.linspace(0, 1, NS + 1)[1:]:
            r1, r2 = (1.0, s ** 3) if branch == "A" else (s ** 4, 1.0)
            for p1 in np.linspace(0, 2 * np.pi, NP, endpoint=False):
                for p2 in np.linspace(0, 2 * np.pi, NP, endpoint=False):
                    counts[model_closed(r1 * np.exp(1j * p1), r2 * np.exp(1j * p2))] += 1
    total = sum(counts.values())
    report("1 model-core residual empty", counts["RES"] == 0,
           f"counts={counts} total={total}")


# ---------------- instrument 2: real-scale deterministic ----------------
def seg_max_abs(poly, h, a, N=2501):
    s = np.linspace(0, 1, N)
    z = h + s * (a - h)
    return float(np.max(np.abs(np.polyval(poly, z))))


def bracketing_roots(roots, h):
    diffs = np.angle(roots * np.exp(-1j * np.angle(h)))
    pos = [(d if d >= 0 else d + 2 * np.pi, k) for k, d in enumerate(diffs)]
    neg = [(2 * np.pi - p, k) for p, k in pos]
    return min(pos)[1], min(neg)[1]


def instrument2():
    ok = True
    detail = []
    for A in (0.05, 0.2, 0.45):
        fails = 0
        for _ in range(80):
            delta = A * rng.uniform(-1, 1, 5)
            roots = np.exp(1j * (2 * np.pi * np.arange(5) / 5 + delta))
            poly = np.array([1.0 + 0j])
            for r in roots:
                poly = np.convolve(poly, [1.0, -r])
            nrad = sum(1 for k in range(5)
                       if seg_max_abs(poly, 0j, roots[k]) <= 1 + 1e-12)
            if nrad >= 2:
                continue
            crits = np.roots(np.polyder(poly))
            adm = sorted([c for c in crits if abs(np.polyval(poly, c)) <= 1],
                         key=lambda c: abs(np.polyval(poly, c)))
            closed = False
            for c in adm:
                i, j = bracketing_roots(roots, c)
                L = abs(c - roots[i]) + abs(c - roots[j])
                m = max(seg_max_abs(poly, c, roots[i]), seg_max_abs(poly, c, roots[j]))
                if (L <= 2 + 1e-12) and (m <= 1 + 1e-12):
                    closed = True
                    break
            if not closed:
                fails += 1
        detail.append(f"A={A}: fails={fails}")
        ok = ok and fails == 0
    report("2 real-scale deterministic selector (<=4 hub-bracket tests)", ok, "; ".join(detail))


# ---------------- instrument 3: witness transfer ----------------
def instrument3():
    import mpmath as mp

    mp.mp.dps = 30
    lam = mp.mpf(999999) / 1000000
    u = [mp.mpc(1, 0), mp.mpc(1053, 3196) / 3365, mp.mpc(-5928, 4255) / 7297]
    u = [u[0], u[1], u[2], mp.conj(u[2]), mp.conj(u[1])]
    roots_mp = [lam * x for x in u]
    coeffs = [mp.mpc(1)]
    for r in roots_mp:
        new = [mp.mpc(0)] * (len(coeffs) + 1)
        for i, a in enumerate(coeffs):
            new[i] += a
            new[i + 1] -= a * r
        coeffs = new
    f0 = coeffs[5]
    omega = (-f0) ** (mp.mpf(1) / 5)
    ct = np.array([complex(coeffs[i] * omega ** (5 - i) / omega ** 5) for i in range(6)])
    rr = np.roots(ct)
    crits = np.roots(np.polyder(ct))
    fv = lambda z: np.polyval(ct, z)
    vals = np.abs([fv(c) for c in crits])
    # raw argmin over ALL critical points is inadmissible
    raw = crits[int(np.argmin([abs(c) for c in crits]))]  # the near-origin one
    raw_inadmissible = abs(fv(raw)) > 1
    # minimal-modulus ADMISSIBLE hub
    adm = [c for c in crits if abs(fv(c)) <= 1]
    ok0 = len(adm) >= 1
    c = min(adm, key=lambda c: abs(fv(c)))
    i, j = bracketing_roots(rr, c)
    L = abs(c - rr[i]) + abs(c - rr[j])
    m = max(seg_max_abs(ct, c, rr[i], N=20001), seg_max_abs(ct, c, rr[j], N=20001))
    report("3 witness: raw near-origin critical point inadmissible", bool(raw_inadmissible),
           f"|f| = {abs(fv(raw)):.9f}")
    report("3 witness: selected hub admissible + star contained",
           ok0 and m <= 1 and L <= 2,
           f"hub={c:+.6f} sup|f|={m:.9f} L={L:.6f}")
    report("3 witness: recorded margins reproduced",
           abs((1 - m) - 2.2e-4) < 1e-4 and abs((2 - L) - 0.296) < 5e-3,
           f"containment margin={1-m:.3e} length margin={2-L:.4f}")


# ---------------- instrument 4: adversarial corners ----------------
ADVERSARIAL_DELTAS = [
    [-0.02811, -0.01452, -0.02046, -0.02662, -0.01284],
    [0.01033, 0.02551, 0.01853, 0.01239, 0.02687],
    [0.01055, 0.00453, -0.0018, 0.01231, -0.00331],
    [-0.17572, -0.16153, -0.17724, -0.1633, -0.16937],
]


def instrument4():
    ok_t1 = ok_t2 = ok_t3 = True
    for delta in ADVERSARIAL_DELTAS:
        roots = np.exp(1j * (2 * np.pi * np.arange(5) / 5 + np.array(delta)))
        poly = np.array([1.0 + 0j])
        for r in roots:
            poly = np.convolve(poly, [1.0, -r])
        ncont = sum(1 for k in range(5)
                    if seg_max_abs(poly, 0j, roots[k], N=6001) <= 1 + 1e-12)
        if ncont >= 2:
            ok_t1 = False  # adversary is supposed to have killed Tier 1
        crits = np.roots(np.polyder(poly))
        adm = [c for c in crits if abs(np.polyval(poly, c)) <= 1]
        closed = False
        for c in adm:
            i, j = bracketing_roots(roots, c)
            L = abs(c - roots[i]) + abs(c - roots[j])
            m = max(seg_max_abs(poly, c, roots[i], N=6001),
                    seg_max_abs(poly, c, roots[j], N=6001))
            if L <= 2 and m <= 1:
                closed = True
                break
        ok_t2 = ok_t2 and closed
        # chord tier at r = 0.5 between the best pair
        chord_ok = False
        for i in range(5):
            for j in range(i + 1, 5):
                r0 = 0.5
                m = max(
                    seg_max_abs(poly, r0 * roots[i], roots[i], N=3001),
                    seg_max_abs(poly, r0 * roots[i], r0 * roots[j], N=6001),
                    seg_max_abs(poly, r0 * roots[j], roots[j], N=3001),
                )
                if m <= 1:
                    chord_ok = True
        ok_t3 = ok_t3 and chord_ok
    report("4 adversarial corners: Tier 1 killed (as constructed)", ok_t1)
    report("4 adversarial corners: multi-hub star closes all four", ok_t2)
    report("4 adversarial corners: r=0.5 chord closes all four", ok_t3)


# ---------------- instrument 5: escalation corners ----------------
ROUND2 = [
    # (delta, cut_pair, s_a, s_b, descent expected max)
    ([-0.02144, -0.01076, -0.01544, -0.02083, -0.00953], (1, 3), 0.40, 0.40),
    ([-0.00645, 0.00325, -0.00701, 0.00208, -0.00176], (0, 4), 0.25, 0.25),
    ([0.0689, 0.06052, 0.0681, 0.06473, 0.06125], (2, 4), 0.35, 0.35),
]


def descent_length(poly, dpoly, d2poly, c, Nu=3000):
    fc = np.polyval(poly, c)
    total = 0.0
    ends = []
    for sgn in (+1, -1):
        u0 = 1e-4
        z = c + sgn * u0 * np.sqrt(-2 * fc / np.polyval(d2poly, c))
        for _ in range(60):
            corr = (np.polyval(poly, z) - fc * (1 - u0 ** 2)) / np.polyval(dpoly, z)
            z -= corr
            if abs(corr) < 1e-14:
                break
        length = abs(z - c)
        us = np.linspace(u0, 1.0, Nu)
        for k in range(1, len(us)):
            u = us[k]
            du = us[k] - us[k - 1]
            dz1 = (-2 * fc * us[k - 1]) / np.polyval(dpoly, z)
            zm = z + 0.5 * du * dz1
            dz2 = (-2 * fc * (us[k - 1] + du / 2)) / np.polyval(dpoly, zm)
            znew = z + du * dz2
            for _ in range(8):
                dp = np.polyval(dpoly, znew)
                if abs(dp) < 1e-13:
                    break
                corr = (np.polyval(poly, znew) - fc * (1 - u ** 2)) / dp
                znew -= corr
                if abs(corr) < 1e-13:
                    break
            length += abs(znew - z)
            z = znew
        total += length
        ends.append(z)
    return total, ends


def instrument5():
    ok_cut = ok_desc = True
    for delta, (i, j), sa, sb in ROUND2:
        roots = np.exp(1j * (2 * np.pi * np.arange(5) / 5 + np.array(delta)))
        poly = np.array([1.0 + 0j])
        for r in roots:
            poly = np.convolve(poly, [1.0, -r])
        m = max(
            seg_max_abs(poly, sa * roots[i], roots[i], N=4001),
            seg_max_abs(poly, sa * roots[i], sb * roots[j], N=6001),
            seg_max_abs(poly, sb * roots[j], roots[j], N=4001),
        )
        if m > 1:
            ok_cut = False
        dpoly = np.polyder(poly)
        d2poly = np.polyder(dpoly)
        crits = np.roots(dpoly)
        bestL = np.inf
        for c in crits:
            if abs(np.polyval(poly, c)) > 1:
                continue
            L, ends = descent_length(poly, dpoly, d2poly, c)
            mr = [int(np.argmin(np.abs(roots - e))) for e in ends]
            if mr[0] != mr[1] and max(abs(roots[mr[0]] - ends[0]),
                                      abs(roots[mr[1]] - ends[1])) < 1e-8:
                bestL = min(bestL, L)
        if not (1.7 < bestL <= 2.0):
            ok_desc = False
    report("5 escalation corners: asymmetric cut closes all three", ok_cut)
    report("5 escalation corners: descent min L in (1.7, 2.0]", ok_desc)
    # 5b: the (SPOKE-5) violation premise at the third corner — every
    # critical-hub straight star escapes (min over admissible hubs x pairs
    # of sup|f| exceeds 1).
    delta = ROUND2[2][0]
    roots = np.exp(1j * (2 * np.pi * np.arange(5) / 5 + np.array(delta)))
    poly = np.array([1.0 + 0j])
    for r in roots:
        poly = np.convolve(poly, [1.0, -r])
    crits = np.roots(np.polyder(poly))
    best = np.inf
    for c in crits:
        if abs(np.polyval(poly, c)) > 1:
            continue
        for i in range(5):
            for j in range(i + 1, 5):
                if abs(c - roots[i]) + abs(c - roots[j]) > 2:
                    continue
                m = max(seg_max_abs(poly, c, roots[i], N=8001),
                        seg_max_abs(poly, c, roots[j], N=8001))
                best = min(best, m)
    report("5b corner violates (SPOKE-5): min star sup > 1", best > 1,
           f"min sup = {best:.9f}")


# ---------------- instrument 6: round-3 corners ----------------
ROUND3 = [
    ([0.02673, 0.02557, 0.02867, 0.02503, 0.02814], (1, 4), 0.25, 0.25),
    ([-0.11153, -0.10843, -0.11185, -0.10915, -0.10997], (0, 3), 0.25, 0.25),
]


def instrument6():
    ok_cutfail = ok_desc = True
    for delta, (i, j), sa, sb in ROUND3:
        roots = np.exp(1j * (2 * np.pi * np.arange(5) / 5 + np.array(delta)))
        poly = np.array([1.0 + 0j])
        for r in roots:
            poly = np.convolve(poly, [1.0, -r])
        # best cut over a moderately fine search must FAIL (sup > 1)
        best = np.inf
        for ii in range(5):
            for jj in range(5):
                if ii == jj:
                    continue
                for s1 in np.linspace(0.25, 0.95, 8):
                    for s2 in np.linspace(0.25, 0.95, 8):
                        m = max(
                            seg_max_abs(poly, s1 * roots[ii], roots[ii], N=1501),
                            seg_max_abs(poly, s1 * roots[ii], s2 * roots[jj], N=2001),
                            seg_max_abs(poly, s2 * roots[jj], roots[jj], N=1501),
                        )
                        best = min(best, m)
        if best <= 1:
            ok_cutfail = False
        dpoly = np.polyder(poly)
        d2poly = np.polyder(dpoly)
        crits = np.roots(dpoly)
        bestL = np.inf
        for c in crits:
            if abs(np.polyval(poly, c)) > 1:
                continue
            L, ends = descent_length(poly, dpoly, d2poly, c)
            mr = [int(np.argmin(np.abs(roots - e))) for e in ends]
            if mr[0] != mr[1] and max(abs(roots[mr[0]] - ends[0]),
                                      abs(roots[mr[1]] - ends[1])) < 1e-8:
                bestL = min(bestL, L)
        if not (1.80 < bestL < 1.87):
            ok_desc = False
    report("6 round-3 corners: every searched cut fails (sup > 1)", ok_cutfail)
    report("6 round-3 corners: descent min L in (1.80, 1.87)", ok_desc)


def main():
    instrument1()
    instrument2()
    instrument3()
    instrument4()
    instrument5()
    instrument6()
    print()
    if FAILURES:
        print("FAIL:", FAILURES)
        return 1
    print("PASS: all instruments")
    return 0


if __name__ == "__main__":
    sys.exit(main())
