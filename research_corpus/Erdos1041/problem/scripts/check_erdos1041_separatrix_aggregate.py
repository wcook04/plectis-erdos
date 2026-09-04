"""Checker for SeparatrixAggregateReduction.md.

The aggregate (AGG-MEC): Sigma_c L(c) <= 2(n-1) * R_MEC (sum over all
critical points of the two-arm inverse-ray lengths; R_MEC = minimum enclosing
circle radius of the roots).  Open; equality on the radial family.  This
checker replays the note's evidence:

  1. the two hardest stored witnesses hold the aggregate with the recorded
     margins (killer/ComponentDepthRefutation witness: ratio ~0.983;
     falsifier n=4 tie-locus witness: ratio ~0.959) -- the compensation
     phenomenon: argmin arms exceed 2 while runner-up hubs pay it back;
  2. a sub-mean-value (plurisubharmonicity) spot test on random holomorphic
     disks of configurations: circle-mean >= center for Sigma_c L(c);
  3. a random-configuration sweep: aggregate ratio < 1 off the degenerate
     stratum (guarded instrument; the radial equality family is asserted from
     the ordinary proof, never from the integrator).

Instrument: resolved-chart lift f(z(u)) = v(1-u^2) by DOP853 (rtol 1e-11,
cluster-aware max_step <= d_pt/20), endpoint landing on two distinct roots,
near-degenerate shell d_pt < 0.02 max|root| excluded.

Usage: check_erdos1041_separatrix_aggregate.py [--check]
Exit 0 iff all checks pass.
"""
import argparse
import itertools
import sys

import numpy as np
from scipy.integrate import solve_ivp

RNG = np.random.default_rng(2041)


def crit_data(roots):
    c = np.poly(roots)
    dc = np.polyder(c)
    cps = np.roots(dc)
    cvs = np.polyval(c, cps)
    idx = np.argsort(np.abs(cvs))
    return cps[idx], cvs[idx], c, dc


def lift_arm(c_poly, dc_poly, cstar, v, sign, all_cps, eps=1e-8):
    ddc = np.polyder(dc_poly)
    A = 0.5 * np.polyval(ddc, cstar)
    if A == 0:
        return None
    rd = np.sqrt(-v / A)
    others = [c for c in all_cps if abs(c - cstar) > 1e-13]
    d_pt = min((abs(c - cstar) for c in others), default=np.inf)
    ms = min(1e-3, d_pt / 20.0) if np.isfinite(d_pt) else 1e-3
    z0 = cstar + sign * eps * rd

    def rhs(u, y):
        z = y[0] + 1j * y[1]
        dp = np.polyval(dc_poly, z)
        if dp == 0:
            return [0.0, 0.0, 0.0]
        d = -2.0 * u * v / dp
        return [d.real, d.imag, abs(d)]

    try:
        sol = solve_ivp(rhs, (eps, 1.0), [z0.real, z0.imag, eps * abs(rd)],
                        method="DOP853", rtol=1e-11, atol=1e-13, max_step=ms)
    except Exception:
        return None
    if not sol.success:
        return None
    zf = sol.y[0, -1] + 1j * sol.y[1, -1]
    if abs(np.polyval(c_poly, zf)) > 1e-8 * max(1.0, abs(v)):
        return None
    return float(sol.y[2, -1]), zf


def mec_radius(pts):
    best = None
    n = len(pts)
    for i, j in itertools.combinations(range(n), 2):
        c = (pts[i] + pts[j]) / 2
        r = abs(pts[i] - pts[j]) / 2
        if all(abs(p - c) <= r * (1 + 1e-12) for p in pts):
            best = r if best is None else min(best, r)
    for i, j, k in itertools.combinations(range(n), 3):
        ax, ay, bx, by, cx, cy = (pts[i].real, pts[i].imag, pts[j].real,
                                  pts[j].imag, pts[k].real, pts[k].imag)
        d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
        if d == 0:
            continue
        ux = ((ax ** 2 + ay ** 2) * (by - cy) + (bx ** 2 + by ** 2) * (cy - ay)
              + (cx ** 2 + cy ** 2) * (ay - by)) / d
        uy = ((ax ** 2 + ay ** 2) * (cx - bx) + (bx ** 2 + by ** 2) * (ax - cx)
              + (cx ** 2 + cy ** 2) * (bx - ax)) / d
        cc = complex(ux, uy)
        r = abs(pts[i] - cc)
        if all(abs(p - cc) <= r * (1 + 1e-10) for p in pts):
            best = r if best is None else min(best, r)
    return best


def aggregate(roots, allow_shell=False):
    """(Sigma_c L(c), n, R_MEC, per-hub list) or None on guarded rejection."""
    roots = np.asarray(roots, dtype=complex)
    n = len(roots)
    cps, cvs, c_poly, dc_poly = crit_data(roots)
    R_scale = float(np.max(np.abs(roots)))
    tot, per = 0.0, []
    for i in range(len(cps)):
        others = [c for c in cps if abs(c - cps[i]) > 1e-13]
        d_pt = min((abs(c - cps[i]) for c in others), default=np.inf)
        if not allow_shell and np.isfinite(d_pt) and d_pt < 0.02 * R_scale:
            return None
        ra = lift_arm(c_poly, dc_poly, cps[i], cvs[i], +1, cps)
        rb = lift_arm(c_poly, dc_poly, cps[i], cvs[i], -1, cps)
        if ra is None or rb is None:
            return None
        ia = int(np.argmin(np.abs(roots - ra[1])))
        ib = int(np.argmin(np.abs(roots - rb[1])))
        if ia == ib or abs(roots[ia] - ra[1]) > 1e-6 * max(1, R_scale) \
                or abs(roots[ib] - rb[1]) > 1e-6 * max(1, R_scale):
            return None
        L = ra[0] + rb[0]
        per.append(L)
        tot += L
    return tot, n, mec_radius(list(roots)), per


# (AGG) REFUTATION witness (addendum): closed-disk quartic, MEC = unit circle,
# all hubs admissible, ratio > 1 certified by six instruments + flow-free
# polyline.  Asserted ratio > 1.0009 here.
REFUTATION_ROOTS = [
    9.983958848690963e-01 - 6.084363263325326e-04j,
    -1.473349861451955e-04 + 9.999999891462010e-01j,
    -9.984325248818108e-01 + 4.538173765221395e-04j,
    1.473349861451955e-04 - 9.999999891462010e-01j,
]

# n=5 refutation witness C (single certified point; see addendum caveat)
REFUTATION_ROOTS_N5 = [
    0.9995628702448384 - 2.4081377614440128e-04j,
    0.3091759926144788 + 9.5100483994081331e-01j,
    -0.8087734272148104 + 5.8812034774458355e-01j,
    -0.8090475039794104 - 5.8744304835350258e-01j,
    0.3084984195773588 - 9.5122485518318545e-01j,
]

WITNESSES = [
    ("killer_CDR_deg4",
     [1, complex(float.fromhex("0x1.6fa15252d066ep-5"), float.fromhex("0x1.3895293ffc3ebp-6")),
      complex(-float.fromhex("0x1.8c5640e53fa34p-9"), -float.fromhex("0x1.69a016b3f0c4ap-9")),
      0, -1],
     0.985),
    ("tie_locus_deg4",
     [1, complex(-float.fromhex("0x1.0bddcc73f5e5cp-2"), float.fromhex("0x1.c3dec89f5b0e8p-4")),
      complex(-float.fromhex("0x1.9b73f0ef75d0cp-11"), float.fromhex("0x1.f9f51c318c348p-13")),
      0, -1],
     0.965),
]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.parse_args()
    ok = True

    # 1. hard witnesses (chart polynomials ftil = z^4 - b3 z^3 - b2 z^2 - 1;
    #    coefficient arrays stored directly above)
    for label, coeffs, cap in WITNESSES:
        roots = np.roots(np.array(coeffs, dtype=complex))
        # stored witnesses sit on the near-double-saddle stratum; their arm
        # values are cross-certified at 50 dps (falsifier + main loop), so the
        # sweep-instrument shell guard is lifted for exactly these rows
        res = aggregate(roots, allow_shell=True)
        if res is None:
            print(f"witness {label}: guarded rejection (unexpected)")
            ok = False
            continue
        tot, n, Rm, per = res
        ratio = tot / (2 * (n - 1) * Rm)
        print(f"witness {label}: per-hub {[round(x, 6) for x in sorted(per, reverse=True)]} "
              f"Sigma={tot:.6f} budget={2 * (n - 1) * Rm:.6f} ratio={ratio:.6f}")
        ok &= ratio < cap
        ok &= max(per) > 2.0  # the compensation phenomenon: one hub over 2

    # 2. sub-mean-value spot test (psh evidence)
    smv_ok, smv_tests = 0, 0
    for _ in range(5):
        n = int(RNG.integers(3, 6))
        base = 0.85 * np.sqrt(RNG.uniform(0, 1, n)) * np.exp(2j * np.pi * RNG.uniform(0, 1, n))
        m0 = aggregate(base)
        if m0 is None:
            continue
        v = RNG.standard_normal(n) + 1j * RNG.standard_normal(n)
        v /= np.max(np.abs(v))
        vals = []
        good = True
        for phi in np.linspace(0, 2 * np.pi, 10, endpoint=False):
            m = aggregate(base + 0.01 * np.exp(1j * phi) * v)
            if m is None:
                good = False
                break
            vals.append(m[0])
        if not good:
            continue
        smv_tests += 1
        smv_ok += (np.mean(vals) >= m0[0] - 1e-6)
    print(f"sub-mean-value spot test: {smv_ok}/{smv_tests} passed")
    ok &= smv_tests > 0 and smv_ok == smv_tests

    # 2b. the (AGG) refutation witness: ratio must exceed 1 (addendum)
    res = aggregate(np.array(REFUTATION_ROOTS), allow_shell=True)
    if res is None:
        print("refutation witness: unexpected rejection")
        ok = False
    else:
        tot, n, Rm, per = res
        r = tot / (2 * (n - 1) * Rm)
        print(f"refutation witness: Sigma={tot:.9f} ratio={r:.9f} "
              f"admissible_all={all(x is not None for x in per)} min_hub_over_2R={min(per)/(2*Rm):.6f}")
        ok &= 1.0009 < r < 1.0012
        ok &= min(per) / (2 * Rm) < 1.0

    # 2c. the n=5 refutation witness C (single certified point)
    res = aggregate(np.array(REFUTATION_ROOTS_N5), allow_shell=True)
    if res is None:
        print("n5 refutation witness: unexpected rejection")
        ok = False
    else:
        tot, n, Rm, per = res
        r = tot / (2 * (n - 1) * Rm)
        print(f"n5 refutation witness: Sigma={tot:.9f} ratio={r:.9f} min_hub={min(per)/(2*Rm):.6f}")
        ok &= 1.0003 < r < 1.0004
        ok &= min(per) / (2 * Rm) < 1.0

    # 3. random sweep: ratio < 1 on the guarded locus
    worst = 0.0
    for _ in range(40):
        n = int(RNG.integers(3, 7))
        roots = np.sqrt(RNG.uniform(0, 1, n)) * np.exp(2j * np.pi * RNG.uniform(0, 1, n))
        res = aggregate(roots)
        if res is None:
            continue
        tot, n, Rm, per = res
        worst = max(worst, tot / (2 * (n - 1) * Rm))
    print(f"random sweep worst aggregate ratio: {worst:.6f}")
    ok &= worst < 1.0

    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
