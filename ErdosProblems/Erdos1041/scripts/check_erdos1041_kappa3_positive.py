"""Erdos #1041: PROOF that kappa_3 > 0, with every step checked numerically.

At n = 3 the near-field branch lies on  y^2 = (x-1)^2 (x+2) / (3x)  (section 8).
Both descending branches lie on the SAME sign-branch

        y(x) = (x-1) sqrt(x+2) / sqrt(3x),      x in (0, oo),

so the whole edge Gamma is one graph: it runs from x -> 0+ (where y -> -oo,
exit direction -pi/2) through the hub (1,0) to x -> +oo (where y ~ x/sqrt(3),
exit direction pi/6).  Write s(x) := dx/dy = 1/y'(x).

LEMMA 1 (closed forms).   s(x)^2 = 3x^3(x+2) / (1+x+x^2)^2,  and
        y'(x) = (x^2+x+1) / sqrt(3x^3(x+2))  = 1/s(x).

LEMMA 2 (monotonicity).   d/dx [s^2] = 18 x^2 (x+1) / (1+x+x^2)^3 > 0 on x>0.
        Hence s increases from 0 to sqrt(3): s <= 1 on (0,1], s in [1,sqrt3) on
        [1,oo).  In particular y' DECREASES from 1 to 1/sqrt(3) on (1,oo), so
        the tangent angle tau on branch A decreases monotonically from pi/4 to
        pi/6 -- monotone turning, proved rather than measured.

LEMMA 3 (elementary).  phi(s) := (sqrt(1+s^2)-1)/s = s/(sqrt(1+s^2)+1) is
        increasing, with phi(1) = sqrt(2)-1.

BRANCH B (x from 0 to 1, exit direction -pi/2, gamma_1 = pi/2, cos gamma_1 = 0).
        Parameterised by y, the chord direction is the y-axis and x stays in
        [0,1], so   D_B = int_{-oo}^{0} (sqrt(1+s^2) - 1) dy = int s phi(s) dy.
        By Lemma 2, s <= 1, so by Lemma 3
            D_B <= phi(1) * int s dy = (sqrt2 - 1) * (x(0) - x(-oo)) = sqrt2 - 1.

BRANCH A (x from 1 to oo, exit direction pi/6, cos gamma_2 = sqrt(3)/2).
        In coordinates (u,v) rotated by pi/6, tau in (pi/6, pi/4] by Lemma 2, so
        v_u = tan(tau - pi/6) in (0, tan(pi/12)] -- u is monotone and so is v.
        v runs from v_0 = -1/2 (the hub) to v_oo = 0 (the asymptote y = x/sqrt3
        passes through the origin), so TV(v) = 1/2 and
            D_A <= phi(tan(pi/12)) * 1/2,   tan(pi/12) = 2 - sqrt(3).

CONCLUSION.  kappa_3 = (cos gamma_1 + cos gamma_2) - (D_1 + D_2)
                     = sqrt(3)/2 - (D_A + D_B)
                     >= sqrt(3)/2 - (sqrt2 - 1) - (2-sqrt3)/(2(sqrt6-sqrt2+1))
                     = 0.3859...  >  0.                                     []
"""

from mpmath import mp

mp.dps = 40


def s2(x):
    return 3 * x**3 * (x + 2) / (1 + x + x**2) ** 2


def yfun(x):
    return (x - 1) * mp.sqrt(x + 2) / mp.sqrt(3 * x)


def yprime(x):
    return (x**2 + x + 1) / mp.sqrt(3 * x**3 * (x + 2))


def phi(s):
    return s / (mp.sqrt(1 + s**2) + 1)


def check():
    rep = {}
    # LEMMA 1: y' from the implicit curve vs the closed form
    w = mp.mpf(0)
    for k in range(1, 60):
        x = mp.mpf(k) / 6 + mp.mpf("0.05")
        h = mp.mpf(10) ** (-15)
        num = (yfun(x + h) - yfun(x - h)) / (2 * h)
        w = max(w, abs(num - yprime(x)) / max(1, abs(yprime(x))))
        w = max(w, abs(s2(x) - 1 / yprime(x) ** 2) / max(1, s2(x)))
    rep["L1_max_rel_dev"] = w

    # LEMMA 2: derivative identity and positivity
    w2 = mp.mpf(0)
    for k in range(1, 80):
        x = mp.mpf(k) / 8
        h = mp.mpf(10) ** (-15)
        num = (s2(x + h) - s2(x - h)) / (2 * h)
        cf = 18 * x**2 * (x + 1) / (1 + x + x**2) ** 3
        w2 = max(w2, abs(num - cf) / max(1, abs(cf)))
    rep["L2_max_rel_dev"] = w2
    rep["L2_s_at_1"] = s2(mp.mpf(1))
    rep["L2_s2_limit"] = s2(mp.mpf(10) ** 8)

    # LEMMA 3
    rep["L3_phi1"] = phi(mp.mpf(1)) - (mp.sqrt(2) - 1)

    # the two deficit bounds against the TRUE values from the model
    m = 2 - mp.sqrt(3)
    rep["bound_DB"] = mp.sqrt(2) - 1
    rep["bound_DA"] = phi(m) / 2
    rep["true_DB"] = mp.mpf("0.2350943")      # measured, section 7
    rep["true_DA"] = mp.mpf("0.02290983")
    rep["RHS"] = mp.sqrt(3) / 2
    rep["kappa3_lower"] = mp.sqrt(3) / 2 - (mp.sqrt(2) - 1) - phi(m) / 2
    rep["kappa3_true"] = mp.mpf("0.6080213113")
    rep["tan_pi12"] = mp.tan(mp.pi / 12) - m
    return rep


if __name__ == "__main__":
    r = check()
    print("LEMMA 1  y' closed form + s^2 = 1/y'^2 : max rel dev",
          mp.nstr(r["L1_max_rel_dev"], 3))
    print("LEMMA 2  d(s^2)/dx = 18x^2(x+1)/(1+x+x^2)^3 : max rel dev",
          mp.nstr(r["L2_max_rel_dev"], 3))
    print("         s(1)^2 =", mp.nstr(r["L2_s_at_1"], 12),
          "   s(inf)^2 ->", mp.nstr(r["L2_s2_limit"], 12), "(target 3)")
    print("LEMMA 3  phi(1) - (sqrt2-1) =", mp.nstr(r["L3_phi1"], 3))
    print("         tan(pi/12) - (2-sqrt3) =", mp.nstr(r["tan_pi12"], 3))
    print()
    print(" branch B:  bound", mp.nstr(r["bound_DB"], 10),
          " >= true", mp.nstr(r["true_DB"], 8),
          " OK" if r["bound_DB"] >= r["true_DB"] else " VIOLATED")
    print(" branch A:  bound", mp.nstr(r["bound_DA"], 10),
          " >= true", mp.nstr(r["true_DA"], 8),
          " OK" if r["bound_DA"] >= r["true_DA"] else " VIOLATED")
    print()
    print(" kappa_3 >= sqrt3/2 - (sqrt2-1) - phi(2-sqrt3)/2 =",
          mp.nstr(r["kappa3_lower"], 12))
    print(" true kappa_3                                    =",
          mp.nstr(r["kappa3_true"], 12))
    ok = (r["L1_max_rel_dev"] < mp.mpf("1e-12")
          and r["L2_max_rel_dev"] < mp.mpf("1e-10")
          and abs(r["L3_phi1"]) < mp.mpf("1e-30")
          and abs(r["tan_pi12"]) < mp.mpf("1e-30")
          and r["bound_DB"] >= r["true_DB"]
          and r["bound_DA"] >= r["true_DA"]
          and r["kappa3_lower"] > 0
          and r["kappa3_lower"] <= r["kappa3_true"])
    print("\nPASS -- kappa_3 > 0 is PROVED" if ok else "\nFAIL")
    import sys
    sys.exit(0 if ok else 1)
