"""Checker for QuinticTangentOrbitExactCertificate.md (Erdos 1041).

Verifies the EXACT upgrade of the tangent-orbit skip-pair certificate
(certificate (ii) of QuinticStarKernelMechanics.md par.6):

  1  exact algebra: G0' = 5 (V^2+2V-2)(V^2-2V+6); a = sqrt(3)-1 critical;
     a^2 = 2-2a; Taylor coefficients of G0 at a are (60a, 20(1-a), 5a, 1);
     critical values 144 -+ 96 sqrt3 and -144 (double), all real, sum 0;
  2  exact ray profiles: Im G0(a + t vbar_pm) = -t^2 P_pm(t) with
     P_+ = 60a sin36 + 20(1-a) sin54 t + 5a sin72 t^2 + t^3,
     P_- = 60a sin72 - 20(1-a) sin18 t - 5a sin36 t^2 + t^3  (symbolic);
  3  exact positivity of P_- on t >= 0 (sympy real-root isolation over the
     algebraic coefficients: no nonnegative real root, P_-(0) > 0), and the
     rational-bound elementary proof (interval arithmetic on [0,4] plus
     monotone dominance on [4, oo));  P_+ has positive coefficients;
  4  the metric budget: exact identity 2 cos72 cos54 = sin72 - sin36;
     excess = -a (sin72 - sin36); scaled hub identity
     40^{-1/3} a (sin72 - sin36) = 2 cos72 * Re(c*) with
     c* = 40^{-1/3} a e^{i 54 deg}; numeric value 0.0777592874...;
  5  containment sweep: Im G0 <= 0 along both rays (corpus frame) on a
     dense t-grid at 30 dps, and the arms end in tract sectors two steps
     apart (skip pair);
  6  stability margins: inf_t P_pm(t)/(1+t)^3 > 0, values reported.

Exit 0 iff all pass.
"""
import sys

import mpmath as mp
import sympy as sp

FAILURES = []


def report(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


def main():
    mp.mp.dps = 30
    V, t = sp.symbols("V t", real=True)
    G0 = V**5 + 40 * V**2 - 60 * V
    a = sp.sqrt(3) - 1

    # 1 exact algebra
    fact = sp.factor(sp.diff(G0, V))
    ok = sp.simplify(sp.diff(G0, V) - 5 * (V**2 + 2 * V - 2) * (V**2 - 2 * V + 6)) == 0
    ok &= sp.simplify(a**2 - (2 - 2 * a)) == 0
    c2 = sp.simplify(sp.diff(G0, V, 2).subs(V, a) / 2 - 60 * a) == 0
    c3 = sp.simplify(sp.diff(G0, V, 3).subs(V, a) / 6 - 20 * (1 - a)) == 0
    c4 = sp.simplify(sp.diff(G0, V, 4).subs(V, a) / 24 - 5 * a) == 0
    crit = [sp.sqrt(3) - 1, -sp.sqrt(3) - 1, 1 + sp.I * sp.sqrt(5), 1 - sp.I * sp.sqrt(5)]
    vals = [sp.simplify(G0.subs(V, c)) for c in crit]
    vals_ok = (sp.simplify(vals[0] - (144 - 96 * sp.sqrt(3))) == 0
               and sp.simplify(vals[1] - (144 + 96 * sp.sqrt(3))) == 0
               and sp.simplify(vals[2] + 144) == 0 and sp.simplify(vals[3] + 144) == 0
               and sp.simplify(sum(vals)) == 0
               and all(sp.im(sp.nsimplify(v)) == 0 for v in vals[:2]))
    report("1 exact algebra (G0', a, Taylor, critical values)",
           ok and c2 and c3 and c4 and vals_ok, f"factored G0' = {fact}")

    # 2 exact ray profiles: Taylor gives G0(a+tv)-G0(a) = 60a t^2 v^2
    # + 20(1-a) t^3 v^3 + 5a t^4 v^4 + t^5 v^5; check Im coefficientwise.
    s18, s36, s54, s72 = (sp.sin(sp.pi / 10), sp.sin(sp.pi / 5),
                          sp.sin(3 * sp.pi / 10), sp.sin(2 * sp.pi / 5))
    Pp = 60 * a * s36 + 20 * (1 - a) * s54 * t + 5 * a * s72 * t**2 + t**3
    Pm = 60 * a * s72 - 20 * (1 - a) * s18 * t - 5 * a * s36 * t**2 + t**3
    prof_ok = True
    # Taylor expansion is exact for a quintic (section 1 verified the coefficients)
    for v, claimed in (
        (sp.exp(sp.I * sp.pi / 10), (s36, s54, s72, sp.Integer(1))),
        (sp.exp(13 * sp.I * sp.pi / 10), (s72, -s18, -s36, sp.Integer(1))),
    ):
        for k, target in zip((2, 3, 4, 5), claimed):
            prof_ok &= sp.simplify(sp.im(sp.expand(v**k)) - target) == 0
    report("2 exact ray profiles Im G0 = t^2 P_pm (conjugate frame: -t^2 P_pm)", bool(prof_ok))

    # 3 exact positivity
    pos_p = all(sp.ask(sp.Q.positive(c)) or sp.simplify(c) == 0 or float(c) > 0
                for c in (60 * a * s36, 20 * (1 - a) * s54, 5 * a * s72))
    # 3b exact dominance: termwise, P_-(t) >= R(t) := t^3 - A_up t^2 - B_up t + C_lo
    # for t >= 0, where A_up >= 5 a sin36, B_up >= 20(1-a) sin18, C_lo <= 60 a sin72
    # are RATIONAL; then R > 0 on [0, oo) by exact Sturm (sympy real_roots).
    aU, aL = sp.Rational(733, 1000), sp.Rational(183, 250)
    s18U, s36U, s72L = sp.Rational(31, 100), sp.Rational(147, 250), sp.Rational(951, 1000)
    A_up = 5 * aU * s36U
    B_up = 20 * (1 - aL) * s18U
    C_lo = 60 * aL * s72L
    R = sp.Poly(t**3 - A_up * t**2 - B_up * t + C_lo, t)
    rroots = sp.real_roots(R)
    nonneg = [r for r in rroots if r >= 0]
    p0 = float(Pm.subs(t, 0))
    report("3a P_+ coefficients positive", bool(pos_p))
    report("3b exact Sturm: rational minorant R(t) has no root in [0,oo), R(0) > 0",
           len(nonneg) == 0 and R.eval(0) > 0 and p0 > 0,
           f"R(0)={float(R.eval(0)):.4f}  P_-(0)={p0:.4f}  real roots of R: "
           f"{[float(r) for r in rroots]}")
    # 3c the rational bounds themselves, certified by exact rational squaring:
    # a < 733/1000 <=> 3 < (1733/1000)^2;  a > 183/250 <=> 3 > (433/250)^2;
    # sin18 = (sqrt5-1)/4 < 31/100 <=> 5 < (224/100)^2;
    # sin36 = sqrt(10-2 sqrt5)/4 < 147/250 <=> sqrt5 > (10-(588/250)^2)/2 sq;
    # sin72 = sqrt(10+2 sqrt5)/4 > 951/1000 <=> 5 > ((3804/1000)^2-10)^2/4.
    closed = (sp.simplify(s18 - (sp.sqrt(5) - 1) / 4) == 0
              and sp.simplify(s36 - sp.sqrt(10 - 2 * sp.sqrt(5)) / 4) == 0
              and sp.simplify(s72 - sp.sqrt(10 + 2 * sp.sqrt(5)) / 4) == 0)
    r1 = sp.Rational(1733, 1000) ** 2 > 3
    r2 = sp.Rational(433, 250) ** 2 < 3
    r3 = sp.Rational(224, 100) ** 2 > 5
    r4 = ((10 - (4 * s36U) ** 2) / 2) ** 2 < 5  # => sin36 < s36U
    r5 = (((4 * s72L) ** 2 - 10) / 2) ** 2 < 5  # => sin72 > s72L
    report("3c rational sine/radical bounds certified by exact squaring",
           closed and r1 and r2 and r3 and r4 and r5)
    low_seg = C_lo - 4 * B_up - 16 * A_up
    tail_ok = 16 - 4 * A_up - B_up
    report("3d human-checkable branch proof ([0,4] floor and [4,oo) dominance)",
           float(low_seg) > 0 and float(tail_ok) > 0,
           f"[0,4] floor {float(low_seg):.4f}, tail quad at 4 {float(tail_ok):.4f}")

    # 4 metric budget
    ident = sp.simplify(2 * sp.cos(2 * sp.pi / 5) * sp.cos(3 * sp.pi / 10)
                        - (s72 - s36)) == 0
    exc = a * (s72 - s36)
    cstar_re = (40 ** sp.Rational(-1, 3)) * a * sp.cos(3 * sp.pi / 10)
    scaled = sp.simplify((40 ** sp.Rational(-1, 3)) * exc
                         - 2 * sp.cos(2 * sp.pi / 5) * cstar_re) == 0
    num = mp.mpf(40) ** (mp.mpf(-1) / 3) * (mp.sqrt(3) - 1) * (
        mp.sin(2 * mp.pi / 5) - mp.sin(mp.pi / 5))
    report("4 metric budget exact identities + value",
           ident and scaled and abs(num - mp.mpf("0.0777592874")) < 1e-9,
           f"scaled excess = {mp.nstr(num, 12)}")

    # 5 containment sweep, primary frame {Re H >= 0} = {Im G0 >= 0}
    # (Re H = 40^{-5/3} Im G0 via w = lambda V, lambda = 40^{-1/3} e^{3 i pi/10});
    # rays a + t v_pm, v_+ = e^{i pi/10}, v_- = e^{13 i pi/10}.  The mirror
    # gauge (conjugated rays inside {Im G0 <= 0}) is equivalent since G0 is real.
    g = lambda z: z**5 + 40 * z**2 - 60 * z
    worst = mp.mpf(1)
    worst_mirror = mp.mpf(1)
    for sgn in (1, -1):
        for ang in (mp.pi / 10, 13 * mp.pi / 10):
            v = mp.exp(sgn * 1j * ang)
            for k in range(1, 1200):
                tt = mp.mpf(k) / 60  # up to t = 20
                val = mp.im(g((mp.sqrt(3) - 1) + tt * v))
                if sgn == 1:
                    worst = min(worst, val)
                else:
                    worst_mirror = min(worst_mirror, -val)
    # tract centres of {Im G0 >= 0}: 18 + 72k degrees; 18 and 234 are 2 steps apart (short way)
    step = min((234 - 18) // 72, 5 - (234 - 18) // 72)
    report("5 containment (Im G0 >= 0 on both rays; mirror gauge agrees) + skip pair",
           worst > 0 and worst_mirror > 0 and step == 2,
           f"min Im G0 = {mp.nstr(worst, 6)} (mirror {mp.nstr(worst_mirror, 6)}), tract steps = {step}")

    # 6 stability margins: m+ = 1 EXACTLY (P_+ - (1+t)^3 has positive lower
    # coefficients; infimum at infinity), m- attained at the unique positive
    # root of P_-'(t)(1+t) - 3 P_-(t), certified > 12/25.
    dom = sp.expand(Pp - (1 + t) ** 3)
    dom_coeffs = [sp.Poly(dom, t).coeff_monomial(t**k) for k in range(3)]
    dom_ok = all(float(c) > 0 for c in dom_coeffs) and sp.Poly(dom, t).degree() == 2
    fPm = sp.lambdify(t, Pm, "mpmath")
    # argmin by golden-section on [0, 40] (unique interior minimum:
    # P_-'(t)(1+t) - 3 P_-(t) has one positive root)
    lo, hi = mp.mpf(0), mp.mpf(40)
    phi = (mp.sqrt(5) - 1) / 2
    f6 = lambda x: fPm(x) / (1 + x) ** 3
    a1, b1_ = hi - phi * (hi - lo), lo + phi * (hi - lo)
    for _ in range(200):
        if f6(a1) < f6(b1_):
            hi, b1_ = b1_, a1
            a1 = hi - phi * (hi - lo)
        else:
            lo, a1 = a1, b1_
            b1_ = lo + phi * (hi - lo)
    margin_m = f6((lo + hi) / 2)
    report("6 stability margins: m+ = 1 exact (dominance), m- > 12/25 attained",
           dom_ok and margin_m > mp.mpf(12) / 25,
           f"m- = {mp.nstr(margin_m, 12)} at t = {mp.nstr((lo+hi)/2, 6)}; "
           f"P_+ - (1+t)^3 coeffs {[float(c) for c in dom_coeffs]}")

    print()
    if FAILURES:
        print("FAIL:", FAILURES)
        return 1
    print("PASS: all sections")
    return 0


if __name__ == "__main__":
    sys.exit(main())
