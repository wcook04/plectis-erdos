"""Exact/numerical replay for QuinticTraceMaxUniversalChamber.md."""

from fractions import Fraction as Q
import importlib.util
from pathlib import Path
import sys

import numpy as np
import sympy as sp


FAILURES = []


def report(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


def exact_algebra():
    c, x, b1, b2, mu, y = sp.symbols("c x b1 b2 mu y")
    H = lambda z: z**5 + b2 * z**2 + b1 * z
    centered = sp.expand(H(c + x) - H(c) - x**2 * (
        x**3 + 5*c*x**2 + 10*c**2*x + 10*c**3 + b2))
    ok1 = sp.factor(centered) == x * (5*c**4 + 2*b2*c + b1)
    report("1 exact critical-hub centering", ok1, str(sp.factor(centered)))

    b2u = mu*c**3
    b1u = -(5 + 2*mu)*c**4
    Hu = lambda z: z**5 + b2u*z**2 + b1u*z
    F = x**2 * (x**3 + 5*x**2 + 10*x + 10 + mu)
    shape = sp.factor(Hu(c*(1+x)) - Hu(c) - c**5*F)
    deriv = sp.factor(
        5*(c*(1+x))**4 + 2*b2u*c*(1+x) + b1u
        - c**4*x*(5*x**3 + 20*x**2 + 30*x + 20 + 2*mu))
    report("2 exact universal shape and derivative", shape == 0 and deriv == 0)

    C = 5*x**3 + 20*x**2 + 30*x + 20 + 2*mu
    g = sp.Rational(1, 2)*x**3*(3*x**2 + 10*x + 10)
    gap_rem = sp.rem(sp.together(-F-g), C, x)
    report("3 exact critical-gap simplification", sp.factor(gap_rem) == 0)

    resultant = sp.factor(sp.resultant(C, y-g, x))
    expected = -(
        3125*y**3 + 12500*(mu+4)*y**2
        + (-4500*mu**3 + 7500*mu**2 + 150000*mu + 300000)*y
        + 108*mu**5 + 3800*mu**4 + 50000*mu**3 + 300000*mu**2
        + 800000*mu + 800000)
    report("4 exact gap cubic resultant", sp.expand(resultant-expected) == 0)


def rouche_budget():
    r = Q(3, 50)
    lower = r * (Q(17, 10) - r)**2
    perturb = Q(4, 30)*(1+r)**2 + Q(6, 30**2)*(1+r) + Q(4, 30**3)
    gap_error = ((1+r)**5 - 1 + Q(1, 9)*(1+r)**4
                 + Q(1, 270)*(1+r)**3)
    ok = (lower == Q(5043, 31250) and perturb == Q(52997, 337500)
          and perturb < lower and gap_error == Q(4074569711, 8437500000)
          and gap_error < Q(1, 2))
    report("5 exact Rouche/gap-error budget gives |mu| < 67500", ok,
           f"separation={float(lower-perturb):.8f}, half-gap={float(Q(1,2)-gap_error):.8f}")


def real_axis_classification():
    x, y, mu = sp.symbols("x y mu", real=True)
    C = 5*x**3 + 20*x**2 + 30*x + 20 + 2*mu
    g = sp.Rational(1, 2)*x**3*(3*x**2 + 10*x + 10)
    gap_poly = (
        3125*y**3 + 12500*(mu+4)*y**2
        + (-4500*mu**3 + 7500*mu**2 + 150000*mu + 300000)*y
        + 108*mu**5 + 3800*mu**4 + 50000*mu**3 + 300000*mu**2
        + 800000*mu + 800000)
    disc_c = sp.factor(sp.discriminant(C, x))
    disc_g = sp.factor(sp.discriminant(gap_poly, y))
    expected_c = -100*(27*mu**2+100*mu+100)
    expected_g = (-156250000*(mu**2-100*mu-200)**2
                  *(27*mu**2+100*mu+100)**3)
    report("6 exact critical/gap discriminants on the real slice",
           sp.expand(disc_c-expected_c) == 0
           and sp.expand(disc_g-expected_g) == 0)

    # A=0 is equivalent to the real gap equalling the total gap sum;
    # eliminate the unique real critical displacement.
    Aeq = 3*x**5 + 10*x**4 - 10*x**3 - 80*x**2 - 120*x - 48
    Qmu = (27*mu**5 + 5450*mu**4 + 23000*mu**3 - 105000*mu**2
           - 700000*mu - 1000000)
    res_a = sp.factor(sp.resultant(C, Aeq, x))
    res_g = sp.factor(sp.resultant(C, 2*g, x))
    expected_res_g = 32*(mu+10)**3*(27*mu**2+140*mu+200)
    report("7 exact real-slice boundary resultants",
           sp.expand(res_a-32*Qmu) == 0
           and sp.expand(res_g-expected_res_g) == 0)

    P = sp.Poly(Qmu, mu, domain=sp.QQ)
    counts = [sp.count_roots(P, -198, -197), sp.count_roots(P, -4, -3),
              sp.count_roots(P, 5, 6), sp.count_roots(P, -sp.oo, sp.oo)]
    # Rational real critical displacements r give exact test points mu(r).
    test_r = [sp.Integer(3), sp.Integer(2), -sp.Rational(1, 2),
              sp.Integer(-2), sp.Integer(-3)]
    signs = []
    mus = []
    for r in test_r:
        m = -(5*r**3+20*r**2+30*r+20)/2
        G = sp.Rational(1, 2)*r**3*(3*r**2+10*r+10)
        A = (-4*(m+4)-G)/2
        mus.append(m)
        signs.append(sp.sign(G*A))
    ok = counts == [1, 1, 1, 3] and signs == [-1, 1, -1, 1, -1]
    report("8 exact Sturm/sign replay of the real-axis chamber", ok,
           f"test_mu={mus}, signs={signs}")


def load_excess_module():
    path = Path(__file__).with_name("check_erdos1041_trace_max_radial_excess.py")
    spec = importlib.util.spec_from_file_location("trace_max_excess", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def universal_pair_excess(mu, phi, smax=2.0e7, nstep=1800):
    """Pair excess for F_mu(x)=exp(-i phi)s, based at x=0."""
    direction = np.exp(-1j*phi)
    F2 = 2*(10+mu)
    total = 0.0
    for sign in (1, -1):
        s0 = 1e-12 * max(1.0, abs(F2))
        x = sign*np.sqrt(2*direction*s0/F2)
        length = abs(x)
        ss = np.geomspace(s0, smax, nstep)
        for s in ss[1:]:
            fibre = np.roots([1, 5, 10, 10+mu, 0, -direction*s])
            xn = fibre[np.argmin(abs(fibre-x))]
            length += abs(xn-x)
            x = xn
        total += length-abs(1+x)
    return total


def numerical_scaling_and_chamber():
    M = load_excess_module()
    rng = np.random.default_rng(1041)
    worst = 0.0
    min_gap = 1e100
    tested = 0
    for _ in range(8):
        if rng.uniform() < 0.5:
            b1 = np.exp(2j*np.pi*rng.uniform())
            b2 = np.sqrt(rng.uniform())*np.exp(2j*np.pi*rng.uniform())
        else:
            b2 = np.exp(2j*np.pi*rng.uniform())
            b1 = np.sqrt(rng.uniform())*np.exp(2j*np.pi*rng.uniform())
        c = M.trace_max_hub(b1, b2)
        if abs(c) < 1e-5 or abs(20*c**3+2*b2) < 1e-5:
            continue
        mu = b2/c**3
        phi = np.angle(c**5)
        xs = np.roots([5, 20, 30, 20+2*mu])
        gaps = 0.5*xs**3*(3*xs**2+10*xs+10)
        min_gap = min(min_gap, np.min(np.real(np.exp(1j*phi)*gaps)))
        E0 = M.pair_excess(b1, b2, c, "right", smax=2e6, nstep=1400)/abs(c)
        E1 = universal_pair_excess(mu, phi, smax=2e6/abs(c)**5, nstep=1400)
        worst = max(worst, abs(E0-E1))
        tested += 1
    report("9 trace-max chamber inequalities on random core instances",
           tested >= 6 and min_gap > -2e-8,
           f"tested={tested}, min projected gap={min_gap:.3e}")
    report("10 exact excess scaling E_pair=|c|*E_universal (numerical replay)",
           tested >= 6 and worst < 3e-3, f"worst discrepancy={worst:.3e}")

    b1 = 0.75*5**(-1/3)*np.exp(1j*np.pi/5)
    b2 = np.exp(9j*np.pi/10)
    cs = M.crits(b1, b2)
    c = cs[np.argmin(abs(cs))]
    mu = b2/c**3
    phi = np.angle(c**5)
    target = 50+30*np.sqrt(3)
    E = M.pair_excess(b1, b2, c, "right", smax=2e7, nstep=2600)
    ok = abs(mu-target) < 2e-10 and abs(np.angle(np.exp(1j*(phi+np.pi/2)))) < 2e-10
    report("11 tangent orbit maps to mu=50+30sqrt(3), phi=-pi/2", ok,
           f"mu={mu.real:.10f}{mu.imag:+.1e}i, E_curved={E:.7f}")


def main():
    exact_algebra()
    rouche_budget()
    real_axis_classification()
    numerical_scaling_and_chamber()
    print()
    if FAILURES:
        print("FAIL:", FAILURES)
        return 1
    print("PASS: all universal-chamber sections")
    return 0


if __name__ == "__main__":
    sys.exit(main())
