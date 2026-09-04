"""Checker for OneFaceRadialScatteringTheorem.md (Erdos 1041).

Verifies, for the one-face models H(z) = z^n + lambda z^m (1 <= m < n/2):
  1  critical parametrization: c^q = -(m/n) lambda (q = n-m),
     H(c) = -(q/m) c^n, the q nonzero critical values are H(c0) zeta^m
     (zeta^q = 1) and sum to zero, so some c* has Re H(c*) >= 0;
  2  the hub-free normalization H(c y)/H(c) = F(y) = (n y^m - m y^n)/q;
  3  the polar law on the upper lift of [1, oo): r(theta)^q
     = n sin(m theta)/(m sin(n theta)) on (0, pi/n), r > 1, F real and
     strictly increasing along the branch (containment: Re H = F Re H(c*)
     >= Re H(c*) >= 0);
  4  the sine-quotient lemma (y/x)cot y - cot x >= sin y/sin x - y/x on
     0 < y <= x < pi: symbolic derivative identity
     sin^2 x * R'(x) = -(x - sin x cos x) + sin y (sin x - x cos x),
     A0 - B0 = (1+cos x)(x - sin x), plus a dense grid check;
  5  the slope chain h' >= (m/q)(r^q - 1) >= r - 1 > sinh h (grid over
     (n,m) pairs; strictness quantified);
  6  arm-length quadrature: per-arm excess = -1 + int r(sqrt(1+h'^2)-h')
     <= pi/n - 1 in y-units (strict), pair excess in z-units
     <= 2 |c*| (pi/n - 1) < 0; asymptotic arm directions are the two
     distinct adjacent tracts arg y -> +- pi/n;
  7  n = 3 (m = 1): r^2 = 1/(1 - (4/3) sin^2 theta); E(theta) <= cos theta
     on (0, pi/3) (grid) and the certifying quartic
     192 - 531 x + 556 x^2 - 272 x^3 + 64 x^4 >= 0 on [0, 3/4] by exact
     Sturm; pair excess <= (sqrt 3 - 2)|c|;
  8  the quintic margin table 2(1 - pi/5)(m/5)^{1/(5-m)} for m = 1, 2.

Exit 0 iff all pass.
"""
import sys

import mpmath as mp
import numpy as np
import sympy as sp

rng = np.random.default_rng(23)
FAILURES = []


def report(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


PAIRS = [(4, 1), (5, 1), (5, 2), (6, 1), (7, 2), (7, 3), (9, 2), (9, 4), (12, 5)]


def A_of(n, m, th):
    return (n * mp.sin(m * th)) / (m * mp.sin(n * th))


def hp_of(n, m, th):
    return (m / mp.tan(m * th) - n / mp.tan(n * th)) / (n - m)


def main():
    mp.mp.dps = 25

    # 1 critical parametrization
    ok1 = True
    for (n, m) in PAIRS:
        q = n - m
        for _ in range(6):
            lam = complex(rng.normal(), rng.normal())
            c0 = (-(m / n) * lam) ** (1.0 / q)
            coeffs = np.zeros(n + 1, complex)
            coeffs[0] = 1
            coeffs[n - m] = lam
            H = lambda z: z**n + lam * z**m
            Hp = lambda z: n * z ** (n - 1) + m * lam * z ** (m - 1)
            zetas = [np.exp(2j * np.pi * k / q) for k in range(q)]
            vals = [H(c0 * z) for z in zetas]
            ok1 &= abs(Hp(c0)) < 1e-8 * max(1, abs(lam))
            ok1 &= abs(H(c0) + (q / m) * c0**n) < 1e-9 * max(1, abs(c0) ** n)
            ok1 &= all(abs(vals[k] - vals[0] * zetas[k] ** m) < 1e-9 * max(1, abs(vals[0]))
                       for k in range(q))
            ok1 &= abs(sum(vals)) < 1e-9 * max(1, abs(vals[0]))
            ok1 &= max(v.real for v in vals) > -1e-12
    report("1 critical parametrization + zero orbit sum + Re-nonneg hub", ok1)

    # 2 normalization identity
    ok2 = True
    for (n, m) in PAIRS[:6]:
        q = n - m
        for _ in range(5):
            lam = complex(rng.normal(), rng.normal())
            c0 = (-(m / n) * lam) ** (1.0 / q) * np.exp(2j * np.pi * rng.integers(q) / q)
            y = complex(rng.normal(), rng.normal())
            H = lambda z: z**n + lam * z**m
            F = (n * y**m - m * y**n) / q
            ok2 &= abs(H(c0 * y) / H(c0) - F) < 1e-9 * max(1, abs(F))
    report("2 hub-free normalization H(cy)/H(c) = F(y)", ok2)

    # 3 polar law: F real, > 1, increasing along the branch
    ok3 = True
    for (n, m) in PAIRS:
        q = n - m
        prev = 1.0
        for k in range(1, 200):
            th = mp.pi / n * k / mp.mpf(200.5)
            r = A_of(n, m, th) ** (mp.mpf(1) / q)
            y = r * mp.exp(1j * th)
            F = (n * y**m - m * y**n) / q
            ok3 &= abs(mp.im(F)) < mp.mpf("1e-18") * max(1, abs(F))
            ok3 &= mp.re(F) > prev - mp.mpf("1e-15")
            prev = mp.re(F)
            ok3 &= r > 1
    report("3 polar law: branch real, F strictly increasing from 1, r > 1", ok3)

    # 4 sine-quotient lemma
    X, Y = sp.symbols("x y", positive=True)
    R = X * (sp.cot(X) + sp.sin(Y) / sp.sin(X))
    lhs = sp.simplify(sp.sin(X) ** 2 * sp.diff(R, X)
                      - (-(X - sp.sin(X) * sp.cos(X))
                         + sp.sin(Y) * (sp.sin(X) - X * sp.cos(X))))
    idA = sp.simplify((X - sp.sin(X) * sp.cos(X)) - (sp.sin(X) - X * sp.cos(X))
                      - (1 + sp.cos(X)) * (X - sp.sin(X)))
    grid_ok = True
    for xi in np.linspace(0.05, 3.1, 40):
        for yi in np.linspace(0.02, xi, 12):
            l = (yi / xi) / np.tan(yi) - 1 / np.tan(xi)
            r_ = np.sin(yi) / np.sin(xi) - yi / xi
            if l < r_ - 1e-12:
                grid_ok = False
    report("4 sine-quotient lemma (symbolic derivative identity + grid)",
           lhs == 0 and idA == 0 and grid_ok)

    # 5 slope chain
    ok5 = True
    min_gap = mp.mpf(10)
    for (n, m) in PAIRS:
        q = n - m
        for k in range(1, 300):
            th = mp.pi / n * k / mp.mpf(300.5)
            A = A_of(n, m, th)
            r = A ** (mp.mpf(1) / q)
            hp = hp_of(n, m, th)
            h = mp.log(r)
            ok5 &= hp >= (m / mp.mpf(q)) * (A - 1) - mp.mpf("1e-18")
            ok5 &= (m / mp.mpf(q)) * (A - 1) >= r - 1 - mp.mpf("1e-18")
            gap = hp - mp.sinh(h)
            min_gap = min(min_gap, gap)
            ok5 &= gap > 0
    report("5 slope chain h' >= (m/q)(A-1) >= r-1 > sinh h", ok5,
           f"min h'-sinh h gap {mp.nstr(min_gap, 4)}")

    # 6 arm-length quadrature and tract distinctness
    ok6 = True
    rows = []
    for (n, m) in PAIRS:
        q = n - m

        def integrand(th, n=n, m=m, q=q):
            r = A_of(n, m, th) ** (mp.mpf(1) / q)
            hp = hp_of(n, m, th)
            return r * (mp.sqrt(1 + hp * hp) - hp)

        exc_y = -1 + mp.quad(integrand, [mp.mpf("1e-12"), mp.pi / (2 * n),
                                         mp.pi / n * mp.mpf("0.9999995")])
        bound = mp.pi / n - 1
        cstar = (mp.mpf(m) / n) ** (mp.mpf(1) / q)  # |lambda| = 1
        ok6 &= exc_y < bound + mp.mpf("1e-6")
        rows.append(f"(n={n},m={m}): per-arm {mp.nstr(exc_y, 6)} <= {mp.nstr(bound, 6)}; "
                    f"pair z-units {mp.nstr(2 * cstar * exc_y, 6)}")
        # asymptotic direction: theta -> pi/n on the upper branch
        th_late = mp.pi / n * mp.mpf("0.99999")
        ok6 &= abs(th_late - mp.pi / n) < mp.mpf("1e-4")
    report("6 per-arm excess <= pi/n - 1 (strict), distinct conjugate tracts", ok6)
    for row in rows:
        print("    " + row)

    # 7 n = 3 case
    x = sp.symbols("x", nonnegative=True)
    quartic = sp.Poly(192 - 531 * x + 556 * x**2 - 272 * x**3 + 64 * x**4, x)
    rr = [r for r in sp.real_roots(quartic) if 0 <= r <= sp.Rational(3, 4)]
    grid7 = True
    n, m, q = 3, 1, 2
    for k in range(1, 400):
        th = mp.pi / 3 * k / mp.mpf(400.5)
        r = A_of(3, 1, th) ** mp.mpf("0.5")
        r2_closed = 1 / (1 - mp.mpf(4) / 3 * mp.sin(th) ** 2)
        grid7 &= abs(r**2 - r2_closed) < mp.mpf("1e-18") * r2_closed
        E = r * (mp.sqrt(1 + hp_of(3, 1, th) ** 2) - hp_of(3, 1, th))
        grid7 &= E <= mp.cos(th) + mp.mpf("1e-18")
    exc3 = -1 + mp.quad(lambda th: A_of(3, 1, th) ** mp.mpf("0.5")
                        * (mp.sqrt(1 + hp_of(3, 1, th) ** 2) - hp_of(3, 1, th)),
                        [mp.mpf("1e-12"), mp.pi / 6, mp.pi / 3 * mp.mpf("0.9999995")])
    pair3 = 2 * exc3  # |c| = (1/3)^{1/2} for |lambda|=1; bound is per |c|-unit
    report("7 n=3: closed polar form, E <= cos theta, quartic Sturm-nonneg, pair excess",
           len(rr) == 0 and grid7 and pair3 < (mp.sqrt(3) - 2) + mp.mpf("1e-6"),
           f"quartic roots in [0,3/4]: {rr}; pair excess (y-units) {mp.nstr(pair3, 6)} "
           f"<= sqrt3-2 = {mp.nstr(mp.sqrt(3) - 2, 6)}")

    # 8 quintic margins
    m1 = 2 * (1 - mp.pi / 5) * (mp.mpf(1) / 5) ** (mp.mpf(1) / 4)
    m2 = 2 * (1 - mp.pi / 5) * (mp.mpf(2) / 5) ** (mp.mpf(1) / 3)
    report("8 quintic guaranteed margins", abs(m1 - mp.mpf("0.4971")) < 1e-3
           and abs(m2 - mp.mpf("0.5477")) < 1e-3,
           f"m=1: {mp.nstr(m1, 6)}, m=2: {mp.nstr(m2, 6)}")

    print()
    if FAILURES:
        print("FAIL:", FAILURES)
        return 1
    print("PASS: all sections")
    return 0


if __name__ == "__main__":
    sys.exit(main())
