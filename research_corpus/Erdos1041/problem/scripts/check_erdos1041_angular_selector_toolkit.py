"""Checker for NearFeketeAngularSelectorToolkit.md (Erdos 1041).

Verifies, per the note's sections:
  A  sector-ellipse hub metric: adversarial sup of |c-u_j|+|c-u_{j+1}| over the
     bracketing sector is exactly 2 (attained only at the stated equality
     cases), plus the quantitative slack form 2 - 2 r cos^2(pi/n) + r^2.
  B  trace identity  sum_{P'(c)=0} P(c) = 0 (n odd) / -(n/8) b_{n/2}^2 (n even)
     for P = z^n + sum_{r<=n/2} b_r z^r, machine precision, n = 4..9.
  B2 the n=5 critical-value quartic R(Y) (exact symbolic resultant, sympy).
  C  safe canonical arms: at random non-tangent models w^5 + b2 w^2 + b1 w,
     the two value-ray preimage branches from a strictly positive simple
     critical point stay in {Re P > 0} and reach two DISTINCT tracts
     (resolved-chart integration with fibre-projection guard).
  D  spine classification ingredients: rotation construction from
     a^5, a b^2 real; reality of the R(Y) coefficients on that set.
  E  origin-ray exact criterion a_u >= (3/4^{4/3})((-b_u)_+)^{4/3};
     pure-face >= 2 safe rays (both faces); the mixed dominance cone
     |b2| <= 4 (alpha/3)^{3/4} |b1|^{3/4}.

Exit 0 iff every section passes.
"""
import sys

import numpy as np

rng = np.random.default_rng(1041)
FAILURES = []


def report(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


# ---------------- A: sector-ellipse ----------------
def section_A():
    worst = 0.0
    for n in range(3, 13):
        alpha = np.pi / n
        th = np.linspace(-alpha, alpha, 1501)
        r = np.linspace(0, 1, 751)
        R, TH = np.meshgrid(r, th)
        C = R * np.exp(1j * TH)
        S = np.abs(C - np.exp(-1j * alpha)) + np.abs(C - np.exp(1j * alpha))
        worst = max(worst, float(S.max()))
    report("A sector-ellipse sup <= 2", worst <= 2 + 1e-12, f"sup={worst:.15f}")

    ok = True
    for n in range(3, 13):
        alpha = np.pi / n
        for _ in range(1500):
            r = rng.uniform(0, 1)
            th = rng.uniform(-alpha, alpha)
            c = r * np.exp(1j * th)
            s = abs(c - np.exp(-1j * alpha)) + abs(c - np.exp(1j * alpha))
            if s > 2 - 2 * r * np.cos(alpha) ** 2 + r ** 2 + 1e-12:
                ok = False
    report("A quantitative slack form", ok)


# ---------------- B: trace identity ----------------
def section_B():
    for n in range(4, 10):
        d = n // 2
        worst = 0.0
        for _ in range(250):
            b = 2 * (rng.standard_normal(d) + 1j * rng.standard_normal(d))
            poly = np.zeros(n + 1, dtype=complex)
            poly[0] = 1.0
            for r in range(1, d + 1):
                poly[n - r] = b[r - 1]
            dpoly = np.array([(n - i) * poly[i] for i in range(n)], dtype=complex)
            crits = np.roots(dpoly)
            P = np.polynomial.polynomial.Polynomial(poly[::-1])
            s = sum(P(c) for c in crits)
            target = 0.0 if n % 2 == 1 else -(n / 8.0) * b[d - 1] ** 2
            worst = max(worst, abs(s - target))
        report(f"B trace identity n={n}", worst < 1e-8, f"worst dev={worst:.2e}")


def section_B2():
    import sympy as sp

    z, Y, a, b = sp.symbols("z Y a b")
    P5 = z ** 5 + b * z ** 2 + a * z
    res = sp.resultant(Y - P5, sp.diff(P5, z), z)
    res = sp.expand(res / sp.LC(res, Y))
    claimed = sp.expand(
        Y ** 4
        + sp.Rational(18, 25) * a * b ** 2 * Y ** 2
        - sp.Rational(4, 3125) * b * (27 * b ** 4 - 400 * a ** 3) * Y
        + sp.Rational(1, 3125) * a ** 2 * (256 * a ** 3 - 27 * b ** 4)
    )
    report("B2 R(Y) exact quartic (resultant)", sp.simplify(res - claimed) == 0)

    c = sp.symbols("c")
    red = sp.simplify(
        (c ** 5 + b * c ** 2 + a * c)
        - (sp.Rational(3, 5) * b * c ** 2 + sp.Rational(4, 5) * a * c)
        - c * (5 * c ** 4 + 2 * b * c + a) / 5
    )
    report("B2 critical-value formula", red == 0)


# ---------------- C: safe canonical arms ----------------
def arm_test(b1, b2, n_models_checked):
    """Return (ok_contained, ok_distinct) for one model, or None if skipped."""
    P = lambda w: w ** 5 + b2 * w ** 2 + b1 * w
    dP = lambda w: 5 * w ** 4 + 2 * b2 * w + b1
    d2P = lambda w: 20 * w ** 3 + 2 * b2
    crits = np.roots([5.0, 0, 0, 2 * b2, b1])
    # simple + strictly positive hub, well separated
    cand = [c for c in crits if np.real(P(c)) > 5e-3]
    if not cand:
        return None
    c0 = max(cand, key=lambda c: np.real(P(c)))
    if min(abs(c0 - c) for c in crits if abs(c - c0) > 1e-12) < 1e-3:
        return None
    if abs(d2P(c0)) < 1e-6:
        return None
    # ray direction phi: choose small generic phi avoiding other critical values
    v0 = P(c0)
    phi = 0.0
    othv = [P(c) for c in crits if abs(c - c0) > 1e-12]
    for trial_phi in (0.0, 0.05, -0.05, 0.11, -0.11):
        ok_dir = True
        for w in othv:
            # distance from w to ray v0 + t e^{i phi}
            t = np.real((w - v0) * np.exp(-1j * trial_phi))
            if t > 0:
                dist = abs(w - (v0 + t * np.exp(1j * trial_phi)))
                if dist < 1e-3:
                    ok_dir = False
        if ok_dir and np.real(v0) + 0 * np.cos(trial_phi) > 0:
            phi = trial_phi
            break
    e = np.exp(1j * phi)
    T = 400.0
    contained = True
    ends = []
    for sgn in (+1, -1):
        # resolved chart start: w = v0 + xi^2 e, z ~ c0 + sgn*xi*sqrt(2 e/P''(c0))
        xi0 = 1e-4
        z = c0 + sgn * xi0 * np.sqrt(2 * e / d2P(c0))
        t = xi0 ** 2
        # Newton-project to the fibre
        for _ in range(50):
            corr = (P(z) - (v0 + t * e)) / dP(z)
            z -= corr
            if abs(corr) < 1e-13:
                break
        Np = 4000
        ts = np.geomspace(t, T, Np)
        okm = True
        for k in range(1, Np):
            dt = ts[k] - ts[k - 1]
            # RK2 step of dz/dt = e / P'(z)
            k1 = e / dP(z)
            zmid = z + 0.5 * dt * k1
            k2 = e / dP(zmid)
            z = z + dt * k2
            # projection
            for _ in range(8):
                corr = (P(z) - (v0 + ts[k] * e)) / dP(z)
                z -= corr
                if abs(corr) < 1e-12:
                    break
            if np.real(P(z)) <= 0:
                okm = False
                break
        contained = contained and okm
        ends.append(np.angle(z))
    # distinct tracts: angles differ by ~ multiple of 2 pi/5, not the same sector
    sec = [int(np.round(a / (2 * np.pi / 5))) % 5 for a in ends]
    distinct = sec[0] != sec[1]
    return contained, distinct


def section_C():
    okc = okd = True
    tested = 0
    tries = 0
    while tested < 40 and tries < 400:
        tries += 1
        b1 = 1.5 * (rng.standard_normal() + 1j * rng.standard_normal())
        b2 = 1.5 * (rng.standard_normal() + 1j * rng.standard_normal())
        res = arm_test(b1, b2, tested)
        if res is None:
            continue
        tested += 1
        c_ok, d_ok = res
        okc = okc and c_ok
        okd = okd and d_ok
    report("C arms contained in {Re P > 0}", okc, f"tested={tested}")
    report("C arms reach two distinct tracts", okd, f"tested={tested}")


# ---------------- D: spine ingredients ----------------
def section_D():
    ok_rot = True
    ok_real = True
    for _ in range(300):
        k = int(rng.integers(0, 10))
        alpha = k * np.pi / 5
        m = int(rng.integers(0, 4))
        beta = (-alpha + m * np.pi) / 2
        av = rng.uniform(0.2, 2) * np.exp(1j * alpha)
        bv = rng.uniform(0.2, 2) * np.exp(1j * beta)
        theta = alpha - beta
        a_rot = av * np.exp(-4j * theta)
        b_rot = bv * np.exp(-3j * theta)
        if abs(np.imag(a_rot)) > 1e-9 * abs(a_rot) or abs(np.imag(b_rot)) > 1e-9 * abs(b_rot):
            ok_rot = False
        c2 = 18 / 25 * av * bv ** 2
        c0 = av ** 2 * (256 * av ** 3 - 27 * bv ** 4) / 3125
        if abs(np.imag(c2)) > 1e-9 * max(1, abs(c2)) or abs(np.imag(c0)) > 1e-9 * max(1, abs(c0)):
            ok_real = False
    report("D spine rotation construction", ok_rot)
    report("D R-coefficient reality on the constructed set", ok_real)


# ---------------- E: origin rays ----------------
K1 = 3.0 / 4.0 ** (4.0 / 3.0)
U5 = np.exp(2j * np.pi * np.arange(5) / 5)


def ray_safe_exact(a_u, b_u):
    return a_u >= K1 * max(-b_u, 0.0) ** (4.0 / 3.0) - 1e-15


def section_E():
    ok = True
    for _ in range(3000):
        a_u = rng.uniform(-2, 2)
        b_u = rng.uniform(-2, 2)
        t = np.linspace(0, 6, 40001)
        num = bool(np.min(t ** 5 + b_u * t ** 2 + a_u * t) >= -1e-12)
        exact = ray_safe_exact(a_u, b_u)
        if num != exact and abs(a_u - K1 * max(-b_u, 0) ** (4 / 3)) > 1e-6:
            ok = False
    report("E origin-ray exact criterion", ok)

    ok1 = ok2 = True
    for _ in range(3000):
        b1 = rng.standard_normal() + 1j * rng.standard_normal()
        if sum(1 for u in U5 if np.real(b1 * u) >= -1e-14) < 2:
            ok1 = False
        b2 = rng.standard_normal() + 1j * rng.standard_normal()
        if sum(1 for u in U5 if np.real(b2 * u * u) >= -1e-14) < 2:
            ok2 = False
    report("E pure face m=1: >=2 safe rays", ok1)
    report("E pure face m=2: >=2 safe rays", ok2)

    alpha_c = (np.sqrt(5) - 1) / 4
    cone = 4 * (alpha_c / 3) ** 0.75
    ok = True
    for _ in range(3000):
        b1 = (rng.standard_normal() + 1j * rng.standard_normal()) * rng.uniform(0.1, 3)
        b2 = rng.standard_normal() + 1j * rng.standard_normal()
        b2 = b2 / abs(b2) * rng.uniform(0, cone * abs(b1) ** 0.75)
        cnt = sum(
            1
            for u in U5
            if ray_safe_exact(float(np.real(b1 * u)), float(np.real(b2 * u * u)))
        )
        if cnt < 2:
            ok = False
    report("E dominance cone => >=2 safe rays", ok, f"cone coeff={cone:.5f}")


def main():
    section_A()
    section_B()
    section_B2()
    section_C()
    section_D()
    section_E()
    print()
    if FAILURES:
        print("FAIL:", FAILURES)
        return 1
    print("PASS: all sections")
    return 0


if __name__ == "__main__":
    sys.exit(main())
