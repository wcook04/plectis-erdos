"""Checker for QuinticStarKernelMechanics.md (Erdos 1041).

Sections:
  1  Main Theorem instances: trace-max hub's value-ray arms reach two
     DISTINCT tracts with Re H >= D along them; sharpness: 5 components
     above level D + 0.3.
  2  component-count formula #comp{Re H > 0} = 5 - #{Re H(c) > 0}
     (flood fill), and hub bound |c| <= t0 = root of 5t^4 - 2t - 1.
  3  exceptional orbit: |b1|^3 = 27/320, tangency at 40 dps, closed-form
     critical points/values in the rotated frame, trace = 0.
  4  orbit certificates: (i) G0-arms from V0 = -1 - sqrt3 stay in
     {Im G0 <= 0} with the recorded exit tracts; (ii) skip-pair saddle-hub
     straight arms with recorded cubic minima and metric budget.
  5  origin region: exact criterion vs numeric; #J <= 3 spot; O u B spot
     coverage (150 random core points, bisector hub family).
  6  degree-general trace: zero for n in {7, 9}, K = (n-1)/2; nonzero for
     n = 6, K = 3; exact constants K (arm inequality) spot check.

Exit 0 iff all sections pass.
"""
import sys
from collections import deque

import numpy as np
import mpmath as mp

rng = np.random.default_rng(29)
FAILURES = []
U5 = np.exp(2j * np.pi * np.arange(5) / 5)


def report(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


def arms_from_hub(b1, b2, c0, T=500.0, N=5000):
    H = lambda w: w ** 5 + b2 * w * w + b1 * w
    dH = lambda w: 5 * w ** 4 + 2 * b2 * w + b1
    d2H = lambda w: 20 * w ** 3 + 2 * b2
    v0 = H(c0)
    ends = []
    okmin = True
    for sgn in (+1, -1):
        s0 = 1e-6
        z = c0 + sgn * np.sqrt(2 * s0 / d2H(c0))
        for _ in range(60):
            corr = (H(z) - (v0 + s0)) / dH(z)
            z -= corr
            if abs(corr) < 1e-14:
                break
        ss = np.geomspace(s0, T, N)
        for k in range(1, N):
            ds = ss[k] - ss[k - 1]
            zm = z + 0.5 * ds / dH(z)
            z = z + ds / dH(zm)
            for _ in range(8):
                dd = dH(z)
                if abs(dd) < 1e-13:
                    break
                corr = (H(z) - (v0 + ss[k])) / dd
                z -= corr
                if abs(corr) < 1e-12:
                    break
            if (H(z)).real < v0.real - 1e-9:
                okmin = False
        ends.append(z)
    sec = [int(np.round(np.angle(e) / (2 * np.pi / 5))) % 5 for e in ends]
    return sec, okmin


def flood_components(b1, b2, lam=0.0, R=7.0, N=351):
    x = np.linspace(-R, R, N)
    X, Y = np.meshgrid(x, x)
    W = X + 1j * Y
    M = (W ** 5 + b2 * W * W + b1 * W).real > lam
    lab = -np.ones(M.shape, dtype=int)
    comp = 0
    for i0 in range(N):
        for j0 in range(N):
            if M[i0, j0] and lab[i0, j0] < 0:
                dq = deque([(i0, j0)])
                lab[i0, j0] = comp
                while dq:
                    i, j = dq.popleft()
                    for di, dj in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                        i2, j2 = i + di, j + dj
                        if 0 <= i2 < N and 0 <= j2 < N and M[i2, j2] and lab[i2, j2] < 0:
                            lab[i2, j2] = comp
                            dq.append((i2, j2))
                comp += 1
    return comp


def section1():
    okd = okl = oks = True
    tested = 0
    for _ in range(25):
        b1 = rng.standard_normal() + 1j * rng.standard_normal()
        b2 = rng.standard_normal() + 1j * rng.standard_normal()
        crits = np.roots([5.0, 0, 0, 2 * b2, b1])
        H = lambda w: w ** 5 + b2 * w * w + b1 * w
        vals = [H(c) for c in crits]
        cstar = crits[int(np.argmax([v.real for v in vals]))]
        if min(abs(cstar - c) for c in crits if abs(c - cstar) > 1e-12) < 1e-3:
            continue
        tested += 1
        sec, okm = arms_from_hub(b1, b2, cstar)
        if sec[0] == sec[1]:
            okd = False
        if not okm:
            okl = False
        if tested <= 5:
            D = max(v.real for v in vals)
            if flood_components(b1, b2, lam=D + 0.3) != 5:
                oks = False
    report("1 trace-max arms reach distinct tracts", okd, f"tested={tested}")
    report("1 Re H >= D along arms", okl)
    report("1 sharpness: 5 components above D + 0.3", oks)


def section2():
    ok = True
    for _ in range(15):
        b1 = rng.standard_normal() + 1j * rng.standard_normal()
        b2 = rng.standard_normal() + 1j * rng.standard_normal()
        crits = np.roots([5.0, 0, 0, 2 * b2, b1])
        H = lambda w: w ** 5 + b2 * w * w + b1 * w
        if any(abs(H(c).real) < 1e-9 for c in crits):
            continue
        npos = sum(1 for c in crits if H(c).real > 0)
        if flood_components(b1, b2) != 5 - npos:
            ok = False
    report("2 component-count formula", ok)
    t0 = float(mp.findroot(lambda t: 5 * t ** 4 - 2 * t - 1, 0.86))
    worst = 0.0
    for _ in range(1500):
        b1 = np.exp(1j * rng.uniform(0, 2 * np.pi)) * rng.uniform(0, 1)
        b2 = np.exp(1j * rng.uniform(0, 2 * np.pi)) * rng.uniform(0, 1)
        m = max(abs(b1), abs(b2))
        if m < 0.2:
            continue
        b1, b2 = b1 / m, b2 / m
        worst = max(worst, max(abs(c) for c in np.roots([5.0, 0, 0, 2 * b2, b1])))
    report("2 hub bound |c| <= t0", worst <= t0 + 1e-9, f"max={worst:.6f} t0={t0:.6f}")


def section3():
    mp.mp.dps = 40
    b1e = mp.mpf(3) / 4 * mp.power(5, mp.mpf(-1) / 3) * mp.e ** (1j * mp.pi / 5)
    b2e = mp.e ** (9j * mp.pi / 10)
    report("3 |b1|^3 = 27/320", abs(abs(b1e) ** 3 - mp.mpf(27) / 320) < 1e-35)
    crits = mp.polyroots([5, 0, 0, 2 * b2e, b1e], maxsteps=200, extraprec=100)
    Hc = [c ** 5 + b2e * c * c + b1e * c for c in crits]
    report("3 tangency (all Re = 0) at 40 dps", max(abs(mp.re(v)) for v in Hc) < 1e-30)
    report("3 trace = 0", abs(sum(Hc)) < 1e-30)
    x = mp.power(40, mp.mpf(-1) / 3)
    zs = [x * (mp.sqrt(3) - 1), -x * (1 + mp.sqrt(3)),
          x * (1 + 1j * mp.sqrt(5)), x * (1 - 1j * mp.sqrt(5))]
    ws = [mp.e ** (3j * mp.pi / 10) * z for z in zs]
    ok = all(min(abs(w - c) for c in crits) < 1e-25 for w in ws)
    report("3 closed-form critical points", ok)


def section4():
    s3 = np.sqrt(3)
    G0 = lambda V: V ** 5 + 40 * V ** 2 - 60 * V
    dG = lambda V: 5 * V ** 4 + 80 * V - 60
    V0 = -1 - s3
    lev = 144 + 96 * s3
    d2 = 20 * V0 ** 3 + 80
    ok = True
    exits = []
    for sgn in (+1, -1):
        s0 = 1e-8
        z = V0 + sgn * np.sqrt(np.complex128(-2j * s0 / d2))
        for _ in range(60):
            corr = (G0(z) - (lev - 1j * s0)) / dG(z)
            z -= corr
            if abs(corr) < 1e-14:
                break
        ss = np.geomspace(s0, 1e6, 8000)
        for k in range(1, len(ss)):
            ds = ss[k] - ss[k - 1]
            z = z + (-1j * ds) / dG(z)
            for _ in range(6):
                corr = (G0(z) - (lev - 1j * ss[k])) / dG(z)
                z -= corr
                if abs(corr) < 1e-10:
                    break
            if G0(z).imag > 1e-6 * max(1, abs(G0(z))):
                ok = False
                break
        exits.append(np.degrees(np.angle(z)) % 360)
    report("4 orbit certificate (i): G0 arms in {Im G0 <= 0}", ok,
           f"exits={exits[0]:.1f},{exits[1]:.1f} (claim ~126, ~198)")
    report("4 orbit exits adjacent tracts", abs(exits[0] - 126) < 4 and abs(exits[1] - 198) < 4)
    # certificate (ii): skip-pair saddle hub
    mp.mp.dps = 30
    b1e = mp.mpf(3) / 4 * mp.power(5, mp.mpf(-1) / 3) * mp.e ** (1j * mp.pi / 5)
    b2e = mp.e ** (9j * mp.pi / 10)
    cstar = mp.mpc('0.1258171699590390137', '0.1731724780164701602')
    tau = np.linspace(1e-6, 8.0, 100001)
    c = complex(cstar)
    b1c, b2c = complex(b1e), complex(b2e)
    q = []
    for u in (complex(U5[1]), complex(U5[4])):
        w = c + tau * u
        q.append(float(((w ** 5 + b2c * w * w + b1c * w).real / tau ** 2).min()))
    metric = float((c * np.conj(complex(U5[1]) + complex(U5[4]))).real)
    report("4 orbit certificate (ii): skip-pair arm minima + metric",
           q[0] > 0.64 and q[1] > 0.94 and abs(metric - 0.0777592874) < 1e-8,
           f"q={q[0]:.6f},{q[1]:.6f} metric={metric:.8f}")


K1 = 3.0 / 4.0 ** (4.0 / 3.0)


def ray_safe(a, b):
    return a >= 0 and (b >= 0 or 256 * a ** 3 >= 27 * b ** 4 - 1e-12)


def section5():
    ok = True
    for _ in range(2000):
        a = rng.uniform(-2, 2)
        b = rng.uniform(-2, 2)
        t = np.linspace(0, 6, 30001)
        num = bool(np.min(t ** 4 + b * t + a) >= -1e-12)
        if num != ray_safe(a, b) and abs(a - K1 * max(-b, 0) ** (4 / 3)) > 1e-6:
            ok = False
    report("5 exact origin criterion (semialgebraic form)", ok)
    okJ = True
    unc = 0
    tested = 0
    for _ in range(150):
        qv = rng.uniform(0, 1)
        branch = rng.integers(0, 2)
        r1, r2 = (1.0, qv) if branch == 0 else (qv, 1.0)
        b1 = r1 * np.exp(1j * rng.uniform(0, 2 * np.pi))
        b2 = r2 * np.exp(1j * rng.uniform(0, 2 * np.pi))
        J = sum(1 for j in range(5)
                if ray_safe(float((b1 * U5[j]).real), float((b2 * U5[j] ** 2).real)))
        if J > 3:
            okJ = False
        tested += 1
        if J >= 2:
            continue
        closed = False
        for k in range(5):
            psi = np.exp(1j * np.pi * (2 * k + 1) / 5)
            for r in np.linspace(0.1, 0.9, 33):
                h = r * psi
                good = True
                for j in (k, (k + 1) % 5):
                    u = U5[j]
                    tt = np.linspace(0, 1, 1501)
                    w = h + tt * (6.3 * u - h)
                    if np.min((w ** 5 + b2 * w * w + b1 * w).real) < -1e-12:
                        good = False
                        break
                if good:
                    closed = True
                    break
            if closed:
                break
        if not closed:
            unc += 1
    report("5 #J <= 3 always", okJ)
    report("5 O u B covers random core points", unc == 0, f"uncovered {unc}/{tested}")


def section6():
    ok = True
    for n in (7, 9):
        K = (n - 1) // 2
        for _ in range(30):
            b = rng.standard_normal(K) + 1j * rng.standard_normal(K)
            poly = np.zeros(n + 1, dtype=complex)
            poly[0] = 1
            for k in range(1, K + 1):
                poly[n - k] = b[k - 1]
            dp = np.array([(n - i) * poly[i] for i in range(n)])
            P = np.polynomial.polynomial.Polynomial(poly[::-1])
            if abs(sum(P(c) for c in np.roots(dp))) > 1e-8:
                ok = False
    report("6 degree-general trace = 0 (n = 7, 9)", ok)
    bad = 0
    for _ in range(20):
        n, K = 6, 3
        b = rng.standard_normal(K) + 1j * rng.standard_normal(K)
        poly = np.zeros(n + 1, dtype=complex)
        poly[0] = 1
        for k in range(1, K + 1):
            poly[n - k] = b[k - 1]
        dp = np.array([(n - i) * poly[i] for i in range(n)])
        P = np.polynomial.polynomial.Polynomial(poly[::-1])
        if abs(sum(P(c) for c in np.roots(dp))) > 1e-6:
            bad += 1
    report("6 sharpness at n = 6, K = 3", bad >= 18, f"nonzero {bad}/20")
    K = 3 * 2 ** (2 / 3) / 5 ** (5 / 3)
    tt = np.linspace(0, 3, 200001)
    worst = max(abs(np.min(tt ** 5 - A2 * tt ** 2) + K * A2 ** (5 / 3))
                for A2 in (0.3, 1.0, 2.7))
    report("6 constant K = 3*2^(2/3)/5^(5/3)", worst < 1e-6, f"dev={worst:.1e}")


def main():
    section1()
    section2()
    section3()
    section4()
    section5()
    section6()
    print()
    if FAILURES:
        print("FAIL:", FAILURES)
        return 1
    print("PASS: all sections")
    return 0


if __name__ == "__main__":
    sys.exit(main())
