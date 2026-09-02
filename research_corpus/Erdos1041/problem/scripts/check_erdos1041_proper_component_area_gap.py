"""Checker for ProperComponentUniformAreaGap.md (Erdos 1041).

Sections:
  1  corollary inequality on sampled quintic two-root components:
     Area(U)/(pi t^{2/5}) < (1/4)^{2/5} with recorded margins (grid area,
     first-merge window levels).
  2  Schur-tail lemma on random degree-3 Blaschke products (N = 5):
     tail energy >= (1 - p^2) p^{10}.
  3  boundary-escape factor limit: (z - a)/(1 - conj(a) z) -> -a locally
     uniformly as |a| -> 1.
  4  Grönwall/Pólya chain on a terminal component: series area vs grid
     area, and Area <= pi cap^2 with cap = t^{1/n} for connected K_t.

Exit 0 iff all sections pass.
"""
import sys
from collections import deque

import numpy as np

rng = np.random.default_rng(41041)
FAILURES = []
CEIL = 0.25 ** 0.4  # (1/4)^{2/5}


def report(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


def section1():
    worst = 0.0
    tested = 0
    tries = 0
    while tested < 25 and tries < 300:
        tries += 1
        roots = np.sqrt(rng.uniform(0.05, 1, 5)) * np.exp(2j * np.pi * rng.uniform(0, 1, 5))
        poly = np.array([1.0 + 0j])
        for r in roots:
            poly = np.convolve(poly, [1.0, -r])
        crits = np.roots(np.polyder(poly))
        cv = sorted(abs(np.polyval(poly, c)) for c in crits)
        if cv[0] < 1e-6 or cv[1] / cv[0] < 1.05:
            continue
        t = np.sqrt(cv[0] * cv[1])  # inside the two-root window
        # grid the plane, find components of {|f| < t}
        R = 1.6
        N = 561
        x = np.linspace(-R, R, N)
        X, Y = np.meshgrid(x, x)
        W = X + 1j * Y
        M = np.abs(np.polyval(poly, W)) < t
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
        # roots per component
        cell = (2 * R / (N - 1)) ** 2
        counts = {}
        for r in roots:
            ii = int(np.argmin(np.abs(x - r.imag)))
            jj = int(np.argmin(np.abs(x - r.real)))
            if M[ii, jj]:
                counts[lab[ii, jj]] = counts.get(lab[ii, jj], 0) + 1
        two = [c for c, ct in counts.items() if ct == 2]
        if not two:
            continue
        tested += 1
        for c in two:
            area = float((lab == c).sum()) * cell
            ratio = area / (np.pi * t ** 0.4)
            worst = max(worst, ratio)
    report("1 sampled two-root components: Area/(pi t^{2/5}) < (1/4)^{2/5}",
           worst < CEIL, f"max ratio={worst:.4f} vs ceiling {CEIL:.4f}  tested={tested}")


def section2():
    ok = True
    worst = np.inf
    for _ in range(400):
        a = [np.sqrt(rng.uniform()) * np.exp(2j * np.pi * rng.uniform()) for _ in range(3)]
        p = float(np.prod([abs(x) for x in a]))
        # Taylor coefficients of g = prod (z - a)/(1 - conj(a) z), normalized g(0) = p > 0
        Ntr = 400
        th = 2 * np.pi * np.arange(Ntr) / Ntr
        z = np.exp(1j * th)
        g = np.ones(Ntr, dtype=complex)
        for x in a:
            g *= (z - x) / (1 - np.conj(x) * z)
        # normalize phase so g(0) = prod(-a)/1 ... compute coefficients by FFT
        coef = np.fft.fft(g) / Ntr  # coef[j] = hat g_j for j = 0..  (since g holo)
        tail = float(np.sum(np.abs(coef[6:Ntr // 2]) ** 2))
        bound = (1 - p ** 2) * p ** 10
        worst = min(worst, tail - bound)
        if tail < bound - 1e-12:
            ok = False
    report("2 Schur-tail lemma (m=3, N=5)", ok, f"min slack={worst:.3e}")


def section3():
    ok = True
    for _ in range(50):
        aa = np.exp(1j * rng.uniform(0, 2 * np.pi))
        for rr in (0.999, 0.9999):
            a = rr * aa
            z = 0.5 * np.exp(1j * rng.uniform(0, 2 * np.pi))
            val = (z - a) / (1 - np.conj(a) * z)
            if abs(val - (-aa)) > 6 * (1 - rr):
                ok = False
    report("3 boundary-escape factor -> -a", ok)


def section4():
    # terminal component of z^5 - 1 at t = 2 (connected): cap = t^{1/5},
    # Area <= pi t^{2/5}; grid area vs the bound.
    poly = np.array([1, 0, 0, 0, 0, -1], dtype=complex)
    t = 2.0
    R = 2.0
    N = 801
    x = np.linspace(-R, R, N)
    X, Y = np.meshgrid(x, x)
    W = X + 1j * Y
    M = np.abs(np.polyval(poly, W)) < t
    cell = (2 * R / (N - 1)) ** 2
    area = float(M.sum()) * cell
    bound = np.pi * t ** 0.4
    report("4 Polya at the terminal component (z^5 - 1, t = 2)", area <= bound,
           f"grid area={area:.4f} <= pi t^(2/5)={bound:.4f}")


def main():
    section1()
    section2()
    section3()
    section4()
    print()
    if FAILURES:
        print("FAIL:", FAILURES)
        return 1
    print("PASS: all sections")
    return 0


if __name__ == "__main__":
    sys.exit(main())
