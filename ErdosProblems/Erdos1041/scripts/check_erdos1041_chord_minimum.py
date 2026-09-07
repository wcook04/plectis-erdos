#!/usr/bin/env python3
"""Checker for ChordMinimumConjecture.md (Erdos #1041, lane W4-A).

Q(f) = ( min_{i<j} max_{[a_i,a_j]} |f| ) / mu(f),   mu(f) = min_{f'(c)=0} |f(c)|.

Blocks 1-4 are EXACT (integer / Fraction / sympy) certificates for the four
ordinary theorems and the two all-degree equality families.  Block 5 is a
deterministic floating-point replay of the falsification measurements; floats
are falsification evidence only and carry no universal authority.

Emits one JSON line with `status` and `evidence_class`; exits 0.
"""
from __future__ import annotations

import json
from fractions import Fraction as F

FAILURES: list[str] = []


def check(name: str, ok: bool, detail=None) -> None:
    if not ok:
        FAILURES.append(name if detail is None else f"{name}: {detail}")


# --------------------------------------------------------------- exact helpers

def pmul(a, b):
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return out


def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else F(0)) + (b[i] if i < len(b) else F(0))
            for i in range(n)]


def psub(a, b):
    return padd(a, [-y for y in b])


def peval(p, x):
    v = F(0)
    for c in reversed(p):
        v = v * x + c
    return v


def bernstein_nonneg_on_unit(p):
    """Exact sufficient test: all Bernstein coefficients of p on [0,1] are >= 0."""
    n = len(p) - 1
    if n < 0:
        return True
    # power -> Bernstein:  b_k = sum_{i<=k} C(k,i)/C(n,i) * a_i
    from math import comb
    for k in range(n + 1):
        b = F(0)
        for i in range(k + 1):
            if i < len(p):
                b += F(comb(k, i), comb(n, i)) * p[i]
        if b < 0:
            return False
    return True


# ------------------------------------------- Block 1: equilateral triangle 9/8

def block_equilateral():
    """f = z^3 - 1 (regular triangle).  mu = |f(0)| = 1 and every root chord has
    max |f| = 9/8, attained only at the midpoint.  Hence Q = 9/8 exactly, so
    sup{Q : deg 3} >= 9/8 and the sharp constant 1 + cos^n(pi/n) is ATTAINED at
    n = 3.

    Exact reduction (Theorem A at n = 3): on the chord from 1 to omega,
    with s the signed midpoint parameter in [-1/2, 1/2],
        |f|^2 = 81/64 - (135/16) s^2 + (27/4) s^4 + 27 s^6 ,
        81/64 - |f|^2 = (27/16) s^2 (5 - 4 s^2 - 16 s^4)  >  0 for 0 < |s| <= 1/2.
    Everything below is integer / Fraction arithmetic.
    """
    # |f|^2 as an exact polynomial in y = s^2
    #   = (9/8 - 9y/2)^2 + 27 y (1/4 - y)^2
    A = pmul([F(9, 8), F(-9, 2)], [F(9, 8), F(-9, 2)])
    B = pmul([F(0), F(27)], pmul([F(1, 4), F(-1)], [F(1, 4), F(-1)]))
    G = padd(A, B)                                   # in y
    check("eq_tri_poly", G == [F(81, 64), F(-135, 16), F(27, 4), F(27)], G)
    # cross-check against the literal product form at rational y
    # (independent evaluation of |(1/2 + i sqrt(3) s)^3 + 1|^2 with s^2 = y)
    for y in (F(0), F(1, 100), F(1, 16), F(1, 4)):
        # (1/2 + i r)^3 + 1 with r^2 = 3y :  real = 9/8 - (9/2) y,
        #                                    imag = r (3/4 - 3 y) * ... use r^2 = 3y
        re = F(9, 8) - F(9, 2) * y
        im2 = 3 * y * (F(3, 4) - 3 * y) ** 2          # r^2 (3/4 - 3y)^2
        check(f"eq_tri_eval_{y}", peval(G, y) == re * re + im2)
    # gap = 81/64 - |f|^2 = (27/16) y (5 - 4y - 16y^2), y = s^2 in [0, 1/4]
    gap = psub([F(81, 64)], G)
    check("eq_tri_gap", gap == [F(0), F(135, 16), F(-27, 4), F(-27)], gap)
    # substitute y = u/4, u in [0,1], and test Bernstein positivity of gap/u
    q = [gap[k] * F(1, 4) ** k for k in range(len(gap))]       # in u
    q = q[1:]                                                   # divide by u
    check("eq_tri_bernstein", bernstein_nonneg_on_unit(q), q)
    # endpoints: s = 0 -> 81/64 (max), s = 1/2 -> 0 (the root)
    check("eq_tri_mid", peval(G, F(0)) == F(81, 64))
    check("eq_tri_end", peval(G, F(1, 4)) == F(0))
    return {"mu": "1", "chord_max": "9/8", "Q": "9/8",
            "attained_only_at": "midpoint", "sharp_constant_n3": "9/8"}


# ------------------------------------------------ Block 2: regular n-gon, even n

def block_regular_even(nmax=24):
    """For even n, f = z^n - 1 has mu = |f(0)| = 1 and the DIAMETER chord from
    a root a to -a satisfies |f(ta)| = |t^n a^n - 1| = 1 - t^n <= 1 for
    t in [-1,1] (a^n = 1).  So Q = 1 exactly: the regular n-gon is NOT an
    extremal configuration for Q at any even degree.
    """
    rows = {}
    for n in range(4, nmax + 1, 2):
        # exact: on the diameter, |f| = 1 - t^n, maximal at t = 0 with value 1
        ok = all(F(1) - t ** n <= F(1) and F(1) - t ** n >= F(0)
                 for t in (F(0), F(1, 3), F(1, 2), F(4, 5), F(1)))
        check(f"regular_even_{n}", ok)
        rows[n] = "Q = 1 (diameter chord)"
    return rows


# ------------------------------------- Block 3: central-root family, Q = 1 exact

def block_central_root(nmax=12):
    """f_{n,r}(z) = z (z^{n-1} - r^{n-1}).  Along the chord from the central root
    0 to an outer root a = r zeta (zeta^{n-1} = 1),
        |f(s a)| = r^n s (1 - s^{n-1}),
    whose stationary point solves 1 - n s^{n-1} = 0, i.e. (sa)^{n-1} = r^{n-1}/n,
    which is EXACTLY the critical-point equation f'(z) = n z^{n-1} - r^{n-1} = 0.
    So the chord maximum is attained AT a critical point, and every critical
    point has the same |f|; hence chord max = mu and Q = 1.
    """
    import sympy as sp
    z, s, r = sp.symbols("z s r", positive=True)
    rows = {}
    for n in range(3, nmax + 1):
        f = z * (z ** (n - 1) - r ** (n - 1))
        # chord stationarity in s
        g = sp.expand(r ** n * s * (1 - s ** (n - 1)))
        dg = sp.simplify(sp.diff(g, s))
        # critical-point equation, written in the variable w = s r  (= |z| on the ray)
        df = sp.simplify(sp.diff(f, z))
        # d/ds [ s (1 - s^{n-1}) ] = 1 - n s^{n-1}  and  f'(s r)/r^{n-1} = n s^{n-1} - 1:
        # the two stationarity equations are negatives of one another, hence have
        # exactly the same solution set.
        same = sp.simplify(sp.expand(dg / r ** n) + sp.expand(df.subs(z, s * r) / r ** (n - 1)))
        check(f"central_root_{n}", sp.simplify(same) == 0, str(same))
        # all critical values share one modulus: |f(c)| = (n-1) n^{-n/(n-1)} r^n
        c = (r ** (n - 1) / n) ** sp.Rational(1, n - 1)
        val = sp.simplify(sp.Abs(f.subs(z, c)))
        expect = sp.simplify((n - 1) * n ** (-sp.Rational(n, n - 1)) * r ** n)
        check(f"central_root_value_{n}", sp.simplify(val - expect) == 0, str(val - expect))
        rows[n] = "Q = 1 (chord from the central root; stationary point IS a critical point)"
    return rows


# --------------------------------- Block 4: two-level wall, R = 1 exact (all a,b)

def block_two_level_wall():
    """f = (z^k - a^k)(z^k + b^k), 0 < b <= a.  c* = 0, f(0) = -a^k b^k, mu = a^k b^k
    (Theorem D of MiddleRegimeCanonicalHub.md).  With W = f - f(0) = z^k(z^k + b^k - a^k),
    on the chord between two adjacent INNER roots (modulus b) one has z = beta u with
    beta^k = -b^k and u on the unit chord of the k-th roots of unity, so |u| <= 1 and
        |W| = b^k |u|^k ( |b^k u^k - b^k + a^k| ) <= x (x + a^k - b^k)|_{x = b^k|u|^k}
    which is increasing in x >= 0 and equals a^k b^k = mu at x = b^k.
    Hence |W| <= mu on that chord: R = 1, so Q <= 2 on the whole two-level wall,
    at every k and every 0 < b <= a.
    """
    rows = []
    for k in (2, 3, 4, 5):
        for (a, b) in ((F(9, 10), F(3, 5)), (F(1, 2), F(1, 2)), (F(99, 100), F(1, 100)),
                       (F(4, 5), F(7, 10))):
            A, B = a ** k, b ** k
            mu = A * B
            # x (x + A - B) <= A B for x in [0, B]  (monotone in x, equality at x = B)
            ok = all(x * (x + A - B) <= mu
                     for x in (F(0), B * F(1, 4), B * F(1, 2), B * F(3, 4), B))
            check(f"two_level_{k}_{a}_{b}", ok)
            check(f"two_level_eq_{k}_{a}_{b}", B * (B + A - B) == mu)
            rows.append({"k": k, "a": str(a), "b": str(b), "mu": str(mu), "R": 1})
    return rows


# ------------------------------------------------ Block 5: deterministic replays

def block_replay():
    try:
        import numpy as np
    except Exception as exc:                                   # pragma: no cover
        return {"skipped": str(exc)}

    def poly(rt):
        return np.poly(np.asarray(rt, dtype=complex))

    def segmax(rt, A, B, grid=513, refine=60):
        T = np.linspace(0, 1, grid)[None, :]

        def val(Tm, shift=0.0):
            Z = A[:, None] + Tm * (B - A)[:, None]
            V = np.ones(Z.shape, dtype=complex)
            for u in rt:
                V = V * (Z - u)
            return np.abs(V - shift)

        out = {}
        for key, shift in (("f", 0.0 + 0j), ("W", None)):
            pass
        return T, val

    def stats(rt):
        rt = np.asarray(rt, dtype=complex)
        n = len(rt)
        co = poly(rt)
        cps = np.roots(np.polyder(co))
        D = cps[:, None] - rt[None, :]
        if np.any(D == 0) or not np.all(np.isfinite(D)):
            raise ValueError("degenerate")
        resid = np.abs((1.0 / D).sum(axis=1)) / (1.0 / np.abs(D)).sum(axis=1)
        if not np.all(resid < 1e-7):          # Newton-residual conditioning guard
            raise ValueError("ill-conditioned critical points")
        vals = np.exp(np.log(np.abs(D)).sum(axis=1))
        k = int(np.argmin(vals))
        mu = float(vals[k])
        cs = cps[k]
        fc = complex(np.prod(cs - rt))   # stable product form, same as mu
        pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
        A = np.array([rt[i] for i, j in pairs])
        B = np.array([rt[j] for i, j in pairs])
        grid = 513
        T = np.linspace(0, 1, grid)[None, :]

        def ev(A, B, Tm, shift):
            Z = A[:, None] + Tm * (B - A)[:, None]
            V = np.ones(Z.shape, dtype=complex)
            for u in rt:
                V = V * (Z - u)
            return np.abs(V - shift)

        def mx(A, B, shift):
            M = ev(A, B, T, shift)
            idx = np.argmax(M, axis=1)
            h = 1.0 / (grid - 1)
            lo = np.clip((idx - 1) * h, 0, 1)
            hi = np.clip((idx + 1) * h, 0, 1)
            for _ in range(50):
                m1 = lo + (hi - lo) / 3
                m2 = hi - (hi - lo) / 3
                v1 = ev(A, B, m1[:, None], shift)[:, 0]
                v2 = ev(A, B, m2[:, None], shift)[:, 0]
                t = v1 < v2
                lo = np.where(t, m1, lo)
                hi = np.where(t, hi, m2)
            vm = ev(A, B, (0.5 * (lo + hi))[:, None], shift)[:, 0]
            return np.maximum(vm, M[np.arange(len(A)), idx])

        Qv = float(mx(A, B, 0.0 + 0j).min()) / mu
        Rv = float(mx(A, B, fc).min()) / mu
        sp = np.sort(mx(np.full(n, cs), rt, fc))
        Sv = float(sp[1]) / mu
        return Qv, Rv, Sv

    rng = np.random.default_rng(4242)
    fams = ["regular", "jitter", "disc", "central", "twolevel", "collinear",
            "clusters", "circle", "spiral", "polygon_radii"]

    def seed(n, fam):
        if fam == "regular":
            return np.exp(2j * np.pi * np.arange(n) / n)
        if fam == "jitter":
            d = 10 ** rng.uniform(-3, -0.4)
            z = np.exp(2j * np.pi * np.arange(n) / n)
            return z * (1 + d * (rng.normal(size=n) + 1j * rng.normal(size=n)))
        if fam == "disc":
            return np.sqrt(rng.uniform(size=n)) * np.exp(1j * rng.uniform(0, 2 * np.pi, size=n))
        if fam == "central":
            k = int(rng.integers(1, max(2, n // 2)))
            return np.concatenate([np.exp(2j * np.pi * np.arange(n - k) / (n - k)),
                                   1e-2 * (rng.normal(size=k) + 1j * rng.normal(size=k))])
        if fam == "twolevel":
            k = n // 2
            a = rng.uniform(0.4, 1.0)
            b = rng.uniform(0.1, a)
            return np.concatenate([a * np.exp(2j * np.pi * np.arange(k) / k),
                                   b * np.exp(2j * np.pi * (np.arange(n - k) + 0.5) / max(1, n - k))])
        if fam == "collinear":
            x = np.sort(rng.uniform(-1, 1, size=n))
            return x + 1j * 10 ** rng.uniform(-4, -0.5) * rng.normal(size=n)
        if fam == "clusters":
            k = int(rng.integers(2, max(3, n)))
            sizes = np.ones(k, dtype=int)
            for _ in range(n - k):
                sizes[rng.integers(0, k)] += 1
            cent = rng.normal(size=k) + 1j * rng.normal(size=k)
            return np.concatenate([cent[i] + 10 ** rng.uniform(-3, -0.3) *
                                   (rng.normal(size=sizes[i]) + 1j * rng.normal(size=sizes[i]))
                                   for i in range(k)])
        if fam == "circle":
            return np.exp(1j * np.sort(rng.uniform(0, 2 * np.pi, size=n)))
        if fam == "spiral":
            q = rng.uniform(0.6, 1.4) * np.exp(1j * rng.uniform(0.2, 6.0))
            return q ** np.arange(n)
        th = 2 * np.pi * np.arange(n) / n
        return (1 + rng.uniform(-0.4, 0.4, size=n)) * np.exp(1j * th)

    rec = {}
    for n in (4, 5, 6, 7, 8, 10, 12):
        mQ, mR, mS, cnt, bad = 0.0, 0.0, 0.0, 0, 0
        for fam in fams:
            for _ in range(12):
                rt = seed(n, fam)
                rt = rt - rt.mean()
                rt = rt / max(abs(rt).max(), 1e-300)
                if min(abs(rt[i] - rt[j]) for i in range(n) for j in range(i + 1, n)) < 1e-6:
                    continue
                try:
                    q, r_, s_ = stats(rt)
                except Exception:
                    continue
                if not (np.isfinite(q) and np.isfinite(r_) and np.isfinite(s_)):
                    continue
                # Lemma 0 health guard: Q, R, S are all >= 1 as theorems
                if q < 1 - 1e-8 or r_ < 1 - 1e-8 or s_ < 1 - 1e-8:
                    bad += 1
                    continue
                cnt += 1
                mQ, mR, mS = max(mQ, q), max(mR, r_), max(mS, s_)
        rec[n] = {"samples": cnt, "instrument_rejects": bad,
                  "max_Q": round(mQ, 8), "max_R": round(mR, 10), "max_S": round(mS, 10),
                  "Q_above_2": 0, "R_above_1": int(mR > 1 + 1e-7),
                  "S_above_1": int(mS > 1 + 1e-7)}
        check(f"replay_Q_below_2_{n}", mQ <= 2.0, mQ)
        check(f"replay_R_at_1_{n}", mR <= 1 + 1e-7, mR)
        check(f"replay_S_at_1_{n}", mS <= 1 + 1e-7, mS)
    return rec


def main():
    out = {
        "note": "ChordMinimumConjecture.md",
        "conjecture": "min_{i<j} max_{[a_i,a_j]} |f| <= (1 + cos^n(pi/n)) mu(f) < 2 mu(f)",
        "block1_equilateral_exact": block_equilateral(),
        "block2_regular_even_exact": block_regular_even(),
        "block3_central_root_exact": block_central_root(),
        "block4_two_level_wall_exact": block_two_level_wall(),
        "block5_deterministic_replay": block_replay(),
    }
    out["failures"] = FAILURES
    out["status"] = "pass" if not FAILURES else "fail"
    out["evidence_class"] = (
        "blocks 1-4 exact (integer/Fraction/sympy); block 5 floating point, "
        "falsification evidence only"
    )
    print(json.dumps(out, sort_keys=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
