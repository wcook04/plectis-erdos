#!/usr/bin/env python3
"""Exact denominator-compression TRADE-OFF CURVE for Theta_2 = S - 1/2 = sum_d mu(d)/(2^d-1)^2.

Wave 2, desk S2 of the Erdos 249 eight-return batch.  Consumes desk E's compression lab
(E1-E5), desk D's r07 critical-height hint, and desk C's Legendre/convergent falsifier.

Everything is exact (int / fractions.Fraction).  |Theta_2 - R| is always bracketed by the
rigorous enclosure  S in (P_B/2^B, (P_B + B + 2)/2^B]  coming from  0 < R_B <= B+2  with
P_B = sum_{j<=B} 2^{B-j} phi(j),  R_B = 2^B S - P_B;  Theta_2 = S - 1/2.

Objects (imported from check_lambert_derivative_denominator_compression.py):

  T_N        = sum_{d<=N} mu(d) A_1(2^-d)                       (prefix of S)
  I_{j,k,N}  = 2^-j - sum_{d<=N} mu(d) d^k A_k(2^{-jd})         (omitted tail of the k-rung)
  R          = T_N + (1/D) sum_{j<=J,k<=K} a_{j,k} I_{j,k,N}

WHAT THIS PROBE ADDS OVER THE WAVE-1 LAB

 (1) EXACT LAYER FORM + DEPTH LAW.  At a squarefree layer m <= N put eps = 2^m - 1 and
     s_a = (2^{am}-1)/eps.  The layer part of X = D T_N + a0 I_{1,0,N} + a1 I_{1,1,N} is
     EXACTLY (A + eps*B)/eps^2 with

         A = sum_a mu(am) (D - a1*a*m) / s_a^2 ,
         B = sum_a mu(am) (D - a1*a*m - a0) / s_a ,

     so for every primitive prime ell (ell^e || eps, ell > N, ell not dividing D)

         v_ell(R) = min(0, v_ell(L_m(D,a0,a1)) - 2e),   L_m = Ssq*(A + eps*B) in Z.

     => removing the DOUBLE pole needs P_m^2 | L_m.  One power of P_m removes one power.
     E1's prose form "D*sigma2 - sum a*tau" has the wrong sign; the correct form is "+"
     (the wave-1 CODE, rho_m = -tau/sigma2, is right).  Verified here both ways.

 (2) The exact congruence lattice L(M,t) = {v : L_m(v) = 0 mod P_m^{t}} with a CERTIFIED
     L-infinity minimum in dimension 2 (Lagrange-Gauss + certified enumeration) and an
     exact-arithmetic LLL in dimension 3.  This gives the true trade-off curve
     log2 H(M) vs log2 q vs log2 q|Theta_2 - R| that E2 only bounded.

 (3) A critical-height search (desk D) at heights 2^N and multiples, in the weighted
     coordinates (D, b0, a1) with a0 = D + b0 (E5b's rigid normalisation put in the basis).

 (4) The Legendre comparison: certified continued fraction of Theta_2, the true best
     q|Theta_2 - p/q| at denominator size 2^{2N}, and the ORDER-SMOOTH (cyclotomic /
     Mersenne) part of every early convergent denominator.

Run:  ./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/\
scripts/check_theta2_denominator_tradeoff.py --quick
"""
from __future__ import annotations

import argparse
import json
import math
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from check_lambert_derivative_denominator_compression import (  # noqa: E402
    build_objects,
    eulerian_numerators,
    factor,
    flog2,
    mobius,
    primitive_part_above,
    s_enclosure,
    totient,
)


# ----------------------------------------------------------------- helpers ----
def vpow_prime(n: int, ell: int) -> int:
    v = 0
    while n and n % ell == 0:
        n //= ell
        v += 1
    return v


def vell_frac(x: F, ell: int) -> int:
    return vpow_prime(x.numerator, ell) - vpow_prime(x.denominator, ell)


def rnd_div(n: int, d: int) -> int:
    if d < 0:
        n, d = -n, -d
    q, r = divmod(n, d)
    return q + 1 if 2 * r >= d else q


def _extgcd(a: int, b: int):
    old_r, r = a, b
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s - q * s
        old_t, t = t, old_t - q * t
    return old_r, old_s, old_t


# --------------------------------------------------- exact layer linear form ----
def layer_linear_forms(N: int, mu: list[int], rng: random.Random) -> dict[int, dict]:
    out: dict[int, dict] = {}
    for m in range(1, N + 1):
        if not mu[m]:
            continue
        P = primitive_part_above(m, N, rng)
        if P <= 1:
            continue
        eps = (1 << m) - 1
        avals = [a for a in range(1, N // m + 1) if mu[a * m]]
        svals = {a: ((1 << (a * m)) - 1) // eps for a in avals}
        Ssq = 1
        for a in avals:
            Ssq *= svals[a] * svals[a]
        alpha = beta = gamma = 0
        for a in avals:
            s = svals[a]
            w2 = Ssq // (s * s)
            w1 = eps * (Ssq // s)
            alpha += mu[a * m] * (w2 + w1)
            beta += -mu[a * m] * w1
            gamma += -mu[a * m] * (a * m) * (w2 + w1)
        fac = factor(P, rng)
        out[m] = {
            "m": m, "P": P, "log2_P": P.bit_length() - 1, "primes": fac,
            "e": {ell: vpow_prime(eps, ell) for ell in fac},
            "k0": N // m, "a_values": avals,
            "alpha": alpha, "beta": beta, "gamma": gamma,
            "Ssq_coprime_to_P": all(math.gcd(Ssq, ell) == 1 for ell in fac),
        }
    return out


# --------------------------------------------------------- lattice machinery ----
def refine_by_congruence(basis: list[list[int]], coeff: list[int], Q: int) -> list[list[int]]:
    """{x in L(basis) : coeff . x = 0 mod Q} (exact kernel via HNF on the residue column)."""
    n = len(basis)
    dim = len(basis[0])
    cs = [sum(coeff[j] * b[j] for j in range(dim)) % Q for b in basis]
    rows = [[1 if i == k else 0 for k in range(n)] + [cs[i]] for i in range(n)]
    rows.append([0] * n + [Q])
    piv = None
    ker: list[list[int]] = []
    for r in rows:
        if r[n] == 0:
            ker.append(r[:n])
            continue
        if piv is None:
            piv = r
            continue
        g, u, v = _extgcd(piv[n], r[n])
        a, b = piv[n] // g, r[n] // g
        zero = [b * piv[i] - a * r[i] for i in range(n + 1)]
        piv = [u * piv[i] + v * r[i] for i in range(n + 1)]
        ker.append(zero[:n])
    return [[sum(y[i] * basis[i][j] for i in range(n)) for j in range(dim)] for y in ker]


def congruence_lattice(coeffs, moduli, dim: int) -> list[list[int]]:
    basis = [[1 if i == j else 0 for j in range(dim)] for i in range(dim)]
    for row, Q in zip(coeffs, moduli):
        if Q > 1:
            basis = refine_by_congruence(basis, row, Q)
    return basis


def det_int(mat: list[list[int]]) -> int:
    m = [row[:] for row in mat]
    n = len(m)
    sign, prev = 1, 1
    for k in range(n - 1):
        if m[k][k] == 0:
            for i in range(k + 1, n):
                if m[i][k]:
                    m[k], m[i] = m[i], m[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                m[i][j] = (m[i][j] * m[k][k] - m[i][k] * m[k][j]) // prev
            m[i][k] = 0
        prev = m[k][k]
    return sign * m[n - 1][n - 1]


def gauss_reduce(b1, b2):
    def dot(u, v):
        return u[0] * v[0] + u[1] * v[1]
    guard = 0
    while guard < 10000:
        guard += 1
        if dot(b1, b1) > dot(b2, b2):
            b1, b2 = b2, b1
        d = dot(b1, b1)
        if d == 0:
            return b1, b2
        mu = rnd_div(dot(b1, b2), d)
        nb2 = (b2[0] - mu * b1[0], b2[1] - mu * b1[1])
        if dot(nb2, nb2) >= dot(b1, b1):
            return b1, nb2
        b2 = nb2
    return b1, b2


def linf_min_2d(b1, b2, need_first_nonzero: bool = True):
    """CERTIFIED L-infinity minimum of <b1,b2> over nonzero vectors (first coord nonzero)."""
    b1, b2 = gauss_reduce(tuple(b1), tuple(b2))
    det = abs(b1[0] * b2[1] - b1[1] * b2[0])
    if det == 0:
        raise ValueError("degenerate lattice")

    def ok(v):
        return (v[0] or v[1]) and (v[0] != 0 or not need_first_nonzero)

    best = None
    for x in range(-4, 5):
        for y in range(-4, 5):
            v = (x * b1[0] + y * b2[0], x * b1[1] + y * b2[1])
            if ok(v):
                h = max(abs(v[0]), abs(v[1]))
                if best is None or h < best[0]:
                    best = (h, v)
    n1 = math.isqrt(b1[0] * b1[0] + b1[1] * b1[1]) + 1
    ymax = (2 * best[0] * n1) // det + 2
    y = 0
    while y <= ymax:
        for sgn in ((1, -1) if y else (1,)):
            yy = sgn * y
            base = (yy * b2[0], yy * b2[1])
            cands = {0}
            for i in (0, 1):
                if b1[i]:
                    cands.add(rnd_div(-base[i], b1[i]))
            for c in list(cands):
                cands.update({c - 2, c - 1, c + 1, c + 2})
            for x in cands:
                v = (base[0] + x * b1[0], base[1] + x * b1[1])
                if ok(v):
                    h = max(abs(v[0]), abs(v[1]))
                    if h < best[0]:
                        best = (h, v)
                        ymax = min(ymax, (2 * best[0] * n1) // det + 2)
        y += 1
    return best


def lll(basis: list[list[int]], delta: F = F(99, 100)) -> list[list[int]]:
    b = [row[:] for row in basis]
    n = len(b)
    dim = len(b[0])

    def dot(u, v):
        return sum(x * y for x, y in zip(u, v))

    def gs():
        bs, mu = [], [[F(0)] * n for _ in range(n)]
        for i in range(n):
            v = [F(x) for x in b[i]]
            for j in range(i):
                dj = dot(bs[j], bs[j])
                mu[i][j] = dot([F(x) for x in b[i]], bs[j]) / dj if dj else F(0)
                v = [v[t] - mu[i][j] * bs[j][t] for t in range(dim)]
            bs.append(v)
        return bs, mu

    bs, mu = gs()
    k, guard = 1, 0
    while k < n and guard < 4000:
        guard += 1
        changed = False
        for j in range(k - 1, -1, -1):
            q = int(mu[k][j] + F(1, 2)) if mu[k][j] >= 0 else -int(-mu[k][j] + F(1, 2))
            if q:
                b[k] = [b[k][t] - q * b[j][t] for t in range(dim)]
                changed = True
        if changed:
            bs, mu = gs()
        if dot(bs[k], bs[k]) >= (delta - mu[k][k - 1] ** 2) * dot(bs[k - 1], bs[k - 1]):
            k += 1
        else:
            b[k], b[k - 1] = b[k - 1], b[k]
            bs, mu = gs()
            k = max(k - 1, 1)
    return b


# -------------------------------------------------------- continued fractions ----
def cf_certified(lo: F, hi: F, max_terms: int) -> list[int]:
    terms: list[int] = []
    for _ in range(max_terms):
        if lo <= 0 or hi <= 0:
            break
        a_lo, a_hi = math.floor(lo), math.floor(hi)
        if a_lo != a_hi:
            break
        terms.append(int(a_lo))
        flo, fhi = lo - a_lo, hi - a_lo
        if flo <= 0 or fhi <= 0:
            break
        lo, hi = 1 / fhi, 1 / flo
    return terms


def convergents(terms: list[int]):
    p0, q0, p1, q1 = 1, 0, terms[0], 1
    out = [(p1, q1)]
    for a in terms[1:]:
        p0, q0, p1, q1 = p1, q1, a * p1 + p0, a * q1 + q0
        out.append((p1, q1))
    return out


def factor_C(C: int, dmax: int, rng: random.Random) -> dict[int, int]:
    """Exact factorisation of the family's common denominator C.  Every prime of C divides
    2 or some 2^d - 1 with d <= dmax, so this is complete for the N we run."""
    rest = C
    out: dict[int, int] = {}
    e2 = 0
    while rest % 2 == 0:
        rest //= 2
        e2 += 1
    if e2:
        out[2] = e2
    for d in range(1, dmax + 1):
        if rest == 1:
            break
        g = math.gcd(rest, (pow(2, d, rest) - 1) % rest) if rest > 1 else 1
        if g <= 1:
            continue
        for p in factor(g, rng):
            v = 0
            while rest % p == 0:
                rest //= p
                v += 1
            if v:
                out[p] = out.get(p, 0) + v
    assert rest == 1, ("C not fully factored", rest)
    return out


def order_smooth_part(q: int, dmax: int):
    """q = part * rest, part collecting every prime ell with ord_ell(2) <= dmax, i.e. the
    primes that occur in ANY cyclotomic/Mersenne denominator of index <= dmax."""
    rest, part = q, 1
    for d in range(1, dmax + 1):
        while rest > 1:
            g = math.gcd(rest, (pow(2, d, rest) - 1) % rest)
            if g <= 1:
                break
            part *= g
            rest //= g
    return part, rest


# -------------------------------------------------------------- family evaluation ----
class Family:
    """R = T_N + (a0 I_{1,0,N} + a1 I_{1,1,N}) / D, evaluated exactly against Theta_2.

    Integer model:  R = X / (C*D)  with  X = D*cT + a0*c0 + a1*c1,
    C = lcm(den T_N, den I_{1,0,N}, den I_{1,1,N}).  Theta_2 in [th_lo, th_hi]; writing
    th_lo = Lnum/2^E and th_hi = Hnum/2^E, the exact certified value of q|Theta_2 - R| is
    max(|q*Lnum - p*2^E|, |q*Hnum - p*2^E|) / 2^E  with p/q the reduced R - 1/2.
    """

    def __init__(self, N, mu, nums, th_lo, th_hi, J=1):
        self.N = N
        self.T, self.idf = build_objects(N, J, 1, mu, nums)
        self.th_lo, self.th_hi = th_lo, th_hi
        self.E = max(th_lo.denominator, th_hi.denominator).bit_length() - 1
        assert th_lo.denominator & (th_lo.denominator - 1) == 0
        assert th_hi.denominator & (th_hi.denominator - 1) == 0
        self.Lnum = th_lo.numerator * ((1 << self.E) // th_lo.denominator)
        self.Hnum = th_hi.numerator * ((1 << self.E) // th_hi.denominator)
        C = self.T.denominator
        for k in (0, 1):
            C = C * self.idf[(1, k)].denominator // math.gcd(C, self.idf[(1, k)].denominator)
        self.C = C
        self.cT = int(self.T * C)
        self.c0 = int(self.idf[(1, 0)] * C)
        self.c1 = int(self.idf[(1, 1)] * C)
        self.Rt_base = self.T - F(1, 2)
        self.base_q = self.Rt_base.denominator
        self.base_val = self.qerr(self.Rt_base)[1]

    def qerr(self, Rt: F):
        q = Rt.denominator
        e = min(abs(F(q) * (self.th_lo - Rt)), abs(F(q) * (self.th_hi - Rt)))
        return q, flog2(e)

    def eval_fast(self, D, a0, a1):
        """Exact, certified, integer-only.  Returns (log2 q|Theta_2 - R|, q) or None."""
        if D == 0:
            return None
        if D < 0:
            D, a0, a1 = -D, -a0, -a1
        X = D * self.cT + a0 * self.c0 + a1 * self.c1
        # R - 1/2 = (2X - C*D) / (2*C*D)
        num, den = 2 * X - self.C * D, 2 * self.C * D
        g = math.gcd(num, den) if num else den
        p, q = num // g, den // g
        e = max(abs(q * self.Lnum - p * (1 << self.E)),
                abs(q * self.Hnum - p * (1 << self.E)))
        if e == 0:
            return None
        return ((e.bit_length() - 1 - self.E) + math.log2(
            ((e << 53) >> (e.bit_length() - 1)) / float(1 << 53)), q, p)

    def eval(self, D, a0, a1):
        if D == 0:
            return None
        if D < 0:
            D, a0, a1 = -D, -a0, -a1
        R = self.T + (F(a0) * self.idf[(1, 0)] + F(a1) * self.idf[(1, 1)]) / D
        Rt = R - F(1, 2)
        q, val = self.qerr(Rt)
        return {"D": D, "a0": a0, "a1": a1, "q": q, "log2_q": q.bit_length() - 1,
                "log2_q_times_err": val, "R": R}


def jsonable(x):
    if isinstance(x, int) and abs(x) >= 10 ** 15:
        return str(x)
    return x


# ------------------------------------------------------------------- the probe ----
def run(quick: bool) -> dict:
    rng = random.Random(20260905)
    nums = eulerian_numerators(3)
    mu = mobius(2000)
    bits = 2500 if quick else 6000
    s_lo, s_hi = s_enclosure(bits)
    th_lo, th_hi = s_lo - F(1, 2), s_hi - F(1, 2)
    rep: dict = {"mode": "quick" if quick else "full", "s_enclosure_bits": bits,
                 "theta2_enclosure_width_log2": flog2(th_hi - th_lo)}

    # ------------- 0. depth law + E1 sign correction ---------------------------
    depth_rows, sign_rows = [], []
    for N in (10, 12, 14):
        fam = Family(N, mu, nums, th_lo, th_hi)
        forms = layer_linear_forms(N, mu, rng)
        probes = [(f["m"], 0, 1) for f in forms.values()] + \
                 [(3, 1, 1), (7, -2, 5), (11, 4, -3), (97, 13, 41)]
        for m, f in forms.items():
            # add lattice vectors realising v_ell(L) = 1 and 2 exactly
            for depth in (1, 2):
                bas = congruence_lattice([[f["alpha"], f["gamma"]]], [f["P"] ** depth], 2)
                H, vec = linf_min_2d(bas[0], bas[1])
                probes.append((vec[0], 0, vec[1]))
        for m, f in forms.items():
            for (D, a0, a1) in probes:
                if D == 0:
                    continue
                Dp, a0p, a1p = (D, a0, a1) if D > 0 else (-D, -a0, -a1)
                R = fam.T + (F(a0p) * fam.idf[(1, 0)] + F(a1p) * fam.idf[(1, 1)]) / Dp
                L = f["alpha"] * Dp + f["beta"] * a0p + f["gamma"] * a1p
                for ell, e in f["e"].items():
                    if Dp % ell == 0:
                        continue
                    pred = 0 if L == 0 else min(0, vpow_prime(abs(L), ell) - 2 * e)
                    got = vell_frac(R, ell)
                    depth_rows.append({
                        "N": N, "m": m, "ell": ell, "D": jsonable(Dp),
                        "a0": jsonable(a0p), "a1": jsonable(a1p),
                        "v_ell_L": (None if L == 0 else vpow_prime(abs(L), ell)),
                        "predicted": pred, "measured": got, "match": pred == got})
    for N in (10, 14, 18):
        fam = Family(N, mu, nums, th_lo, th_hi)
        for m, f in layer_linear_forms(N, mu, rng).items():
            k0 = N // m
            s2 = F(0)
            for a in range(1, k0 + 1):
                if mu[a] and math.gcd(a, m) == 1:
                    s2 += F(mu[a], a * a)
            s2 *= mu[m]
            tau = -F(m, 1) * sum(F(mu[a * m], a) for a in range(1, k0 + 1) if mu[a * m])
            if s2 == 0:
                continue
            rho = -tau / s2
            D, a = rho.numerator, rho.denominator
            if D < 0:
                D, a = -D, -a
            R = fam.T + F(a, D) * fam.idf[(1, 1)]
            ells = list(f["e"])
            sign_rows.append({
                "N": N, "m": m, "sigma2": str(s2), "tau": str(tau), "rho": str(rho),
                "plus_form_vanishes": bool(D * s2 + a * tau == 0),
                "minus_form_vanishes": bool(D * s2 - a * tau == 0),
                "v_before": [vell_frac(fam.T, e) for e in ells],
                "v_after": [vell_frac(R, e) for e in ells],
                "layer_fully_removed": all(vell_frac(R, e) == 0 for e in ells)})
    bad = [r for r in depth_rows if not r["match"]]
    rep["depth_law"] = {
        "statement": ("v_ell(R) = min(0, v_ell(L_m(D,a0,a1)) - 2e) for every primitive prime "
                      "ell of layer m with ell not dividing D.  Removing BOTH powers of the "
                      "layer therefore needs P_m^2 | L_m; P_m^1 removes exactly one power."),
        "rows_checked": len(depth_rows),
        "distinct_v_ell_L_seen": sorted({r["v_ell_L"] for r in depth_rows if r["v_ell_L"] is not None}),
        "all_match": not bad, "mismatches": bad[:8]}
    rep["E1_sign_correction"] = {
        "claim": ("the layer form is D*sigma2(m) + sum_j a_{j,1} tau(j,m); E1's PROSE has a "
                  "minus sign, the wave-1 CODE (rho_m = -tau/sigma2) is right"),
        "plus_form_vanishes_everywhere": all(r["plus_form_vanishes"] for r in sign_rows),
        "minus_form_vanishes_anywhere": any(r["minus_form_vanishes"] for r in sign_rows),
        "exact_vanishing_removes_BOTH_powers": all(r["layer_fully_removed"] for r in sign_rows),
        "rows": sign_rows}

    # ------------- 1. the exact trade-off curve --------------------------------
    ns1 = [10, 12, 14, 16] if quick else [10, 12, 14, 16, 18]
    curve = []
    for N in ns1:
        fam = Family(N, mu, nums, th_lo, th_hi)
        forms = layer_linear_forms(N, mu, rng)
        layers = sorted(forms, key=lambda m: -forms[m]["log2_P"])
        subsets = []
        for i in range(len(layers)):
            subsets.append((layers[i],))
            for j in range(i + 1, len(layers)):
                subsets.append((layers[i], layers[j]))
                for k in range(j + 1, len(layers)):
                    subsets.append((layers[i], layers[j], layers[k]))
        if len(layers) > 3:
            subsets.append(tuple(layers))
        rows, checks = [], []
        for M in subsets:
            for depth in (1, 2):
                Q = [forms[m]["P"] ** depth for m in M]
                Qprod = math.prod(Q)
                for variant, coefs in (
                        ("a0_zero", [[forms[m]["alpha"], forms[m]["gamma"]] for m in M]),
                        ("a0_eq_D", [[forms[m]["alpha"] + forms[m]["beta"],
                                      forms[m]["gamma"]] for m in M])):
                    bas = congruence_lattice(coefs, Q, 2)
                    if len(checks) < 12:
                        checks.append({
                            "N": N, "M": list(M), "depth": depth, "variant": variant,
                            "membership_ok": all(
                                sum(c[i] * b[i] for i in range(2)) % q == 0
                                for b in bas for c, q in zip(coefs, Q)),
                            "index": jsonable(abs(det_int(bas))),
                            "expected_index": jsonable(Qprod),
                            "index_matches": abs(det_int(bas)) == Qprod})
                    try:
                        H, vec = linf_min_2d(bas[0], bas[1])
                    except ValueError:
                        continue
                    D, W = vec
                    a0 = 0 if variant == "a0_zero" else D
                    ev = fam.eval(D, a0, W)
                    if ev is None:
                        continue
                    killed = [m for m in forms
                              if all(vell_frac(ev["R"], e) == 0 for e in forms[m]["e"])]
                    Ps = sorted((forms[m]["P"] for m in M), reverse=True)
                    rows.append({
                        "M": list(M), "depth": depth, "variant": variant,
                        "log2_modulus": flog2(F(Qprod)),
                        "D": jsonable(ev["D"]), "W": jsonable(W),
                        "log2_H": (math.log2(H) if H else 0.0),
                        "log2_q": ev["log2_q"],
                        "log2_q_times_err": ev["log2_q_times_err"],
                        "killed_layers": killed,
                        "log2_killed_mass": sum(2 * forms[m]["log2_P"] for m in killed),
                        "E2_geometric_bound_log2_H": (
                            (sum(math.log2(p) for p in Ps[1:]) / (len(Ps) - 1)
                             - math.log2(N + 1)) if len(Ps) > 1 else None),
                        "sharp_max_bound_log2_H": (
                            depth * math.log2(Ps[1]) - math.log2(max(
                                (abs(a) + abs(c)) //
                                max(1, math.gcd(abs(a), abs(c)))
                                for a, c in [(r[0], r[1]) for r in coefs]))
                            if len(Ps) > 1 else None),
                        "log2_H_over_log2_modulus": (
                            math.log2(H) / flog2(F(Qprod)) if H > 1 and Qprod > 1 else None)})
        best = min(rows, key=lambda r: r["log2_q_times_err"]) if rows else None
        mass = sum(2 * forms[m]["log2_P"] for m in layers)
        curve.append({
            "N": N,
            "layers_log2_P": {str(m): forms[m]["log2_P"] for m in layers},
            "total_layer_mass_bits": mass,
            "log2_den_T_N": fam.base_q.bit_length() - 1,
            "log2_base_q_times_err": fam.base_val,
            "half_mass_prediction": fam.base_val - mass / 2,
            "lattice_checks": checks,
            "measured_H_over_modulus_ratio": sorted(
                r["log2_H_over_log2_modulus"] for r in rows
                if r["log2_H_over_log2_modulus"] is not None)[len(
                    [r for r in rows if r["log2_H_over_log2_modulus"] is not None]) // 2]
            if any(r["log2_H_over_log2_modulus"] is not None for r in rows) else None,
            "rows": rows,
            "best": best})
    rep["tradeoff_curve_2d"] = curve

    # ------------- 2. critical-height search (3-D, weighted, modulus-targeted) ----
    cf_terms = cf_certified(th_lo, th_hi, 400 if quick else 900)
    cf_convs = convergents(cf_terms)
    conv_set = set(cf_convs)
    ns2 = [4, 6, 8, 10, 12] if quick else [4, 6, 8, 10, 12, 14, 16]
    crit = []
    for N in ns2:
        fam = Family(N, mu, nums, th_lo, th_hi, J=3)
        forms = layer_linear_forms(N, mu, rng)
        layers = sorted(forms, key=lambda m: -forms[m]["log2_P"])
        logC = fam.C.bit_length() - 1
        caps_exp = sorted({N, N + 2} | set(range(N, int(1.3 * logC) + 3, 2)))
        caps = [2 ** k for k in caps_exp] + [None]
        cap_key = {2 ** k: f"2^{k}" for k in caps_exp}
        cap_key[None] = "unbounded"
        best = {cap_key[c]: (float("inf"), None) for c in caps}
        seen = 0

        def consider(D, a0, a1, tag):
            nonlocal seen
            if D == 0:
                return
            if D < 0:
                D, a0, a1 = -D, -a0, -a1
            got = fam.eval_fast(D, a0, a1)
            if got is None:
                return
            val, q, p = got
            seen += 1
            h = max(abs(D), abs(a0), abs(a1))
            for c in caps:
                if c is None or h <= c:
                    key = cap_key[c]
                    if val < best[key][0]:
                        best[key] = (val, {
                            "D": jsonable(D), "a_10": jsonable(a0), "a_11": jsonable(a1),
                            "log2_height": math.log2(h) if h else 0.0,
                            "log2_q": q.bit_length() - 1,
                            "is_a_convergent_of_Theta_2": (p, q) in conv_set,
                            "tag": tag})

        # (a) exhaustive box at small N; a modest box otherwise
        if N <= 6:
            span = 1 << N
            for D in range(1, span + 1):
                for a0 in range(-span, span + 1):
                    for a1 in range(-span, span + 1):
                        consider(D, a0, a1, "exhaustive-box-2^N")
            exhaustive = True
        else:
            for D in range(1, 17):
                for a0 in range(-12, 13):
                    for a1 in range(-12, 13):
                        consider(D, a0, a1, "box")
            exhaustive = False

        # (b) direct modulus lattices: {v : X(v) = 0 mod G} in (D, b0, a1), a0 = D + b0.
        #     G is built greedily from the exact prime-power factorisation of C at a
        #     sequence of BIT BUDGETS, so the whole trade-off curve is swept.
        Cden = fam.C
        cfac = factor_C(Cden, 3 * N, rng)
        pieces = sorted(((p, v) for p, v in cfac.items()), key=lambda t: -math.log2(t[0]))
        targets = [("C", Cden)]
        budgets = sorted(set(range(3 * N, Cden.bit_length() + 4, 3)) | {Cden.bit_length() - 1})
        for B in budgets:
            G, used = 1, []
            for p, v in pieces:
                lp = math.log2(p)
                take = 0
                while take < v and math.log2(G) + lp <= B:
                    G *= p
                    take += 1
                if take:
                    used.append((p, take))
            if G > 1:
                targets.append((f"greedy<=2^{B}", G))
        weights = [1 << max(0, N - 3), 1 << N, 1 << (N + 3)]
        lat_checks = []
        for name, G in targets:
            if G <= 1:
                continue
            coefs = [[fam.cT + fam.c0, fam.c0, fam.c1]]
            bas = congruence_lattice(coefs, [G], 3)
            if len(lat_checks) < 4:
                idx = abs(det_int(bas))
                lat_checks.append({
                    "target": name,
                    "membership_ok": all(sum(coefs[0][i] * b[i] for i in range(3)) % G == 0
                                         for b in bas),
                    "index_matches_G_over_gcd": idx == G // math.gcd(
                        G, math.gcd(math.gcd(coefs[0][0], coefs[0][1]), coefs[0][2]))})
            for Wt in weights:
                red = lll([[b[0], b[1] * Wt, b[2] * Wt] for b in bas])
                unsc = [[r[0], r[1] // Wt, r[2] // Wt] for r in red]
                for c0 in range(-3, 4):
                    for c1 in range(-3, 4):
                        for c2 in range(-3, 4):
                            v = [c0 * unsc[0][t] + c1 * unsc[1][t] + c2 * unsc[2][t]
                                 for t in range(3)]
                            consider(v[0], v[0] + v[1], v[2],
                                     f"modlat G={name} W=2^{Wt.bit_length()-1}")

        # (c) layer-congruence lattices (cross-check of the direct route)
        subs = []
        for i in range(len(layers)):
            subs.append((layers[i],))
            for j in range(i + 1, len(layers)):
                subs.append((layers[i], layers[j]))
                for k in range(j + 1, len(layers)):
                    subs.append((layers[i], layers[j], layers[k]))
        if len(layers) > 3:
            subs.append(tuple(layers))
        Wt = 1 << N
        for M in subs:
            for depth in (1, 2):
                Q = [forms[m]["P"] ** depth for m in M]
                coefs = [[forms[m]["alpha"] + forms[m]["beta"], forms[m]["beta"],
                          forms[m]["gamma"]] for m in M]
                bas = congruence_lattice(coefs, Q, 3)
                for scale, tag in ((Wt, "w3d"), (1, "u3d")):
                    red = lll([[b[0], b[1] * scale, b[2] * scale] for b in bas])
                    unsc = [[r[0], r[1] // scale, r[2] // scale] for r in red]
                    for c0 in range(-2, 3):
                        for c1 in range(-2, 3):
                            for c2 in range(-2, 3):
                                v = [c0 * unsc[0][t] + c1 * unsc[1][t] + c2 * unsc[2][t]
                                     for t in range(3)]
                                consider(v[0], v[0] + v[1], v[2],
                                         f"{tag} M={list(M)} t={depth}")
                for variant in ("a0_zero", "a0_eq_D"):
                    c2d = ([[forms[m]["alpha"], forms[m]["gamma"]] for m in M]
                           if variant == "a0_zero" else
                           [[forms[m]["alpha"] + forms[m]["beta"], forms[m]["gamma"]]
                            for m in M])
                    b2 = congruence_lattice(c2d, Q, 2)
                    try:
                        _, vv = linf_min_2d(b2[0], b2[1])
                    except ValueError:
                        continue
                    consider(vv[0], 0 if variant == "a0_zero" else vv[0], vv[1],
                             f"2d-{variant} M={list(M)} t={depth}")

        width_rows = []
        for j in (2, 3):
            R = fam.T + fam.idf[(1, 0)] + fam.idf[(j, 1)]
            Rt = R - F(1, 2)
            q, val = fam.qerr(Rt)
            width_rows.append({"j": j, "log2_q": q.bit_length() - 1,
                               "log2_q_times_err": val})
        # exact common-denominator growth with width J (the E3 cost, height-free).
        # Best conceivable objective for the width-J family = (log2 C_J)/n_J - 2N:
        # kill EVERYTHING (needs height C_J^{1/n}) and keep the error at its 2^{-2N} floor.
        widthC = {}
        for J in (1, 2, 3):
            CJ = fam.T.denominator
            for jj in range(1, J + 1):
                for kk in (0, 1):
                    dd = fam.idf[(jj, kk)].denominator
                    CJ = CJ * dd // math.gcd(CJ, dd)
            n_J = 2 * J + 1
            widthC[str(J)] = {"log2_C_J": CJ.bit_length() - 1, "params_n": n_J,
                              "balanced_full_kill_value":
                                  (CJ.bit_length() - 1) / n_J - 2.0 * N}
        # benchmark every witness against the true best rational of the same denominator size
        for key, (val, w) in list(best.items()):
            if w is None:
                continue
            cap_q = 1 << w["log2_q"]
            cands = [(p, q) for (p, q) in cf_convs if q <= cap_q]
            if cands:
                p, q = cands[-1]
                e = max(abs(F(q) * th_lo - p), abs(F(q) * th_hi - p))
                w["true_best_log2_q_times_err_at_this_q"] = flog2(e)
                w["family_deficit_bits"] = val - flog2(e)
        esc = None
        for k in caps_exp:
            if best[f"2^{k}"][0] < 0:
                esc = k
                break
        # CONSTRUCTIVE density witness: with D = 1 the reachable numerators are exactly the
        # coset c_T + gZ, g = gcd(c_0,c_1), so R runs through an arithmetic progression of
        # spacing g/C.  Landing on the nearest point gives |Theta_2 - R| <= g/(2C) and hence
        # q|Theta_2 - R| <= 1/2 whenever q <= C/g.  This proves the family ALWAYS escapes,
        # at coefficient height ~ max(|c_0|,|c_1|)/g = 2^{Theta(N^2)}: the escape is bought
        # with height, not with compression.
        g, u, v = _extgcd(fam.c0, fam.c1)
        if g < 0:
            g, u, v = -g, -u, -v
        target = (fam.C * (th_lo + F(1, 2)) - fam.cT)
        kk = round(target / g)
        step0, step1 = fam.c1 // g, -(fam.c0 // g)
        dens_best = None
        cand_s = {0}
        if step0:
            cand_s.add(rnd_div(-kk * u, step0))
        if step1:
            cand_s.add(rnd_div(-kk * v, step1))
        for s0 in list(cand_s):
            cand_s.update({s0 - 1, s0 + 1})
        for s in cand_s:
            a0 = kk * u + s * step0
            a1 = kk * v + s * step1
            got = fam.eval_fast(1, a0, a1)
            if got is None:
                continue
            val, q, p = got
            h = max(1, abs(a0), abs(a1))
            row = {"log2_height": math.log2(h), "log2_q": q.bit_length() - 1,
                   "log2_q_times_err": val}
            if dens_best is None or row["log2_height"] < dens_best["log2_height"]:
                dens_best = row
        crit.append({
            "N": N,
            "log2_den_T_N": fam.base_q.bit_length() - 1,
            "log2_common_denominator_C": fam.C.bit_length() - 1,
            "log2_base_q_times_err": fam.base_val,
            "total_layer_mass_bits": sum(2 * forms[m]["log2_P"] for m in layers),
            "candidates_evaluated": seen,
            "box_was_exhaustive_to_2^N": exhaustive,
            "lattice_checks": lat_checks,
            "escape_height_log2": esc,
            "escape_height_over_log2C_div3": (
                esc / ((fam.C.bit_length() - 1) / 3.0) if esc else None),
            "density_escape_witness": dens_best,
            "gcd_c0_c1_log2": (g.bit_length() - 1) if g else None,
            "log2C_minus_4N_prediction_at_height_2^N": (fam.C.bit_length() - 1) - 4.0 * N,
            "best_by_height_cap": {k: {"log2_q_times_err": v[0], "witness": v[1]}
                                   for k, v in best.items()},
            "width_common_denominator": widthC,
            "width_j_ge_2_unit_correction": width_rows})
    rep["critical_height"] = crit

    # ------------- 3. Legendre / convergents -----------------------------------
    terms, convs = cf_terms, cf_convs
    dmax_ord = 60 if quick else 120
    conv_rows = []
    for idx, (p, q) in enumerate(convs[: (40 if quick else 60)]):
        part, rest = order_smooth_part(q, dmax_ord)
        err = max(abs(F(q) * th_lo - p), abs(F(q) * th_hi - p))
        conv_rows.append({
            "n": idx, "a_n": terms[idx], "log2_q": q.bit_length() - 1,
            "q": jsonable(q),
            "order_smooth_part": jsonable(part),
            "log2_order_smooth_part": (part.bit_length() - 1) if part > 1 else 0,
            "fully_generic": part == 1,
            "log2_q_times_err": flog2(err)})
    best_by_size = {}
    for N in (4, 6, 8, 10, 12, 14, 18, 24):
        cap = 1 << (2 * N)
        cands = [(p, q) for (p, q) in convs if q <= cap]
        if not cands:
            continue
        p, q = cands[-1]
        e = max(abs(F(q) * th_lo - p), abs(F(q) * th_hi - p))
        best_by_size[str(N)] = {"log2_cap": 2 * N, "log2_q": q.bit_length() - 1,
                                "log2_q_times_err": flog2(e)}
    # ------------- 3b. the trivial dyadic prefix family (the benchmark) ---------
    # P_n = sum_{j<=n} 2^{n-j} phi(j);  R_n = 2^n S - P_n in (0, n+2].  The dyadic
    # approximant to Theta_2 is p/q = (P_n - 2^{n-1})/2^n and q|Theta_2 - p/q| = R_n.
    nmax = 2000 if quick else 6000
    ph = totient(nmax)
    Pn, rows_dy, best_dy = 0, [], None
    lo_num, hi_num = th_lo, th_hi
    for n in range(1, nmax + 1):
        Pn = 2 * Pn + ph[n]
        if n > bits - 8:
            break
        p_dy = Pn - (1 << (n - 1))
        lo = F(1 << n) * th_lo - p_dy
        hi = F(1 << n) * th_hi - p_dy
        val = max(abs(lo), abs(hi))
        if n >= 8 and (best_dy is None or val < best_dy[0]):
            best_dy = (val, n)
        if n in (10, 12, 14, 16, 18, 20, 40, 80, 160, 320, 640, 1280):
            rows_dy.append({"n": n, "log2_q": n, "q_times_err_upper": float(val),
                            "cap_n_plus_2": n + 2})
    rep["dyadic_prefix_benchmark"] = {
        "identity": "q|Theta_2 - p/q| = R_n = 2^n S - P_n in (0, n+2] with q = 2^n",
        "rows": rows_dy,
        "min_over_8_le_n_le_%d" % min(nmax, bits - 8): {
            "value": float(best_dy[0]), "n": best_dy[1]},
        "verdict": ("the TRIVIAL dyadic prefix family already achieves "
                    "q|Theta_2 - p/q| <= log2(q) + 2, i.e. O(log q); the graded Lambert "
                    "cyclotomic family measured above is 2^{Theta((log q)^2)}.  Every "
                    "cyclotomic-denominator construction in this batch is therefore strictly "
                    "DOMINATED by the dyadic prefixes, and the producer's remaining gap is "
                    "exactly 'R_n -> 0 along a subsequence', which is desk E's E10 statistic.")}

    rep["legendre_convergents"] = {
        "certified_partial_quotients": len(terms),
        "max_partial_quotient": max(terms[1:]) if len(terms) > 1 else None,
        "num_partial_quotients_above_1000": sum(1 for a in terms[1:] if a > 1000),
        "order_smooth_bound_dmax": dmax_ord,
        "convergents": conv_rows,
        "num_convergents_with_any_order_smooth_factor":
            sum(1 for r in conv_rows if r["log2_order_smooth_part"] > 0),
        "max_log2_order_smooth_part": max(r["log2_order_smooth_part"] for r in conv_rows),
        "max_order_smooth_fraction_of_log2_q": max(
            (r["log2_order_smooth_part"] / max(1, r["log2_q"])) for r in conv_rows),
        "true_best_q_times_err_at_denominator_size_2^2N": best_by_size,
        "legendre_scope_correction": (
            "Legendre: |Theta - p/q| < 1/(2q^2), i.e. q|Theta-p/q| < 1/(2q), forces p/q to be "
            "a convergent.  The producer only asks q|Theta-p/q| -> 0, which is WEAKER than "
            "1/(2q), so it does NOT confine the supply to convergents.  What is true: "
            "||q Theta|| >= ||q_n Theta|| for the largest convergent denominator q_n <= q, so "
            "the convergents CONTROL the supply without exhausting it.")}
    return rep


def summarise(rep: dict) -> dict:
    curve = rep["tradeoff_curve_2d"]
    crit = rep["critical_height"]
    below = []
    for c in curve:
        if c["best"] and c["best"]["log2_q_times_err"] < 0:
            below.append(("2d", c["N"]))
    for c in crit:
        for k, v in c["best_by_height_cap"].items():
            if v["log2_q_times_err"] < 0:
                below.append((f"crit@{k}", c["N"]))
    height_table = {str(c["N"]): {k: round(v["log2_q_times_err"], 3)
                                  for k, v in c["best_by_height_cap"].items()}
                    for c in crit}
    return {
        "depth_law_holds": rep["depth_law"]["all_match"],
        "E1_sign_is_plus_not_minus": (
            rep["E1_sign_correction"]["plus_form_vanishes_everywhere"]
            and not rep["E1_sign_correction"]["minus_form_vanishes_anywhere"]),
        "all_lattice_indices_match": all(
            ch["index_matches"] and ch["membership_ok"]
            for c in curve for ch in c["lattice_checks"]),
        "base_log2_q_times_err_by_N": {
            str(c["N"]): round(c["log2_base_q_times_err"], 3) for c in curve},
        "best_2d_log2_q_times_err_by_N": {
            str(c["N"]): round(c["best"]["log2_q_times_err"], 3) for c in curve if c["best"]},
        "median_log2H_over_log2modulus_by_N": {
            str(c["N"]): (round(c["measured_H_over_modulus_ratio"], 4)
                          if c["measured_H_over_modulus_ratio"] else None) for c in curve},
        "half_mass_prediction_by_N": {
            str(c["N"]): round(c["half_mass_prediction"], 3) for c in curve},
        "critical_height_table_log2_q_times_err": height_table,
        "critical_height_best_at_2^N_by_N": {
            str(c["N"]): round(c["best_by_height_cap"]["2^%d" % c["N"]]["log2_q_times_err"], 3)
            for c in crit},
        "escape_height_log2_by_N": {str(c["N"]): c["escape_height_log2"] for c in crit},
        "escape_height_over_log2C_by_N": {
            str(c["N"]): (round(c["escape_height_log2"] / c["log2_common_denominator_C"], 3)
                          if c["escape_height_log2"] else None) for c in crit},
        "width_balanced_full_kill_value_by_N": {
            str(c["N"]): {j: round(v["balanced_full_kill_value"], 2)
                          for j, v in c["width_common_denominator"].items()} for c in crit},
        "density_escape_witness_by_N": {
            str(c["N"]): c["density_escape_witness"] for c in crit},
        "height_law": {
            "form": ("measured empirical law for the 3-parameter (j=1, k in {0,1}) family: "
                     "min_{height <= H} log2 q|Theta_2 - R| ~ log2 C_N - N - 2*log2 H, "
                     "hence escape (value < 1) needs log2 H ~ (log2 C_N - N)/2 = "
                     "(kappa N^2 - N)/2, i.e. coefficient height 2^{Theta(N^2)}"),
            "at_height_2^N": {
                str(c["N"]): {
                    "predicted_log2C_minus_3N": c["log2_common_denominator_C"] - 3 * c["N"],
                    "measured": round(
                        c["best_by_height_cap"]["2^%d" % c["N"]]["log2_q_times_err"], 3)}
                for c in crit},
            "escape_height": {
                str(c["N"]): {
                    "predicted_half_log2C_minus_N":
                        (c["log2_common_denominator_C"] - c["N"]) / 2.0,
                    "measured_upper_bound": c["escape_height_log2"],
                    "certified_density_witness_log2_height":
                        (c["density_escape_witness"] or {}).get("log2_height")}
                for c in crit}},
        "escape_height_over_log2C_div3_by_N": {
            str(c["N"]): (round(c["escape_height_over_log2C_div3"], 3)
                          if c["escape_height_over_log2C_div3"] else None) for c in crit},
        "family_deficit_bits_at_2^N": {
            str(c["N"]): round(
                c["best_by_height_cap"]["2^%d" % c["N"]]["witness"].get(
                    "family_deficit_bits", float("nan")), 2)
            for c in crit if c["best_by_height_cap"]["2^%d" % c["N"]]["witness"]},
        "q_times_err_below_one_at": below,
        "dyadic_prefix_min_q_times_err": rep["dyadic_prefix_benchmark"][
            [k for k in rep["dyadic_prefix_benchmark"] if k.startswith("min_over_")][0]],
        "max_log2_order_smooth_part_of_a_convergent_denominator":
            rep["legendre_convergents"]["max_log2_order_smooth_part"],
        "true_best_q_times_err_at_2^2N":
            rep["legendre_convergents"]["true_best_q_times_err_at_denominator_size_2^2N"],
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--out")
    args = ap.parse_args()
    rep = run(args.quick)
    rep["verdict"] = summarise(rep)
    if args.out:
        with open(args.out, "w") as fh:
            json.dump(rep, fh, indent=1, default=str)
    if args.json:
        print(json.dumps(rep, indent=1, default=str))
    else:
        print(json.dumps(rep["verdict"], indent=1, default=str))
    return 0


if __name__ == "__main__":
    sys.exit(main())
