#!/usr/bin/env python3
"""Exact replay of the finite content of the weighted-record octuple returns (Erdős #243).

Source note: ErdosProblems/Erdos243/WeightedRecordOctupleCriteria.md (return batch
erdos243_20260905_weighted_record_octuple_returns_02, returns r01..r08).  Lean
authority for the structural halves lives in RecordIncrementBarrier.lean,
SaturatedSquareTransport.lean, TwoModulusRecordCut.lean and
ProtectedEpochEnergy.lean; this checker is the exact finite falsifier beside those
declarations.  Nothing here is a statement about an infinite orbit.  Erdős #243
remains open.

Primitive one step, nearest-integer selector (Koizumi Lemma 15 in primitive
coordinates; the floor selector floor(v/u)+1 deletes the negative branch):

    a = (2 v + 3 u) // (2 u),  e = v - (a - 1) u,  w = a u - v = u - e,
    h = gcd(w, a v) = gcd(w, a^2),  u' = w/h,  v' = a v/h.

Parts
-----
A  r01 (46): records versus record-setting jumps; (47)-(51): h = d^2 with tiny errors.
B  r01 Lemma 1 / r06 Lemma 1 (7): nu_p(h) >= 2 (nu_p v - nu_p v')_+ on every primitive
   step (per-step historical square payment), plus the two-step erasure square.
C  r02 Lemma 2 one-step content: a barrier first crossing is a clean record with
   jump >= 3; per-step barrier capacity 2p k <= 2p + d; the three-step fixture with
   27 | v_0; the finite epoch inequality p Q <= (8p+8) K + 4 X + 8p on engineered
   crossings.
D  r03 Theorem 3: the simultaneous-erasure family for 2 <= m <= 8 (all fresh
   primes of the first m digits leave the reduced denominator in one step with
   rho = P, h = P^2, M = P, G = P^2, kappa = P), and the sandwich M | G | M^2.
E  r04 Proposition 1: b e e' == (v/c)^2 (mod u') with b, v/c units mod u', on
   random primitive steps INCLUDING paid ones; Lemma 2 on orbits; the family (31)
   with A_1 = p^2 - 1/k and the instance (15,134) -> (4,335) -> (1,5695).
F  r05 (51): 4/43 = 1/12 + 1/104 + 1/13416 and the family (40)-(48).
G  r06 Lemma 3: exhaustive two-modulus cut (jumps <= 4 blocked, jump 5 escapes via
   (33, 7585)); the erasure family (34).
H  r07: the mod-11 word (7,8,0,5) and its two nonresidue discriminants; the norm
   identity (18) for k = 1..12; identities (5)-(6) on random orbits.
I  r08: the two rising-factorial cubic profiles are unrealizable mod 7 (exhaustive
   d_0 table); m = 12 is the only integer scale allowed by (26); Lemma 4's
   countermodel C_n = n(n+1)(n+2) + (-1)^n has ratio 1 + 3/n + O(n^-3) but is not
   eventually polynomial.

Run:
    ./repo-python .../scripts/check_erdos243_weighted_record_octuple.py --quick
    ./repo-python .../scripts/check_erdos243_weighted_record_octuple.py
"""

from __future__ import annotations

import argparse
import json
import random
import sys
from fractions import Fraction
from math import gcd, isqrt


# --------------------------------------------------------------------------- core

def vp(n: int, p: int) -> int:
    k = 0
    while n and n % p == 0:
        n //= p
        k += 1
    return k


def prime_factors(n: int) -> list[int]:
    out, d = [], 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        out.append(n)
    return out


def is_prime(n: int) -> bool:
    return n >= 2 and prime_factors(n) == [n]


def step(u: int, v: int) -> tuple[int, int, int, int, int, int]:
    """One primitive nearest-integer step. Returns (a, e, w, h, u', v')."""
    a = (2 * v + 3 * u) // (2 * u)
    e = v - (a - 1) * u
    w = a * u - v
    h = gcd(w, a * v)
    assert h == gcd(w, a * a), "cancellation factor is gcd(w, a^2)"
    return a, e, w, h, w // h, (a * v) // h


def orbit(u: int, v: int, horizon: int = 60) -> list[dict]:
    rows = []
    for _ in range(horizon):
        a, e, w, h, u1, v1 = step(u, v)
        rows.append({"u": u, "v": v, "a": a, "e": e, "w": w, "h": h, "u1": u1, "v1": v1})
        if e == 0:
            break
        u, v = u1, v1
    return rows


def unreduced_orbit(C: int, D: int, horizon: int = 40) -> list[dict]:
    """Unreduced canonical orbit with gcd bookkeeping (G, M, kappa, rho)."""
    rows = []
    lam = D  # cumulative lcm of q and earlier digits, starting at q = D_0
    for _ in range(horizon):
        # nearest-integer selector in unreduced coordinates
        a = (2 * D + 3 * C) // (2 * C)
        E = D - (a - 1) * C
        G = gcd(C, D)
        M = D // lam
        rho = gcd(lam, a)
        rows.append({"C": C, "D": D, "a": a, "E": E, "G": G, "M": M, "rho": rho,
                     "kappa": lam // (D // G), "lam": lam})
        if E == 0:
            break
        C, D = C - E, a * D
        lam = lam * a // rho
    return rows


def seeds(quick: bool) -> list[tuple[int, int]]:
    rng = random.Random(243)
    out = []
    vmax = 400 if quick else 2500
    for v in range(3, vmax):
        for u in range(1, v // 2 + 1):
            if gcd(u, v) == 1:
                out.append((u, v))
    rng.shuffle(out)
    return out[: 6000 if quick else 60000]


# --------------------------------------------------------------------------- A

def part_a() -> dict:
    # (46): (8,177) -> (7,4071) -> (10,2373393)
    a, e, w, h, u1, v1 = step(8, 177)
    assert (a, e, h, u1, v1) == (23, 1, 1, 7, 4071), (a, e, h, u1, v1)
    a2, e2, w2, h2, u2, v2 = step(7, 4071)
    assert (a2, e2, h2, u2, v2) == (583, -3, 1, 10, 2373393), (a2, e2, h2, u2, v2)
    records = [8, 8, 10]
    increment = records[2] - records[1]
    jump = u2 - u1
    assert increment == 2 and jump == 3 and gcd(8, 10) == 2
    # (47)-(51): u = d^2 k - 1, v = (d-1)u - 1
    fam = 0
    for d in range(2, 30):
        for k in range(3, 30):
            u = d * d * k - 1
            v = (d - 1) * u - 1
            assert gcd(u, v) == 1
            a, e, w, h, u1, v1 = step(u, v)
            assert (a, e, w, h, u1) == (d, -1, d * d * k, d * d, k), (d, k, a, e, w, h, u1)
            assert v1 == k * (d * d - d) - 1
            a1, e1, *_ = step(u1, v1)
            assert (a1, e1) == (d * d - d + 1, -1)
            fam += 1
    return {"fixture_46": {"records": records, "true_increment": increment, "record_setting_jump": jump,
                           "gcd_of_records": 2},
            "family_47_51_members": fam}


# --------------------------------------------------------------------------- B

def part_b(quick: bool) -> dict:
    states = 0
    drops = 0
    erasures = 0
    for (u, v) in seeds(quick):
        for row in orbit(u, v, 12):
            if row["v"] > 10 ** 8:
                break  # trial division only; deeper states are doubly exponential
            states += 1
            for p in prime_factors(row["v"]):
                l, l1, k = vp(row["v"], p), vp(row["v1"], p), vp(row["h"], p)
                # r01 Lemma 1 / r06 (7): nu_p(h) >= 2 (nu_p v - nu_p v')_+
                assert k >= 2 * max(0, l - l1), (row, p)
                if l1 < l:
                    drops += 1
                if l1 == 0:
                    erasures += 1
                    assert k >= 2 * l
    return {"states": states, "valuation_drops": drops, "full_erasures": erasures, "failures": 0}


# --------------------------------------------------------------------------- C

def part_c(quick: bool) -> dict:
    # the exact three-step fixture, 27 | v_0
    u0, v0, a0 = 19, 1792818711, 94358881
    a, e, w, h, u1, v1 = step(u0, v0)
    assert (a, e, h, u1) == (a0, -9, 1, 28), (a, e, h, u1)
    a, e, w, h, u2, v2 = step(u1, v1)
    assert (e, h, u2) == (-9, 1, 37)
    a, e, w, h, u3, v3 = step(u2, v2)
    assert (e, h, u3) == (-9, 1, 46)
    assert v0 % 27 == 0 and v0 % 81 != 0
    p, Q = 3, 27
    barriers = [(2 * k + 1) * p for k in range(0, Q) if Q < 4 * (2 * k + 1) <= 2 * Q]
    assert barriers == [21, 27, 33, 39], barriers
    first_cross = {}
    us = [19, 28, 37, 46]
    for b in barriers:
        for n in range(3):
            if us[n] < b <= us[n + 1]:
                first_cross[b] = n
                break
    assert first_cross == {21: 0, 27: 0, 33: 1, 39: 2}, first_cross
    # one-step content: barrier first crossing => clean record with d >= 3
    one_step = 0
    for (u, v) in seeds(quick):
        for row in orbit(u, v, 12):
            if row["v"] > 10 ** 8:
                break
            if row["h"] != 1 or row["u1"] <= row["u"]:
                continue
            assert 2 * row["w"] <= 3 * row["u"] and row["u"] < 2 * row["w"]
            for p in prime_factors(row["v"]):
                if p == 2:
                    continue
                l = vp(row["v"], p)
                for b in range(row["u"] + 1, row["u1"] + 1):
                    if b % p == 0 and b % 2 == 1 and 3 * b < 2 * p ** (l + 1):
                        one_step += 1
                        assert row["u1"] - row["u"] >= 3, (row, p, b)
                        assert row["u1"] != b
    # capacity: odd multiples of p in (u, u+d] number k with 2p k <= 2p + d
    cap = 0
    rng = random.Random(7)
    for _ in range(3000 if quick else 30000):
        p = rng.choice([3, 5, 7, 11, 13])
        u = rng.randrange(1, 5000)
        d = rng.randrange(1, 400)
        k = sum(1 for b in range(u + 1, u + d + 1) if b % p == 0 and b % 2 == 1)
        assert 2 * p * k <= 2 * p + d
        cap += 1
    # engineered epochs: a primitive walk u_s < u_{s+1} < ... whose steps are records with the
    # odd-cut constraints (never landing on an odd multiple of p, coprime neighbours);
    # verify p Q <= (8p+8) K + 4 X + 8p on the first crossing of L = pQ/2.
    epochs = 0
    from bisect import bisect_left
    pl_pairs = [(3, 3), (3, 4), (5, 2), (5, 3), (7, 2), (7, 3), (3, 5), (11, 2)]
    if not quick:
        pl_pairs += [(3, 6), (5, 4), (13, 2), (7, 4)]
    for p, l in pl_pairs:
        Q = p ** l
        if Q < 16:
            continue
        for R in range(1, max(2, (p * Q) // 4), max(1, (p * Q) // 12)):
            if 4 * R >= p * Q:
                continue
            rng2 = random.Random(R * 1000 + Q)
            u = R
            path = [u]
            while 2 * u < p * Q:
                # choose a jump in {1..7} keeping coprimality and avoiding odd multiples of p
                for _try in range(50):
                    d = rng2.randrange(1, 8)
                    cand = u + d
                    if cand % p == 0 and cand % 2 == 1:
                        continue
                    if gcd(u, cand) != 1:
                        continue
                    break
                else:
                    cand = u + 2 * p + 1 if gcd(u, u + 2 * p + 1) == 1 else u + 2 * p + 2
                u = cand
                path.append(u)
            barriers = [(2 * k + 1) * p for k in range(0, Q) if Q < 4 * (2 * k + 1) <= 2 * Q]
            J = {}
            for b in barriers:
                # first index n with path[n+1] >= b; path is strictly increasing
                n = bisect_left(path, b) - 1
                if 0 <= n < len(path) - 1 and path[n] < b <= path[n + 1]:
                    J.setdefault(n, []).append(b)
            K = len(J)
            X = sum(path[n + 1] - path[n] - 2 for n in J)
            assert all(path[n + 1] - path[n] >= 3 for n in J), (p, Q, R, path)
            assert p * Q <= (8 * p + 8) * K + 4 * X + 8 * p, (p, Q, R, K, X)
            epochs += 1
    return {"fixture_three_step": {"u": us, "barriers": barriers if False else [21, 27, 33, 39],
                                   "first_crossings": first_cross},
            "one_step_barrier_crossings": one_step, "capacity_checks": cap,
            "engineered_epochs": epochs, "failures": 0}


# --------------------------------------------------------------------------- D

def sylvester_prefix(m: int) -> tuple[list[int], int, int]:
    P, s = 1, []
    for _ in range(m):
        sj = P + 1
        s.append(sj)
        P *= sj
    Q = P * (P - 1) + 1
    return s, P, Q


def part_d(quick: bool) -> dict:
    out = {}
    for m in range(2, 9):
        s, P, Q = sylvester_prefix(m)
        total = sum(Fraction(1, x) for x in s) + Fraction(1, P) + Fraction(1, Q)
        assert total == 1 + Fraction(1, Q)
        # canonical unreduced orbit for x = (Q+1)/Q, digits must be s_1..s_m, P, Q+1, ...
        rows = unreduced_orbit(Q + 1, Q, m + 3)
        digits = [r["a"] for r in rows]
        assert digits[:m] == s and digits[m] == P and digits[m + 1] == Q + 1, digits
        exc = rows[m]
        nxt = rows[m + 1]
        # (23): rho at the exceptional step is P; after it M = P, G = P^2, kappa = P
        assert exc["rho"] == P and exc["G"] == 1 and exc["M"] == 1, exc
        assert nxt["M"] == P and nxt["G"] == P * P and nxt["kappa"] == P, nxt
        # the reduced denominator after the exceptional step is Q: every fresh prime is gone
        vred = nxt["D"] // nxt["G"]
        assert vred == Q
        for x in s:
            assert gcd(x, vred) == 1
        # h at the exceptional step = G_{m+2}/G_{m+1}
        assert nxt["G"] // exc["G"] == P * P
        # sup |theta| <= 1/(P-1)
        assert all(abs(Fraction(r["E"], r["C"])) <= Fraction(1, P - 1) for r in rows)
        out[m] = {"P": P, "Q": Q, "rho": exc["rho"], "h": nxt["G"] // exc["G"]}
    # sandwich M | G | M^2 on random unreduced orbits (r03 Theorem 1, first assertion)
    sandwich = 0
    for (u, v) in seeds(quick)[: 600 if quick else 6000]:
        for r in unreduced_orbit(u, v, 9):
            assert r["G"] % r["M"] == 0 and (r["M"] * r["M"]) % r["G"] == 0, r
            sandwich += 1
    return {"families": out, "sandwich_states": sandwich, "failures": 0}


# --------------------------------------------------------------------------- E

def normal_form(a: int, v: int, w: int, h: int) -> tuple[int, int, int, int]:
    """d = gcd(a,v), c = h/d, b = d/c, l = a/d, s = v/d  (DynamicCancellation normal form)."""
    d = gcd(a, v)
    assert h % d == 0
    c = h // d
    assert d % c == 0 and gcd(w // d, d) == c
    return d // c, c, a // d, v // d


def part_e(quick: bool) -> dict:
    checked = paid = 0
    for (u, v) in seeds(quick):
        rows = orbit(u, v, 12)
        for i in range(len(rows) - 1):
            r, r1 = rows[i], rows[i + 1]
            a, e, w, h, u1, v1 = r["a"], r["e"], r["w"], r["h"], r["u1"], r["v1"]
            e1 = r1["e"]
            b, c, l, s = normal_form(a, v if i == 0 else r["v"], w, h)
            vv = r["v"]
            b, c, l, s = normal_form(a, vv, w, h)
            assert a == b * c * l and vv == b * c * s and h == b * c * c and v1 == b * l * s
            # Proposition 1: b e e' == (v/c)^2 mod u', with b, v/c units mod u'
            assert (b * e * e1 - (vv // c) ** 2) % u1 == 0, (r, r1, b, c)
            assert gcd(b, u1) == 1 and gcd(vv // c, u1) == 1 and gcd(l, u1) == 1
            checked += 1
            if h > 1:
                paid += 1
    # Lemma 2 on orbits: at the first negative index t after s, u_s * u_t <= R_t * m_t * u_{s+1}
    lemma2 = 0
    for (u, v) in seeds(quick)[: 2000 if quick else 20000]:
        rows = orbit(u, v, 20)
        us = [r["u"] for r in rows] + [rows[-1]["u1"]]
        es = [r["e"] for r in rows]
        for sidx in range(len(rows) - 1):
            t = None
            for j in range(sidx + 1, len(rows)):
                if es[j] < 0:
                    t = j
                    break
                if es[j] == 0:
                    break
            if t is None:
                continue
            R_t = max(us[: t + 1])
            m_t = -es[t]
            assert us[sidx] * us[t] <= R_t * m_t * us[sidx + 1], (u, v, sidx, t)
            lemma2 += 1
    # instance (15,134) and the family (31)
    a, e, w, h, u1, v1 = step(15, 134)
    assert (a, e, h, u1, v1) == (10, -1, 4, 4, 335)
    a, e, w, h, u2, v2 = step(4, 335)
    assert (a, e, h, u2, v2) == (85, -1, 5, 1, 5695)
    assert Fraction(15, 134) == Fraction(1, 10) + Fraction(1, 85) + Fraction(1, 5695)
    fam = 0
    for p in [2, 3, 5, 7]:
        for k in range(3, 20):
            if (k + 1) % p == 0:
                continue
            for J in range(0, 4):
                z = (k + 1) * (1 + k * p * J)
                if z % p == 0:
                    continue
                assert z % k == 1 and z % (k + 1) == 0
                u = p * p * k - 1
                a_ = p * z
                v = (a_ - 1) * u - 1
                assert gcd(u, v) == 1
                a, e, w, h, u1, v1 = step(u, v)
                assert (a, e, w, h, u1) == (a_, -1, p * p * k, p * p, k), (p, k, J, a, e, w, h, u1)
                a1, e1, w1, h1, u2, v2 = step(u1, v1)
                assert e1 == -1 and a1 % (k + 1) == 0 and w1 == k + 1 and h1 == k + 1 and u2 == 1
                A1 = Fraction(u, 1) * Fraction(-e1, u1) if False else Fraction(u * 1, u1)  # R_1 m_1 / u_1 with R_1 = u, m_1 = 1
                assert A1 == p * p - Fraction(1, k)
                fam += 1
    return {"transport_steps": checked, "of_which_paid": paid, "lemma2_checks": lemma2,
            "family_31_members": fam, "failures": 0}


# --------------------------------------------------------------------------- F

def part_f() -> dict:
    assert Fraction(4, 43) == Fraction(1, 12) + Fraction(1, 104) + Fraction(1, 13416)
    fam = 0
    for s in range(2, 12):
        for K in range(1, 6):
            u = s * s
            A = u * ((u + 1) * K - s)
            v = (A - 1) * u - 1
            assert gcd(u, v) == 1
            a, e, w, h, u1, v1 = step(u, v)
            assert (a, e, h, u1) == (A, -1, 1, u + 1), (s, K, a, e, h, u1)
            assert v1 == A * v
            A2, rem = divmod(A * v + u, u + 1)
            assert rem == 0
            a2, e2, w2, h2, u2, v2 = step(u1, v1)
            assert (a2, e2, w2, h2, u2) == (A2, 1, u, u, 1), (s, K, a2, e2, w2, h2, u2)
            T = A2 * A * v // u
            assert v2 == T
            assert Fraction(u, v) == Fraction(1, A) + Fraction(1, A2) + Fraction(1, T)
            assert Fraction(A2, A * A) == Fraction(u, u + 1) - Fraction(1, A) + Fraction(u, (u + 1) * A * A)
            fam += 1
    return {"identity_51": True, "family_40_48_members": fam, "failures": 0}


# --------------------------------------------------------------------------- G

def part_g() -> dict:
    # (33, 7585): jump 5 across H = 35 with 5 | 35 and 37 | 37
    a, e, w, h, u1, v1 = step(33, 7585)
    assert (a, e, w, h, u1, v1) == (231, -5, 38, 1, 38, 1752135), (a, e, w, h, u1, v1)
    assert 7585 == 5 * 37 * 41 and v1 % 5 == 0 and v1 % 37 == 0 and gcd(33, 38) == 1
    # exhaustive two-modulus cut: H = 5 mod 6, landings H and H+2 forbidden, jump <= 4
    cut = 0
    for H in range(5, 6 * 400, 6):
        for u in range(max(1, H - 4), H):
            for u1 in range(H, u + 5):
                if u1 in (H, H + 2):
                    continue
                assert gcd(u, u1) > 1, (H, u, u1)
                cut += 1
    # erasure family (34)
    fam = 0
    for P in [2, 3, 4, 5, 7, 8, 9, 11, 16, 25, 27]:
        pf = prime_factors(P)
        if len(pf) != 1:
            continue
        p = pf[0]
        for t in range(3, 25):
            u = P * P * t + 1
            v = (P - 1) * u + 1
            assert v == P * (P * (P - 1) * t + 1) and gcd(u, v) == 1
            a, e, w, h, u1, v1 = step(u, v)
            assert (a, e, w, h, u1) == (P, 1, P * P * t, P * P, t), (P, t, a, e, w, h, u1)
            assert v1 == P * (P - 1) * t + 1 and v1 % p != 0 and vp(v, p) == vp(P, p)
            a1, e1, *_ = step(u1, v1)
            assert (a1, e1) == (P * (P - 1) + 1, 1)
            fam += 1
    return {"escape_fixture": {"u": 33, "v": 7585, "a": 231, "e": -5, "u1": 38, "H": 35},
            "two_modulus_cut_pairs": cut, "erasure_family_34_members": fam, "failures": 0}


# --------------------------------------------------------------------------- H

def is_square_mod(x: int, p: int) -> bool:
    x %= p
    return any((y * y) % p == x for y in range(p))


def part_h(quick: bool) -> dict:
    # k = 1, p = 11, t = 4: word (7,8,0,5), discriminants L_s = (1-t)^2 + 8 s k (4 - 2t)
    k, p, t = 1, 11, 4
    assert (t * t - (4 * k * k + 1)) % p == 0
    word = [(4 - 2 * t) % p, (1 - t) % p, 0, (1 + t) % p]
    assert word == [7, 8, 0, 5], word
    Ls = {s: ((1 - t) ** 2 + 8 * s * k * (4 - 2 * t)) % p for s in (1, -1)}
    assert Ls == {1: 10, -1: 8}, Ls
    assert not is_square_mod(10, 11) and not is_square_mod(8, 11)
    # norm identity (18): N(L_s) = A^2 - B^2 (4k^2+1) with A = 4k^2+2+32sk, B = -2-16sk
    for kk in range(1, 13):
        for s in (1, -1):
            A = 4 * kk * kk + 2 + 32 * s * kk
            B = -2 - 16 * s * kk
            assert A * A - B * B * (4 * kk * kk + 1) == -16 * kk * (63 * kk ** 3 - 48 * kk - 4 * s)
            assert 63 * kk ** 3 - 48 * kk - 4 * s > 0
    # identities (5) and (6) on unreduced orbits
    ident = 0
    for (u, v) in seeds(quick)[: 600 if quick else 6000]:
        rows = unreduced_orbit(u, v, 9)
        for i in range(len(rows) - 1):
            C, D, a = rows[i]["C"], rows[i]["D"], rows[i]["a"]
            C1, D1 = rows[i + 1]["C"], rows[i + 1]["D"]
            assert C * D1 == D * (D + C1)
            ident += 1
        for i in range(1, len(rows) - 1):
            C0, D0 = rows[i - 1]["C"], rows[i - 1]["D"]
            Cm, C2 = rows[i]["C"], rows[i + 1]["C"]
            for q in prime_factors(Cm):
                assert (D0 * D0 + C0 * C2) % q == 0
    return {"mod11_word": word, "discriminants_mod11": Ls, "norm_identity_k_range": [1, 12],
            "identity_checks": ident, "failures": 0}


# --------------------------------------------------------------------------- I

def realizable_word_mod(word: list[int], q: int) -> bool:
    """Is the numerator word (c0,c1,c2,c3) realizable by u' = a u - v, v' = a v over F_q
    with c0 a unit?  Brute force over d0 and a0 (a1, a2 determined when c1, c2 are units)."""
    c0, c1, c2, c3 = word
    for d0 in range(q):
        for a0 in range(q):
            if (a0 * c0 - d0) % q != c1:
                continue
            d1 = (a0 * d0) % q
            for a1 in range(q):
                if (a1 * c1 - d1) % q != c2:
                    continue
                d2 = (a1 * d1) % q
                for a2 in range(q):
                    if (a2 * c2 - d2) % q == c3:
                        return True
    return False


def part_i() -> dict:
    prof_plus = [2 * n * (n + 1) * (n + 2) + 1 for n in range(0, 4)]
    prof_minus = [2 * n * (n + 1) * (n + 2) - 1 for n in range(1, 5)]
    wp = [x % 7 for x in prof_plus]
    wm = [x % 7 for x in prof_minus]
    assert wp == [1, 6, 0, 2] and wm == [4, 5, 0, 1], (wp, wm)
    assert not realizable_word_mod(wp, 7) and not realizable_word_mod(wm, 7)
    # the d_1 images (34): d1 = d0 (d0 + c1) / c0
    img_plus = sorted({(d0 * (d0 + 6)) % 7 for d0 in range(7)})
    img_minus = sorted({(2 * d0 * (d0 + 5)) % 7 for d0 in range(7)})
    assert img_plus == [0, 2, 5, 6] and img_minus == [0, 2, 5, 6]
    assert {3, 4}.isdisjoint(img_plus)
    # (26): (r^2+s^2)^2 | 48 with r s != 0 forces |r| = s = 1, m = 12
    sols = set()
    for r in range(-10, 11):
        for s in range(1, 11):
            if r == 0 or gcd(abs(r), s) != 1:
                continue
            d = (r * r + s * s) ** 2
            for c in (1, -1):
                for num in (48 * c * r * s ** 3, 48 * c * r ** 3 * s):
                    if num % d == 0 and num // d > 0:
                        sols.add(num // d)
    assert sols == {12}, sols
    # Lemma 4 countermodel: ratio 1 + 3/n + O(n^-3) but not eventually polynomial
    Cn = [n * (n + 1) * (n + 2) + (-1) ** n for n in range(1, 60)]
    third = [Cn[i + 3] - 3 * Cn[i + 2] + 3 * Cn[i + 1] - Cn[i] for i in range(len(Cn) - 3)]
    assert all(x != 6 for x in third[-10:])  # never stabilises at the polynomial value 6
    worst = max(abs(Fraction(Cn[n], Cn[n - 1]) - 1 - Fraction(3, n)) * n ** 3 for n in range(20, 59))
    assert worst < 4, worst
    return {"word_plus_mod7": wp, "word_minus_mod7": wm, "d1_image": img_plus,
            "integer_scales_from_26": sorted(sols), "countermodel_ratio_error_times_n3_max": float(worst),
            "failures": 0}


# --------------------------------------------------------------------------- main

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()
    report = {"script": "check_erdos243_weighted_record_octuple.py", "quick": args.quick}
    report["A_records_vs_jumps"] = part_a()
    report["B_square_payment"] = part_b(args.quick)
    report["C_protected_epoch"] = part_c(args.quick)
    report["D_simultaneous_erasure"] = part_d(args.quick)
    report["E_saturated_transport"] = part_e(args.quick)
    report["F_continuation_fixtures"] = part_f()
    report["G_two_modulus_cut"] = part_g()
    report["H_quadratic_antishadowing"] = part_h(args.quick)
    report["I_cubic_profile"] = part_i()
    report["evidence_class"] = "exact_finite_computation_beside_ordinary_proofs_and_lean_declarations"
    report["claim_ceiling"] = "finite exact replay only; Erdős #243 remains open"
    print(json.dumps(report, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
