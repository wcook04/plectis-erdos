#!/usr/bin/env python3
"""Prefix confinement for Erdos 249: one theorem, and the exclusion machine it runs.

  S = sum_{m>=1} phi(m) 2^-m,  P_n = 2 P_{n-1} + phi(m),  P_0 = 0,
  R_n = 2^n S - P_n = sum_{j>=1} phi(n+j) 2^-j,   0 < R_n <= n+1.

THEOREM (confinement).  Let S = a/(2^c v) with a in Z, c >= 0, v odd > 0.
Then for every n >= c the number u_n := v R_n = a 2^{n-c} - v P_n is an
INTEGER with 0 < u_n <= v (n+1), and for every t with 0 <= t <= n - c,

        u_n  ==  - v P_n   (mod 2^t).

Write rho_t(v) for the unique integer in [1, 2^t] congruent to -v P_n mod 2^t.
Since u_n is a positive integer in that class, u_n >= rho_t(v).  Hence:

EXCLUSION TEMPLATE.  For any n and any t <= n, the pair (c, v) is REFUTED by
the single residue P_n mod 2^t as soon as

        c <= n - t     and     rho_t(v) > v R_n.

So the set of (c,v) NOT excluded by that one residue is exactly
        { c > n - t }  union  { v : rho_t(v) <= v R_n }.

COROLLARY (E10, desk E).  If 2^t | P_n then rho_t(v) = 2^t for every v, so the
excluded set is the rectangle {c <= n-t} x {odd v < 2^t / R_n}; and
limsup_n (v_2(P_n) - log2 n) = +infinity implies S irrational.

COROLLARY (CD, r04).  For n >= c + t with 2^t > v(n+1) the value of u_n is
FORCED to be rho_t(v), so n -> P_n mod 2^t is injective on any set where
n -> u_n is injective, and u_n ranges in a set of size <= v(2N+1)/2^k once
2^k | P_n holds (density one for each fixed k, r03 Lemma 1.1); hence
D_N = o(N) under rationality, and limsup D_N/N > 0 implies S irrational.

WHAT IS NEW HERE.  Desk E used only the corollary rho_t(v) = 2^t, i.e. the RARE
event 2^t | P_n, and got c <= 2786603, odd v <= 259 from a single witness.  The
template needs no divisibility at all: a GENERIC residue already refutes every
odd v with rho_t(v) > v R_n, and the joint test over odd v <= V is a
2-dimensional lattice emptiness question that a Lagrange-Gauss reduction settles
exactly.  Because P_n mod 2^t depends only on phi(n-t+1..n), the cost of the
test is O(t) totient evaluations NEAR n and is independent of n itself.  That
is what moves the reachable exponent range from ~10^6 to ~10^18.

Parts:
  A  the theorem checked against EXACT rational surrogates (including the
     extremal one, g(m) = m, where u_n = n+2 sits on the boundary);
  B  desk E's rectangle at n = 2786632 reproduced, and the t-staircase that
     strictly enlarges it;
  C  the template as a machine: excluded odd v <= V from one residue;
  D  occupancy of the admissible band, v in {1,3,5,7,15,63}, Delta = 0..6;
  E  the v-uniform exclusion: the first n killing every odd v <= 63, and the
     record rectangle certified by lattice reduction at a large n.

Run: ./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/\
Erdos249/scripts/check_prefix_confinement_exclusion.py --quick
"""
from __future__ import annotations

import argparse
import json
import math
import random
import sys
import time
from fractions import Fraction as Fr

try:
    import numpy as np
except ImportError:                                    # pragma: no cover
    np = None


# ----------------------------------------------------------------- totient --
def totient_sieve(X: int):
    ph = list(range(X + 1))
    for i in range(2, X + 1):
        if ph[i] == i:
            for j in range(i, X + 1, i):
                ph[j] -= ph[j] // i
    ph[0] = 0
    return ph


_SMALL = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    for p in _SMALL:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in _SMALL:                                   # deterministic < 3.3e24
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def _rho(n: int, rnd: random.Random) -> int:
    if n % 2 == 0:
        return 2
    while True:
        c = rnd.randrange(1, n)
        x = y = rnd.randrange(0, n)
        d = 1
        while d == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = math.gcd(abs(x - y), n)
        if d != n:
            return d


def factor(n: int, rnd: random.Random, out=None):
    out = {} if out is None else out
    if n == 1:
        return out
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47):
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
    if n == 1:
        return out
    if is_prime(n):
        out[n] = out.get(n, 0) + 1
        return out
    d = _rho(n, rnd)
    factor(d, rnd, out)
    factor(n // d, rnd, out)
    return out


def phi_big(n: int, rnd: random.Random) -> int:
    f = factor(n, rnd)
    out = 1
    for p, e in f.items():
        out *= (p - 1) * p ** (e - 1)
    return out


# ------------------------------------------------------- confinement algebra --
def rho_t(P_mod: int, v: int, t: int) -> int:
    """The least POSITIVE integer congruent to -v P_n modulo 2^t (value in [1,2^t])."""
    r = (-v * P_mod) % (1 << t)
    return r if r else (1 << t)


def excluded(P_mod: int, v: int, t: int, R_upper) -> bool:
    """True iff the single residue P_n mod 2^t refutes (c, v) for every c <= n - t."""
    return rho_t(P_mod, v, t) > v * R_upper


def equality_fails_without_size_hypothesis() -> dict:
    """Control a_n=n, S=2, n=3, t=1: least positive residue is not the carry.

    Type B r3: the generic argument proves congruence and u_n <= v(n+2), not
    equality of the least positive representative with u_n, unless u_n <= 2^t.
    """
    g = lambda m: m
    P = 0
    for m in range(1, 4):
        P = 2 * P + g(m)
    n, t, v, c = 3, 1, 1, 0
    S = Fr(2, 1)
    R = Fr(1 << n) * S - P
    u = int(v * R)
    r_plus = rho_t(P % (1 << t), v, t)
    return {
        "control": "a_n=n, S=2",
        "n": n, "t": t, "c": c, "v": v,
        "P_n": P, "u_n": u, "least_positive_residue": r_plus,
        "equality_fails": r_plus != u,
        "congruence_holds": (u + v * P) % (1 << t) == 0,
        "inequality_holds": 0 < r_plus <= u <= v * (n + 2),
        "size_hypothesis_u_le_2_t": u <= (1 << t),
        "exclusion_consumer_uses_only_inequality": True,
    }


# ------------------------------------------------------------------ PART A --
def part_a_surrogates(nmax: int = 400) -> dict:
    """The theorem against exact rationals S' = sum g(m) 2^-m with g(m) <= m."""
    cases = []

    # (i) g(m) = m : S = 2 = 2/(2^0 * 1), R_n = n+2 EXACTLY (the extremal tail)
    cases.append({"name": "g(m)=m", "a": 2, "c": 0, "v": 1,
                  "g": (lambda m: m), "kappa": (lambda n: n + 2)})
    # (ii) g(m) = m on even m : S = 8/9, odd part 9, tail of order n
    cases.append({"name": "g(m)=m*[2|m]", "a": 8, "c": 0, "v": 9,
                  "g": (lambda m: m if m % 2 == 0 else 0), "kappa": (lambda n: n + 2)})
    # (iii) g(m) = m on 3|m : S = 24/49, odd part 49
    cases.append({"name": "g(m)=m*[3|m]", "a": 24, "c": 0, "v": 49,
                  "g": (lambda m: m if m % 3 == 0 else 0), "kappa": (lambda n: n + 2)})
    # (iv) binary digits of a/(2^c v) : bounded tail, exercises c > 0 and odd v
    for (a, c, v) in [(1, 0, 3), (1, 0, 7), (1, 0, 63), (3, 5, 7), (5, 9, 341)]:
        cases.append({"name": "digits of %d/(2^%d*%d)" % (a, c, v), "a": a, "c": c, "v": v,
                      "g": (lambda m, a=a, c=c, v=v: (a * 2 ** m) // (v * 2 ** c) % 2),
                      "kappa": (lambda n: 1)})

    rows = []
    for case in cases:
        a, c, v, g, kappa = case["a"], case["c"], case["v"], case["g"], case["kappa"]
        S = Fr(a, (1 << c) * v)
        P = 0
        bad_int = bad_pos = bad_up = bad_cong = bad_excl = 0
        false_excluded = false_tested = 0
        for n in range(1, nmax + 1):
            P = 2 * P + g(n)
            R = Fr(1 << n) * S - P
            if n >= c:
                u = v * R
                if u.denominator != 1:
                    bad_int += 1
                u = int(u)
                if u <= 0:
                    bad_pos += 1
                if u > v * kappa(n):
                    bad_up += 1
                for t in range(0, min(n - c, 30) + 1):
                    if (u + v * P) % (1 << t) != 0:
                        bad_cong += 1
                    # the true (c,v) must never be excluded
                    if excluded(P % (1 << t), v, t, kappa(n)):
                        bad_excl += 1
            # teeth: how many WRONG odd v are excluded by this residue.  The
            # modulus is calibrated to the LARGEST v tested, else the test is
            # vacuous for the big v by construction.
            t = min(n, (63 * kappa(n)).bit_length() + 4)
            if 1 <= t <= n:
                Pm = P % (1 << t)
                for vv in range(1, 64, 2):
                    if vv == v:
                        continue
                    false_tested += 1
                    if excluded(Pm, vv, t, kappa(n)):
                        false_excluded += 1
        rows.append({
            "case": case["name"], "S": str(S), "a": a, "c": c, "v": v,
            "n_range": [1, nmax],
            "u_n_not_integer": bad_int, "u_n_not_positive": bad_pos,
            "u_n_above_v_kappa": bad_up, "congruence_failures": bad_cong,
            "true_(c,v)_wrongly_excluded": bad_excl,
            "wrong_v_tested": false_tested, "wrong_v_excluded": false_excluded,
            "teeth_fraction": round(false_excluded / false_tested, 4) if false_tested else None,
        })
    ok = all(r["u_n_not_integer"] == 0 and r["u_n_not_positive"] == 0
             and r["u_n_above_v_kappa"] == 0 and r["congruence_failures"] == 0
             and r["true_(c,v)_wrongly_excluded"] == 0 for r in rows)
    lat = lattice_adversarial(cases, nmax)
    return {"all_surrogates_consistent_with_the_theorem": ok and lat["all_safe"],
            "rows": rows, "lattice_certificate_adversarial": lat,
            "note": ("g(m)=m is the extremal case u_n = v kappa(n) exactly, so it "
                     "certifies that the upper bound in the theorem cannot be improved "
                     "by any additive constant. It also has ZERO teeth, correctly: "
                     "S = 2 is an integer, so a/(2^c v) holds for EVERY odd v and no v "
                     "may be excluded.")}


def lattice_adversarial(cases, nmax: int) -> dict:
    """The lattice certificate must NEVER certify past the true odd part v.

    For a genuine S = a/(2^c v) the lattice {(w,u) : u == -w P_n mod 2^t} contains
    the point (v, u_n) with 1 <= u_n <= v kappa(n), so the reduced lambda_1 is at
    most sqrt2 * v * kappa(n) and the certificate can return at most v - 1.  This
    is the sharpest available test of the reduction code: it fails loudly if the
    Gauss reduction ever over-reports.
    """
    rows = []
    for case in cases:
        c, v, g, kappa = case["c"], case["v"], case["g"], case["kappa"]
        P = 0
        worst = -1
        for n in range(1, nmax + 1):
            P = 2 * P + g(n)
            if n < c + 4:
                continue
            for t in (n - c, min(n - c, 40)):
                if t < 1:
                    continue
                W = int(kappa(n))
                cert = lattice_certificate(P % (1 << t), t, W)
                worst = max(worst, cert["certified_all_odd_v_le"])
        rows.append({"case": case["name"], "true_v": v,
                     "max_v_ever_certified": worst, "safe": worst < v})
    return {"all_safe": all(r["safe"] for r in rows), "rows": rows}


# ------------------------------------------------------------------ PART B --
def tail_R_bounds_sieved(n: int, ph, terms: int = 100):
    acc = Fr(0)
    for j in range(1, terms + 1):
        acc += Fr(ph[n + j], 1 << j)
    return acc, acc + Fr(n + terms + 1, 1 << terms)


def prefix_window(n: int, width: int, phi_at) -> int:
    """P_n mod 2^width = sum_{j<width} 2^j phi(n-j): only the last `width` letters."""
    P = 0
    for j in range(min(width, n) - 1, -1, -1):
        P += phi_at(n - j) << j
    return P & ((1 << width) - 1)


def part_b_desk_e_rectangle(n: int, ph, Vcheck: int = 4001) -> dict:
    """Reproduce desk E's n = 2786632 rectangle and give the t-staircase."""
    P = prefix_window(n, 96, lambda m: ph[m])
    t_max = (P & -P).bit_length() - 1
    Rlo, Rhi = tail_R_bounds_sieved(n, ph, 100)
    stair = []
    for t in range(1, t_max + 1):
        Pm = P % (1 << t)
        vs = [v for v in range(1, Vcheck, 2) if excluded(Pm, v, t, Rhi)]
        largest = 0
        for v in range(1, Vcheck, 2):
            if excluded(Pm, v, t, Rhi):
                largest = v
            else:
                break
        stair.append({"t": t, "all_c_le": n - t,
                      "P_n_mod_2^t": int(Pm),
                      "odd_v_excluded_up_to_(contiguous)": largest,
                      "odd_v_excluded_count_below_%d" % Vcheck: len(vs),
                      "closed_form_bound_2^t/R_n": round(float(Fr(1 << t) / Rhi), 4)})
    return {"n": n, "v_2(P_n)": t_max, "R_n_lower": float(Rlo), "R_n_upper": float(Rhi),
            "desk_E_rectangle": {"t": t_max, "all_c_le": n - t_max,
                                 "all_odd_v_le": max(v for v in range(1, Vcheck, 2)
                                                     if excluded(P % (1 << t_max),
                                                                 v, t_max, Rhi))
                                 if any(excluded(P % (1 << t_max), v, t_max, Rhi)
                                        for v in range(1, Vcheck, 2)) else 0},
            "staircase_over_t": stair,
            "reading": ("For every t <= v_2(P_n) the residue is 0, so rho_t(v) = 2^t and "
                        "the excluded v-set is exactly {odd v < 2^t / R_n}: SMALLER v-range "
                        "but LARGER c-range. The union over t is a staircase strictly "
                        "containing desk E's single rectangle; the gain is one exponent "
                        "per halving of the v-range, i.e. cosmetic. The real enlargement "
                        "is Part C/E, which does not need 2^t | P_n at all.")}


# ------------------------------------------------------------------ PART C --
def part_c_template(n: int, t: int, ph, V: int) -> dict:
    """List odd v <= V not excluded by the single residue P_n mod 2^t."""
    Pm = prefix_window(n, t, lambda m: ph[m])
    Rlo, Rhi = tail_R_bounds_sieved(n, ph, 100)
    survivors = [v for v in range(1, V + 1, 2) if not excluded(Pm, v, t, Rhi)]
    tested = (V + 1) // 2
    return {"n": n, "t": t, "all_c_le": n - t, "P_n_mod_2^t": int(Pm),
            "R_n_upper": float(Rhi), "odd_v_tested": tested,
            "odd_v_excluded": tested - len(survivors),
            "survivors": survivors[:40],
            "survivor_count": len(survivors),
            "heuristic_survivor_count": round(sum(v * float(Rhi) / (1 << t)
                                                  for v in range(1, V + 1, 2)), 3)}


# ------------------------------------------------------------------ PART D --
def prefix_array(X: int, ph) -> "np.ndarray":
    """P_n mod 2^64 for 1 <= n <= X, by the 6-pass doubling scan."""
    ext = np.concatenate([np.zeros(63, dtype=np.int64),
                          np.asarray(ph[1:X + 1], dtype=np.int64)])
    C = ext.astype(np.uint64)
    s = 1
    while s <= 32:
        sh = np.zeros_like(C)
        sh[s:] = C[:-s]
        C = C + (sh << np.uint64(s))
        s *= 2
    return C[63:]                                     # index k <-> n = k+1


def _bl_blocks(v: int, nlo: int, nhi: int):
    """Yield (n_start, n_end, bitlength) where bitlength(v(n+1)) is constant."""
    b = (v * (nlo + 1)).bit_length()
    while True:
        # v(n+1) < 2^b  <=>  n+1 <= ceil(2^b / v) - 1
        end = min(nhi, -(-(1 << b) // v) - 2)
        if end >= nlo:
            yield (nlo, end, b)
        if end >= nhi:
            return
        nlo = end + 1
        b = (v * (nlo + 1)).bit_length()


def part_d_occupancy(X: int, Pm: "np.ndarray", vs, deltas) -> dict:
    """Fraction of n whose forced residue lands in the admissible band (0, v R_n]."""
    rows = []
    for v in vs:
        for d in deltas:
            hit = tot = 0
            heur = 0.0
            for (a, b_, bl) in _bl_blocks(v, 64, X):
                t = bl + d
                if t >= 64:
                    continue
                lo = max(a, t)                        # need t <= n
                if lo > b_:
                    continue
                P = Pm[lo - 1:b_]                     # n = lo..b_
                ns = np.arange(lo, b_ + 1, dtype=np.uint64)
                w = np.uint64(v) * (ns + np.uint64(1))
                mask = np.uint64((1 << t) - 1)
                rho = (np.uint64(0) - np.uint64(v) * P) & mask
                # rho == 0 means the true residue is 2^t > w, hence NOT a band hit
                hit += int(np.count_nonzero((rho != 0) & (rho <= w)))
                tot += int(ns.size)
                heur += float(np.sum(w.astype(np.float64))) / float(1 << t)
            rows.append({"v": v, "delta": d, "n_tested": tot, "band_hits": hit,
                         "observed_fraction": round(hit / tot, 6) if tot else None,
                         "heuristic_fraction": round(heur / tot, 6) if tot else None,
                         "ratio": round(hit / heur, 4) if heur else None,
                         "excluded_fraction": round(1 - hit / tot, 6) if tot else None})
    return {"X": X, "rows": rows,
            "reading": ("The forced residue lands in the rationality-admissible band "
                        "at essentially the density a uniform residue would, so the "
                        "true totient prefix supplies no anti-correlation to exploit; "
                        "equivalently, ONE n excludes a fixed odd v with probability "
                        "1 - 2^-delta, which is why the v-uniform kill of D' is generic.")}


def part_d_first_uniform(X: int, Pm: "np.ndarray", Vmax: int = 63,
                         deltas=(0, 1, 2, 3, 4, 5, 6)) -> dict:
    """n at which EVERY odd v <= Vmax is excluded at one common modulus 2^t.

    Reports the FIRST such n (a curiosity), the DENSITY of such n (the honest
    statistic: the v-uniform kill is generic, not exceptional), and the LARGEST
    such n in range, whose c-bound is the best rectangle the scan reaches.
    """
    out = []
    odd_v = list(range(1, Vmax + 1, 2))
    for d in deltas:
        first = last = None
        good = tot = 0
        heur = 0.0
        for (a, b_, bl) in _bl_blocks(Vmax, 8, X):
            t = bl + d
            if t >= 64:
                continue
            lo = max(a, t)
            if lo > b_:
                continue
            P = Pm[lo - 1:b_]
            ns = np.arange(lo, b_ + 1, dtype=np.uint64)
            mask = np.uint64((1 << t) - 1)
            ok = np.ones(ns.size, dtype=bool)
            hp = np.ones(ns.size, dtype=np.float64)
            for v in odd_v:
                rho = (np.uint64(0) - np.uint64(v) * P) & mask
                w = np.uint64(v) * (ns + np.uint64(1))
                ok &= (rho == 0) | (rho > w)          # rho == 0 means rho_t = 2^t > w
                hp *= np.clip(1.0 - w.astype(np.float64) / float(1 << t), 0.0, 1.0)
            good += int(np.count_nonzero(ok))
            heur += float(hp.sum())
            tot += int(ns.size)
            idx = np.nonzero(ok)[0]
            if idx.size:
                if first is None:
                    n0 = int(ns[idx[0]])
                    first = {"n": n0, "t": t, "all_c_le": n0 - t, "all_odd_v_le": Vmax}
                n1 = int(ns[idx[-1]])
                last = {"n": n1, "t": t, "all_c_le": n1 - t, "all_odd_v_le": Vmax}
        out.append({"delta": d, "n_tested": tot,
                    "first_simultaneous_exclusion": first,
                    "best_c_bound_in_range": last,
                    "density_of_n_that_kill_all_odd_v": round(good / tot, 5) if tot else None,
                    "independence_heuristic_density": round(heur / tot, 7) if tot else None,
                    "observed_over_heuristic": round(good / heur, 3) if heur else None})
    return {"Vmax": Vmax, "rows": out,
            "correlation_note": (
                "The independence heuristic prod_v (1 - v(n+1)/2^t) is a LOWER bound in "
                "practice: the 32 events share one residue P_n mod 2^t, so they are "
                "positively correlated and the observed density exceeds the product at "
                "small delta (by ~10^3 at delta = 0). That correlation is a lattice fact "
                "about the map v -> (-v P_n mod 2^t), not a signal about phi; the v = 1 "
                "row of Part D shows the single-v occupancy is flat to within 3%.",),
            "reading": ("The v-uniform kill is GENERIC, not exceptional: a positive "
                        "and rapidly rising fraction of ALL n excludes every odd "
                        "v <= 63 at once. That is what separates this from E10, "
                        "which needs the rare event 2^t | P_n.")}


# ------------------------------------------------------------------ PART E --
def gauss_reduce(b1, b2):
    """Exact integer Lagrange-Gauss reduction of a rank-2 lattice."""
    def dot(x, y):
        return x[0] * y[0] + x[1] * y[1]
    while True:
        if dot(b1, b1) > dot(b2, b2):
            b1, b2 = b2, b1
        num, den = dot(b1, b2), dot(b1, b1)
        mu = (2 * num + den) // (2 * den)              # nearest integer, exact
        b2 = (b2[0] - mu * b1[0], b2[1] - mu * b1[1])
        if dot(b2, b2) >= dot(b1, b1):
            return b1, b2


def isqrt(n: int) -> int:
    return math.isqrt(n)


def lattice_certificate(P_mod: int, t: int, W: int) -> dict:
    """Largest V for which NO (v,u) has 1<=v<=V, 1<=u<=vW, u == -vP mod 2^t.

    The set L = {(v,u) : u == A v mod 2^t}, A = (-P) mod 2^t, is a lattice of
    determinant 2^t.  Scaling v by W maps the search box into
    (0, VW] x (0, VW], so lambda_1^inf(L') > VW certifies emptiness, and
    lambda_1^inf >= lambda_1^2 / sqrt 2.  Everything is exact integer work.
    """
    A = (-P_mod) % (1 << t)
    b1, b2 = gauss_reduce((W, A), (0, 1 << t))
    l1sq = b1[0] * b1[0] + b1[1] * b1[1]
    # need 2 (V W)^2 < l1sq
    Vmax = (isqrt((l1sq - 1) // 2)) // W
    return {"t": t, "W_used_as_R_n_upper_bound": W,
            "lambda_1_squared": l1sq,
            "log2_lambda_1": round(math.log2(l1sq) / 2, 4) if l1sq > 0 else None,
            "certified_all_odd_v_le": Vmax,
            "log10_certified_v": round(math.log10(Vmax), 3) if Vmax > 0 else None}


def part_e_record(n: int, t: int, rnd: random.Random, scan_V: int = 0) -> dict:
    """Certified rectangle at a large n, using only phi on a window of length t."""
    t0 = time.time()
    ws = [phi_big(n - j, rnd) for j in range(t)]
    P_mod = 0
    for j in range(t - 1, -1, -1):
        P_mod = (P_mod + (ws[j] << j))
    P_mod &= (1 << t) - 1
    W = n + 1                                          # rigorous R_n <= n+1
    cert = lattice_certificate(P_mod, t, W)
    out = {"n": n, "log10_n": round(math.log10(n), 4), "t": t,
           "all_c_le": n - t, "certificate": cert,
           "phi_window_seconds": round(time.time() - t0, 2)}
    if scan_V:
        surv = [v for v in range(1, scan_V + 1, 2)
                if not excluded(P_mod, v, t, W)]
        out["brute_force_cross_check"] = {
            "odd_v_scanned_to": scan_V, "survivors": surv,
            "agrees_with_certificate": (not surv) and cert["certified_all_odd_v_le"] >= scan_V}
    return out


# --------------------------------------------------------------------- main --
def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--out")
    ap.add_argument("--big-n", type=int, default=None)
    ap.add_argument("--big-t", type=int, default=None)
    args = ap.parse_args()
    rnd = random.Random(20260905)

    quick = args.quick
    rep = {"mode": "quick" if quick else "full"}
    t0 = time.time()

    rep["part_a_surrogates"] = part_a_surrogates(200 if quick else 400)
    rep["equality_countermodel_a_n_n"] = equality_fails_without_size_hypothesis()

    Xocc = 1 << 16 if quick else 1 << 20
    ph = totient_sieve(max(Xocc + 200, 4000))
    Pm = prefix_array(Xocc, ph)
    rep["part_d_occupancy"] = part_d_occupancy(
        Xocc, Pm, (1, 3, 5, 7, 15, 63), (0, 1, 2, 3, 4, 5, 6))
    rep["part_d_first_v_uniform_exclusion"] = part_d_first_uniform(Xocc, Pm)

    rep["part_c_template_example"] = part_c_template(
        4096 if quick else 65536, 30 if quick else 36, ph, 999)

    if not quick:
        phbig = totient_sieve(2786632 + 200)
        rep["part_b_desk_e_rectangle"] = part_b_desk_e_rectangle(2786632, phbig)
    else:
        rep["part_b_desk_e_rectangle"] = part_b_desk_e_rectangle(88, ph)

    bn = args.big_n if args.big_n else (10 ** 12 if quick else 10 ** 18)
    bt = args.big_t if args.big_t else (256 if quick else 2048)
    rep["part_e_record_rectangle"] = part_e_record(
        bn, bt, rnd, scan_V=20001 if quick else 200001)
    if not quick:
        rep["part_e_tradeoff_table"] = [
            part_e_record(n, t, rnd) for (n, t) in
            [(10 ** 12, 256), (10 ** 15, 512), (10 ** 18, 1024),
             (10 ** 21, 1024), (10 ** 24, 1024)]]

    rep["elapsed_s"] = round(time.time() - t0, 2)
    rep["claim_boundary"] = (
        "PROVED: the confinement theorem and the exclusion template (Part A checks "
        "them against exact rationals, including the extremal surrogate g(m)=m where "
        "the upper bound is attained). CERTIFIED BY COMPUTATION: the specific "
        "rectangles reported. NOT PROVED and not approached: that every (c,v) is "
        "excluded, which is the parent. Every rectangle here is finite and the "
        "machine's reach per unit of work is O(t) totient evaluations near n, so the "
        "reachable c grows only as fast as the largest n whose neighbourhood can be "
        "factored, and the reachable v only as 2^{t/2}.")

    if args.out:
        with open(args.out, "w") as fh:
            json.dump(rep, fh, indent=1)
    if args.json:
        print(json.dumps(rep, indent=1))
    else:
        a = rep["part_a_surrogates"]
        eq = rep["equality_countermodel_a_n_n"]
        print("A  confinement theorem vs exact rational surrogates: %s"
              % ("ALL CONSISTENT" if a["all_surrogates_consistent_with_the_theorem"]
                 else "FAILURE"))
        print("   equality countermodel a_n=n n=3 t=1: r_+=%s u=%s equality_fails=%s"
              % (eq["least_positive_residue"], eq["u_n"], eq["equality_fails"]))
        for r in a["rows"]:
            print("     %-28s S=%-10s (c,v)=(%d,%d)  true pair excluded %d times; "
                  "wrong v excluded %d/%d" %
                  (r["case"], r["S"], r["c"], r["v"], r["true_(c,v)_wrongly_excluded"],
                   r["wrong_v_excluded"], r["wrong_v_tested"]))
        la = a["lattice_certificate_adversarial"]
        print("   lattice certificate never over-reports: %s" % la["all_safe"])
        for r in la["rows"]:
            print("        %-28s true v = %-5d max v ever certified = %-5d safe=%s"
                  % (r["case"], r["true_v"], r["max_v_ever_certified"], r["safe"]))
        b = rep["part_b_desk_e_rectangle"]
        print("B  n=%d  v_2(P_n)=%d  R_n=%.4f  ->  desk E rectangle: all c <= %d, "
              "all odd v <= %d" % (b["n"], b["v_2(P_n)"], b["R_n_lower"],
                                   b["desk_E_rectangle"]["all_c_le"],
                                   b["desk_E_rectangle"]["all_odd_v_le"]))
        print("     t-staircase (smaller t: wider c, narrower v):")
        for s in b["staircase_over_t"][-8:]:
            print("        t=%-3d c <= %-10d odd v <= %-6d (2^t/R_n = %.2f)" %
                  (s["t"], s["all_c_le"], s["odd_v_excluded_up_to_(contiguous)"],
                   s["closed_form_bound_2^t/R_n"]))
        c = rep["part_c_template_example"]
        print("C  template at n=%d, t=%d: %d of %d odd v <= 999 excluded by ONE residue "
              "(survivors %s; heuristic count %.2f)" %
              (c["n"], c["t"], c["odd_v_excluded"], c["odd_v_tested"],
               c["survivors"], c["heuristic_survivor_count"]))
        print("D  band occupancy (fraction NOT excluded), X = %d:" % rep["part_d_occupancy"]["X"])
        print("     %-4s %-7s %-9s %-9s %-6s" % ("v", "delta", "observed", "heuristic", "ratio"))
        for r in rep["part_d_occupancy"]["rows"]:
            print("     %-4d %-7d %-9.6f %-9.6f %-6.4f" %
                  (r["v"], r["delta"], r["observed_fraction"],
                   r["heuristic_fraction"], r["ratio"]))
        print("D' n killing EVERY odd v <= 63 at one modulus (v-uniform finite exclusion):")
        print("     %-7s %-9s %-11s %-12s %-11s" %
              ("delta", "first n", "density", "indep.heur", "best c <= "))
        for r in rep["part_d_first_v_uniform_exclusion"]["rows"]:
            f, l = r["first_simultaneous_exclusion"], r["best_c_bound_in_range"]
            print("     %-7d %-9s %-11s %-12s %-11s" %
                  (r["delta"], (f["n"] if f else "-"),
                   r["density_of_n_that_kill_all_odd_v"],
                   r["independence_heuristic_density"],
                   (l["all_c_le"] if l else "-")))
        e = rep["part_e_record_rectangle"]
        cert = e["certificate"]
        print("E  record rectangle: n = 10^%.2f, t = %d, phi window in %.1fs" %
              (e["log10_n"], e["t"], e["phi_window_seconds"]))
        print("     CERTIFIED: S != a/(2^c v) for every c <= %d and every odd v <= 10^%.2f"
              % (e["all_c_le"], cert["log10_certified_v"]))
        if "brute_force_cross_check" in e:
            x = e["brute_force_cross_check"]
            print("     brute-force cross-check to odd v <= %d: survivors %s (agrees: %s)"
                  % (x["odd_v_scanned_to"], x["survivors"], x["agrees_with_certificate"]))
        if "part_e_tradeoff_table" in rep:
            print("     trade-off (cost is O(t) totient evaluations near n, not O(n)):")
            for r in rep["part_e_tradeoff_table"]:
                print("        n=10^%-5.1f t=%-6d %6.1fs   c <= %-24d odd v <= 10^%.2f"
                      % (r["log10_n"], r["t"], r["phi_window_seconds"], r["all_c_le"],
                         r["certificate"]["log10_certified_v"]))
        print(rep["claim_boundary"])
    return 0


if __name__ == "__main__":
    sys.exit(main())
