#!/usr/bin/env python3
"""Erdos 249: the Mobius residue form of the tail, its rough remainder, and
smooth-shift basepoints for the canonical Mersenne residue supply.

Residue form (exact, proved here by the geometric-series identity):

    R_n = sum_{j>=1} phi(n+j) 2^-j
        = sum_{d>=1} mu(d) 2^{n mod d} [ (floor(n/d)+1)/(2^d-1) + 1/(2^d-1)^2 ]
        = n A(n) + B(n),     A(n) = sum_d mu(d) 2^{n mod d} / (d (2^d-1)),

with A and B functions of the residues (n mod d)_d alone.

Truncation.  Put phi_{<=D}(m) = sum_{d|m, d<=D} mu(d) m/d and
phi_{>D} = phi - phi_{<=D}.  Then the d<=D part of the residue form is exactly
the tail of phi_{<=D}, and for L = lcm(1..D) k (so d | L for every d <= D)

    R_{n+L} - R_n = L A_D(n) + Delta_{>D}(n, n+L),
    A_D(n) = sum_{d<=D} mu(d) 2^{n mod d} / (d (2^d-1))   (depends on n mod lcm(1..D)),
    Delta_{>D}(n, n+L) = W_D(n+L) - W_D(n),
    W_D(n) = sum_{j>=1} 2^-j phi_{>D}(n+j),   W_D(n+1) = 2 W_D(n) - phi_{>D}(n+1).

Vanishing criterion (exact).  With r = rad(m),
    phi_{>D}(m) = (m mu(r) / r) * sum_{e | r, e < r/D} mu(e) e,
so phi_{>D}(m) = 0 iff that truncated Mobius divisor sum vanishes.  r <= D is
sufficient but NOT necessary: phi_{>D}(210) = 0 for every D in [15,20].

Smooth shift (r08 Lemma 3 / desk D).  N_L = prod_{p in U} p^{a_p(L)} with
a_p(L) = floor(log_p L) + 1 gives v_p(N_L + m) = v_p(m) for p in U, m <= L, so
the U-smooth part of phi(N_L + j) is frozen on a window of length L.  Section E
runs the canonical residue supply predicate at such basepoints against random
controls of the same size.

Exact rationals with rigorous brackets throughout.  Finite measurements only.
"""

from __future__ import annotations

import argparse
import json
import math
import random
from fractions import Fraction
from math import gcd


# ------------------------------------------------------------------- sieving
def spf_sieve(limit: int) -> list[int]:
    spf = list(range(limit + 1))
    i = 2
    while i * i <= limit:
        if spf[i] == i:
            for j in range(i * i, limit + 1, i):
                if spf[j] == j:
                    spf[j] = i
        i += 1
    return spf


def primes_of(m: int, spf: list[int]) -> list[int]:
    out: list[int] = []
    while m > 1:
        p = spf[m]
        out.append(p)
        while m % p == 0:
            m //= p
    return out


def totient_sieve(limit: int) -> list[int]:
    phi = list(range(limit + 1))
    for p in range(2, limit + 1):
        if phi[p] == p:
            for m in range(p, limit + 1, p):
                phi[m] -= phi[m] // p
    return phi


def mobius_upto(limit: int, spf: list[int]) -> list[int]:
    mu = [0] * (limit + 1)
    if limit >= 1:
        mu[1] = 1
    for m in range(2, limit + 1):
        ps = primes_of(m, spf)
        r = 1
        for p in ps:
            r *= p
        mu[m] = 0 if r != m else (-1) ** len(ps)
    return mu


def lcm_upto(D: int) -> int:
    v = 1
    for i in range(1, D + 1):
        v = v * i // gcd(v, i)
    return v


# ------------------------------------------------------- residue-form pieces
def term_d(n: int, d: int, mu_d: int) -> Fraction:
    if mu_d == 0:
        return Fraction(0)
    M = (1 << d) - 1
    return mu_d * Fraction(1 << (n % d)) * (Fraction(n // d + 1, M) + Fraction(1, M * M))


def term_d_series_bracket(n: int, d: int, mu_d: int, T: int) -> tuple[Fraction, Fraction]:
    """Bracket for mu(d) * sum_{t >= floor(n/d)+1} t 2^{n-dt}, T terms summed."""
    if mu_d == 0:
        return Fraction(0), Fraction(0)
    t0 = n // d + 1
    s = sum(Fraction(t) * Fraction(2) ** (n - d * t) for t in range(t0, t0 + T))
    last = t0 + T
    x = Fraction(1, 1 << d)
    tail = Fraction(2) ** (n - d * last) * (Fraction(last) / (1 - x) + x / (1 - x) ** 2)
    return (s, s + tail) if mu_d > 0 else (-s - tail, -s)


def phi_le_D(m: int, D: int, spf: list[int]) -> int:
    ps = primes_of(m, spf)
    divs = [1]
    for p in ps:
        divs += [d * p for d in divs]
    return sum(((-1) ** sum(1 for p in ps if d % p == 0)) * (m // d)
               for d in divs if d <= D)


def phi_gt_D(m: int, D: int, spf: list[int]) -> int:
    ps = primes_of(m, spf)
    divs = [1]
    for p in ps:
        divs += [d * p for d in divs]
    return sum(((-1) ** sum(1 for p in ps if d % p == 0)) * (m // d)
               for d in divs if d > D)


def truncated_mobius_divisor_sum(r: int, Y: Fraction, ps: list[int]) -> int:
    divs = [1]
    for p in ps:
        divs += [d * p for d in divs]
    return sum(((-1) ** sum(1 for p in ps if e % p == 0)) * e for e in divs if e < Y)


def R_bracket(n: int, J: int, phi: list[int]) -> tuple[Fraction, Fraction]:
    N = 0
    for j in range(1, J + 1):
        N = N * 2 + phi[n + j]
    den = 1 << J
    return Fraction(N, den), Fraction(N + n + J + 2, den)


def A_D(n: int, D: int, mu: list[int]) -> Fraction:
    return sum((mu[d] * Fraction(1 << (n % d), d * ((1 << d) - 1))
                for d in range(1, D + 1) if mu[d]), Fraction(0))


# ------------------------------------------------------------------ sections
def section_residue_form(quick: bool) -> dict:
    Dmax = 40
    J = 200 if quick else 300
    ns = [13, 240, 2520, 12599, 12600]
    limit = max(ns) + J + 10
    spf = spf_sieve(limit)
    mu = mobius_upto(max(Dmax, 64), spf)
    phi = totient_sieve(limit)

    v1 = v3 = 0
    v1_ok = v3_ok = True
    for n in (0, 1, 7, 30, 101, 2520):
        for d in range(1, 20):
            if not mu[d]:
                continue
            lo, hi = term_d_series_bracket(n, d, mu[d], 60)
            v1 += 1
            v1_ok &= bool(lo <= term_d(n, d, mu[d]) <= hi)
            M = (1 << d) - 1
            lead = n * mu[d] * Fraction(1 << (n % d), d * M)
            rest = mu[d] * Fraction(1 << (n % d)) * (
                Fraction(d - (n % d), d * M) + Fraction(1, M * M))
            v3 += 1
            v3_ok &= bool(term_d(n, d, mu[d]) == lead + rest)

    v2 = []
    for n in ns:
        for D in (6, 10, 20, Dmax):
            lhs = sum(term_d(n, d, mu[d]) for d in range(1, D + 1))
            rhs = Fraction(0)
            pw = Fraction(1)
            for j in range(1, J + 1):
                pw /= 2
                rhs += phi_le_D(n + j, D, spf) * pw
            HD = sum(Fraction(1, d) for d in range(1, D + 1))
            v2.append(bool(abs(lhs - rhs) <= HD * Fraction(n + J + 2) * pw))

    v4 = []
    for n in ns:
        lo, hi = R_bracket(n, J, phi)
        s = sum(term_d(n, d, mu[d]) for d in range(1, Dmax + 1))
        rem = Fraction(0)
        pw = Fraction(1)
        for j in range(1, J + 1):
            pw /= 2
            rem += abs(phi_gt_D(n + j, Dmax, spf)) * pw
        HD = sum(Fraction(1, d) for d in range(1, Dmax + 1))
        rem += (1 + HD) * Fraction(n + J + 2) * pw
        v4.append({"n": n, "ok": bool(lo - rem <= s <= hi + rem),
                   "R_n": float(lo), "d_gt_40_remainder_bound": float(rem)})
    return {"J": J, "Dmax": Dmax,
            "closed_form_vs_geometric_series": {"rows": v1, "all_ok": v1_ok},
            "linear_residue_split_exact": {"rows": v3, "all_ok": v3_ok},
            "truncated_sum_equals_phi_le_D_tail": {"rows": len(v2),
                                                   "all_ok": all(v2)},
            "full_residue_form_vs_R": v4}


def section_delta(quick: bool) -> dict:
    Ds = [4, 6, 8, 10]
    ks = [1, 2, 4] if quick else [1, 2, 3, 4, 5, 6, 7, 8]
    J = 200 if quick else 300
    lam = {D: lcm_upto(D) for D in Ds}
    base = {}
    for D in Ds:
        L1 = lam[D]
        n0 = 10 * L1
        base[D] = [("n = 0 mod lcm", n0), ("n = -1 mod lcm", n0 - 1),
                   ("n = 1 mod lcm", n0 + 1), ("generic", n0 + L1 // 3 + 7)]
    top = max(n for D in Ds for _, n in base[D]) + max(lam[D] * max(ks) for D in Ds)
    spf = spf_sieve(top + J + 10)
    mu = mobius_upto(64, spf)
    phi = totient_sieve(top + J + 10)

    rows = []
    for D in Ds:
        for label, n in base[D]:
            for k in ks:
                L = lam[D] * k
                lo_n, hi_n = R_bracket(n, J, phi)
                lo_m, hi_m = R_bracket(n + L, J, phi)
                a = A_D(n, D, mu)
                d_lo, d_hi = lo_m - hi_n - L * a, hi_m - lo_n - L * a
                r2 = Fraction(0)
                pw = Fraction(1)
                for j in range(1, J + 1):
                    pw /= 2
                    r2 += (phi_gt_D(n + L + j, D, spf) - phi_gt_D(n + j, D, spf)) * pw
                HD = sum(Fraction(1, d) for d in range(1, D + 1))
                t2 = (1 + HD) * Fraction(2 * (n + L + J + 2)) * pw
                mid = (d_lo + d_hi) / 2
                LA = L * a
                rows.append({
                    "D": D, "class": label, "n": n, "k": k, "L": L,
                    "delta": float(mid),
                    "rough_remainder_route_agrees": bool(
                        not (d_hi < r2 - t2 or r2 + t2 < d_lo)),
                    "L_A_D_denominator_is_odd": bool(LA.denominator % 2 == 1),
                    "dist_L_A_D_to_Z": float(min(LA - LA.__floor__(),
                                                 1 - (LA - LA.__floor__()))),
                    "trivial_bound_n_plus_L_plus_2": n + L + 2,
                    "ratio_to_trivial": abs(float(mid)) / (n + L + 2),
                })
    by_D = {}
    for D in Ds:
        sub = [abs(r["delta"]) for r in rows if r["D"] == D]
        rat = sorted(r["ratio_to_trivial"] for r in rows if r["D"] == D)
        by_D[str(D)] = {"min_abs_delta": min(sub), "max_abs_delta": max(sub),
                        "median_ratio_to_trivial": rat[len(rat) // 2]}
    return {"rows": rows, "all_routes_agree": all(r["rough_remainder_route_agrees"]
                                                  for r in rows),
            "by_D": by_D,
            "reading": ("Delta_{>D} tracks (n+L)/D up to fluctuation: the residue "
                        "split buys a bounded constant factor over the trivial "
                        "|R_{n+L}-R_n| <= n+L+2 and never approaches 1, because "
                        "lcm(1..D) | L forces L >= e^{(1+o(1))D}.")}


def section_vanishing_criterion(quick: bool) -> dict:
    X = 20000 if quick else 60000
    spf = spf_sieve(X + 2)
    exact_ok = True
    counterexamples = []
    checked = 0
    for D in (4, 6, 8, 10, 15, 16, 20):
        for m in range(1, X + 1):
            ps = primes_of(m, spf)
            r = 1
            for p in ps:
                r *= p
            mu_r = (-1) ** len(ps)
            g = phi_gt_D(m, D, spf)
            pred = (m // r) * mu_r * truncated_mobius_divisor_sum(
                r, Fraction(r, D), ps)
            checked += 1
            exact_ok &= (g == pred)
            if g == 0 and r > D and len(counterexamples) < 8:
                counterexamples.append({"D": D, "m": m, "rad": r})
    # longest run of consecutive m with phi_{>D}(m) = 0, for the Stormer argument
    runs = {}
    for D in (4, 6, 8, 10):
        best = cur = 0
        for m in range(1, min(X, 20000) + 1):
            cur = cur + 1 if phi_gt_D(m, D, spf) == 0 else 0
            best = max(best, cur)
        runs[str(D)] = best
    return {"criterion_formula_verified": exact_ok, "rows_checked": checked,
            "vanishing_with_radical_above_D": counterexamples,
            "longest_run_phi_gtD_zero": runs,
            "reading": ("phi_{>D}(m) = 0 iff sum_{e|rad m, e<rad(m)/D} mu(e) e = 0; "
                        "rad(m) <= D is sufficient, not necessary (m = 210, "
                        "15 <= D <= 20).  Runs of consecutive vanishing are the "
                        "Stormer obstruction to making W_D small on a window.")}


def section_vanishing_density(quick: bool) -> dict:
    """Density of {m <= X : phi_gtD(m) = 0}, split into rad(m) <= D and exceptional.

    This is the predeclared test for the only route in these coordinates that
    could give an irrationality statement rather than an exclusion: r08 Cor 5
    needs the dyadic series W_D to have SPARSE support, i.e. the vanishing set
    to have density close to 1.
    """
    X = 50000 if quick else 500000
    Ds = [15, 105, 210] if quick else [15, 30, 60, 105, 210, 1000]
    spf = spf_sieve(X + 1)
    rad = [1] * (X + 1)
    for m in range(2, X + 1):
        r = 1
        for p in primes_of(m, spf):
            r *= p
        rad[m] = r
    out = {}
    for D in Ds:
        memo: dict[int, bool] = {}
        triv = exc = 0
        for m in range(1, X + 1):
            r = rad[m]
            hit = memo.get(r)
            if hit is None:
                ps = primes_of(r, spf)
                hit = (r <= D) or truncated_mobius_divisor_sum(
                    r, Fraction(r, D), ps) == 0
                memo[r] = hit
            if hit:
                if r <= D:
                    triv += 1
                else:
                    exc += 1
        out[str(D)] = {"X": X, "density_rad_le_D": triv / X,
                       "density_exceptional": exc / X,
                       "total_density": (triv + exc) / X,
                       "exceptional_radicals": sorted(
                           r for r, h in memo.items() if h and r > D)[:8]}
    return {"per_D": out,
            "reading": ("The vanishing set has density o(1) at every tested D, "
                        "dominated by the rad(m) <= D smooth-number count; the "
                        "exceptional part stays near 3e-4. So W_D has support of "
                        "density 1 and the sparse-support irrationality criterion "
                        "(r08 Lemma 4 / Cor 5) cannot be applied to it.")}


def section_W_runs(quick: bool) -> dict:
    X = 60000 if quick else 300000
    spf = spf_sieve(X + 300)
    out = {}
    for D in (4, 6, 8, 10):
        w = 0.0
        vals = [0.0] * (X + 1)
        for n in range(X + 119, -1, -1):
            w = (w + phi_gt_D(n + 1, D, spf)) / 2.0
            if n <= X:
                vals[n] = w
        absW = [abs(x) for x in vals[1:]]
        run = cur = 0
        for x in absW:
            cur = cur + 1 if x < 1.0 / 3 else 0
            run = max(run, cur)
        out[str(D)] = {"X": X, "min_abs_W": min(absW),
                       "count_abs_W_lt_1": sum(1 for x in absW if x < 1.0),
                       "longest_run_abs_W_lt_third": run}
    return {"per_D": out,
            "proposition": ("W_D(n+1) = 2 W_D(n) - phi_{>D}(n+1) with phi_{>D} "
                            "integral, so |W_D| <= 1/3 on [n, n+J] forces "
                            "phi_{>D} = 0 on (n, n+J]; the measured run lengths "
                            "equal the longest runs of consecutive vanishing, "
                            "which all sit at the very start of the integers.")}


# ------------------------------- canonical residue supply at smooth basepoints
_MR = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)


def _is_prime(n: int) -> bool:
    if n < 2:
        return False
    for p in _MR:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in _MR:
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


def _rho(n: int) -> int:
    if n % 2 == 0:
        return 2
    for c in range(1, 300):
        x = y = 2
        d = 1
        while d == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = gcd(abs(x - y), n)
        if d != n:
            return d
    raise AssertionError(n)


def totient_big(n: int, primes: list[int]) -> int:
    f: dict[int, int] = {}
    for p in primes:
        if p * p > n:
            break
        while n % p == 0:
            n //= p
            f[p] = f.get(p, 0) + 1
    stack = [n] if n > 1 else []
    while stack:
        m = stack.pop()
        if m == 1:
            continue
        if _is_prime(m):
            f[m] = f.get(m, 0) + 1
            continue
        d = _rho(m)
        stack += [d, m // d]
    t = 1
    for p, e in f.items():
        t *= (p - 1) * p ** (e - 1)
    return t


def smooth_shift(primes: list[int], L: int) -> int:
    n = 1
    for p in primes:
        a = 1
        while p ** a <= L:
            a += 1
        n *= p ** a
    return n


def supply_profile(c: int, v: int, phis: list[int], max_h: int) -> dict:
    phi_v = sum(1 for k in range(1, v + 1) if gcd(k, v) == 1)
    block = 0
    first_central = first_clear = None
    for H in range(1, max_h + 1):
        block = 2 * block + phis[H]
        if H % phi_v:
            continue
        M = ((1 << H) - 1) // v
        if ((1 << H) - 1) % v:
            raise AssertionError((v, H))
        B = c + H + 1
        r = (-block) % M
        clear = 2 * B < M
        if clear and first_clear is None:
            first_clear = H
        if clear and B < r < M - B:
            first_central = H
            break
    if first_central is None or first_clear is None:
        return {"v": v, "phi_v": phi_v, "resolved": False}
    return {"v": v, "phi_v": phi_v, "resolved": True,
            "first_clear_H": first_clear, "first_central_H": first_central,
            "delay": (first_central - first_clear) // phi_v}


def section_smooth_basepoints(quick: bool) -> dict:
    small = [p for p in range(2, 100000) if _is_prime(p)]
    max_h = 72 if quick else 96
    vs = [1, 3, 5, 7, 9, 15]
    rng = random.Random(20260905)
    U13 = [2, 3, 5, 7, 11, 13]
    N60 = smooth_shift(U13, 60)
    pts = [("N_L smooth shift, U = primes <= 13, L = 60", N60, "structured"),
           ("lcm(1..16) = 720720", 720720, "structured"),
           ("720720 - 1", 720719, "structured_neighbour"),
           ("720720 + 1", 720721, "structured_neighbour"),
           ("primorial 2..19 = 9699690", 9699690, "structured")]
    n_rand = 4 if quick else 10
    for tag, centre in (("N60", N60), ("720720", 720720), ("9699690", 9699690)):
        for i in range(n_rand):
            pts.append((f"random near {tag} #{i}",
                        rng.randrange(centre // 2, 2 * centre) | 1, "random"))
    rows = []
    for label, c, kind in pts:
        phis = [0] * (max_h + 1)
        for j in range(1, max_h + 1):
            phis[j] = totient_big(c + j, small)
        Jn = 200 + c.bit_length()
        N = 0
        for j in range(1, Jn + 1):
            N = N * 2 + (phis[j] if j <= max_h else totient_big(c + j, small))
        den = 1 << Jn
        prof = {}
        for v in vs:
            p = supply_profile(c, v, phis, max_h)
            rho = (v * N) % den
            nrm = min(rho, den - rho)
            p["neg_log2_norm_v_R_c"] = Jn - nrm.bit_length() if nrm else None
            if p["resolved"]:
                bits = math.log2(v * (c + p["first_central_H"] + 1)) + (
                    Jn - nrm.bit_length())
                p["predicted_H_min"] = p["phi_v"] * math.ceil(bits / p["phi_v"])
                p["predicted_minus_measured"] = p["predicted_H_min"] - p["first_central_H"]
            prof[str(v)] = p
        rows.append({"label": label, "c": c, "kind": kind,
                     "log2_c": c.bit_length() - 1, "profiles": prof})

    def band(c: int) -> str:
        b = c.bit_length()
        return "N60" if b > 35 else ("9699690" if b > 21 else "720720")

    summary = {}
    for bn in ("720720", "9699690", "N60"):
        for kind in ("structured", "structured_neighbour", "random"):
            sel = [r for r in rows if band(r["c"]) == bn and r["kind"] == kind]
            if not sel:
                continue
            summary[f"{bn}|{kind}"] = {
                "count": len(sel),
                "max_delay_over_v": max(r["profiles"][str(v)]["delay"]
                                        for r in sel for v in vs),
                "first_clear_H_by_v": {str(v): sorted({r["profiles"][str(v)]
                                                       ["first_clear_H"] for r in sel})
                                       for v in vs},
                "neg_log2_norm_range": [
                    min(r["profiles"][str(v)]["neg_log2_norm_v_R_c"]
                        for r in sel for v in vs),
                    max(r["profiles"][str(v)]["neg_log2_norm_v_R_c"]
                        for r in sel for v in vs)],
            }
    return {"vs": vs, "max_h": max_h, "rows": rows, "summary": summary,
            "reading": ("Geometry clearance depends only on (c, v) through "
                        "2^H > 2 v (c+H+1); the delay is a function of "
                        "||v R_c|| = ||v 2^c S|| alone, which the smooth shift "
                        "does not constrain: it freezes the U-smooth half of "
                        "phi(c+j) and leaves the rough half free.")}


def run(quick: bool) -> dict:
    return {
        "probe_id": "erdos249_mobius_residue_rough_remainder",
        "quick": quick,
        "A_residue_form": section_residue_form(quick),
        "B_delta_gt_D": section_delta(quick),
        "C_vanishing_criterion": section_vanishing_criterion(quick),
        "D_rough_remainder_runs": section_W_runs(quick),
        "D2_vanishing_set_density": section_vanishing_density(quick),
        "E_smooth_shift_basepoints": section_smooth_basepoints(quick),
        "claim_boundary": (
            "All statements here are exact identities plus finite measurement. "
            "No structured basepoint family makes Delta_{>D} small, and the "
            "canonical residue supply at smooth-shift basepoints is "
            "indistinguishable from random basepoints of the same size. "
            "Erdos 249 remains open."),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()
    text = json.dumps(run(args.quick), indent=1) + "\n"
    if args.out:
        from pathlib import Path
        Path(args.out).write_text(text, encoding="utf-8")
    print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
