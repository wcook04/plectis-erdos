#!/usr/bin/env python3
"""Erdos 249: the h-difference tail coordinate T_h(m) = R_{m+h} - R_m.

Coordinates
-----------
    R_n   = sum_{j>=1} phi(n+j) 2^-j = 2^n S - P_n,   0 < R_n <= n+2
    T_h(m)= R_{m+h} - R_m = 2^m (2^h - 1) S - (P_{m+h} - P_m)

Ordinary proofs certified numerically here
------------------------------------------
(A) recurrence      T_h(m+1) = 2 T_h(m) - (phi(m+1+h) - phi(m+1))
(B) confinement     -(m+2) < T_h(m) < m+h+2
(C) integrality     if S = a/(2^c v) with v odd, v | 2^h - 1 and c <= m, then
                    T_h(m) is an integer; so a certified |T_h(m)| < 1 with
                    T_h(m) != 0 excludes every such (c,v) with c <= m.
(D) tail-only form  {2^C S} = {R_C}, and R_C depends only on phi(C+1..C+J).
                    If S = a/(2^c v) with c <= C then v R_C is an integer.
                    So ONE exact tail evaluation at C excludes the whole
                    rectangle {c <= C} x {odd v <= V} whenever ||v R_C|| beats
                    the truncation bracket.  Cost is O(J) totients, not O(C).

Every real quantity carries a rigorous rational bracket: with
    N_J(n) = sum_{j=1}^J phi(n+j) 2^{J-j},
    N_J(n) / 2^J  <  R_n  <=  (N_J(n) + n + J + 2) / 2^J.

Finite exclusions only.  Erdos 249 remains open.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction


# --------------------------------------------------------------- small sieve
def totient_sieve(limit: int) -> list[int]:
    phi = list(range(limit + 1))
    for p in range(2, limit + 1):
        if phi[p] == p:  # p prime
            for m in range(p, limit + 1, p):
                phi[m] -= phi[m] // p
    return phi


def small_primes(limit: int) -> list[int]:
    sieve = bytearray([1]) * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    i = 2
    while i * i <= limit:
        if sieve[i]:
            sieve[i * i:: i] = bytearray(len(sieve[i * i:: i]))
        i += 1
    return [i for i in range(limit + 1) if sieve[i]]


# ------------------------------------------------------- big-number factoring
_MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    for p in _MR_BASES:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in _MR_BASES:
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def _gcd(a: int, b: int) -> int:
    while b:
        a, b = b, a % b
    return a


def brent_rho(n: int) -> int:
    """Brent's variant of Pollard rho; deterministic parameter ladder."""
    if n % 2 == 0:
        return 2
    for c in range(1, 500):
        y, m = 2, 128
        g = q = 1
        r = 1
        x = ys = y
        while g == 1:
            x = y
            for _ in range(r):
                y = (y * y + c) % n
            k = 0
            while k < r and g == 1:
                ys = y
                for _ in range(min(m, r - k)):
                    y = (y * y + c) % n
                    q = q * abs(x - y) % n
                g = _gcd(q, n)
                k += m
            r *= 2
        if g == n:
            g = 1
            y = ys
            while g == 1:
                y = (y * y + c) % n
                g = _gcd(abs(x - y), n)
        if g != n:
            return g
    raise AssertionError(f"rho failed on {n}")


def factorise(n: int, primes: list[int]) -> dict[int, int]:
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
        if is_prime(m):
            f[m] = f.get(m, 0) + 1
            continue
        d = brent_rho(m)
        stack.append(d)
        stack.append(m // d)
    return f


def totient_big(n: int, primes: list[int]) -> int:
    t = 1
    for p, e in factorise(n, primes).items():
        t *= (p - 1) * p ** (e - 1)
    return t


# --------------------------------------------------------------- exact tails
def tail_numerator(n: int, J: int, phi_at) -> int:
    """N_J(n) = sum_{j=1}^J phi(n+j) 2^{J-j}, computed by Horner."""
    acc = 0
    for j in range(1, J + 1):
        acc = acc * 2 + phi_at(n + j)
    return acc


def R_bracket(n: int, J: int, phi_at) -> tuple[Fraction, Fraction]:
    N = tail_numerator(n, J, phi_at)
    den = 1 << J
    return Fraction(N, den), Fraction(N + n + J + 2, den)


# ------------------------------------------------------------------ sections
def section_recurrence_and_confinement(J: int) -> dict:
    limit = 4000 + J + 80
    phi = totient_sieve(limit)
    at = phi.__getitem__
    rows = []
    ok_rec = ok_conf = ok_R = True
    for h in (1, 2, 6, 12, 60):
        for m in (1, 2, 37, 500, 1234, 3000):
            lo_a, hi_a = R_bracket(m + h, J, at)
            lo_b, hi_b = R_bracket(m, J, at)
            t_lo, t_hi = lo_a - hi_b, hi_a - lo_b
            lo_a1, hi_a1 = R_bracket(m + 1 + h, J, at)
            lo_b1, hi_b1 = R_bracket(m + 1, J, at)
            t1_lo, t1_hi = lo_a1 - hi_b1, hi_a1 - lo_b1
            rhs_lo = 2 * t_lo - (phi[m + 1 + h] - phi[m + 1])
            rhs_hi = 2 * t_hi - (phi[m + 1 + h] - phi[m + 1])
            rec = not (t1_hi < rhs_lo or rhs_hi < t1_lo)
            conf = (-(m + 2) < t_lo) and (t_hi < m + h + 2)
            rr = (0 < lo_b) and (hi_b <= m + 2 + Fraction(1, 1 << (J - 20)))
            ok_rec &= rec
            ok_conf &= conf
            ok_R &= rr
            rows.append({"h": h, "m": m, "recurrence_ok": rec,
                         "confinement_ok": conf, "R_bounds_ok": rr})
    return {"rows_checked": len(rows), "recurrence_all_ok": ok_rec,
            "confinement_all_ok": ok_conf, "R_bounds_all_ok": ok_R,
            "sample": rows[:4]}


def backward_T(h: int, X: int, phi: list[int], pad: int = 96) -> list[float]:
    """T_h(m) for m = 0..X by the stable backward recurrence
       T_h(m) = (T_h(m+1) + phi(m+1+h) - phi(m+1)) / 2, seeded at X+pad."""
    t = 0.0
    out = [0.0] * (X + 1)
    for m in range(X + pad - 1, -1, -1):
        t = (t + phi[m + 1 + h] - phi[m + 1]) / 2.0
        if m <= X:
            out[m] = t
    return out


def section_near_zero_census(hs: list[int], X: int) -> dict:
    phi = totient_sieve(X + max(hs) + 200)
    res = {}
    for h in hs:
        T = backward_T(h, X, phi)
        cnt = {"lt_1": 0, "lt_0.1": 0, "lt_0.01": 0}
        best_m, best_v = None, None
        for m in range(1, X + 1):
            a = abs(T[m])
            if a < 1.0:
                cnt["lt_1"] += 1
                if a < 0.1:
                    cnt["lt_0.1"] += 1
                if a < 0.01:
                    cnt["lt_0.01"] += 1
                if best_v is None or a < best_v:
                    best_v, best_m = a, m
        res[str(h)] = {"counts": cnt, "record_m": best_m,
                       "record_abs_T_float": best_v}
    return {"X": X, "per_h": res}


def divisor_count_and_max(n: int, primes: list[int]) -> tuple[int, int]:
    """(number of divisors, largest divisor) -- the largest divisor is n itself."""
    f = factorise(n, primes)
    tau = 1
    for e in f.values():
        tau *= e + 1
    return tau, n


def section_record_certification(records: list[tuple[int, int]], J: int,
                                 primes: list[int]) -> dict:
    out = []
    for h, m in records:
        span = m + h + J + 4
        phi = totient_sieve(span)
        at = phi.__getitem__
        lo_a, hi_a = R_bracket(m + h, J, at)
        lo_b, hi_b = R_bracket(m, J, at)
        t_lo, t_hi = lo_a - hi_b, hi_a - lo_b
        width = t_hi - t_lo
        nonzero = (t_lo > 0) or (t_hi < 0)
        below_one = (abs(t_lo) < 1) and (abs(t_hi) < 1)
        mers = (1 << h) - 1
        tau, vmax = divisor_count_and_max(mers, primes)
        # certified "no integer in [t_lo, t_hi]"
        not_integer = (t_lo.__floor__() == t_hi.__floor__()) and (t_lo.denominator != 1)
        out.append({
            "h": h, "m": m,
            "T_lower": float(t_lo), "T_upper": float(t_hi),
            "bracket_width_log2": (width.denominator.bit_length()
                                   - width.numerator.bit_length()) * -1,
            "certified_nonzero": bool(nonzero),
            "certified_abs_below_one": bool(below_one),
            "certified_not_an_integer": bool(not_integer),
            "mersenne_2h_minus_1": str(mers),
            "admissible_odd_v_count": tau,
            "largest_admissible_odd_v": vmax,
            "exclusion": (f"S != a/(2^c v) for every c <= {m} and every one of "
                          f"the {tau} odd v dividing 2^{h}-1"),
        })
    return {"J": J, "records": out}


def divisors_from_factorisation(f: dict[int, int]) -> list[int]:
    divs = [1]
    for p, e in f.items():
        divs = [d * p ** k for d in divs for k in range(e + 1)]
    return sorted(divs)


def section_tail_only_exclusion(cs: list[int], vmax: int, mersenne_hs: list[int],
                                primes: list[int]) -> dict:
    """One exact tail evaluation at C excludes {c <= C} x {every odd v tested}.

    Uses only phi(C+1..C+J): R_C = 2^C S - P_C and P_C is an integer, so
    {2^C S} = {R_C}.  If S = a/(2^c v) with c <= C then v R_C is an integer.
    """
    vset = set(range(1, vmax + 1, 2))
    mersenne_detail = []
    for h in mersenne_hs:
        divs = divisors_from_factorisation(factorise((1 << h) - 1, primes))
        vset.update(divs)
        mersenne_detail.append({"h": h, "mersenne": str((1 << h) - 1),
                                "divisor_count": len(divs),
                                "largest_divisor": str(max(divs))})
    vlist = sorted(vset)
    vbits = max(v.bit_length() for v in vlist)
    out = []
    for C in cs:
        J = 200 + C.bit_length() + vbits
        N = 0
        for j in range(1, J + 1):
            N = N * 2 + totient_big(C + j, primes)
        den = 1 << J
        slack = C + J + 2                      # R_C in (N, N+slack) / 2^J
        worst_v, worst_margin = None, None
        failures = []
        for v in vlist:
            rho = (v * N) % den
            margin = min(rho, den - rho - v * slack)
            if margin <= 0:
                failures.append(v)
            if worst_margin is None or margin < worst_margin:
                worst_margin, worst_v = margin, v
        out.append({
            "C": str(C), "log10_C": len(str(C)) - 1, "J": J,
            "odd_v_tested": len(vlist),
            "largest_odd_v_tested": str(max(vlist)),
            "all_v_excluded": not failures,
            "failures": failures[:10],
            "worst_v": worst_v,
            "worst_margin_log2": (worst_margin.bit_length() - J
                                  if worst_margin and worst_margin > 0 else None),
            "truncation_bracket_log2": vbits + slack.bit_length() - J,
            "exclusion": (f"S != a/(2^c v) for every c <= {C} and every one of the "
                          f"{len(vlist)} tested odd v (all odd v <= {vmax}, plus "
                          f"every divisor of 2^h-1 for h in {mersenne_hs})")
            if not failures else "FAILED",
        })
    return {"vmax_dense": vmax, "mersenne_v_sets": mersenne_detail,
            "total_odd_v_tested": len(vlist), "ladder": out}


def section_consistency(J: int) -> dict:
    """{2^C S} = {R_C}: check R_C from the tail against 2^C S - P_C from a prefix."""
    C_list = [1, 5, 40, 200, 900]
    span = max(C_list) + J + 8
    phi = totient_sieve(span)
    at = phi.__getitem__
    rows = []
    B = 2 * span + 200
    phiB = totient_sieve(B + 4)
    S_lo = Fraction(sum(phiB[n] * (1 << (B - n)) for n in range(1, B + 1)), 1 << B)
    S_hi = S_lo + Fraction(B + 2, 1 << B)
    for C in C_list:
        P = 0
        for n in range(1, C + 1):
            P = P * 2 + phi[n]
        lhs_lo = (1 << C) * S_lo - P
        lhs_hi = (1 << C) * S_hi - P
        lo, hi = R_bracket(C, J, at)
        rows.append({"C": C, "ok": bool(not (hi < lhs_lo or lhs_hi < lo)),
                     "R_C": float(lo)})
    return {"rows": rows, "all_ok": all(r["ok"] for r in rows)}


def section_sliding_window_cross_check(C: int, J: int, vs: list[int]) -> dict:
    """Independent check of the tail evaluation.

    Corpus method: A_0 = sum_{j<=J} phi(j) 2^{J-j} mod 2^J, then
    A_{c+1} = 2 A_c + phi(c+J+1) mod 2^J, which needs phi(1..C+J).
    This desk's method needs only phi(C+1..C+J).  They must agree mod 2^J.
    """
    phi = totient_sieve(C + J + 2)
    den = 1 << J
    A = 0
    for j in range(1, J + 1):
        A = (A * 2 + phi[j]) % den
    for c in range(0, C):
        A = (2 * A + phi[c + J + 1]) % den
    N = 0
    for j in range(1, J + 1):
        N = N * 2 + phi[C + j]
    agree = (N % den) == A
    slack = C + J + 2
    rows = []
    for v in vs:
        rho = (v * N) % den
        rows.append({"v": v, "neg_log2_norm_v_R_C": J - min(rho, den - rho).bit_length(),
                     "excluded": bool(rho > 0 and (den - rho) > v * slack)})
    return {"C": C, "J": J, "sliding_window_agrees_with_tail_only": bool(agree),
            "per_v": rows}


def run(quick: bool) -> dict:
    primes = small_primes(200000)
    J = 320 if quick else 512
    census_X = 200000 if quick else 2000000
    hs = [1, 2, 4, 6, 12, 60]
    cs = [10 ** 7, 10 ** 9, 10 ** 12] if quick else [
        10 ** 7, 10 ** 9, 10 ** 12, 10 ** 15, 10 ** 18, 10 ** 24, 10 ** 30]
    vmax = 9999 if quick else 999999
    mersenne_hs = [6, 12, 60] if quick else [6, 12, 24, 36, 60]
    payload = {
        "probe_id": "erdos249_totient_difference_tail_near_zeros",
        "quick": quick,
        "coordinates": {
            "R_n": "sum_{j>=1} phi(n+j) 2^-j = 2^n S - P_n, 0 < R_n <= n+2",
            "T_h(m)": "R_{m+h} - R_m = 2^m (2^h-1) S - (P_{m+h} - P_m)",
            "bracket": "N_J(n)/2^J < R_n <= (N_J(n)+n+J+2)/2^J",
        },
        "A_recurrence_and_confinement": section_recurrence_and_confinement(240),
        "B_tail_prefix_consistency": section_consistency(240),
        "B2_sliding_window_cross_check": section_sliding_window_cross_check(
            20000 if quick else 200000, 220, [1, 3, 5, 7, 9, 11, 15, 31]),
        "C_near_zero_census": section_near_zero_census(hs, census_X),
        "D_record_certification": section_record_certification(
            [(6, 1380810), (60, 6425)] if not quick else [(60, 6425), (6, 13808)],
            J, primes),
        "E_tail_only_denominator_exclusion": section_tail_only_exclusion(
            cs, vmax, mersenne_hs, primes),
    }
    payload["claim_boundary"] = (
        "All exclusions are finite: each certifies one rectangle "
        "{c <= C} x {odd v in a finite set}. A cofinal statement needs a uniform "
        "lower bound ||v 2^c S|| >= c^-A over all odd v, which is strictly "
        "stronger than the irrationality of S. Erdos 249 remains open."
    )
    return payload


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()
    payload = run(args.quick)
    text = json.dumps(payload, indent=1) + "\n"
    if args.out:
        from pathlib import Path
        Path(args.out).write_text(text, encoding="utf-8")
    print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
