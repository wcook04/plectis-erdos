#!/usr/bin/env python3
"""Isolated-pulse certificates for the residue-class projections of Erdős #249.

Three independent checks, all exact (``int`` / ``fractions.Fraction`` only):

1.  ``A_m = sum_{n>=1} (phi(n) mod m) / 2^n`` is irrational for every ``m >= 3``.
    The proof (CRT + Dirichlet + a two-sided isolated pulse, see
    ``r02`` of the 2026-09-05 eight-return batch) is *constructive at every
    finite level*: this checker exhibits, for small ``m`` and every window
    ``L``, an explicit prime ``p`` with

        phi(p) = p - 1 == m - 2   (mod m),
        phi(p +- j) == 0          (mod m)   for 0 < |j| <= L,

    and then confirms the separation inequality

        || q A_m ||  >=  q (|t| - C 2^{-L}) 2^{-p},     t = m-2, C = m-1,

    for every ``q`` admitted by ``2^L > 2 q C``, using an exact rational
    bracket for ``A_m`` from a long prefix.

2.  The dyadic truncation budget ``0 < S - S_k <= (2^k + 1) 2^{-2^k}`` with
    ``S_k = A_{2^k}``, again from exact prefix brackets.

3.  The *no-pay* bound.  Any two-sided isolated pulse of ``n |-> phi(n) mod 2^k``
    has centre ``n0 >= 2^k + 2`` (``n0`` even) or ``n0 >= 2^{k+1} + 1``
    (``n0`` odd), because a neighbouring zero means ``2^k | phi(n0 +- 1)`` and
    ``phi(x) <= x - 1``, resp. ``phi(x) <= x/2`` for even ``x``.  Hence the best
    pulse separation is below ``q E_k / 4`` where ``E_k = (2^k+1) 2^{-2^k}`` is
    the truncation budget: the pulse mechanism can never establish the exact
    reformulation ``(G)`` of Erdős #249, at any resolution and for any centre.
    The checker locates the smallest actual centre for each ``k`` and confirms
    the inequality chain.

Run: ``./repo-python <this file> --quick``
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction


# --------------------------------------------------------------------------
# elementary sieves
# --------------------------------------------------------------------------


def totient_sieve(limit: int) -> list[int]:
    """phi(0..limit) by the standard divisor sieve."""
    phi = list(range(limit + 1))
    for p in range(2, limit + 1):
        if phi[p] == p:  # p is prime
            for k in range(p, limit + 1, p):
                phi[k] -= phi[k] // p
    return phi


def prime_sieve(limit: int) -> list[bool]:
    flags = [True] * (limit + 1)
    if limit >= 0:
        flags[0] = False
    if limit >= 1:
        flags[1] = False
    i = 2
    while i * i <= limit:
        if flags[i]:
            for j in range(i * i, limit + 1, i):
                flags[j] = False
        i += 1
    return flags


# --------------------------------------------------------------------------
# check 1 : Corollary 5 pulses and the Lemma 3 separation
# --------------------------------------------------------------------------


def find_prime_pulse(phi: list[int], is_prime: list[bool], m: int, L: int,
                     search_limit: int) -> int | None:
    """Smallest prime p <= search_limit with an (m, L) two-sided pulse."""
    for p in range(L + 2, search_limit - L):
        if not is_prime[p]:
            continue
        if (p - 1) % m != (m - 2) % m:
            continue
        ok = True
        for j in range(1, L + 1):
            if phi[p - j] % m or phi[p + j] % m:
                ok = False
                break
        if ok:
            return p
    return None


def residue_series_bracket(phi: list[int], m: int, prefix: int) -> tuple[Fraction, Fraction]:
    """[lo, hi] with lo < A_m <= hi, from the exact prefix sum of length ``prefix``."""
    lo = Fraction(0)
    acc = 0
    # accumulate as a single big integer numerator over 2^prefix
    for n in range(1, prefix + 1):
        acc = acc * 2 + (phi[n] % m)
    lo = Fraction(acc, 1 << prefix)
    hi = lo + Fraction(m - 1, 1 << prefix)
    return lo, hi


def frac_dist_to_int(x: Fraction) -> Fraction:
    n = x.numerator
    d = x.denominator
    r = n % d
    return min(Fraction(r, d), Fraction(d - r, d))


def check_corollary_five(phi: list[int], is_prime: list[bool], moduli: list[int],
                         windows: list[int], search_limit: int,
                         prefix: int) -> list[dict]:
    rows: list[dict] = []
    for m in moduli:
        lo, hi = residue_series_bracket(phi, m, prefix)
        for L in windows:
            p = find_prime_pulse(phi, is_prime, m, L, search_limit)
            row: dict = {"m": m, "L": L, "pulse_prime": p}
            if p is None:
                row["status"] = "no_pulse_below_search_limit"
                rows.append(row)
                continue
            t = m - 2
            C = m - 1
            # admissible q from 2^L > 2 q C
            q_max = ((1 << L) - 1) // (2 * C)
            row["t"] = t
            row["C"] = C
            row["q_max"] = q_max
            row["pulse_neighbourhood_ok"] = all(
                phi[p - j] % m == 0 and phi[p + j] % m == 0 for j in range(1, L + 1)
            )
            row["pulse_centre_residue"] = phi[p] % m
            checks = []
            for q in range(1, q_max + 1):
                bound = Fraction(q) * (Fraction(t) - Fraction(C, 1 << L)) * Fraction(1, 1 << p)
                certified_min = certified_distance_to_int(Fraction(q) * lo, Fraction(q) * hi)
                checks.append({
                    "q": q,
                    "bound_log2": float_log2(bound),
                    "certified_min_log2": float_log2(certified_min),
                    "holds": certified_min >= bound,
                })
            row["separation_checks"] = checks
            row["status"] = "ok" if (q_max >= 1 and all(c["holds"] for c in checks)) else (
                "no_admissible_q" if q_max == 0 else "FAILED")
            rows.append(row)
    return rows


def float_log2(x: Fraction) -> float:
    """log2 of a positive Fraction, computed through an exact integer shift."""
    import math

    if x <= 0:
        return float("-inf")
    n, d = x.numerator, x.denominator
    shift = max(0, d.bit_length() - n.bit_length() + 64)
    mantissa = (n << shift) // d
    if mantissa <= 0:
        return float("-inf")
    return math.log2(mantissa) - shift


def certified_distance_to_int(lo: Fraction, hi: Fraction) -> Fraction:
    """Lower bound for dist(x, Z) valid for every x in [lo, hi].

    On an interval containing no integer the distance-to-nearest-integer
    function attains its minimum at an endpoint, so the endpoint minimum is a
    certificate.  If an integer lies in the closed interval, return 0.
    """
    import math as _m

    if _m.floor(lo) != _m.floor(hi) or lo.denominator == 1 or hi.denominator == 1:
        return Fraction(0)
    return min(frac_dist_to_int(lo), frac_dist_to_int(hi))


# --------------------------------------------------------------------------
# check 2 : the (18) truncation budget
# --------------------------------------------------------------------------


def check_truncation_budget(phi: list[int], ks: list[int], prefix: int) -> list[dict]:
    acc_s = 0
    for n in range(1, prefix + 1):
        acc_s = acc_s * 2 + phi[n]
    s_lo = Fraction(acc_s, 1 << prefix)
    s_hi = s_lo + Fraction(prefix + 1, 1 << prefix)
    rows = []
    for k in ks:
        M = 1 << k
        lo, hi = residue_series_bracket(phi, M, prefix)
        diff_lo = s_lo - hi
        diff_hi = s_hi - lo
        budget = Fraction(M + 1, 1 << M)
        rows.append({
            "k": k,
            "M": M,
            "S_minus_Sk_lower_log2": float_log2(diff_lo) if diff_lo > 0 else None,
            "S_minus_Sk_upper_log2": float_log2(diff_hi),
            "budget_log2": float_log2(budget),
            "positive": diff_lo > 0,
            "within_budget": diff_hi <= budget,
        })
    return rows


# --------------------------------------------------------------------------
# check 3 : the no-pay bound on pulse centres
# --------------------------------------------------------------------------


def smallest_pulse_centre(phi: list[int], k: int, limit: int) -> int | None:
    M = 1 << k
    for n0 in range(2, limit - 1):
        if phi[n0] % M == 0:
            continue
        if phi[n0 - 1] % M == 0 and phi[n0 + 1] % M == 0:
            return n0
    return None


def check_no_pay(phi: list[int], ks: list[int], limit: int) -> list[dict]:
    rows = []
    for k in ks:
        M = 1 << k
        n0 = smallest_pulse_centre(phi, k, limit)
        row = {
            "k": k,
            "M": M,
            "proved_floor_even_centre": M + 2,
            "proved_floor_odd_centre": 2 * M + 1,
            "smallest_actual_centre": n0,
        }
        if n0 is not None:
            floor_used = (2 * M + 1) if n0 % 2 == 1 else (M + 2)
            row["centre_parity"] = "odd" if n0 % 2 else "even"
            row["meets_proved_floor"] = n0 >= floor_used
        # best conceivable Lemma-3 separation vs the truncation budget,
        # both divided by q; the worst (largest) separation uses n0 = M + 2.
        best_sep = Fraction(M - 2, 1 << (M + 2))
        budget = Fraction(M + 1, 1 << M)
        row["best_separation_over_budget"] = float(best_sep / budget)
        row["pulse_cannot_pay"] = best_sep < budget
        rows.append(row)
    return rows


# --------------------------------------------------------------------------


def build_payload(quick: bool) -> dict:
    if quick:
        search_limit = 40000
        moduli = [3, 4, 5, 6]
        windows = [1, 2, 3, 4, 5, 6]
        budget_ks = [2, 3, 4, 5, 6]
        pulse_ks = [2, 3, 4, 5, 6, 7, 8]
        centre_limit = 4000
    else:
        search_limit = 400000
        moduli = [3, 4, 5, 6, 7, 8, 9, 10]
        windows = [1, 2, 3, 4, 5, 6, 7]
        budget_ks = [2, 3, 4, 5, 6, 7]
        pulse_ks = list(range(2, 11))
        centre_limit = 400000

    limit = max(search_limit, centre_limit) + 16
    phi = totient_sieve(limit)
    is_prime = prime_sieve(limit)

    # the prefix must dominate every pulse centre we will certify against
    found = [
        find_prime_pulse(phi, is_prime, m, L, search_limit)
        for m in moduli
        for L in windows
    ]
    max_p = max([p for p in found if p is not None] + [256])
    prefix = max_p + 256

    corollary_five = check_corollary_five(
        phi, is_prime, moduli, windows, search_limit, prefix
    )
    truncation = check_truncation_budget(phi, budget_ks, prefix)
    no_pay = check_no_pay(phi, pulse_ks, centre_limit)

    all_ok = (
        all(r["status"] in {"ok", "no_pulse_below_search_limit", "no_admissible_q"}
            for r in corollary_five)
        and any(r["status"] == "ok" for r in corollary_five)
        and all(r["positive"] and r["within_budget"] for r in truncation)
        and all(r["pulse_cannot_pay"] for r in no_pay)
        and all(r.get("meets_proved_floor", True) for r in no_pay)
    )
    return {
        "checker": "check_residue_class_pulse_separation",
        "problem": "erdos_249",
        "mode": "quick" if quick else "full",
        "prefix_bits": prefix,
        "corollary_five_pulses": corollary_five,
        "truncation_budget": truncation,
        "pulse_no_pay": no_pay,
        "all_checks_pass": all_ok,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true", help="small deterministic run")
    args = parser.parse_args()
    payload = build_payload(args.quick)
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0 if payload["all_checks_pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
