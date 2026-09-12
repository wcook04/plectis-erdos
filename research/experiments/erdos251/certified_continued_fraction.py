#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Reproduce the finite continued-fraction denominator calculation for Erdős 251.

Every emitted partial quotient is forced by an integer bracket. This program
checks finite arithmetic in Python; it does not run Lean or prove irrationality.
The paper supplies the analytic tail bound and explains the finite conclusion.
Run --problem erdos_251 --scale-bits 512 for a small example, or use the
recorded 80000-bit settings to compare with the shipped result.
"""

from __future__ import annotations

import math
from typing import Iterable

LEVY = math.pi ** 2 / (12 * math.log(2))     # 1.18656911... , limit of log(q_n)/n


def common_cf_prefix(lo: int, hi: int, scale_bits: int,
                     max_terms: int = 1 << 30) -> list[int]:
    """Continued-fraction quotients forced by the bracket `[lo, hi] / 2^scale_bits`.

    Emits a quotient only when both endpoints agree, so every returned term is
    certified for any real in the bracket.
    """
    if lo > hi:
        raise ValueError("bracket endpoints are out of order")
    scale = 1 << scale_bits
    a_num, a_den = lo, scale          # lower endpoint
    b_num, b_den = hi, scale          # upper endpoint
    quotients: list[int] = []
    while len(quotients) < max_terms:
        if a_den == 0 or b_den == 0:
            break
        qa = a_num // a_den
        qb = b_num // b_den
        if qa != qb:
            break
        quotients.append(qa)
        # x <= y have the same integer part, so frac(x) <= frac(y) and the
        # reciprocals swap order.
        a_num, a_den, b_num, b_den = (
            b_den, b_num - qb * b_den,
            a_den, a_num - qa * a_den,
        )
    return quotients


def convergents(quotients: Iterable[int]) -> list[tuple[int, int]]:
    """`[(p_0,q_0), (p_1,q_1), ...]` for the given quotient list."""
    p_prev, p_cur = 0, 1          # p_(-2), p_(-1)
    q_prev, q_cur = 1, 0          # q_(-2), q_(-1)
    out: list[tuple[int, int]] = []
    for a in quotients:
        p_prev, p_cur = p_cur, a * p_cur + p_prev
        q_prev, q_cur = q_cur, a * q_cur + q_prev
        out.append((p_cur, q_cur))
    return out


def denominator_power_bounds(denominator: int) -> dict[str, int]:
    """Exact size counts and exponents for ``q >= denominator > 1``.

    The decimal bound is strict, including when the denominator is a power
    of ten. No floating-point logarithm enters either certified exponent.
    """
    if denominator <= 1:
        raise ValueError("denominator must exceed one")
    lower, upper = 0, denominator.bit_length()
    while lower + 1 < upper:
        middle = (lower + upper) // 2
        if 10 ** middle < denominator:
            lower = middle
        else:
            upper = middle
    decimal_digits = lower + 1 + (10 ** (lower + 1) == denominator)
    return {
        "denominator_lower_bound_bit_length": denominator.bit_length(),
        "denominator_lower_bound_decimal_digits": decimal_digits,
        "denominator_lower_bound_power_of_two_exponent": denominator.bit_length() - 1,
        "strict_decimal_power_lower_bound": lower,
    }


def denominator_exclusion(lo: int, hi: int, scale_bits: int,
                          max_terms: int = 1 << 30) -> dict:
    """Certify a CF prefix and turn it into a lower bound on any denominator.

    Returns the bound `q >= q_(n+1)`, the evidence that `q_n S != p_n`, and the
    Gauss-Kuzmin / Levy statistics of the certified quotients.
    """
    quotients = common_cf_prefix(lo, hi, scale_bits, max_terms)
    if len(quotients) < 3:
        raise ValueError("bracket too wide to certify a usable prefix")
    conv = convergents(quotients)
    # Best approximation of the second kind needs q_(n+1), so the bound is read
    # off the last certified convergent and the separation is checked at the one
    # before it.
    p_n, q_n = conv[-2]
    _, q_next = conv[-1]
    scale = 1 << scale_bits
    low_side = q_n * lo - p_n * scale
    high_side = q_n * hi - p_n * scale
    separated = low_side != 0 and high_side != 0 and (low_side > 0) == (high_side > 0)
    if not separated:
        raise AssertionError("the bracket does not separate q_n S from p_n")

    # The right anomaly coordinate.  A large partial quotient `a_(i+1)` means
    # `|S - p_i/q_i| < 1/(a_(i+1) q_i^2)`, i.e. an approximation of exponent
    # `2 + log(a_(i+1))/log(q_i)`.  The raw maximum quotient is misleading:
    # Erdos 251 shows one of 973919, twenty-seven times the other targets, and
    # it contributes exponent 2.0007 -- entirely ordinary -- because it sits at
    # a denominator of about 10^8520.  Reported above rising denominator floors,
    # since at tiny `q` the ratio is dominated by `log q` being small.
    exponent_witness = {}
    for floor_bits in (100, 1000, 10000):
        best_exponent, best_index = 0.0, -1
        for i in range(1, len(quotients) - 1):
            q_i = conv[i - 1][1]
            if q_i < (1 << floor_bits):
                continue
            candidate = 2 + math.log(quotients[i]) / math.log(q_i)
            if candidate > best_exponent:
                best_exponent, best_index = candidate, i
        if best_index >= 0:
            exponent_witness[f"q_at_least_2_pow_{floor_bits}"] = {
                "max_exponent": best_exponent, "at_index": best_index}

    counts: dict[str, int] = {}
    for a in quotients:
        key = str(a) if a <= 5 else ("6-10" if a <= 10 else ("11-100" if a <= 100
                                                             else "101+"))
        counts[key] = counts.get(key, 0) + 1
    total = len(quotients)
    gauss_kuzmin = {}
    for k in range(1, 6):
        expected = math.log2(1 + 1.0 / (k * (k + 2)))
        observed = counts.get(str(k), 0) / total
        gauss_kuzmin[str(k)] = {"observed": observed, "expected": expected,
                                "z": (observed - expected) /
                                     math.sqrt(expected * (1 - expected) / total)}
    levy = math.log(q_next) / len(quotients)

    return {
        "certified_quotients": len(quotients),
        "scale_bits": scale_bits,
        "bracket_width": hi - lo,
        **denominator_power_bounds(q_next),
        "separation_verified": separated,
        "max_partial_quotient": max(quotients),
        "argmax_partial_quotient_index": quotients.index(max(quotients)),
        "irrationality_exponent_witness": exponent_witness,
        "partial_quotient_histogram": counts,
        "gauss_kuzmin": gauss_kuzmin,
        "levy_observed": levy,
        "levy_expected": LEVY,
        "levy_relative_error": abs(levy - LEVY) / LEVY,
        "first_quotients": quotients[:24],
    }


# --------------------------------------------------------------------------
# brackets
# --------------------------------------------------------------------------

def erdos68_bracket(scale_bits: int) -> tuple[int, int, int]:
    """`lo <= 2^B * sum_(n>=2) 1/(n!-1) <= hi`, exact integers.

    Each term is floored, losing under 1 apiece, and the omitted tail satisfies
    `sum_(n>N) 1/(n!-1) < 2/((N+1)!-1)` because
    `(n+1)!-1 > (n+1)((n)!-1)`.
    """
    scale = 1 << scale_bits
    total = 0
    factorial = 1
    terms = 0
    n = 1
    while True:
        n += 1
        factorial *= n
        denominator = factorial - 1
        if denominator > scale:
            break
        total += scale // denominator
        terms += 1
    # `n` is the first omitted index; its own denominator already exceeds 2^B.
    tail = 2 * scale // (factorial - 1) + 1
    return total, total + terms + tail, scale_bits


def erdos249_bracket(scale_bits: int) -> tuple[int, int, int]:
    """`lo <= 2^B * sum_(n>=1) phi(n)/2^n <= hi`, exact integers.

    The prefix through `N = B` is exact; the omitted tail is bounded by
    `sum_(n>N) n 2^(-n) = (N+2) 2^(-N)`.
    """
    limit = scale_bits
    phi = list(range(limit + 1))
    for p in range(2, limit + 1):
        if phi[p] == p:
            for k in range(p, limit + 1, p):
                phi[k] -= phi[k] // p
    total = 0
    for n in range(1, limit + 1):
        total += phi[n] << (scale_bits - n)
    return total, total + limit + 2, scale_bits


def erdos251_bracket(scale_bits: int) -> tuple[int, int, int]:
    """`lo <= 2^B * sum_(i>=0) p_i/2^(i+1) <= hi` for the zero-based primes.

    This is Lean's normalized prime series `dyadicPartialSumQ prime0`.  The
    actual prime-gap series differs from it by exactly 2 -- summation by parts
    gives `prime series = 2 + gap series` -- so the two have the *same*
    denominator and one certificate bounds both.

    The omitted tail is bounded by the module's own Lean-checked elementary
    estimate `p_i <= 1250(i+1)^4`, not by a heuristic prime bound.  Working at
    an internal scale `2^(B+128)` and shifting down keeps the bracket one unit
    wide, since the tail bound is around `2^77` and dies under the shift.
    """
    guard = 128
    inner = scale_bits + guard
    terms = inner                       # every exponent inner-(i+1) stays >= 0
    limit = terms + 16
    # zero-based primes p_0 = 2, ... by a sieve sized from the prime counting
    # estimate, grown until it holds enough.
    import math as _math
    bound = max(32, int((limit + 2) * (_math.log(limit + 2) +
                                       _math.log(_math.log(limit + 2)))) + 32)
    while True:
        sieve = bytearray([1]) * (bound + 1)
        sieve[0] = sieve[1] = 0
        for value in range(2, int(bound ** 0.5) + 1):
            if sieve[value]:
                sieve[value * value :: value] = bytearray(
                    len(sieve[value * value :: value]))
        primes = [i for i, flag in enumerate(sieve) if flag]
        if len(primes) >= terms:
            break
        bound *= 2
    total = 0
    for i in range(terms):
        total += primes[i] << (inner - i - 1)
    # 1250 * sum_(k>=0) (terms+k+1)^4 2^(-k-1) is under this, with room.
    tail = 4000 * (terms + 300) ** 4
    lo = total >> guard
    hi = ((total + tail) >> guard) + 1
    return lo, hi, scale_bits


BRACKETS = {"erdos_68": erdos68_bracket, "erdos_249": erdos249_bracket,
            "erdos_251": erdos251_bracket}


def self_check() -> dict:
    """Check the arithmetic against two expansions that are known in closed form.

    `e = [2;1,2,1,1,4,1,1,6,...]` exercises the interval algorithm, and the
    convergents of `pi` exercise the recurrence.  The recurrence was initialised
    with `p` and `q` transposed when this module was first written, which this
    catches immediately and a plausible-looking bound would not.
    """
    scale_bits = 512
    # e by its own factorial series, bracketed exactly:
    # lo <= 2^B e <= lo + (terms + 1), one unit per floored term plus the tail,
    # which is under 2/(N+1)! once (N+1)! > 2^B.
    scale = 1 << scale_bits
    total, factorial, terms = 0, 1, 0
    n = 0
    while factorial <= scale:
        total += scale // factorial
        terms += 1
        n += 1
        factorial *= n
    e_quotients = common_cf_prefix(total, total + terms + 1, scale_bits, 14)
    e_expected = [2, 1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 8, 1, 1]
    pi_convergents = convergents([3, 7, 15, 1, 292])[:4]
    pi_expected = [(3, 1), (22, 7), (333, 106), (355, 113)]
    if e_quotients != e_expected:
        raise AssertionError(f"interval expansion of e is wrong: {e_quotients}")
    if pi_convergents != pi_expected:
        raise AssertionError(f"convergent recurrence is wrong: {pi_convergents}")
    return {"e_prefix": e_quotients, "pi_convergents": pi_convergents,
            "status": "arithmetic_verified_against_known_expansions"}


def run(problem_id: str, scale_bits: int) -> dict:
    checked = self_check()
    lo, hi, bits = BRACKETS[problem_id](scale_bits)
    result = denominator_exclusion(lo, hi, bits)
    result["problem_id"] = problem_id
    result["self_check"] = checked
    return result


if __name__ == "__main__":
    import argparse
    import json

    ap = argparse.ArgumentParser()
    ap.add_argument("--problem", default="erdos_251", choices=sorted(BRACKETS))
    ap.add_argument("--scale-bits", type=int, default=512)
    args = ap.parse_args()
    if args.scale_bits < 32:
        ap.error("--scale-bits must be at least 32")
    print(json.dumps(run(args.problem, args.scale_bits), indent=2, default=str))
