#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Replay the exact continued-fraction denominator certificate for Erdos #68.

The bracket and Euclidean recurrences use integer arithmetic throughout.
The mathematical bracket and denominator argument are explained in the #68
paper. This is an exact arithmetic replay, not a Lean proof.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
from typing import Iterable

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


def replay(bits: int) -> dict:
    if not 128 <= bits <= 1000000:
        raise ValueError("scale bits must lie between 128 and 1000000")
    self_check()
    lo, hi, _ = erdos68_bracket(bits)
    prefix = common_cf_prefix(lo, hi, bits)
    if len(prefix) < 3 or any(a < 1 for a in prefix[1:]):
        raise AssertionError("invalid continued-fraction prefix")
    conv = convergents(prefix)
    p, q = conv[-2]
    q_next = conv[-1][1]
    low_error, high_error = q * lo - p * (1 << bits), q * hi - p * (1 << bits)
    if not (low_error > 0 and high_error > 0 or low_error < 0 and high_error < 0):
        raise AssertionError("penultimate convergent is not separated from the bracket")
    bound_bits = q_next.bit_length() - 1
    decimal_power, upper = 0, bound_bits
    while decimal_power + 1 < upper:
        mid = (decimal_power + upper) // 2
        if 10 ** mid < (1 << bound_bits):
            decimal_power = mid
        else:
            upper = mid
    def integer_hash(n: int) -> str:
        return "sha256:" + hashlib.sha256(n.to_bytes((n.bit_length()+7)//8, "big")).hexdigest()
    result = {
        "schema": "erdos68-continued-fraction-certificate/1",
        "series": "sum_{n>=2} 1/(n!-1)",
        "evidence": "exact integer arithmetic with an ordinary continued-fraction proof",
        "source_sha256": "sha256:" + hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scale_bits": bits,
        "bracket_width": hi - lo,
        "lower_endpoint_sha256": integer_hash(lo),
        "upper_endpoint_sha256": integer_hash(hi),
        "certified_quotients": len(prefix),
        "first_quotients": prefix[:24],
        "last_denominator_sha256": integer_hash(q_next),
        "denominator_lower_bound_power_of_two_exponent": bound_bits,
        "strict_decimal_power_lower_bound": decimal_power,
        "penultimate_separation_verified": True,
        "self_check": "known e prefix and pi convergent recurrence passed"
    }
    if bits == 80000:
        assert (len(prefix), bound_bits, decimal_power) == (23449, 39990, 12038), (len(prefix), bound_bits, decimal_power)
    return result


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--scale-bits", type=int, default=80000)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    rendered = json.dumps(replay(args.scale_bits), indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end="")
