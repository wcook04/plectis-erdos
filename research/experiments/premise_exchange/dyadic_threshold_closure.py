#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact finite checks for the closed dyadic-threshold question.

Run with Python's standard library only:
    python3 research/experiments/premise_exchange/dyadic_threshold_closure.py

dyadic_threshold_probe.py asked whether 1/3 is the best cofinal constant for
irrational tails.  A literature comparison answers it: Dubickas proved that
limsup ||xi 2^n|| >= tau for every irrational xi, with equality at xi = tau,
the Thue-Morse number (as stated by Akiyama and Kaneko, arXiv:1911.06170,
p. 3).  The README gives the ordinary argument that the endpoint is not a
cofinal-return constant: ||2^n tau|| < tau for every n >= 1.

This script checks, in exact arithmetic on finite prefixes only:

1. tau = 1/2 - (1/4) prod_{j>=0} (1 - 2^(-2^j)), comparing the digit sum and
   the truncated product to within 2^-4000, and 2/5 < tau < 1/2;
2. for every shift 1 <= n < 2^15, the binary suffix of the Thue-Morse word at
   n is strictly below the word itself when it starts with 0 and strictly
   above its complement when it starts with 1, each comparison decided inside
   the available prefix.  This is the finite shadow of the strict inequality
   ||2^n tau|| < tau; the infinite statement is the README's proof.

Bounds are recorded as exact rationals; decimals are for display only.  The
historical output of dyadic_threshold_probe.py is left as it was.
"""

from __future__ import annotations

from fractions import Fraction
import json
from pathlib import Path


def require(condition: bool, message: str) -> None:
    """Keep verification enabled even when Python is run with -O."""
    if not condition:
        raise AssertionError(message)


def thue_morse(length: int) -> list[int]:
    return [bin(i).count("1") & 1 for i in range(length)]


def tau_enclosure(bits: int) -> tuple[Fraction, Fraction]:
    digits = thue_morse(bits)
    low = sum(Fraction(d, 2 ** (n + 1)) for n, d in enumerate(digits))
    return low, low + Fraction(1, 2 ** bits)


def product_form(terms: int) -> Fraction:
    product = Fraction(1)
    for j in range(terms):
        product *= 1 - Fraction(1, 2 ** (2 ** j))
    return Fraction(1, 2) - product / 4


def strict_shift_comparisons(shifts: int) -> dict:
    word = thue_morse(2 * shifts)
    complement = [1 - d for d in word]
    deepest = 0
    for n in range(1, shifts):
        target = word if word[n] == 0 else complement
        wanted = -1 if word[n] == 0 else 1
        for k in range(len(word) - n):
            a, b = word[n + k], target[k]
            if a != b:
                require((a > b) - (a < b) == wanted,
                        f"shift {n}: wrong strict order at depth {k}")
                deepest = max(deepest, k)
                break
        else:
            raise AssertionError(f"shift {n}: comparison undecided in prefix")
    return {"shifts_checked": [1, shifts - 1],
            "prefix_bits": 2 * shifts,
            "deepest_decision": deepest,
            "violations": 0}


def main() -> None:
    low, high = tau_enclosure(4096)
    product = product_form(12)
    require(low <= product <= high, "product form outside the digit enclosure")
    require(Fraction(2, 5) < low and high < Fraction(1, 2), "2/5 < tau < 1/2 fails")
    shifts = strict_shift_comparisons(1 << 15)
    result = {
        "evidence": "exact rational arithmetic on finite prefixes",
        "boundary": (
            "Finite checks only. The sharp limsup bound is Dubickas's published "
            "theorem as stated by Akiyama and Kaneko; the strict endpoint "
            "inequality for all n >= 1 is the ordinary proof in README.md."
        ),
        "tau_enclosure_4096_bits": {
            "lower": {"numerator": str(low.numerator), "denominator": str(low.denominator)},
            "upper_minus_lower": "2^-4096",
            "display": f"{float(low):.15f}",
        },
        "product_form_within_enclosure": True,
        "two_fifths_below_tau_below_one_half": True,
        "strict_shift_comparisons": shifts,
    }
    out = Path(__file__).with_name("results") / "dyadic_threshold_closure.json"
    out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"written": out.name, **shifts}, indent=2))


if __name__ == "__main__":
    main()
