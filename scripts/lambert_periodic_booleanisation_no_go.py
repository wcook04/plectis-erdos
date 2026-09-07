#!/usr/bin/env python3
"""Exact finite audit for LambertPeriodicBooleanisationNoGo.md.

The proof in the note is all-depth.  This program checks its explicit
divisor-inclusion witness and exhausts bounded periodic coefficient words;
the finite search is not used as a proof of the theorem.
"""

from __future__ import annotations

from itertools import product
from math import isqrt


def divisors(n: int) -> list[int]:
    low: list[int] = []
    high: list[int] = []
    for d in range(1, isqrt(n) + 1):
        if n % d:
            continue
        low.append(d)
        if d * d != n:
            high.append(n // d)
    return low + high[::-1]


def support_coefficient(support: set[int], n: int) -> int:
    return sum(d in support for d in divisors(n))


def audit_theorem_witness() -> int:
    checked = 0
    for period in range(1, 21):
        period_divisors = set(divisors(period))
        for threshold in range(0, 12):
            for selected in range(1, 41):
                if selected in period_divisors:
                    continue
                multiplier = selected * threshold + 1
                base = multiplier * period
                enlarged = selected * base
                assert base >= threshold
                assert base % selected != 0
                assert enlarged % selected == 0
                assert set(divisors(base)) < set(divisors(enlarged))
                support = period_divisors | {selected}
                assert support_coefficient(support, enlarged) > (
                    support_coefficient(support, base)
                )
                checked += 1
    return checked


def boolean_inverse_of_periodic_word(
    word: tuple[int, ...], proper_divisors: list[list[int]]
) -> list[int] | None:
    """Recover b from a(n)=sum_{d|n}b(d), rejecting non-Boolean rows."""
    depth = len(proper_divisors) - 1
    support_bit = [0] * (depth + 1)
    period = len(word)
    for n in range(1, depth + 1):
        proper_selected = sum(support_bit[d] for d in proper_divisors[n])
        bit = word[(n - 1) % period] - proper_selected
        if bit not in (0, 1):
            return None
        support_bit[n] = bit
    return support_bit


def audit_small_periodic_words() -> tuple[int, int]:
    words_checked = 0
    boolean_words = 0
    depth = 80
    proper_divisors = [
        [d for d in range(1, n) if n % d == 0]
        for n in range(depth + 1)
    ]
    for period in range(1, 8):
        for word in product(range(4), repeat=period):
            words_checked += 1
            inverse = boolean_inverse_of_periodic_word(word, proper_divisors)
            if inverse is None:
                continue
            boolean_words += 1
            support = {n for n in range(1, depth + 1) if inverse[n]}
            assert support <= set(divisors(period))
    return words_checked, boolean_words


def audit_converse() -> int:
    checked = 0
    for period in range(1, 21):
        period_divisors = divisors(period)
        for mask in range(1 << len(period_divisors)):
            support = {
                d for i, d in enumerate(period_divisors) if mask & (1 << i)
            }
            for n in range(1, 101):
                assert support_coefficient(support, n + period) == (
                    support_coefficient(support, n)
                )
            checked += 1
    return checked


def main() -> None:
    witness_count = audit_theorem_witness()
    words_checked, boolean_words = audit_small_periodic_words()
    converse_count = audit_converse()
    print(
        "Lambert eventual-periodicity no-go PASS: "
        f"{witness_count} strict divisor witnesses, "
        f"{words_checked} bounded periodic words ({boolean_words} Boolean), "
        f"and {converse_count} divisor-supported converse cases"
    )


if __name__ == "__main__":
    main()
