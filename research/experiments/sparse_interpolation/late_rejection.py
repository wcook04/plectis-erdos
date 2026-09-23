#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact regression certificates for two corrected synthesis assertions.

Run with Python's standard library only:
    python3 research/experiments/sparse_interpolation/late_rejection.py

The earlier investigation's Desk B report supplied the witness 189/388.
This independently checks its first rejection and its translate by 1.

For R_n = sum_{k>n} 1/(2**k - 1), the bounds used here follow from
    1/(2**k - 1) = 2**(-k) + 4**(-k)/(1 - 2**(-k))
and 1/(1 - 2**(-k)) <= 2.  Hence
    2**(-n) < R_n <= 2**(-n) + 2/(3 * 4**n).
These analytic bounds, not floating-point tail approximations, certify every
earlier skip and the rejection.  The upper bound is strictly below the current
weight, so each greedy take is forced for a subsum representation.  Taking a
digit preserves r <= R_n whenever
the preceding remainder was <= R_{n-1} = 1/(2**n - 1) + R_n.

The factorial check verifies finite telescoping identities and sample greedy
expansions.  The proof that all of [0, 1] is attained uses the exact infinite
tail 1/(2*k+1)! and the interval-covering lemma; no finite sample proves that
universal conclusion.  Neither computation is a Lean proof or a resolution
of Erdős problem 257.
"""

from fractions import Fraction
import json
from math import factorial


def require(condition: bool, message: str) -> None:
    """Keep verification enabled even when Python is run with -O."""
    if not condition:
        raise AssertionError(message)


def certify_late_rejection(target: Fraction) -> dict:
    remainder = target
    selected = []
    earlier_skips = []
    # Both targets are in [0, E]: 189/388 < 1/2 < R_1 and 1 + R_1 = E.
    require(target in (Fraction(189, 388), Fraction(577, 388)), "target domain")
    for n in range(1, 18):
        weight = Fraction(1, 2**n - 1)
        upper_tail = Fraction(1, 2**n) + Fraction(2, 3 * 4**n)
        require(upper_tail < weight, f"greedy choice not forced at {n}")
        if remainder >= weight:
            selected.append(n)
            remainder -= weight
        elif n < 17:
            lower_tail = Fraction(1, 2**n)
            require(remainder <= lower_tail, f"earlier rejection possible at {n}")
            earlier_skips.append(n)
        else:
            require(upper_tail < remainder < weight, "step-17 gap certificate")

    expected = [2, 3, 7, 9, 10, 14, 15, 16]
    if target > 1:
        expected.insert(0, 1)
    require(selected == expected, "selected support differs")
    require(remainder == Fraction(9291822600689, 1217890317075045460),
            "remainder differs")
    upper_tail = Fraction(196609, 25769803776)
    weight = Fraction(1, 131071)
    require(upper_tail < remainder < weight, "final certificate differs")
    return {
        "target": str(target),
        "first_rejection": 17,
        "selected_before_rejection": selected,
        "earlier_skips_certified": earlier_skips,
        "remainder": str(remainder),
        "tail_upper_bound": str(upper_tail),
        "weight": str(weight),
    }


def factorial_allowance(n: int) -> int:
    return n * (n - 1) - 1 if n >= 3 and n % 2 else 0


def verify_factorial_telescope(stages: int = 32, max_denominator: int = 24) -> dict:
    capacity = Fraction(0)
    for k in range(1, stages + 1):
        n = 2 * k + 1
        require(factorial_allowance(n - 1) == 0, "even allowance must vanish")
        contribution = Fraction(factorial_allowance(n), factorial(n))
        require(contribution == Fraction(1, factorial(n - 2))
                - Fraction(1, factorial(n)), "single telescoping term")
        capacity += contribution
        require(capacity == 1 - Fraction(1, factorial(n)), "prefix capacity")

    targets_checked = 0
    for q in range(1, max_denominator + 1):
        for p in range(q + 1):
            remainder = Fraction(p, q)
            for k in range(1, stages + 1):
                n = 2 * k + 1
                denominator = factorial(n)
                digit = min(factorial_allowance(n), remainder * denominator // 1)
                require(isinstance(digit, int), "digit must be an integer")
                require(0 <= digit <= factorial_allowance(n), "digit allowance")
                remainder -= Fraction(digit, denominator)
                require(0 <= remainder <= Fraction(1, denominator),
                        f"factorial remainder for {p}/{q} at {n}")
            targets_checked += 1
    return {
        "odd_allowance": "F(2k+1)=(2k)(2k+1)-1 for k>=1",
        "even_allowance": 0,
        "finite_capacity_identity": "sum(k=1..K) F(2k+1)/(2k+1)! = 1-1/(2K+1)!",
        "telescoping_stages_checked": stages,
        "largest_index_checked": 2 * stages + 1,
        "sample_targets": f"p/q with 1<=q<={max_denominator} and 0<=p<=q (including repeats)",
        "sample_targets_checked": targets_checked,
        "all_sample_remainders_within_exact_tail": True,
        "evidence_boundary": "finite identities and expansions; interval filling uses the proof",
    }


def main() -> None:
    print(json.dumps({
        "late_rejection_certificates": [
            certify_late_rejection(Fraction(189, 388)),
            certify_late_rejection(Fraction(577, 388)),
        ],
        "factorial_counterexample": verify_factorial_telescope(),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
