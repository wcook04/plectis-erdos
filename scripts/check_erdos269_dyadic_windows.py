#!/usr/bin/env python3
"""Exact dyadic-window certificate engine for Erdős #269.

The computation uses integers only.  It constructs the actual compressed
`{2,3,5}` dyadic block bases and digits, composes local windows, and asks
whether the canonical least-positive residue escapes the proved quadratic
carry bound.  A successful finite scan is regression evidence for the exact
Lean consumer, never a cofinal theorem.
"""

from __future__ import annotations

import argparse
import json
from bisect import bisect_left, bisect_right
from math import gcd


PRIMES = (2, 3, 5)
OTHERS = {2: (3, 5), 3: (2, 5), 5: (2, 3)}
PACKET_CERTIFICATES = (
    (1, 1, 2, 4, 60, 47, 13, 9),
    (7, 1, 3, 6, 360, 289, 137, 95),
    (16, 1, 4, 9, 10_800, 8_735, 640, 352),
)


def pair_count_lt(target: int, xs: list[int], ys: list[int]) -> int:
    """Count pairs `(x,y)` from increasing power lists with `x*y < target`."""

    j = len(ys) - 1
    while j >= 0 and ys[j] >= target:
        j -= 1
    answer = 0
    for x in xs:
        if x >= target or j < 0:
            break
        while j >= 0 and x * ys[j] >= target:
            j -= 1
        if j < 0:
            break
        answer += j + 1
    return answer


def build_dyadic_blocks(max_a: int) -> list[tuple[int, int, int]]:
    """Return `(block_base, block_digit, ending_jump_index)` for `1 <= a <= max_a`."""

    if max_a < 1:
        raise ValueError("max_a must be positive")
    limit = 1 << (max_a + 1)
    powers: dict[int, list[int]] = {}
    for prime in PRIMES:
        values = [1]
        while values[-1] * prime <= limit:
            values.append(values[-1] * prime)
        powers[prime] = values

    block_counts: dict[int, list[int]] = {}
    cumulative_counts: dict[int, list[int]] = {}
    for prime in PRIMES:
        other_left, other_right = OTHERS[prime]
        widths = [0] * len(powers[prime])
        cumulative = [0] * len(powers[prime])
        for exponent in range(1, len(powers[prime])):
            widths[exponent] = pair_count_lt(
                powers[prime][exponent],
                powers[other_left],
                powers[other_right],
            )
            cumulative[exponent] = cumulative[exponent - 1] + widths[exponent]
        block_counts[prime] = widths
        cumulative_counts[prime] = cumulative

    jumps: list[tuple[int, int, int]] = []
    for prime in PRIMES:
        for exponent, value in enumerate(powers[prime][1:], start=1):
            if value < limit:
                jumps.append((value, prime, exponent))
    jumps.sort()
    jump_values = [value for value, _, _ in jumps]

    blocks: list[tuple[int, int, int]] = []
    for a in range(1, max_a + 1):
        lower = 1 << a
        upper = 1 << (a + 1)
        left = bisect_right(jump_values, lower)
        right = bisect_left(jump_values, upper)
        internal = jumps[left:right]
        internal_channels = [prime for _, prime, _ in internal]
        if len(internal_channels) > 2 or len(set(internal_channels)) != len(
            internal_channels
        ):
            raise AssertionError(("dyadic internal-channel uniqueness", a, internal))

        block_base = 2
        for _, prime, _ in internal:
            block_base *= prime
        if block_base not in (2, 6, 10, 30):
            raise AssertionError(("unexpected block base", a, block_base))

        block_digit = block_counts[2][a + 1]
        suffix_base = 1
        for _, prime, exponent in reversed(internal):
            strip_count = (
                cumulative_counts[prime][exponent] - cumulative_counts[2][a]
            )
            block_digit += (prime - 1) * suffix_base * strip_count
            suffix_base *= prime
        blocks.append((block_base, block_digit, right))
    return blocks


def least_positive_residue(value: int, modulus: int) -> int:
    if modulus <= 0:
        raise ValueError("modulus must be positive")
    residue = value % modulus
    return modulus if residue == 0 else residue


def short_bound(denominator: int, jump_index: int) -> int:
    return denominator * (
        jump_index * jump_index + 10 * jump_index + 27
    ) // 9


def window(
    blocks: list[tuple[int, int, int]], a: int, length: int
) -> tuple[int, int, int]:
    if a < 1 or length < 1 or a + length - 1 > len(blocks):
        raise ValueError("window is outside the constructed block range")
    base, forcing = 1, 0
    for index in range(a - 1, a + length - 1):
        block_base, block_digit, _ = blocks[index]
        base *= block_base
        forcing = block_base * forcing + block_digit
    ending_index = blocks[a + length - 2][2]
    return base, forcing, ending_index


def certificate(
    blocks: list[tuple[int, int, int]], denominator: int, a: int, length: int
) -> dict[str, int | bool]:
    base, forcing, ending_index = window(blocks, a, length)
    bound = short_bound(denominator, ending_index)
    residue = least_positive_residue(-denominator * forcing, base)
    return {
        "denominator": denominator,
        "dyadic_start": a,
        "length": length,
        "ending_jump_index": ending_index,
        "window_base": base,
        "window_forcing": forcing,
        "least_positive_residue": residue,
        "short_bound": bound,
        "base_clears_bound": base > bound,
        "residue_escapes": residue > bound,
        "consumer_fires": base > bound and residue > bound,
    }


def assert_packet_certificates(blocks: list[tuple[int, int, int]]) -> None:
    for expected in PACKET_CERTIFICATES:
        denominator, a, length, ending, base, forcing, residue, bound = expected
        actual = certificate(blocks, denominator, a, length)
        observed = (
            actual["ending_jump_index"],
            actual["window_base"],
            actual["window_forcing"],
            actual["least_positive_residue"],
            actual["short_bound"],
        )
        if observed != (ending, base, forcing, residue, bound):
            raise AssertionError((expected, observed))


def scan(
    blocks: list[tuple[int, int, int]],
    max_denominator: int,
    start_min: int,
    start_max: int,
    max_length: int,
) -> dict[str, object]:
    failures: list[tuple[int, int]] = []
    tested_pairs = 0
    largest_minimal_length = 0
    first_worst: dict[str, int | bool] | None = None
    length_histogram: dict[int, int] = {}
    for denominator in range(1, max_denominator + 1):
        if gcd(denominator, 30) != 1:
            continue
        for a in range(start_min, start_max + 1):
            tested_pairs += 1
            for length in range(1, max_length + 1):
                current = certificate(blocks, denominator, a, length)
                if current["consumer_fires"]:
                    length_histogram[length] = length_histogram.get(length, 0) + 1
                    if length > largest_minimal_length:
                        largest_minimal_length = length
                        first_worst = current
                    break
            else:
                failures.append((denominator, a))
    return {
        "tested_pairs": tested_pairs,
        "failure_count": len(failures),
        "first_failures": failures[:20],
        "largest_minimal_length": largest_minimal_length,
        "first_worst_case": first_worst,
        "minimal_length_histogram": {
            str(length): count for length, count in sorted(length_histogram.items())
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-denominator", type=int, default=200)
    parser.add_argument("--start-min", type=int, default=20)
    parser.add_argument("--start-max", type=int, default=120)
    parser.add_argument("--max-length", type=int, default=18)
    parser.add_argument("--assert-packet", action="store_true")
    args = parser.parse_args()
    if args.max_denominator < 1:
        parser.error("--max-denominator must be positive")
    if args.start_min < 1 or args.start_max < args.start_min:
        parser.error("invalid dyadic start interval")
    if args.max_length < 1:
        parser.error("--max-length must be positive")

    blocks = build_dyadic_blocks(args.start_max + args.max_length)
    if args.assert_packet:
        assert_packet_certificates(blocks)
    result = {
        "schema": "erdos269-dyadic-window-exact-check/1",
        "claim_ceiling": "finite_exact_consumer_experiment_not_cofinal_escape",
        "parameters": {
            "max_denominator": args.max_denominator,
            "start_min": args.start_min,
            "start_max": args.start_max,
            "max_length": args.max_length,
        },
        "packet_regressions_checked": args.assert_packet,
        "block_base_alphabet": [2, 6, 10, 30],
        "scan": scan(
            blocks,
            args.max_denominator,
            args.start_min,
            args.start_max,
            args.max_length,
        ),
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["scan"]["failure_count"] == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
