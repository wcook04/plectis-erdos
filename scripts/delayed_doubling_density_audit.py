#!/usr/bin/env python3
"""Exact audit of the delayed doubling-density candidate for 1/21.

The first lane certifies actual greedy bits with a dyadic integer enclosure.
The second lane uses the independently derived odd-depth quotient-suffix
recurrence.  Its word is not identified with the actual greedy doubling
block.  Neither finite lane is an infinite proof.
"""

from __future__ import annotations

import argparse
import json


def greedy_density(depth: int) -> dict[str, int]:
    precision = 2 * depth + 64
    scale = 1 << precision
    lower = scale // 21
    upper = (scale + 20) // 21
    counts = [0] * (depth + 1)
    selected = 0
    maximum = (-10**9, 0)
    source_maximum = (-10**9, 0)
    divisor_counts = [0] * (depth + 1)
    target_ones = 0
    quotient_defect = 0
    reservoir_minimum = (10**9, 0)
    reservoir_minus_defect_minimum = (10**9, 0)
    quotient_maximum = (-10**9, 0)
    for n in range(1, depth + 1):
        weight_floor = scale // ((1 << n) - 1)
        if lower >= weight_floor + 1:
            lower -= weight_floor + 1
            upper -= weight_floor
            selected += 1
            for multiple in range(n, depth + 1, n):
                divisor_counts[multiple] += 1
        elif upper <= weight_floor:
            pass
        else:
            raise AssertionError(f"ambiguous branch at rank {n}")
        counts[n] = selected
        target_digit = int(n % 6 in (0, 5))
        target_ones += target_digit
        quotient_defect = (
            2 * quotient_defect + target_digit - divisor_counts[n]
        )
        source_excess = counts[n] - target_ones - counts[n // 2]
        source_maximum = max(source_maximum, (source_excess, -n))
        reservoir = -source_excess + 3 - quotient_defect
        reservoir_minimum = min(reservoir_minimum, (reservoir, n))
        reservoir_minus_defect_minimum = min(
            reservoir_minus_defect_minimum,
            (reservoir - quotient_defect, n),
        )
        quotient_maximum = max(quotient_maximum, (quotient_defect, -n))
        excess = counts[n] - n // 3 - counts[n // 2]
        maximum = max(maximum, (excess, -n))
    return {
        "depth": depth,
        "selected": selected,
        "skipped": depth - selected,
        "max_density_excess": maximum[0],
        "first_max_density_excess_rank": -maximum[1],
        "max_source_clock_excess": source_maximum[0],
        "first_max_source_clock_excess_rank": -source_maximum[1],
        "min_reservoir": reservoir_minimum[0],
        "first_min_reservoir_rank": reservoir_minimum[1],
        "min_reservoir_minus_defect": reservoir_minus_defect_minimum[0],
        "first_min_reservoir_minus_defect_rank": (
            reservoir_minus_defect_minimum[1]
        ),
        "max_quotient_defect": quotient_maximum[0],
        "first_max_quotient_defect_rank": -quotient_maximum[1],
    }


def quotient_suffix_density(depth: int) -> dict[str, int]:
    suffix = 1
    divisor_counts = [0] * (2 * depth + 10)
    maximum = (-10**9, 0)
    for k in range(2, depth + 1):
        excess = 3 * suffix.bit_count() - 2 * k
        maximum = max(maximum, (excess, -k))
        source = (
            2 * int((2 * k + 2) % 6 in (5, 0))
            + int((2 * k + 3) % 6 in (5, 0))
        )
        load = 2 * divisor_counts[2 * k + 2] + divisor_counts[2 * k + 3]
        core = 4 * suffix + source - load
        bit = core // (1 << (k + 1))
        suffix = core - bit * (1 << (k + 1))
        if bit not in (0, 1) or not 0 <= suffix < 1 << (k + 1):
            raise AssertionError(f"non-Boolean suffix transition at {k}")
        if bit:
            rank = k + 2
            for multiple in range(rank, 2 * depth + 10, rank):
                divisor_counts[multiple] += 1
    return {
        "depth": depth,
        "max_three_popcount_sub_two_depth": maximum[0],
        "first_max_suffix_rank": -maximum[1],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--greedy-depth", type=int, default=20_000)
    parser.add_argument("--suffix-depth", type=int, default=200_000)
    args = parser.parse_args()
    if args.greedy_depth < 5 or args.suffix_depth < 5:
        raise SystemExit("depths must be at least five")
    result = {
        "method": "exact dyadic enclosure plus distinct integer quotient-suffix recurrence",
        "greedy": greedy_density(args.greedy_depth),
        "quotient_suffix": quotient_suffix_density(args.suffix_depth),
        "claim_status": "finite evidence; suffix word is not the actual greedy block",
    }
    assert result["greedy"]["max_density_excess"] <= 2
    assert result["greedy"]["max_source_clock_excess"] <= 2
    assert result["greedy"]["min_reservoir"] >= 0
    assert result["greedy"]["min_reservoir_minus_defect"] >= -1
    assert result["quotient_suffix"]["max_three_popcount_sub_two_depth"] <= 5
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
