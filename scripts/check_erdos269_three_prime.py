#!/usr/bin/env python3
"""Exact regression and exploration surface for the three-prime #269 lane.

The script deliberately uses integer comparisons and ``fractions.Fraction``.
Floating-point logarithms never decide a height, jump ordering, or certificate.
Its finite output is regression evidence, not an irrationality proof.
"""

from __future__ import annotations

problem_id = "erdos_269"

import argparse
import heapq
import json
from decimal import Decimal, getcontext
from fractions import Fraction
from typing import Iterable


PRIMES = (2, 3, 5)
EXPECTED_SHELLS_235 = (
    1,
    1,
    1,
    2,
    1,
    4,
    4,
    1,
    2,
    8,
    4,
    6,
    1,
    12,
    2,
    16,
    4,
    5,
    10,
    23,
)


def ilog(base: int, value: int) -> int:
    """Return ``floor(log_base(value))`` using integer division only."""

    if base < 2 or value < 1:
        raise ValueError("ilog requires base >= 2 and value >= 1")
    exponent = 0
    while value >= base:
        value //= base
        exponent += 1
    return exponent


def smooth_value(primes: tuple[int, int, int], exponents: tuple[int, int, int]) -> int:
    return (
        primes[0] ** exponents[0]
        * primes[1] ** exponents[1]
        * primes[2] ** exponents[2]
    )


def running_height(primes: tuple[int, int, int], value: int) -> int:
    """Product of the largest pure prime powers not exceeding ``value``."""

    result = 1
    for prime in primes:
        result *= prime ** ilog(prime, value)
    return result


def kernel(
    primes: tuple[int, int, int], exponents: tuple[int, int, int]
) -> Fraction:
    value = smooth_value(primes, exponents)
    return Fraction(1, running_height(primes, value))


def box_sum(primes: tuple[int, int, int], side: int) -> Fraction:
    if side < 1:
        raise ValueError("box side must be positive")
    total = Fraction(0)
    for i in range(side):
        for j in range(side):
            for k in range(side):
                total += kernel(primes, (i, j, k))
    return total


def cubic_tail_bound(primes: tuple[int, int, int], side: int) -> Fraction:
    """Exact geometric bound outside ``[0, side)^3``."""

    full = Fraction(1)
    box = Fraction(1)
    for prime in primes:
        ratio = Fraction(1, prime**3)
        full *= Fraction(1, 1) / (1 - ratio)
        box *= (1 - ratio**side) / (1 - ratio)
    product = primes[0] * primes[1] * primes[2]
    return product * (full - box)


def pure_power_jumps(primes: tuple[int, int, int], count: int) -> list[int]:
    """Merge the three exact pure-power streams, excluding the common value 1."""

    heap: list[tuple[int, int]] = [(prime, prime) for prime in primes]
    heapq.heapify(heap)
    result: list[int] = []
    while len(result) < count:
        value, prime = heapq.heappop(heap)
        if not result or result[-1] != value:
            result.append(value)
        heapq.heappush(heap, (value * prime, prime))
    return result


def powers_below(base: int, limit: int) -> Iterable[int]:
    value = 1
    while value < limit:
        yield value
        value *= base


def shell_multiplicity(
    primes: tuple[int, int, int], lower: int, upper: int
) -> int:
    """Count smooth values in ``[lower, upper)`` by exact exponent enumeration."""

    count = 0
    for p_power in powers_below(primes[0], upper):
        for q_power in powers_below(primes[1], upper):
            pq = p_power * q_power
            if pq >= upper:
                break
            for r_power in powers_below(primes[2], upper):
                value = pq * r_power
                if value >= upper:
                    break
                if lower <= value:
                    count += 1
    return count


def shell_prefix(primes: tuple[int, int, int], count: int) -> list[int]:
    # u_0 = 1; the j-th displayed digit is [u_j, u_{j+1}).
    jumps = [1, *pure_power_jumps(primes, count + 1)]
    return [
        shell_multiplicity(primes, jumps[index], jumps[index + 1])
        for index in range(1, count + 1)
    ]


def decimal_string(value: Fraction, digits: int = 60) -> str:
    getcontext().prec = digits
    return str(Decimal(value.numerator) / Decimal(value.denominator))


def run(box_side: int, shell_count: int, assert_packet: bool) -> dict[str, object]:
    kernels = {
        "000": kernel(PRIMES, (0, 0, 0)),
        "100": kernel(PRIMES, (1, 0, 0)),
        "010": kernel(PRIMES, (0, 1, 0)),
        "110": kernel(PRIMES, (1, 1, 0)),
    }
    rank_one_determinant = kernels["000"] * kernels["110"] - kernels["100"] * kernels["010"]
    shells = shell_prefix(PRIMES, shell_count)
    partial = box_sum(PRIMES, box_side)
    tail = cubic_tail_bound(PRIMES, box_side)

    if assert_packet:
        expected_kernels = {
            "000": Fraction(1),
            "100": Fraction(1, 2),
            "010": Fraction(1, 6),
            "110": Fraction(1, 60),
        }
        if kernels != expected_kernels:
            raise AssertionError((kernels, expected_kernels))
        if rank_one_determinant != Fraction(-1, 15):
            raise AssertionError(rank_one_determinant)
        expected_prefix = list(EXPECTED_SHELLS_235[:shell_count])
        if shell_count <= len(EXPECTED_SHELLS_235) and shells != expected_prefix:
            raise AssertionError((shells, expected_prefix))

    return {
        "schema": "erdos269-three-prime-exact-check/1",
        "claim_ceiling": "finite_exact_regression_not_irrationality_proof",
        "primes": list(PRIMES),
        "box_side": box_side,
        "box_term_count": box_side**3,
        "box_sum": str(partial),
        "box_sum_decimal": decimal_string(partial),
        "cubic_tail_bound": str(tail),
        "cubic_tail_bound_decimal": decimal_string(tail),
        "kernel_values": {key: str(value) for key, value in kernels.items()},
        "rank_one_determinant": str(rank_one_determinant),
        "shell_multiplicities": shells,
        "packet_regressions_checked": assert_packet,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--box-side", type=int, default=12)
    parser.add_argument("--shell-count", type=int, default=20)
    parser.add_argument("--assert-packet", action="store_true")
    args = parser.parse_args()
    print(
        json.dumps(
            run(args.box_side, args.shell_count, args.assert_packet),
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
