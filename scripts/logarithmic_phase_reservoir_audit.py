#!/usr/bin/env python3
"""Exact finite audit of the logarithmic phase/reservoir candidate.

The long audit uses directed dyadic residual bounds.  The two small receipts
use Fraction arithmetic.  Nothing in this script is an all-depth proof.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction


def source_digit(target: Fraction, rank: int) -> int:
    here = ((1 << rank) * target.numerator) // target.denominator
    before = ((1 << (rank - 1)) * target.numerator) // target.denominator
    return here - 2 * before


def exact_small_receipt(target: Fraction, depth: int) -> dict[str, object]:
    residual = target
    bits = [0] * (depth + 1)
    counts = [0] * (depth + 1)
    divisor_counts = [0] * (depth + 1)
    selected = 0
    target_ones = 0
    quotient_defect = 0
    energy = 4
    skip_rows: dict[int, dict[str, object]] = {}
    energies: dict[int, int] = {}
    for rank in range(1, depth + 1):
        weight = Fraction(1, (1 << rank) - 1)
        before = residual
        take = int(weight <= residual)
        bits[rank] = take
        if take:
            residual -= weight
            selected += 1
            for multiple in range(rank, depth + 1, rank):
                divisor_counts[multiple] += 1
        else:
            beta = Fraction(1 << rank, (1 << rank) - 1)
            delta = beta - (1 << rank) * before
            skip_rows[rank] = {
                "delta_numerator": delta.numerator,
                "delta_denominator": delta.denominator,
                "energy_before": energy,
            }
        counts[rank] = selected
        target_ones += source_digit(target, rank)
        quotient_defect = (
            2 * quotient_defect
            + source_digit(target, rank)
            - divisor_counts[rank]
        )
        discrepancy = target_ones + counts[rank // 2] - selected
        energy = discrepancy + 4 - 2 * quotient_defect
        energies[rank] = energy
    return {
        "bits": "".join(str(bits[rank]) for rank in range(1, depth + 1)),
        "energies": energies,
        "skip_rows": skip_rows,
    }


def audit_long(depth: int) -> dict[str, object]:
    precision = 2 * depth + 96
    scale = 1 << precision
    lower = scale // 21
    upper = (scale + 20) // 21
    bits = [0] * (depth + 1)
    counts = [0] * (depth + 1)
    divisor_counts = [0] * (depth + 1)
    selected = 0
    target_ones = 0
    quotient_defect = 0
    energy = 4
    maximum_extra_exponent = (-10**9, 0, 0, 0)
    skipped = 0
    for rank in range(1, depth + 1):
        power = 1 << rank
        weight_floor = scale // (power - 1)
        take = 0
        if lower >= weight_floor + 1:
            take = 1
            lower -= weight_floor + 1
            upper -= weight_floor
            selected += 1
            for multiple in range(rank, depth + 1, rank):
                divisor_counts[multiple] += 1
        elif upper <= weight_floor:
            skipped += 1
            # Delta >= power * gap_core / ((power - 1) * scale).
            gap_core = scale - (power - 1) * upper
            if gap_core <= 0:
                raise AssertionError(f"uncertified positive seam gap at {rank}")
            numerator = power * gap_core
            denominator = (power - 1) * scale
            exponent = max(0, denominator.bit_length() - numerator.bit_length())
            while (numerator << exponent) < denominator:
                exponent += 1
            while exponent and (numerator << (exponent - 1)) >= denominator:
                exponent -= 1
            row = (exponent - energy, rank, exponent, energy)
            maximum_extra_exponent = max(maximum_extra_exponent, row)
        else:
            raise AssertionError(f"ambiguous greedy decision at rank {rank}")

        bits[rank] = take
        counts[rank] = selected
        digit = int(rank % 6 in (0, 5))
        target_ones += digit
        quotient_defect = (
            2 * quotient_defect + digit - divisor_counts[rank]
        )
        discrepancy = target_ones + counts[rank // 2] - selected
        energy = discrepancy + 4 - 2 * quotient_defect

    if maximum_extra_exponent[0] > 2:
        raise AssertionError(
            "finite logarithmic phase bound failed at "
            f"rank {maximum_extra_exponent[1]}"
        )
    return {
        "depth": depth,
        "selected": selected,
        "skipped": skipped,
        "maximum_ceil_minus_log2_delta_minus_energy": (
            maximum_extra_exponent[0]
        ),
        "sharp_rank": maximum_extra_exponent[1],
        "sharp_ceil_minus_log2_delta": maximum_extra_exponent[2],
        "sharp_energy_before": maximum_extra_exponent[3],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=20_000)
    args = parser.parse_args()
    if args.depth < 63:
        raise SystemExit("depth must be at least 63")

    exact = exact_small_receipt(Fraction(1, 21), 63)
    perturbed = exact_small_receipt(
        Fraction(1, 21) - Fraction(1, 3 * (1 << 63)), 63
    )
    delta_56 = Fraction(
        exact["skip_rows"][56]["delta_numerator"],
        exact["skip_rows"][56]["delta_denominator"],
    )
    if not (Fraction(1, 64) <= delta_56 < Fraction(1, 32)):
        raise AssertionError("rank-56 sharp exponent receipt failed")
    if perturbed["bits"][60:63] != "011":
        raise AssertionError("perturbed seam block was not 011")
    if [perturbed["energies"][rank] for rank in range(60, 64)] != [5, 3, 0, -1]:
        raise AssertionError("perturbed energy receipt failed")

    result = {
        "claim_status": "exact finite audit; not an all-depth proof",
        "long_audit": audit_long(args.depth),
        "rank_56": {
            "energy_before": exact["skip_rows"][56]["energy_before"],
            "delta_numerator": delta_56.numerator,
            "delta_denominator": delta_56.denominator,
            "certified_interval": "1/64 <= delta < 1/32",
        },
        "perturbed_target": {
            "block_61_through_63": perturbed["bits"][60:63],
            "energies_60_through_63": [
                perturbed["energies"][rank] for rank in range(60, 64)
            ],
            "conclusion": "the logarithmic bound alone is insufficient",
        },
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
