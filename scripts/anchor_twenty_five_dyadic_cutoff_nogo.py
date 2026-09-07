#!/usr/bin/env python3
"""Directed exact audit of the anchor-25 dyadic cutoff at 1/465.

The computation certifies greedy decisions with one common dyadic enclosure.
It also reads leading anchor-coefficient bits only when the lower and upper
enclosures lie in the same binary cylinder.  The finite audit is not an
all-depth proof of the dyadic-cutoff conjecture.
"""

from __future__ import annotations

import argparse
import json


TARGET_DENOMINATOR = 465
ANCHOR = (1 << 25) - 1


def weight_floor(precision: int, rank: int) -> int:
    """Return floor(2^precision / (2^rank - 1)) without division."""
    return sum(
        1 << (precision - multiple * rank)
        for multiple in range(1, precision // rank + 1)
    )


def certified_prefix(
    lower: int,
    upper: int,
    precision: int,
    bit_depth: int,
) -> int:
    """Common bit_depth prefix of ANCHOR times the enclosed residual."""
    shift = precision - bit_depth
    assert shift >= 0
    lower_prefix = (ANCHOR * lower) >> shift
    upper_prefix = (ANCHOR * upper) >> shift
    if lower_prefix != upper_prefix:
        raise AssertionError(f"uncertified prefix at depth {bit_depth}")
    return lower_prefix


def audit(depth: int) -> dict[str, object]:
    if depth < 24_092:
        raise ValueError("depth must be at least 24092")

    precision = 2 * depth + 80
    scale = 1 << precision
    lower = scale // TARGET_DENOMINATOR
    upper = (scale + TARGET_DENOMINATOR - 1) // TARGET_DENOMINATOR
    bits = bytearray(depth + 1)
    half_cutoff_violations: list[int] = []
    maximum_run = (0, 0)

    for rank in range(1, depth + 1):
        floor_weight = weight_floor(precision, rank)
        ceil_weight = floor_weight + 1
        if lower >= ceil_weight:
            lower -= ceil_weight
            upper -= floor_weight
            bits[rank] = 1
        elif upper <= floor_weight:
            # At a skip, upper * 2^rank <= scale certifies r_rank < 2^-rank.
            if (upper << rank) > scale:
                half_cutoff_violations.append(rank)
        else:
            raise AssertionError(f"undecided greedy branch at rank {rank}")

        if bits[rank] == 0:
            lower_anchor = ANCHOR * lower
            upper_anchor = ANCHOR * upper
            lower_length = lower_anchor.bit_length()
            upper_length = upper_anchor.bit_length()
            if lower_length != upper_length:
                raise AssertionError(f"uncertified first anchor bit at {rank}")
            first = precision - lower_length + 1
            if first == rank - 24:
                sample_depth = first + 32
                word = certified_prefix(
                    lower, upper, precision, sample_depth
                )
                suffix = word & ((1 << 33) - 1)
                run = 0
                for offset in range(32, -1, -1):
                    if (suffix >> offset) & 1:
                        run += 1
                    else:
                        break
                maximum_run = max(maximum_run, (run, rank))

    # The actual state at 24092 has first anchor bit 24068 and then exactly
    # sixteen ones followed by zero.  Multiplication by 2^(24068+16) turns
    # that prefix into the integer 2^17 - 2.
    witness_rank = 24_092
    assert bits[witness_rank] == 0

    # Replay only to the witness using the already certified bit word, avoiding
    # storage of all intermediate residual enclosures.
    witness_lower = scale // TARGET_DENOMINATOR
    witness_upper = (scale + TARGET_DENOMINATOR - 1) // TARGET_DENOMINATOR
    predecessor_lower = 0
    predecessor_upper = 0
    for rank in range(1, witness_rank + 1):
        floor_weight = weight_floor(precision, rank)
        if bits[rank]:
            witness_lower -= floor_weight + 1
            witness_upper -= floor_weight
        if rank == 24_087:
            predecessor_lower = witness_lower
            predecessor_upper = witness_upper
    witness_first = witness_rank - 24
    witness_prefix_depth = witness_first + 16
    witness_prefix = certified_prefix(
        witness_lower,
        witness_upper,
        precision,
        witness_prefix_depth,
    )
    assert witness_prefix == (1 << 17) - 2
    predecessor_first = 24_063
    predecessor_prefix_depth = predecessor_first + 21
    predecessor_prefix = certified_prefix(
        predecessor_lower,
        predecessor_upper,
        precision,
        predecessor_prefix_depth,
    )
    assert predecessor_prefix == int("1" + "0" * 4 + "1" * 16 + "0", 2)
    assert bits[24_088] == 1
    assert bits[24_089:24_093] == bytes((0, 0, 0, 0))

    pulses = [0] * (witness_rank + 1)
    for divisor in range(1, witness_rank + 1):
        if bits[divisor]:
            for multiple in range(2 * divisor, witness_rank + 1, divisor):
                pulses[multiple] += 1
    target_period_numerator = ((1 << 20) - 1) // TARGET_DENOMINATOR

    def target_bit(rank: int) -> int:
        shift = 20 - 1 - ((rank - 1) % 20)
        return (target_period_numerator >> shift) & 1

    quotient = 0
    quotient_window: list[dict[str, int]] = []
    for rank in range(1, witness_rank + 1):
        quotient = (
            2 * quotient
            + target_bit(rank)
            - pulses[rank]
            - bits[rank]
        )
        if rank >= 24_080:
            quotient_window.append(
                {
                    "rank": rank,
                    "bit": bits[rank],
                    "pulse": pulses[rank],
                    "target_bit": target_bit(rank),
                    "Q": quotient,
                    "E": rank // 20 - quotient,
                }
            )
    assert quotient == 2

    selected_proper_divisors = [
        divisor
        for divisor in range(1, witness_rank)
        if witness_rank % divisor == 0 and bits[divisor]
    ]
    assert selected_proper_divisors == [19, 76, 634, 1268, 6023, 12046]

    # A compact rigorous enclosure for 1-y_m, where y_m=2^m r_m.
    margin_bits = 64
    margin_shift = precision - margin_bits
    margin_lower_numerator = (
        scale - (witness_upper << witness_rank)
    ) >> margin_shift
    margin_upper_raw = scale - (witness_lower << witness_rank)
    margin_upper_numerator = (
        margin_upper_raw + (1 << margin_shift) - 1
    ) >> margin_shift
    assert (margin_lower_numerator, margin_upper_numerator) == (
        252_419_230_679_353,
        252_419_230_679_354,
    )

    alpha_numerator = pow(2, witness_rank, TARGET_DENOMINATOR)
    assert alpha_numerator == 376

    predecessor_words: dict[int, str] = {}
    for gap in range(1, 25):
        word = bin(ANCHOR * ((1 << gap) + 1))[2:]
        expected = "1" + "0" * gap + "1" * (24 - gap) + "0" + "1" * gap
        assert word == expected
        assert "1" * 25 not in word
        predecessor_words[gap] = word

    expected_maximum = (16, 24_092) if depth < 80_364 else (17, 80_364)
    if depth in (30_000, 100_000):
        assert maximum_run == expected_maximum
    if half_cutoff_violations:
        raise AssertionError(
            f"directed audit found half-cutoff candidates: {half_cutoff_violations[:5]}"
        )

    return {
        "target": "1/465",
        "depth": depth,
        "method": "directed dyadic integer enclosure",
        "certified_half_cutoff_violations": half_cutoff_violations,
        "anchor_run_counterexample": {
            "skip_rank": witness_rank,
            "first_anchor_bit": witness_first,
            "leading_one_run": 16,
            "previous_take_rank": 24_088,
            "predecessor_anchor_prefix": "10000" + "1" * 16 + "0",
            "predecessor_first_anchor_bit": predecessor_first,
            "local_greedy_word_24080_24092": "".join(
                str(bit) for bit in bits[24_080:24_093]
            ),
        },
        "witness_state": {
            "Q": quotient,
            "K": witness_rank // 20,
            "E": witness_rank // 20 - quotient,
            "support_count": sum(bits[: witness_rank + 1]),
            "alpha": f"{alpha_numerator}/{TARGET_DENOMINATOR}",
            "one_minus_y_dyadic_enclosure": {
                "denominator": f"2^{margin_bits}",
                "strict_lower_numerator": margin_lower_numerator,
                "strict_upper_numerator": margin_upper_numerator,
            },
            "selected_proper_divisors": selected_proper_divisors,
            "proper_divisor_pulse": pulses[witness_rank],
            "quotient_window": quotient_window,
        },
        "maximum_aligned_skip_run": maximum_run[0],
        "maximum_run_rank": maximum_run[1],
        "unsafe_predecessor_word_family": {
            "gap_range": [1, 24],
            "formula": "1 0^g 1^(24-g) 0 1^g",
            "contains_25_run": False,
            "endpoint_checks": {
                "g=1": predecessor_words[1],
                "g=24": predecessor_words[24],
            },
        },
        "claim_status": "exact finite audit only",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=30_000)
    args = parser.parse_args()
    print(json.dumps(audit(args.depth), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
