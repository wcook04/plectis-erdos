#!/usr/bin/env python3
"""Exact finite audit of the compressed 1/465 source-corridor cylinder.

The full dynamic program retains one complete Boolean prefix for every
admissible endpoint.  Once these prefixes form a common-prefix cylinder, the
same tree can be advanced without endpoint-by-endpoint expansion.  This file
checks the two implementations against each other and then runs the compressed
recurrence to a larger finite horizon.

No finite horizon is promoted to an all-depth statement.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from math import isqrt


DENOMINATOR = 465


def proper_divisors(rank: int) -> tuple[int, ...]:
    result: list[int] = []
    for divisor in range(1, isqrt(rank) + 1):
        if rank % divisor:
            continue
        other = rank // divisor
        if divisor < rank:
            result.append(divisor)
        if other != divisor and other < rank:
            result.append(other)
    return tuple(result)


def common_prefix_length(words: list[int], depth: int) -> int:
    reference = words[0]
    variation = 0
    for word in words[1:]:
        variation |= reference ^ word
    if variation == 0:
        return depth
    return (variation & -variation).bit_length() - 1


@dataclass(frozen=True)
class Cylinder:
    depth: int
    prefix_length: int
    suffix_width: int
    endpoint: int
    corridor_ceiling: int


def full_audit(horizon: int) -> Cylinder:
    states: list[tuple[int, int]] = [(0, 0)]
    remainder = 1

    for rank in range(1, horizon + 1):
        remainder *= 2
        target_bit, remainder = divmod(remainder, DENOMINATOR)
        ceiling = rank // 20
        divisors = proper_divisors(rank)
        next_states: list[tuple[int, int]] = []

        for bits, old_defect in states:
            proper_count = sum(
                (bits >> (divisor - 1)) & 1 for divisor in divisors
            )
            before_new_bit = 2 * old_defect + target_bit - proper_count
            for new_bit in (0, 1):
                defect = before_new_bit - new_bit
                if 0 <= defect <= ceiling:
                    next_states.append(
                        (bits | (new_bit << (rank - 1)), defect)
                    )

        states = next_states
        endpoint_map = {defect: bits for bits, defect in states}
        assert len(states) == ceiling + 1
        assert set(endpoint_map) == set(range(ceiling + 1))

    prefix_length = common_prefix_length(
        [bits for bits, _ in states], horizon
    )
    suffix_width = horizon - prefix_length
    endpoints = set()
    for bits, defect in states:
        suffix_string = "".join(
            str((bits >> (rank - 1)) & 1)
            for rank in range(prefix_length + 1, horizon + 1)
        )
        suffix_value = int(suffix_string or "0", 2)
        endpoints.add(suffix_value + defect)
    assert len(endpoints) == 1
    return Cylinder(
        horizon,
        prefix_length,
        suffix_width,
        endpoints.pop(),
        horizon // 20,
    )


def backward_certificate_audit(horizon: int) -> dict[str, int | str]:
    """Exclude the first-seam quotient certificate through ``horizon``.

    At each ``s`` this checks every prefix that has survived the complete
    corridor tree through depth ``s-1``.  The arithmetic is exact.
    """

    target_bits = [0] * (2 * horizon + 1)
    remainder = 1
    for rank in range(1, 2 * horizon + 1):
        remainder *= 2
        target_bits[rank], remainder = divmod(remainder, DENOMINATOR)

    divisor_table = [tuple()] * horizon
    for rank in range(1, horizon):
        divisor_table[rank] = proper_divisors(rank)

    states: dict[int, int] = {0: 0}
    tested_prefix_count = 0

    for prefix_depth in range(1, horizon):
        ceiling = prefix_depth // 20
        next_states: dict[int, int] = {}
        new_bit_mask = 1 << (prefix_depth - 1)
        for old_defect, bits in states.items():
            proper_count = sum(
                (bits >> (divisor - 1)) & 1
                for divisor in divisor_table[prefix_depth]
            )
            before_new_bit = (
                2 * old_defect
                + target_bits[prefix_depth]
                - proper_count
            )
            for new_bit in (0, 1):
                defect = before_new_bit - new_bit
                if not 0 <= defect <= ceiling:
                    continue
                if defect in next_states:
                    raise AssertionError(
                        "distinct complete prefixes reached one endpoint"
                    )
                next_states[defect] = bits | (
                    new_bit_mask if new_bit else 0
                )
        states = next_states

        s = prefix_depth + 1
        doubled_depth = 2 * s
        scale = 1 << doubled_depth
        target_quotient = scale // DENOMINATOR
        lower = 1 << s
        upper = lower + doubled_depth // 20
        reference = states[min(states)]
        reference_quotient = target_quotient
        selected = reference
        while selected:
            low_bit = selected & -selected
            divisor = low_bit.bit_length()
            reference_quotient -= scale // ((1 << divisor) - 1)
            selected -= low_bit

        for bits in states.values():
            quotient = reference_quotient
            difference = bits ^ reference
            while difference:
                low_bit = difference & -difference
                divisor = low_bit.bit_length()
                weight = scale // ((1 << divisor) - 1)
                if (reference >> (divisor - 1)) & 1:
                    quotient += weight
                else:
                    quotient -= weight
                difference -= low_bit
            tested_prefix_count += 1
            if lower <= quotient <= upper:
                raise AssertionError(
                    "first-seam backward certificate found: "
                    f"s={s}, z={quotient - lower}"
                )

    return {
        "max_s": horizon,
        "tested_globally_corridor_admissible_prefixes": tested_prefix_count,
        "certificate": "Q_(2s)(P) = 2^s + z, 0 <= z <= floor(2s/20)",
        "status": "excluded by exact finite computation only",
    }


def compressed_audit(horizon: int) -> tuple[Cylinder, dict[str, object]]:
    # ``proper_counts[m]`` receives one unit whenever a newly fixed selected
    # bit has index dividing the future rank ``m``.
    proper_counts = bytearray(horizon + 1)
    prefix_length = 0
    suffix_width = 0
    endpoint = 0
    old_ceiling = 0
    remainder = 1
    selected_fixed_count = 0
    maximum_suffix = (0, 0, 0)
    current_no_extraction_run = 0
    longest_no_extraction_run = (0, 0, 0)
    current_no_extraction_rows: list[dict[str, int]] = []
    longest_no_extraction_rows: list[dict[str, int]] = []

    for rank in range(1, horizon + 1):
        # Every proper divisor of ``rank`` is at most floor(rank/2).  This is
        # the exact ancestry gate needed before replacing statewise divisor
        # counts by one common count.
        assert prefix_length >= rank // 2

        remainder *= 2
        target_bit, remainder = divmod(remainder, DENOMINATOR)
        proper_count = proper_counts[rank]
        correction = target_bit - proper_count
        new_ceiling = rank // 20

        # For old endpoint q and new bit e, q' = 2q + correction - e.
        # These two-point blocks are disjoint and tile the displayed raw
        # interval.  Containment of the new corridor is therefore equivalent
        # to the two endpoint inequalities below.
        raw_lower = correction - 1
        raw_upper = 2 * old_ceiling + correction
        assert raw_lower <= 0
        assert raw_upper >= new_ceiling

        # If the old suffix numeral is endpoint-q, appending e gives
        # 2(endpoint-q)+e = (2 endpoint+correction)-q'.
        enlarged_width = suffix_width + 1
        enlarged_endpoint = 2 * endpoint + correction
        lower_suffix = enlarged_endpoint - new_ceiling
        upper_suffix = enlarged_endpoint
        assert 0 <= lower_suffix <= upper_suffix < (1 << enlarged_width)

        if lower_suffix == upper_suffix:
            remaining_width = 0
        else:
            remaining_width = (lower_suffix ^ upper_suffix).bit_length()
        extracted_count = enlarged_width - remaining_width
        common_value = (
            upper_suffix >> remaining_width if extracted_count else 0
        )

        if extracted_count == 0:
            current_no_extraction_run += 1
            current_no_extraction_rows.append(
                {
                    "rank": rank,
                    "phase_mod_20": rank % 20,
                    "ceiling": new_ceiling,
                    "target_bit": target_bit,
                    "proper_divisor_count": proper_count,
                    "correction": correction,
                    "suffix_width_after": remaining_width,
                    "endpoint_after": upper_suffix,
                    "displacement_after": (
                        upper_suffix - (1 << (remaining_width - 1))
                    ),
                }
            )
            if current_no_extraction_run > longest_no_extraction_run[0]:
                longest_no_extraction_run = (
                    current_no_extraction_run,
                    rank - current_no_extraction_run + 1,
                    rank,
                )
                longest_no_extraction_rows = current_no_extraction_rows.copy()
        else:
            current_no_extraction_run = 0
            current_no_extraction_rows = []

        for offset in range(extracted_count):
            bit = (
                common_value >> (extracted_count - offset - 1)
            ) & 1
            fixed_rank = prefix_length + offset + 1
            if not bit:
                continue
            selected_fixed_count += 1
            for multiple in range(
                2 * fixed_rank, horizon + 1, fixed_rank
            ):
                if proper_counts[multiple] == 255:
                    raise OverflowError(
                        "proper-divisor counter exceeded byte range"
                    )
                proper_counts[multiple] += 1

        prefix_length += extracted_count
        suffix_width = remaining_width
        endpoint = (
            upper_suffix & ((1 << remaining_width) - 1)
            if remaining_width
            else 0
        )
        old_ceiling = new_ceiling
        assert prefix_length + suffix_width == rank

        if suffix_width > maximum_suffix[1]:
            maximum_suffix = (rank, suffix_width, endpoint)

    cylinder = Cylinder(
        horizon,
        prefix_length,
        suffix_width,
        endpoint,
        old_ceiling,
    )
    receipt = {
        "horizon": horizon,
        "maximum_variable_suffix": {
            "rank": maximum_suffix[0],
            "width": maximum_suffix[1],
            "endpoint": maximum_suffix[2],
        },
        "longest_no_common_bit_extraction_run": {
            "length": longest_no_extraction_run[0],
            "first_rank": longest_no_extraction_run[1],
            "last_rank": longest_no_extraction_run[2],
            "exact_rows": longest_no_extraction_rows,
        },
        "selected_fixed_count": selected_fixed_count,
        "status": "exact finite computation, not an all-depth theorem",
    }
    return cylinder, receipt


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--horizon", type=int, default=100_000)
    parser.add_argument("--full-crosscheck", type=int, default=3_000)
    parser.add_argument("--backward-certificate-horizon", type=int, default=1_000)
    args = parser.parse_args()
    if not 1 <= args.full_crosscheck <= args.horizon:
        raise SystemExit("require 1 <= --full-crosscheck <= --horizon")
    if not 1 <= args.backward_certificate_horizon <= args.horizon:
        raise SystemExit(
            "require 1 <= --backward-certificate-horizon <= --horizon"
        )

    full = full_audit(args.full_crosscheck)
    compressed_crosscheck, _ = compressed_audit(args.full_crosscheck)
    assert full == compressed_crosscheck

    terminal, receipt = compressed_audit(args.horizon)
    backward_certificate = backward_certificate_audit(
        args.backward_certificate_horizon
    )
    print(
        {
            "crosscheck": {
                "full_prefix_dp_through": args.full_crosscheck,
                "compressed_cylinder_agrees": True,
            },
            "terminal_cylinder": terminal.__dict__,
            "backward_certificate_audit": backward_certificate,
            **receipt,
        }
    )


if __name__ == "__main__":
    main()
