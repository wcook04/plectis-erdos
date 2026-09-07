#!/usr/bin/env python3
"""Exact finite audit for the 90/511 winding and divisor resolvent.

The script separates exact algebraic identities from finite observations.  It
audits the unshifted energy F=P-2Q, protective-alternate winding heights, the
order-73 residue obstruction, and the labelled future-divisor resolvent.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import lcm


NUMERATOR = 90
DENOMINATOR = 511
PERIOD = 9
WORD = [int(character) for character in "001011010"]


def ceil_fraction(value: Fraction) -> int:
    return (value.numerator + value.denominator - 1) // value.denominator


def source_bit(rank: int, word: list[int] = WORD) -> int:
    return word[(rank - 1) % len(word)]


def greedy_enclosure(depth: int) -> tuple[list[int], list[int], list[int], int]:
    precision = 2 * depth + 64
    scale = 1 << precision
    lower = scale * NUMERATOR // DENOMINATOR
    upper = (scale * NUMERATOR + DENOMINATOR - 1) // DENOMINATOR
    bits = [0] * (depth + 1)
    before_lower = [0] * (depth + 1)
    before_upper = [0] * (depth + 1)
    for rank in range(1, depth + 1):
        before_lower[rank] = lower
        before_upper[rank] = upper
        weight_floor = scale // ((1 << rank) - 1)
        if lower >= weight_floor + 1:
            lower -= weight_floor + 1
            upper -= weight_floor
            bits[rank] = 1
        elif upper <= weight_floor:
            continue
        else:
            raise AssertionError(f"ambiguous greedy branch at rank {rank}")
    return bits, before_lower, before_upper, scale


def orbit_states(bits: list[int], word: list[int] = WORD) -> dict[str, list[int]]:
    depth = len(bits) - 1
    prefix = [0] * (depth + 1)
    source = [0] * (depth + 1)
    divisor_load = [0] * (depth + 1)
    for rank in range(1, depth + 1):
        prefix[rank] = prefix[rank - 1] + bits[rank]
        source[rank] = source[rank - 1] + source_bit(rank, word)
        if bits[rank]:
            for multiple in range(rank, depth + 1, rank):
                divisor_load[multiple] += 1
    defect = [0] * (depth + 1)
    energy = [0] * (depth + 1)
    for rank in range(1, depth + 1):
        defect[rank] = (
            2 * defect[rank - 1]
            + source_bit(rank, word)
            - divisor_load[rank]
        )
        delayed = source[rank] + prefix[rank // 2] - prefix[rank]
        energy[rank] = delayed - 2 * defect[rank]
    return {
        "prefix": prefix,
        "source": source,
        "divisor_load": divisor_load,
        "defect": defect,
        "energy": energy,
    }


def delta_bounds(
    rank: int,
    before_lower: int,
    before_upper: int,
    scale: int,
) -> tuple[Fraction, Fraction]:
    threshold = Fraction(1 << rank, (1 << rank) - 1)
    lower = threshold - Fraction((1 << rank) * before_upper, scale)
    upper = threshold - Fraction((1 << rank) * before_lower, scale)
    if not 0 < lower <= upper:
        raise AssertionError(f"invalid forced-coin excess at rank {rank}")
    return lower, upper


def winding_residue_mod_73(
    horizon: int,
    forcing_rank: int,
    bits: list[int],
) -> int:
    """Principal 73-adic residue of Phi_alt-alpha below rank 657.

    The value is 73*(Phi-alpha) modulo 73.  Ranks divisible by 657 would
    create a higher 73-adic pole and are deliberately outside this function.
    """
    if not horizon < 657:
        raise ValueError("principal residue formula is restricted to horizon < 657")
    residue = 0
    for rank in range(9, min(horizon, forcing_rank) + 1, 9):
        selected = (rank < forcing_rank and bits[rank]) or rank == forcing_rank
        if not selected:
            continue
        quotient = ((1 << rank) - 1) // 73
        if quotient % 73 == 0:
            raise AssertionError("unexpected higher 73-adic pole")
        residue += (
            pow(2, horizon % rank, 73) * pow(quotient % 73, -1, 73)
        )
    target_residue = (NUMERATOR * pow(2, horizon, DENOMINATOR)) % DENOMINATOR
    residue -= target_residue * pow(7, -1, 73)
    return residue % 73


def protective_winding_audit(
    depth: int,
    lookahead: int,
) -> dict[str, object]:
    bits, before_lower, before_upper, scale = greedy_enclosure(depth)
    states = orbit_states(bits)
    prefix = states["prefix"]
    source = states["source"]
    divisor_load = states["divisor_load"]
    defect = states["defect"]
    energy = states["energy"]

    minimum_height: tuple[int, dict[str, int]] | None = None
    minimum_height_after_initial_prefix: tuple[int, dict[str, int]] | None = None
    negative_heights: list[dict[str, int]] = []
    realized_ceiling_counts: dict[int, int] = {}
    realized_ceiling_above_one_after_rank_five: list[dict[str, int]] = []
    half_scale_crossing_runs = 0
    largest_run_ratio = (0.0, 0, 0)
    phase_payment_examples: dict[tuple[int, int, int], dict[str, int]] = {}

    for rank in range(1, depth):
        if bits[rank]:
            continue
        lower_delta, upper_delta = delta_bounds(
            rank, before_lower[rank], before_upper[rank], scale
        )
        initial_lower_ceiling = ceil_fraction(lower_delta)
        initial_upper_ceiling = ceil_fraction(upper_delta)
        if initial_lower_ceiling != initial_upper_ceiling:
            raise AssertionError(f"initial ceiling not certified at rank {rank}")
        previous_ceiling = initial_lower_ceiling

        proper_at_rank = divisor_load[rank] - bits[rank]
        forced_q = (
            2 * defect[rank - 1]
            + source_bit(rank)
            - proper_at_rank
            - 1
        )
        forced_total = prefix[rank - 1] + 1
        upper_k = min(lookahead, rank - 1, depth - rank)
        heights: dict[int, int] = {}
        ceilings: dict[int, int] = {}
        for offset in range(1, upper_k + 1):
            horizon = rank + offset
            # offset < rank, so every proper divisor is below the forcing rank.
            proper_load = divisor_load[horizon] - bits[horizon]
            forced_q = (
                2 * forced_q + source_bit(horizon) - proper_load
            )
            forced_p = (
                source[horizon]
                + prefix[horizon // 2]
                - forced_total
            )
            forced_f = forced_p - 2 * forced_q
            scaled_lower = (1 << offset) * lower_delta
            scaled_upper = (1 << offset) * upper_delta
            ceiling_lower = ceil_fraction(scaled_lower)
            ceiling_upper = ceil_fraction(scaled_upper)
            if ceiling_lower != ceiling_upper:
                raise AssertionError(
                    f"scaled ceiling not certified at rank={rank}, k={offset}"
                )
            height = forced_f - offset - ceiling_lower
            receipt = {
                "rank": rank,
                "offset": offset,
                "horizon": horizon,
                "F_alt": forced_f,
                "Q_alt": forced_q,
                "ceil_2_pow_k_Delta": ceiling_lower,
                "height": height,
            }
            if minimum_height is None or height < minimum_height[0]:
                minimum_height = (height, receipt)
            if rank >= 6 and (
                minimum_height_after_initial_prefix is None
                or height < minimum_height_after_initial_prefix[0]
            ):
                minimum_height_after_initial_prefix = (height, receipt)
            if height < 0:
                negative_heights.append(receipt)
            heights[offset] = height
            ceilings[offset] = ceiling_lower

            phase_payment = 2 * previous_ceiling - ceiling_lower
            if phase_payment not in (0, 1):
                raise AssertionError("non-Boolean phase payment")
            if rank >= 6 and horizon - 1 < 657:
                residue = winding_residue_mod_73(horizon - 1, rank, bits)
                key = (residue, (horizon - 1) % 9, phase_payment)
                phase_payment_examples.setdefault(
                    key,
                    {
                        "rank": rank,
                        "offset": offset,
                        "phase_horizon": horizon - 1,
                        "residue_mod_73": residue,
                        "phase_class_mod_9": (horizon - 1) % 9,
                        "phase_payment": phase_payment,
                        "previous_ceiling": previous_ceiling,
                        "next_ceiling": ceiling_lower,
                    },
                )
            previous_ceiling = ceiling_lower

        if rank + 1 <= depth and bits[rank + 1]:
            run = 1
            while rank + run + 1 <= depth and bits[rank + run + 1]:
                run += 1
            largest_run_ratio = max(largest_run_ratio, (run / rank, -rank, run))
            if run >= rank:
                half_scale_crossing_runs += 1
            if run <= upper_k:
                ceiling = ceilings[run]
                realized_ceiling_counts[ceiling] = (
                    realized_ceiling_counts.get(ceiling, 0) + 1
                )
                if rank >= 6 and ceiling > 1:
                    realized_ceiling_above_one_after_rank_five.append(
                        {"rank": rank, "run": run, "ceiling": ceiling}
                    )
                # Exact claim-discipline identity on a realized upper-half seam.
                if heights[run] != energy[rank + run] + 1 - ceiling:
                    raise AssertionError(
                        f"realized-seam height identity failed at rank {rank}"
                    )

    collisions: list[dict[str, object]] = []
    grouped: dict[tuple[int, int], dict[int, dict[str, int]]] = {}
    for (residue, phase, payment), receipt in phase_payment_examples.items():
        grouped.setdefault((residue, phase), {})[payment] = receipt
    for (residue, phase), examples in sorted(grouped.items()):
        if set(examples) == {0, 1}:
            collisions.append(
                {
                    "residue_mod_73": residue,
                    "phase_class_mod_9": phase,
                    "payment_zero": examples[0],
                    "payment_one": examples[1],
                }
            )

    # Prefer the chronologically earliest counterexample, rather than the
    # lexicographically first residue class.  This makes the printed receipt
    # a small exact obstruction which can be checked by hand.
    collisions.sort(
        key=lambda row: (
            max(
                row["payment_zero"]["phase_horizon"],
                row["payment_one"]["phase_horizon"],
            ),
            row["residue_mod_73"],
            row["phase_class_mod_9"],
        )
    )

    if minimum_height is None or minimum_height_after_initial_prefix is None:
        raise AssertionError("audit range too small")
    return {
        "minimum_winding_height": minimum_height[1],
        "negative_winding_heights": negative_heights,
        "minimum_height_for_rejected_rank_at_least_6": (
            minimum_height_after_initial_prefix[1]
        ),
        "realized_seam_excess_ceiling_counts": realized_ceiling_counts,
        "realized_seam_ceiling_above_one_after_rank_5": (
            realized_ceiling_above_one_after_rank_five
        ),
        "half_scale_crossing_realized_runs": half_scale_crossing_runs,
        "largest_realized_run_ratio": {
            "rank": -largest_run_ratio[1],
            "run": largest_run_ratio[2],
            "ratio": largest_run_ratio[0],
        },
        "mod_73_and_phase_class_do_not_determine_phase_payment": {
            "collision_count_below_rank_657": len(collisions),
            "first_collision": collisions[0] if collisions else None,
        },
        "claim_status": "exact finite directed-interval audit only",
    }


def exact_small_target_state(numerator: int, depth: int) -> dict[str, object]:
    target = Fraction(numerator, DENOMINATOR)
    remainder = target
    bits = [0] * (depth + 1)
    for rank in range(1, depth + 1):
        weight = Fraction(1, (1 << rank) - 1)
        if weight <= remainder:
            bits[rank] = 1
            remainder -= weight
    word = [(numerator >> (PERIOD - 1 - index)) & 1 for index in range(PERIOD)]
    states = orbit_states(bits, word)
    return {
        "bits": bits,
        "states": states,
        "word": word,
        "remainder": remainder,
    }


def order_73_no_go_receipt() -> dict[str, object]:
    low = exact_small_target_state(17, 12)
    target = exact_small_target_state(90, 12)
    assert 90 - 17 == 73
    assert Fraction(90, 511) == Fraction(1, 7) + Fraction(17, 511)
    assert [rank for rank in range(1, 4) if target["bits"][rank]] == [3]
    assert not any(low["bits"][1:4])
    low_after_three = Fraction(17, 511)
    target_after_three = Fraction(90, 511) - Fraction(1, 7)
    assert low_after_three == target_after_three
    low_energy = low["states"]["energy"]
    target_energy = target["states"]["energy"]
    assert low_energy[9] == -1
    assert target_energy[9] == 1
    residues_low = [17 * pow(2, rank, 73) % 73 for rank in range(9)]
    residues_target = [90 * pow(2, rank, 73) % 73 for rank in range(9)]
    assert residues_low == residues_target
    return {
        "targets": ["17/511", "90/511"],
        "numerator_difference": 73,
        "common_order_9_residue_orbit_mod_73": residues_target,
        "exact_recut": "90/511 = 1/7 + 17/511",
        "greedy_tail_agrees_after_rank": 3,
        "rank_9_energy": {"17/511": -1, "90/511": 1},
        "rank_9_quotient_defect": {
            "17/511": low["states"]["defect"][9],
            "90/511": target["states"]["defect"][9],
        },
        "claim_status": "exact rational and integer recurrence counterexample",
    }


def future_divisor_count(bits: list[int], support_limit: int, boundary: int, offset: int) -> int:
    return sum(
        bits[rank]
        for rank in range(1, support_limit + 1)
        if (boundary + offset) % rank == 0
    )


def resolvent_receipt(depth: int, maximum_r: int) -> dict[str, object]:
    bits, _, _, _ = greedy_enclosure(depth)
    states = orbit_states(bits)
    defect = states["defect"]
    energy = states["energy"]
    maximum_r = min(maximum_r, (depth - 2) // 2)
    transport_checks = 0
    scalar_checks = 0
    two_step_checks = 0
    phase_split_checks = 0
    last_scalar = Fraction()
    for radius in range(2, maximum_r + 1):
        selected = [rank for rank in range(1, radius + 1) if bits[rank]]
        scalar = sum(
            (
                Fraction(1 << ((2 * radius) % rank), (1 << rank) - 1)
                for rank in selected
            ),
            Fraction(),
        )
        clock_scalar = Fraction()
        for rank in selected:
            residue = (2 * radius) % rank
            next_arrival = rank if residue == 0 else rank - residue
            clock_scalar += Fraction(1, 1 << next_arrival) / (
                1 - Fraction(1, 1 << rank)
            )
        if scalar != clock_scalar:
            raise AssertionError(f"resolvent scalar identity failed at R={radius}")
        scalar_checks += 1
        last_scalar = scalar

        horizon = 2 * radius
        upper_selected = [
            rank
            for rank in range(radius + 1, horizon + 1)
            if bits[rank]
        ]
        upper_phase = sum(
            (
                Fraction(
                    1 << (horizon % rank),
                    (1 << rank) - 1,
                )
                for rank in upper_selected
            ),
            Fraction(),
        )
        remainder = Fraction(NUMERATOR, DENOMINATOR) - sum(
            (
                Fraction(1, (1 << rank) - 1)
                for rank in range(1, horizon + 1)
                if bits[rank]
            ),
            Fraction(),
        )
        scaled_remainder = (1 << horizon) * remainder
        alpha = Fraction(
            NUMERATOR * pow(2, horizon, DENOMINATOR) % DENOMINATOR,
            DENOMINATOR,
        )
        split_defect = scaled_remainder - alpha + scalar + upper_phase
        if split_defect != defect[horizon]:
            raise AssertionError(f"phase split failed at R={radius}")
        source_count = sum(source_bit(rank) for rank in range(1, horizon + 1))
        split_energy = (
            source_count
            - len(upper_selected)
            + 2 * alpha
            - 2 * scaled_remainder
            - 2 * scalar
            - 2 * upper_phase
        )
        if split_energy != energy[horizon]:
            raise AssertionError(f"energy split failed at R={radius}")
        phase_split_checks += 1

        nu_one = future_divisor_count(bits, radius, 2 * radius, 1)
        nu_two = future_divisor_count(bits, radius, 2 * radius, 2)
        next_selected = [
            rank for rank in range(1, radius + 2) if bits[rank]
        ]
        next_scalar = sum(
            (
                Fraction(1 << ((2 * radius + 2) % rank), (1 << rank) - 1)
                for rank in next_selected
            ),
            Fraction(),
        )
        transported = (
            4 * scalar
            - 2 * nu_one
            - nu_two
            + Fraction(bits[radius + 1], (1 << (radius + 1)) - 1)
        )
        if next_scalar != transported:
            raise AssertionError(f"resolvent transport failed at R={radius}")
        for offset in range(1, 33):
            left = future_divisor_count(
                bits, radius + 1, 2 * radius + 2, offset
            )
            right = future_divisor_count(
                bits, radius, 2 * radius, offset + 2
            )
            if bits[radius + 1] and offset % (radius + 1) == 0:
                right += 1
            if left != right:
                raise AssertionError(
                    f"coefficient transport failed at R={radius}, c={offset}"
                )
        transport_checks += 1

        expected_energy_step = (
            nu_one
            + nu_two
            + 2 * bits[radius + 1]
            - defect[2 * radius + 1]
            - defect[2 * radius + 2]
        )
        if energy[2 * radius + 2] - energy[2 * radius] != expected_energy_step:
            raise AssertionError(f"two-step energy identity failed at R={radius}")
        two_step_checks += 1

    # A small exact demonstration that the infinite coefficient sequence is
    # lossless for a finite support: shift by lcm(1,...,R), then use Möbius.
    recovery_radius = 12
    period_lcm = 1
    for rank in range(1, recovery_radius + 1):
        period_lcm = lcm(period_lcm, rank)
    recovered_incidence: list[int] = []
    for rank in range(1, recovery_radius + 1):
        lifted = rank
        while lifted <= 2 * recovery_radius:
            lifted += period_lcm
        recovered_incidence.append(
            future_divisor_count(
                bits,
                recovery_radius,
                2 * recovery_radius,
                lifted - 2 * recovery_radius,
            )
        )
        direct = sum(
            bits[divisor]
            for divisor in range(1, rank + 1)
            if rank % divisor == 0
        )
        if recovered_incidence[-1] != direct:
            raise AssertionError("tail coefficient did not recover incidence")

    return {
        "maximum_R": maximum_r,
        "resolvent_scalar_identity_checks": scalar_checks,
        "coefficient_and_scalar_transport_checks": transport_checks,
        "two_step_energy_identity_checks": two_step_checks,
        "phase_and_energy_split_checks": phase_split_checks,
        "last_resolvent_scalar": str(last_scalar),
        "lossless_tail_recovery": {
            "R": recovery_radius,
            "period_lcm": period_lcm,
            "recovered_divisor_incidence": recovered_incidence,
        },
        "transport_coefficient_mismatch": {
            "phase_evaluation_removes": "2*nu_R(1) + nu_R(2)",
            "two_step_F_service_receives": "nu_R(1) + nu_R(2) + 2*b_(R+1)",
        },
        "claim_status": "displayed identities checked exactly on the finite range",
    }


def alpha_phase_table() -> list[dict[str, object]]:
    table: list[dict[str, object]] = []
    for radius_mod_nine in range(9):
        exponent = 2 * radius_mod_nine
        residue = NUMERATOR * pow(2, exponent, DENOMINATOR) % DENOMINATOR
        table.append(
            {
                "R_mod_9": radius_mod_nine,
                "alpha_2R_numerator_mod_511": residue,
                "alpha_numerator_mod_73": residue % 73,
                "alpha_numerator_mod_7": residue % 7,
                "source_pair": [
                    WORD[exponent % 9],
                    WORD[(exponent + 1) % 9],
                ],
            }
        )
    return table


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=5000)
    parser.add_argument("--lookahead", type=int, default=64)
    parser.add_argument("--resolvent-depth", type=int, default=80)
    args = parser.parse_args()
    if args.depth < 700:
        raise SystemExit("--depth must be at least 700")
    output = {
        "target": "90/511",
        "source_word": "001011010",
        "alpha_phase_table": alpha_phase_table(),
        "protective_winding": protective_winding_audit(
            args.depth, args.lookahead
        ),
        "order_73_no_go": order_73_no_go_receipt(),
        "future_divisor_resolvent": resolvent_receipt(
            args.depth, args.resolvent_depth
        ),
        "global_claim_status": (
            "exact identities plus finite audits; no all-depth proof of SC0"
        ),
    }
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
