#!/usr/bin/env python3
"""Exact even-endpoint experiment for the Erdős 257 half route.

Let ``B_d`` be the real greedy support for ``1/2`` through rank ``d`` and

    W_d = 2^(2d-1) - sum_{a in B_d} floor(2^(2d)/(2^a-1)).

Two applications of the quotient transition give the exact recurrence

    W_(d+1) = 4 W_d - 2 g_(2d+1) - g_(2d+2)
              - b_(d+1) (2^(d+1)+1),

where ``g_n`` counts selected divisors of ``n`` and ``b`` is the certified
real half-greedy bit.  This avoids a quadratic quotient-row recomputation.

The probe compares the midpoint quotient decision with the independently
certified real decision and measures every quotient take against the exact
square-cleared form of the Lean boundary ``R < 2*sqrt(2d)+4``.

Finite success is evidence only.  It selects or falsifies mechanisms; it is
not promoted to an all-depth theorem.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from typing import Any


def certified_half_bits(max_rank: int, slack_bits: int) -> bytearray:
    """Certify the real greedy half word by a dyadic interval enclosure."""

    precision = 2 * max_rank + slack_bits
    scale = 1 << precision
    lower = scale // 2
    upper = lower
    bits = bytearray(max_rank + 1)

    for d in range(2, max_rank + 1):
        quotient = scale // ((1 << d) - 1)
        if lower >= quotient + 1:
            bits[d] = 1
            lower -= quotient + 1
            upper -= quotient
        elif upper <= quotient:
            bits[d] = 0
        else:
            raise AssertionError(
                f"real half decision ambiguous at rank {d}; "
                "increase --slack-bits"
            )
        if lower < 0 or lower > upper:
            raise AssertionError(f"invalid residual enclosure at rank {d}")

    return bits


def packed_sha256(bits: bytearray, max_rank: int) -> str:
    packed = bytearray((max_rank + 7) // 8)
    for rank in range(1, max_rank + 1):
        if bits[rank]:
            packed[(rank - 1) // 8] |= 1 << ((rank - 1) % 8)
    return hashlib.sha256(bytes(packed)).hexdigest()


def smallest_prime_factors(limit: int) -> list[int]:
    spf = list(range(limit + 1))
    if limit >= 1:
        spf[1] = 1
    for p in range(2, math.isqrt(limit) + 1):
        if spf[p] != p:
            continue
        for multiple in range(p * p, limit + 1, p):
            if spf[multiple] == multiple:
                spf[multiple] = p
    return spf


def divisors_from_spf(n: int, spf: list[int]) -> list[int]:
    divisors = [1]
    while n > 1:
        p = spf[n]
        exponent = 0
        while n % p == 0:
            n //= p
            exponent += 1
        old = tuple(divisors)
        power = 1
        for _ in range(exponent):
            power *= p
            divisors.extend(d * power for d in old)
    return divisors


def selected_divisor_pulse(
    n: int, cutoff: int, bits: bytearray, spf: list[int]
) -> int:
    return sum(
        1 for divisor in divisors_from_spf(n, spf)
        if 2 <= divisor <= cutoff and bits[divisor]
    )


def candidate_selected_divisor_pulse(
    n: int,
    cutoff: int,
    bits: bytearray,
    spf: list[int],
    forced_rank: int,
) -> int:
    """Selected-divisor pulse after forcibly adjoining the midpoint rank."""

    return sum(
        1 for divisor in divisors_from_spf(n, spf)
        if 2 <= divisor <= cutoff
        and (bits[divisor] or divisor == forced_rank)
    )


def minimal_sqrt_tail_lookahead(endpoint: int) -> int:
    """Least ``L`` with ``2*isqrt(endpoint+L)+3 <= 2^L``."""

    lookahead = 0
    while 2 * math.isqrt(endpoint + lookahead) + 3 > 1 << lookahead:
        lookahead += 1
    return lookahead


def candidate_finite_window_numerator(
    bits: bytearray,
    rank: int,
    lookahead: int,
    spf: list[int],
) -> int:
    """Weighted future incidence for the prefix with ``rank`` adjoined."""

    endpoint = 2 * rank
    numerator = 0
    for offset in range(1, lookahead + 1):
        numerator = 2 * numerator + candidate_selected_divisor_pulse(
            endpoint + offset, rank, bits, spf, rank
        )
    return numerator


def fixed_support_window_profile(
    support: set[int], endpoint: int, length: int, spf: list[int]
) -> dict[str, Any]:
    """Division-free binary multiplicity window for a frozen support.

    The returned numerator is ``2^length`` times the finite tail

        sum_{j=1}^length tau_support(endpoint+j) / 2^j.

    Subtracting ``2^length-1`` removes the layer-one baseline and exposes
    the finite excess-multiplicity coordinate (with holes counted as -1).
    """

    def centered_carry(index: int) -> int:
        carry = 0
        for carry_index in range(index):
            coefficient = sum(
                1
                for divisor in divisors_from_spf(carry_index + 2, spf)
                if divisor in support
            )
            carry = 2 * carry + 1 - coefficient
        return carry

    numerator = 0
    hole_numerator = 0
    positive_excess_numerator = 0
    coefficients: list[int] = []
    for offset in range(1, length + 1):
        coefficient = sum(
            1 for divisor in divisors_from_spf(endpoint + offset, spf)
            if divisor in support
        )
        coefficients.append(coefficient)
        numerator = 2 * numerator + coefficient
        hole_numerator = 2 * hole_numerator + int(coefficient == 0)
        positive_excess_numerator = (
            2 * positive_excess_numerator + max(coefficient - 1, 0)
        )
    baseline = (1 << length) - 1
    start_centered_carry = centered_carry(endpoint - 1)
    end_centered_carry = centered_carry(endpoint + length - 1)
    if numerator - baseline != positive_excess_numerator - hole_numerator:
        raise AssertionError("centered multiplicity split failed")
    if numerator - baseline != (
        (1 << length) * start_centered_carry - end_centered_carry
    ):
        raise AssertionError("multiplicity window did not telescope to carries")
    return {
        "numerator": numerator,
        "baseline_numerator": baseline,
        "centered_excess_numerator": numerator - baseline,
        "hole_numerator": hole_numerator,
        "positive_excess_numerator": positive_excess_numerator,
        "start_centered_carry": start_centered_carry,
        "end_centered_carry": end_centered_carry,
        "hole_count": sum(coefficient == 0 for coefficient in coefficients),
        "excess_incidence_count": sum(
            max(coefficient - 1, 0) for coefficient in coefficients
        ),
        "minimum_coefficient": min(coefficients, default=0),
        "maximum_coefficient": max(coefficients, default=0),
    }


def in_sqrt_crossing_window(residual: int, rank: int) -> bool:
    """Decide ``R < 2*sqrt(2d)+4`` without floating point."""

    if residual < 4:
        return True
    return (residual - 4) ** 2 < 8 * rank


def ceil_div(numerator: int, denominator: int) -> int:
    """Ceiling division for a nonnegative denominator."""

    return -((-numerator) // denominator)


def direct_even_residual(bits: bytearray, rank: int) -> int:
    endpoint = 2 * rank
    residual = 1 << (endpoint - 1)
    for a in range(2, rank + 1):
        if bits[a]:
            residual -= (1 << endpoint) // ((1 << a) - 1)
    return residual


def audit_forced_seam_words(
    max_rank: int, *, include_pullback_events: bool = False
) -> dict[str, Any]:
    """Test the finite certificate on every deterministic seam-greedy word.

    If a first quotient-take/real-skip mismatch occurs at rank ``d``, the
    landed full-shell theorem forces the real prefix below ``d`` to equal the
    integer-greedy representation of

        2^(2d-1) - 2^d

    using ranks ``2,...,d-1``.  If that seam word has remainder ``E``, the
    counterfactual midpoint take leaves residual ``R=E-1``.  For ``E>=2``
    the Lean finite-window certificate says a crossing requires

        N_L - (E-2) * 2^L > 0.

    The computation below tests that necessary inequality on the forced word,
    not merely on the actual no-mismatch orbit.
    """

    if max_rank < 3:
        raise ValueError("--seam-word-max-rank must be at least 3")
    spf = smallest_prime_factors(
        2 * max_rank + max_rank.bit_length() + 16
    )
    zero_candidate_residuals: list[dict[str, int]] = []
    positive_certificate_events: list[dict[str, int]] = []
    maximum_certificate_surplus: tuple[int, int, int, int, int] | None = None
    minimum_positive_seam_remainder: tuple[int, int] | None = None
    card_bound_failures: list[dict[str, int]] = []
    minimum_card_bound_slack_from_rank_eight: tuple[int, int, int, int] | None = None
    minimum_card_bound_slack_by_branch: dict[str, tuple[int, int, int, int]] = {}
    branch_counts: dict[str, int] = {"upper": 0, "middle": 0, "right": 0}
    record_card_bound_slacks_from_rank_eight: list[dict[str, int | str]] = []
    previous_support: set[int] | None = None
    last_nonright_branch: str | None = None
    right_run_length = 0
    maximum_upper_right_run_length = 0
    upper_right_congruence_dangers: list[dict[str, int]] = []
    minimum_upper_right_congruence_clearance: tuple[int, int, int, int, int] | None = None
    upper_pullback_events: list[dict[str, int | bool]] = []
    upper_predecessor_branch_failures: list[dict[str, int | str]] = []
    late_upper_parent_missing_events: list[dict[str, int]] = []
    late_upper_pullback_growth_failures: list[dict[str, int]] = []
    unit_reset_lattice_events: list[dict[str, int]] = []
    active_upper_run: dict[str, Any] | None = None
    seam_remainders = [0] * (max_rank + 1)
    seam_support_cards = [0] * (max_rank + 1)
    incoming_branches = ["unseen"] * (max_rank + 1)
    seam_take_count = 0

    def finish_upper_run(endpoint_rank: int, outgoing_branch: str) -> None:
        """Close one observed upper/right block in its backward coordinate."""

        nonlocal active_upper_run
        if active_upper_run is None:
            return
        source_rank = active_upper_run["source_rank"]
        largest_false = active_upper_run["largest_false"]
        backward_length = source_rank - largest_false
        right_run_length_local = active_upper_run["right_run_length"]
        reset_charge = active_upper_run["reset_charge"]
        backward_charge = active_upper_run["backward_charge"]
        reduced_exponent = 2 * largest_false + 1 - source_rank
        expected_endpoint = source_rank + right_run_length_local + 1
        if endpoint_rank != expected_endpoint:
            raise AssertionError("upper/right endpoint bookkeeping failed")

        critical_gap = (
            (1 << (source_rank - right_run_length_local + 1))
            - reset_charge
        )
        pullback_numerator = critical_gap + backward_charge
        pullback_modulus = 4 ** backward_length
        pullback_coordinate, pullback_residue = divmod(
            pullback_numerator, pullback_modulus
        )
        if pullback_residue:
            raise AssertionError("backward critical-gap pullback is not exact")

        predecessor_branch = incoming_branches[largest_false + 1]
        if source_rank >= 13 and predecessor_branch != "middle":
            upper_predecessor_branch_failures.append(
                {
                    "source_rank": source_rank,
                    "largest_false_rank": largest_false,
                    "predecessor_branch": predecessor_branch,
                }
            )
        parent_upper = next(
            (
                event
                for event in reversed(upper_pullback_events)
                if int(event["endpoint_rank"]) == largest_false
            ),
            None,
        )
        is_late_largest_false = 2 * source_rank < 3 * largest_false
        if is_late_largest_false and parent_upper is None:
            late_upper_parent_missing_events.append(
                {
                    "source_rank": source_rank,
                    "largest_false_rank": largest_false,
                }
            )
        middle_landing_excess = (
            seam_remainders[largest_false + 1]
            - (1 << (largest_false + 1))
        )
        middle_source_pulse = (
            4 * seam_remainders[largest_false]
            - middle_landing_excess
        )
        base_pullback_coordinate = (
            middle_landing_excess
            - 4
            - (1 << reduced_exponent)
        )
        dyadic_staircase = (
            (1 << reduced_exponent)
            - (1 << (reduced_exponent - right_run_length_local))
        )
        if (
            base_pullback_coordinate - dyadic_staircase
            != pullback_coordinate
        ):
            raise AssertionError("reduced dyadic-staircase identity failed")
        if (
            is_late_largest_false
            and parent_upper is not None
            and pullback_coordinate
            <= int(parent_upper["pullback_coordinate"])
        ):
            late_upper_pullback_growth_failures.append(
                {
                    "source_rank": source_rank,
                    "largest_false_rank": largest_false,
                    "pullback_coordinate": pullback_coordinate,
                    "parent_source_rank": int(parent_upper["source_rank"]),
                    "parent_pullback_coordinate": int(
                        parent_upper["pullback_coordinate"]
                    ),
                }
            )

        endpoint_remainder = seam_remainders[endpoint_rank]
        endpoint_support_card = len(previous_support or set())
        right_run_charge = (
            (4 ** right_run_length_local) * critical_gap
            - endpoint_remainder
        )
        endpoint_packet = endpoint_remainder + right_run_charge
        endpoint_half_threshold = 1 << (
            source_rank + right_run_length_local
        )
        endpoint_packet_slack = endpoint_half_threshold - endpoint_packet - 1

        terminal_outgoing_branch = outgoing_branch
        terminal_pulse = (
            4 * endpoint_remainder
            + (1 << (endpoint_rank + 1))
            - seam_remainders[endpoint_rank + 1]
        )
        returned_charge = 4 * right_run_charge + terminal_pulse + 4
        returned_packet = (
            seam_remainders[endpoint_rank + 1] + returned_charge
        )
        returned_threshold = 1 << (
            source_rank + right_run_length_local + 3
        )
        returned_packet_slack = returned_threshold + 4 - returned_packet - 1
        if (
            right_run_length_local > 0
            and 2 * (source_rank + right_run_length_local) < 3 * source_rank
        ):
            reset_support = set(active_upper_run["reset_support"])
            forward_profile = fixed_support_window_profile(
                reset_support,
                2 * (source_rank + 1),
                2 * right_run_length_local,
                spf,
            )
            modulus = 4 ** right_run_length_local
            window_numerator = int(forward_profile["numerator"])
            end_carry = int(forward_profile["end_centered_carry"])
            window_residue = (3 * window_numerator - 1) % modulus
            carry_residue = (3 * end_carry + 4) % modulus
            if (window_residue + carry_residue) % modulus:
                raise AssertionError(
                    "multiplicity-window and centered-carry residues disagree"
                )
            congruence_depth = 0
            reduced_residue = carry_residue
            while (
                congruence_depth < right_run_length_local
                and reduced_residue % 4 == 0
            ):
                congruence_depth += 1
                reduced_residue //= 4
            unit_reset_lattice_events.append(
                {
                    "source_rank": source_rank,
                    "endpoint_rank": endpoint_rank,
                    "right_run_length": right_run_length_local,
                    "endpoint_remainder": endpoint_remainder,
                    "terminal_pulse": terminal_pulse,
                    "modulus": modulus,
                    "window_numerator": window_numerator,
                    "window_residue": window_residue,
                    "end_centered_carry": end_carry,
                    "carry_residue": carry_residue,
                    "congruence_depth": congruence_depth,
                    "lattice_distance": min(
                        carry_residue, (-carry_residue) % modulus
                    ),
                }
            )
        if terminal_outgoing_branch == "middle":
            if returned_packet != (
                4 * endpoint_packet + (1 << (endpoint_rank + 1)) + 4
            ):
                raise AssertionError("terminal middle packet transfer failed")
            if returned_packet_slack != 4 * endpoint_packet_slack + 3:
                raise AssertionError("terminal middle packet slack transfer failed")
        nested_charge = (
            right_run_charge
            + (4 ** right_run_length_local) * backward_charge
        )
        if (
            endpoint_remainder + nested_charge
            != (4 ** (right_run_length_local + backward_length))
            * pullback_coordinate
        ):
            raise AssertionError("nested upper/right pullback identity failed")
        factor_range = (
            source_rank + right_run_length_local
            <= 2 * largest_false + 1
        )
        two_block_amplification_slack = (
            9 * endpoint_remainder
            - (4 ** (backward_length + right_run_length_local))
            * pullback_coordinate
            - 2 * (4 ** right_run_length_local) * pullback_coordinate
            - 6 * critical_gap
        )

        upper_pullback_events.append(
            {
                "source_rank": source_rank,
                "largest_false_rank": largest_false,
                "backward_length": backward_length,
                "reduced_exponent": reduced_exponent,
                "right_run_length": right_run_length_local,
                "remaining_reduced_exponent": (
                    reduced_exponent - right_run_length_local
                ),
                "endpoint_rank": endpoint_rank,
                "endpoint_remainder": endpoint_remainder,
                "endpoint_support_card": endpoint_support_card,
                "source_remainder": seam_remainders[source_rank],
                "source_exp_barrier_slack": (
                    seam_remainders[source_rank]
                    - (1 << source_rank)
                    - source_rank
                ),
                "predecessor_branch": predecessor_branch,
                "is_late_largest_false": is_late_largest_false,
                "parent_upper_source_rank": (
                    -1
                    if parent_upper is None
                    else int(parent_upper["source_rank"])
                ),
                "parent_upper_pullback_coordinate": (
                    -1
                    if parent_upper is None
                    else int(parent_upper["pullback_coordinate"])
                ),
                "middle_source_remainder": seam_remainders[largest_false],
                "middle_source_support_card": (
                    seam_support_cards[largest_false]
                ),
                "middle_source_row_slack": (
                    seam_remainders[largest_false] - largest_false
                ),
                "middle_source_pulse": middle_source_pulse,
                "middle_landing_excess": middle_landing_excess,
                "critical_gap": critical_gap,
                "backward_fixed_support_charge": backward_charge,
                "backward_multiplicity_window_baseline": active_upper_run[
                    "multiplicity_window_baseline"
                ],
                "backward_multiplicity_window_centered_excess": (
                    active_upper_run[
                        "multiplicity_window_centered_excess"
                    ]
                ),
                "backward_multiplicity_window_hole_count": active_upper_run[
                    "multiplicity_window_hole_count"
                ],
                "backward_multiplicity_window_hole_numerator": (
                    active_upper_run["multiplicity_window_hole_numerator"]
                ),
                "backward_multiplicity_window_positive_excess_numerator": (
                    active_upper_run[
                        "multiplicity_window_positive_excess_numerator"
                    ]
                ),
                "backward_multiplicity_window_start_centered_carry": (
                    active_upper_run[
                        "multiplicity_window_start_centered_carry"
                    ]
                ),
                "backward_multiplicity_window_end_centered_carry": (
                    active_upper_run[
                        "multiplicity_window_end_centered_carry"
                    ]
                ),
                "backward_multiplicity_window_excess_incidence_count": (
                    active_upper_run[
                        "multiplicity_window_excess_incidence_count"
                    ]
                ),
                "backward_multiplicity_window_minimum_coefficient": (
                    active_upper_run[
                        "multiplicity_window_minimum_coefficient"
                    ]
                ),
                "backward_multiplicity_window_maximum_coefficient": (
                    active_upper_run[
                        "multiplicity_window_maximum_coefficient"
                    ]
                ),
                "right_run_charge": right_run_charge,
                "terminal_outgoing_branch": terminal_outgoing_branch,
                "terminal_pulse": terminal_pulse,
                "endpoint_packet": endpoint_packet,
                "endpoint_half_threshold": endpoint_half_threshold,
                "endpoint_packet_slack": endpoint_packet_slack,
                "returned_charge": returned_charge,
                "returned_packet": returned_packet,
                "returned_threshold": returned_threshold + 4,
                "returned_packet_slack": returned_packet_slack,
                "nested_charge": nested_charge,
                "base_pullback_coordinate": base_pullback_coordinate,
                "dyadic_staircase": dyadic_staircase,
                "pullback_coordinate": pullback_coordinate,
                "pullback_card_slack": (
                    pullback_coordinate - endpoint_support_card - 2
                ),
                "factor_range": factor_range,
                "two_block_amplification_slack": (
                    two_block_amplification_slack
                ),
                "entire_right_run_before_two_thirds_crossing": (
                    right_run_length_local == 0
                    or 2 * (source_rank + right_run_length_local)
                    < 3 * source_rank
                ),
            }
        )
        active_upper_run = None

    for rank in range(3, max_rank + 1):
        scale = 1 << (2 * rank)
        target = (1 << (2 * rank - 1)) - (1 << rank)
        remainder = target
        bits = bytearray(rank + 1)
        for divisor in range(2, rank):
            coin = scale // ((1 << divisor) - 1)
            if coin <= remainder:
                bits[divisor] = 1
                remainder -= coin

        support = {divisor for divisor in range(2, rank) if bits[divisor]}
        seam_remainders[rank] = remainder
        seam_support_cards[rank] = len(support)
        incoming_branch = "base"
        if previous_support is not None:
            if support == previous_support | {rank - 1}:
                incoming_branch = "right"
            elif support == previous_support:
                incoming_branch = "middle"
            else:
                incoming_branch = "upper"
            branch_counts[incoming_branch] += 1
            if incoming_branch == "right":
                right_run_length += 1
            else:
                last_nonright_branch = incoming_branch
                right_run_length = 0

            if active_upper_run is not None:
                if incoming_branch == "right":
                    active_upper_run["right_run_length"] += 1
                else:
                    finish_upper_run(rank - 1, incoming_branch)

            if incoming_branch == "upper":
                source_rank = rank - 1
                largest_false = max(
                    divisor for divisor in range(2, source_rank)
                    if divisor not in previous_support
                )
                backward_length = source_rank - largest_false
                reset_charge = (1 << (source_rank + 1)) - remainder
                backward_charge = (
                    (4 ** backward_length)
                    * seam_remainders[largest_false + 1]
                    + reset_charge
                    - (1 << (source_rank + 2))
                    - (4 ** backward_length)
                    * ((1 << (largest_false + 1)) + 4)
                )
                if backward_charge < 0:
                    raise AssertionError("negative fixed-support charge")
                fixed_support = {
                    divisor for divisor in previous_support
                    if divisor < largest_false
                } | {largest_false}
                multiplicity_profile = fixed_support_window_profile(
                    fixed_support,
                    2 * (largest_false + 1),
                    2 * backward_length,
                    spf,
                )
                if multiplicity_profile["numerator"] != backward_charge:
                    raise AssertionError(
                        "base-four fixed-support charge is not its paired "
                        "binary multiplicity-window numerator"
                    )
                active_upper_run = {
                    "source_rank": source_rank,
                    "largest_false": largest_false,
                    "reset_support": tuple(sorted(support)),
                    "right_run_length": 0,
                    "reset_charge": reset_charge,
                    "backward_charge": backward_charge,
                    "multiplicity_window_baseline": int(
                        multiplicity_profile["baseline_numerator"]
                    ),
                    "multiplicity_window_centered_excess": int(
                        multiplicity_profile["centered_excess_numerator"]
                    ),
                    "multiplicity_window_hole_count": int(
                        multiplicity_profile["hole_count"]
                    ),
                    "multiplicity_window_hole_numerator": int(
                        multiplicity_profile["hole_numerator"]
                    ),
                    "multiplicity_window_positive_excess_numerator": int(
                        multiplicity_profile["positive_excess_numerator"]
                    ),
                    "multiplicity_window_start_centered_carry": int(
                        multiplicity_profile["start_centered_carry"]
                    ),
                    "multiplicity_window_end_centered_carry": int(
                        multiplicity_profile["end_centered_carry"]
                    ),
                    "multiplicity_window_excess_incidence_count": int(
                        multiplicity_profile["excess_incidence_count"]
                    ),
                    "multiplicity_window_minimum_coefficient": int(
                        multiplicity_profile["minimum_coefficient"]
                    ),
                    "multiplicity_window_maximum_coefficient": int(
                        multiplicity_profile["maximum_coefficient"]
                    ),
                }
        incoming_branches[rank] = incoming_branch
        previous_support = support

        if remainder == 0:
            continue
        seam_take_count += 1
        support_card = len(support)
        card_bound_slack = remainder - support_card - 2
        if last_nonright_branch == "upper" and right_run_length:
            maximum_upper_right_run_length = max(
                maximum_upper_right_run_length, right_run_length
            )
            modulus = 4 ** right_run_length
            residue = remainder % modulus
            if modulus > support_card + 1:
                congruence_clearance = residue - support_card - 1
                congruence_candidate = (
                    congruence_clearance,
                    rank,
                    right_run_length,
                    residue,
                    support_card,
                )
                if (
                    minimum_upper_right_congruence_clearance is None
                    or congruence_candidate
                    < minimum_upper_right_congruence_clearance
                ):
                    minimum_upper_right_congruence_clearance = (
                        congruence_candidate
                    )
                if residue <= support_card + 1:
                    upper_right_congruence_dangers.append(
                        {
                            "rank": rank,
                            "right_run_length": right_run_length,
                            "modulus": modulus,
                            "residue": residue,
                            "seam_support_card": support_card,
                        }
                    )
        if card_bound_slack < 0:
            card_bound_failures.append(
                {
                    "rank": rank,
                    "seam_remainder": remainder,
                    "seam_support_card": support_card,
                    "card_bound_slack": card_bound_slack,
                }
            )
        if rank >= 8:
            card_candidate = (
                card_bound_slack,
                rank,
                remainder,
                support_card,
            )
            if (
                minimum_card_bound_slack_from_rank_eight is None
                or card_candidate < minimum_card_bound_slack_from_rank_eight
            ):
                minimum_card_bound_slack_from_rank_eight = card_candidate
                record_card_bound_slacks_from_rank_eight.append(
                    {
                        "rank": rank,
                        "incoming_branch": incoming_branch,
                        "seam_remainder": remainder,
                        "seam_support_card": support_card,
                        "card_bound_slack": card_bound_slack,
                    }
                )
            old_branch_candidate = minimum_card_bound_slack_by_branch.get(
                incoming_branch
            )
            if (
                old_branch_candidate is None
                or card_candidate < old_branch_candidate
            ):
                minimum_card_bound_slack_by_branch[incoming_branch] = (
                    card_candidate
                )
        seam_candidate = (remainder, rank)
        if (
            minimum_positive_seam_remainder is None
            or seam_candidate < minimum_positive_seam_remainder
        ):
            minimum_positive_seam_remainder = seam_candidate

        lookahead = minimal_sqrt_tail_lookahead(2 * rank)
        numerator = candidate_finite_window_numerator(
            bits, rank, lookahead, spf
        )
        if remainder == 1:
            zero_candidate_residuals.append(
                {
                    "rank": rank,
                    "seam_remainder": remainder,
                    "lookahead": lookahead,
                    "finite_window_numerator": numerator,
                }
            )
            continue

        certificate_surplus = numerator - (
            (remainder - 2) << lookahead
        )
        surplus_candidate = (
            certificate_surplus,
            rank,
            remainder,
            lookahead,
            numerator,
        )
        if (
            maximum_certificate_surplus is None
            or surplus_candidate > maximum_certificate_surplus
        ):
            maximum_certificate_surplus = surplus_candidate
        if certificate_surplus > 0:
            positive_certificate_events.append(
                {
                    "rank": rank,
                    "seam_remainder": remainder,
                    "candidate_residual": remainder - 1,
                    "lookahead": lookahead,
                    "finite_window_numerator": numerator,
                    "certificate_surplus": certificate_surplus,
                }
            )

    assert minimum_positive_seam_remainder is not None
    assert maximum_certificate_surplus is not None
    assert minimum_card_bound_slack_from_rank_eight is not None
    completed_pullbacks = sorted(
        upper_pullback_events,
        key=lambda event: (
            int(event["pullback_coordinate"]),
            int(event["source_rank"]),
        ),
    )
    pullback_card_failures = [
        event for event in upper_pullback_events
        if int(event["pullback_card_slack"]) < 0
    ]
    late_pullbacks = [
        event for event in upper_pullback_events
        if bool(event["is_late_largest_false"])
    ]
    late_pullback_card_failures = [
        event for event in late_pullbacks
        if int(event["pullback_card_slack"]) < 0
    ]
    minimum_late_pullback_card_slack = min(
        late_pullbacks,
        key=lambda event: (
            int(event["pullback_card_slack"]),
            int(event["source_rank"]),
        ),
        default=None,
    )
    crossing_failures = [
        event for event in upper_pullback_events
        if not bool(event["entire_right_run_before_two_thirds_crossing"])
    ]
    applicable_two_block_amplifications = [
        event for event in late_pullbacks
        if bool(event["factor_range"])
        and int(event["pullback_card_slack"]) >= 0
    ]
    two_block_amplification_failures = [
        event for event in applicable_two_block_amplifications
        if int(event["two_block_amplification_slack"]) < 0
    ]
    minimum_two_block_amplification_slack = min(
        applicable_two_block_amplifications,
        key=lambda event: (
            int(event["two_block_amplification_slack"]),
            int(event["source_rank"]),
        ),
        default=None,
    )
    terminal_middle_events = [
        event for event in upper_pullback_events
        if event["terminal_outgoing_branch"] == "middle"
    ]
    terminal_not_middle_events = [
        event for event in upper_pullback_events
        if event["terminal_outgoing_branch"] != "middle"
    ]
    endpoint_packet_failures = [
        event for event in terminal_middle_events
        if int(event["endpoint_packet_slack"]) < 0
    ]
    minimum_endpoint_packet_slack = min(
        terminal_middle_events,
        key=lambda event: (
            int(event["endpoint_packet_slack"]),
            int(event["source_rank"]),
        ),
        default=None,
    )
    minimum_returned_packet_slack = min(
        terminal_middle_events,
        key=lambda event: (
            int(event["returned_packet_slack"]),
            int(event["source_rank"]),
        ),
        default=None,
    )
    multiplicity_positive_centered_events = [
        event for event in upper_pullback_events
        if int(event["backward_multiplicity_window_centered_excess"]) > 0
    ]
    multiplicity_zero_centered_events = [
        event for event in upper_pullback_events
        if int(event["backward_multiplicity_window_centered_excess"]) == 0
    ]
    multiplicity_negative_centered_events = [
        event for event in upper_pullback_events
        if int(event["backward_multiplicity_window_centered_excess"]) < 0
    ]
    multiplicity_zero_hole_events = [
        event for event in upper_pullback_events
        if int(event["backward_multiplicity_window_hole_count"]) == 0
    ]
    minimum_multiplicity_centered_event = min(
        upper_pullback_events,
        key=lambda event: (
            int(event["backward_multiplicity_window_centered_excess"]),
            int(event["source_rank"]),
        ),
        default=None,
    )
    maximum_multiplicity_centered_event = max(
        upper_pullback_events,
        key=lambda event: (
            int(event["backward_multiplicity_window_centered_excess"]),
            -int(event["source_rank"]),
        ),
        default=None,
    )
    maximum_unit_reset_lattice_depth = max(
        unit_reset_lattice_events,
        key=lambda event: (
            int(event["congruence_depth"]),
            -int(event["endpoint_rank"]),
        ),
        default=None,
    )
    minimum_unit_reset_lattice_distance = min(
        unit_reset_lattice_events,
        key=lambda event: (
            int(event["lattice_distance"]),
            int(event["endpoint_rank"]),
        ),
        default=None,
    )
    full_unit_reset_lattice_hits = [
        event for event in unit_reset_lattice_events
        if int(event["carry_residue"]) == 0
    ]
    pulse_one_unit_reset_lattice_hits = [
        event for event in full_unit_reset_lattice_hits
        if int(event["terminal_pulse"]) == 1
    ]
    fatal_phase_unit_reset_lattice_hits = [
        event for event in pulse_one_unit_reset_lattice_hits
        if int(event["endpoint_rank"]) % 3 == 0
    ]
    maximum_full_unit_reset_lattice_hit = max(
        full_unit_reset_lattice_hits,
        key=lambda event: (
            int(event["right_run_length"]),
            -int(event["endpoint_rank"]),
        ),
        default=None,
    )
    result: dict[str, Any] = {
        "schema": "erdos257_forced_seam_second_shell_audit_v0",
        "ranks_checked": [3, max_rank],
        "positive_seam_remainder_count": seam_take_count,
        "minimum_positive_seam_remainder": {
            "value": minimum_positive_seam_remainder[0],
            "rank": minimum_positive_seam_remainder[1],
        },
        "zero_candidate_residual_count": len(zero_candidate_residuals),
        "first_zero_candidate_residuals": zero_candidate_residuals[:8],
        "card_bound_failure_count": len(card_bound_failures),
        "first_card_bound_failures": card_bound_failures[:8],
        "minimum_card_bound_slack_from_rank_8": {
            "value": minimum_card_bound_slack_from_rank_eight[0],
            "rank": minimum_card_bound_slack_from_rank_eight[1],
            "seam_remainder": minimum_card_bound_slack_from_rank_eight[2],
            "seam_support_card": minimum_card_bound_slack_from_rank_eight[3],
            "meaning": "E-card-2; nonnegative lets the exact floor-error theorem rule out a real skip",
        },
        "incoming_branch_counts": branch_counts,
        "minimum_card_bound_slack_by_incoming_branch_from_rank_8": {
            branch: {
                "value": candidate[0],
                "rank": candidate[1],
                "seam_remainder": candidate[2],
                "seam_support_card": candidate[3],
            }
            for branch, candidate in sorted(
                minimum_card_bound_slack_by_branch.items()
            )
        },
        "record_card_bound_slacks_from_rank_8": (
            record_card_bound_slacks_from_rank_eight
        ),
        "maximum_upper_right_run_length": maximum_upper_right_run_length,
        "unit_reset_lattice_event_count": len(unit_reset_lattice_events),
        "maximum_unit_reset_lattice_depth": maximum_unit_reset_lattice_depth,
        "minimum_unit_reset_lattice_distance": (
            minimum_unit_reset_lattice_distance
        ),
        "full_unit_reset_lattice_hit_count": len(
            full_unit_reset_lattice_hits
        ),
        "maximum_full_unit_reset_lattice_hit": (
            maximum_full_unit_reset_lattice_hit
        ),
        "pulse_one_unit_reset_lattice_hit_count": len(
            pulse_one_unit_reset_lattice_hits
        ),
        "first_pulse_one_unit_reset_lattice_hits": (
            pulse_one_unit_reset_lattice_hits[:8]
        ),
        "fatal_phase_unit_reset_lattice_hit_count": len(
            fatal_phase_unit_reset_lattice_hits
        ),
        "first_fatal_phase_unit_reset_lattice_hits": (
            fatal_phase_unit_reset_lattice_hits[:8]
        ),
        "unit_reset_lattice_meaning": (
            "For every upper/right block wholly before the two-thirds "
            "crossing, F is the exact frozen reset-support multiplicity "
            "window numerator and c_end its centered Mobius carry. The "
            "identity (3F-1)+(3c_end+4)=0 mod 4^k is asserted. A unit "
            "endpoint would force both residues to zero; congruence_depth "
            "is the 4-adic depth already matched by the actual block."
        ),
        "upper_right_congruence_danger_count": len(
            upper_right_congruence_dangers
        ),
        "first_upper_right_congruence_dangers": (
            upper_right_congruence_dangers[:8]
        ),
        "minimum_upper_right_congruence_clearance": (
            None
            if minimum_upper_right_congruence_clearance is None
            else {
                "value": minimum_upper_right_congruence_clearance[0],
                "rank": minimum_upper_right_congruence_clearance[1],
                "right_run_length": (
                    minimum_upper_right_congruence_clearance[2]
                ),
                "residue": minimum_upper_right_congruence_clearance[3],
                "seam_support_card": (
                    minimum_upper_right_congruence_clearance[4]
                ),
                "meaning": (
                    "(E mod 4^k)-card-1 on upper-then-right runs where "
                    "4^k>card+1; positivity rules out a card-small endpoint "
                    "using the exact cylinder congruence"
                ),
            }
        ),
        "completed_upper_critical_pullback_count": len(
            upper_pullback_events
        ),
        "minimum_upper_critical_pullback_coordinates": completed_pullbacks[:8],
        "upper_critical_pullback_card_failure_count": len(
            pullback_card_failures
        ),
        "first_upper_critical_pullback_card_failures": (
            pullback_card_failures[:8]
        ),
        "completed_late_upper_critical_pullback_count": len(late_pullbacks),
        "late_upper_critical_pullback_card_failure_count": len(
            late_pullback_card_failures
        ),
        "first_late_upper_critical_pullback_card_failures": (
            late_pullback_card_failures[:8]
        ),
        "minimum_late_upper_critical_pullback_card_slack": (
            None
            if minimum_late_pullback_card_slack is None
            else minimum_late_pullback_card_slack
        ),
        "upper_predecessor_not_middle_failure_count_from_rank_13": len(
            upper_predecessor_branch_failures
        ),
        "first_upper_predecessor_not_middle_failures_from_rank_13": (
            upper_predecessor_branch_failures[:8]
        ),
        "late_upper_parent_missing_count": len(
            late_upper_parent_missing_events
        ),
        "first_late_upper_parent_missing_events": (
            late_upper_parent_missing_events[:8]
        ),
        "late_upper_pullback_strict_growth_failure_count": len(
            late_upper_pullback_growth_failures
        ),
        "first_late_upper_pullback_strict_growth_failures": (
            late_upper_pullback_growth_failures[:8]
        ),
        "upper_right_two_thirds_crossing_failure_count": len(
            crossing_failures
        ),
        "first_upper_right_two_thirds_crossing_failures": (
            crossing_failures[:8]
        ),
        "applicable_two_block_amplification_count": len(
            applicable_two_block_amplifications
        ),
        "two_block_amplification_failure_count": len(
            two_block_amplification_failures
        ),
        "first_two_block_amplification_failures": (
            two_block_amplification_failures[:8]
        ),
        "minimum_two_block_amplification_slack": (
            None
            if minimum_two_block_amplification_slack is None
            else minimum_two_block_amplification_slack
        ),
        "terminal_middle_packet_event_count": len(terminal_middle_events),
        "terminal_not_middle_event_count": len(terminal_not_middle_events),
        "first_terminal_not_middle_events": terminal_not_middle_events[:8],
        "endpoint_packet_failure_count": len(endpoint_packet_failures),
        "first_endpoint_packet_failures": endpoint_packet_failures[:8],
        "minimum_endpoint_packet_slack": minimum_endpoint_packet_slack,
        "minimum_returned_packet_slack": minimum_returned_packet_slack,
        "backward_multiplicity_window_identity_count": len(
            upper_pullback_events
        ),
        "backward_multiplicity_window_positive_centered_count": len(
            multiplicity_positive_centered_events
        ),
        "backward_multiplicity_window_zero_centered_count": len(
            multiplicity_zero_centered_events
        ),
        "backward_multiplicity_window_negative_centered_count": len(
            multiplicity_negative_centered_events
        ),
        "backward_multiplicity_window_zero_hole_count": len(
            multiplicity_zero_hole_events
        ),
        "minimum_backward_multiplicity_centered_event": (
            minimum_multiplicity_centered_event
        ),
        "maximum_backward_multiplicity_centered_event": (
            maximum_multiplicity_centered_event
        ),
        "backward_multiplicity_window_meaning": (
            "The fixed-support base-four pullback charge equals the "
            "2*(s-d)-row binary divisor-multiplicity window numerator. "
            "After subtracting the all-ones baseline, the window splits "
            "exactly as positive excess incidence minus hole correction "
            "and telescopes to 4^(s-d)*e_start-e_end for the centered "
            "Mobius carry. Sign variation is reported because the rational "
            "full-support lattice theorem cannot be transferred by simply "
            "discarding the finite seam holes."
        ),
        "terminal_middle_packet_meaning": (
            "For a terminal middle reset, the exact next-landing identity is "
            "P_next=4*P_endpoint+2^(endpoint+1)+4. Therefore its strict "
            "packet slack is exactly four times the endpoint strict slack "
            "plus three. This is the computation-side mirror of Lean theorem "
            "terminalMiddle_endpointPacket_lt_half_iff_nextLandingPacket_lt."
        ),
        "two_block_amplification_meaning": (
            "For every late pullback in the exact factor range with "
            "Q>=endpoint_card+2, this audits 9*R - "
            "(4^(s-d+k)*Q + 2*4^k*Q + 6*critical_gap). "
            "Nonnegativity is the exact conclusion of Lean theorem "
            "lateUpperReset_twoBlock_amplification_of_pullbackCoordinate."
        ),
        "upper_critical_pullback_meaning": (
            "For an upper reset s with largest false d and terminal right "
            "length k, (critical_gap + backward_fixed_support_charge) / "
            "4^(s-d) is an exact earlier-row coordinate Q, and the terminal "
            "remainder plus the nested ordered charge is 4^(k+s-d) Q. "
            "The audit tests whether Q itself already clears card+2."
        ),
        "late_upper_critical_pullback_meaning": (
            "This is the exact premise consumed by Lean theorem "
            "lateUpperReset_endpointRemainder_ge_card_add_two_of_"
            "pullbackCoordinate. Only events satisfying 2*s<3*d are "
            "included; nonlate base failures are reported separately by "
            "upper_critical_pullback_card_failure_count."
        ),
        "positive_finite_certificate_count": len(positive_certificate_events),
        "first_positive_finite_certificates": positive_certificate_events[:8],
        "maximum_finite_certificate_surplus": {
            "value": maximum_certificate_surplus[0],
            "rank": maximum_certificate_surplus[1],
            "seam_remainder": maximum_certificate_surplus[2],
            "lookahead": maximum_certificate_surplus[3],
            "finite_window_numerator": maximum_certificate_surplus[4],
            "meaning": "N_L-(E-2)2^L; a first positive-residual mismatch requires positivity",
        },
        "claim_ceiling": (
            "finite forced-word discriminator only; it does not prove the "
            "all-rank seam inequality"
        ),
    }
    if include_pullback_events:
        result["upper_pullback_events"] = upper_pullback_events
    return result


def audit(max_rank: int, slack_bits: int, direct_check_through: int) -> dict[str, Any]:
    if max_rank < 2:
        raise ValueError("--max-rank must be at least 2")
    if slack_bits < 32:
        raise ValueError("--slack-bits must be at least 32")

    bits = certified_half_bits(max_rank, slack_bits)
    # The square-root tail certificate needs only logarithmic look-ahead.
    # The explicit additive allowance is deliberately generous and checked
    # at every use below.
    spf = smallest_prime_factors(
        2 * max_rank + max_rank.bit_length() + 16
    )

    # Replay the certified real residual beside the quotient recurrence.  At
    # rank m, ``real_lower/scale <= r_(m-1) <= real_upper/scale`` before the
    # m-th decision.  Since ``scale`` is divisible by 4^m, this gives a
    # rigorous dyadic enclosure for the candidate fractional phase
    #
    #   Phi_m = pre_m - 4^m r_(m-1) + 1/(2^m-1).
    #
    # If ``J_m = pre_m-(2^m+1)``, real greedy takes exactly when
    # ``J_m >= Phi_m``.  Quotient greedy takes when ``J_m >= 0``.  Hence the
    # first possible quotient-take/real-skip mismatch is the exact band
    # ``0 <= J_m < Phi_m``.
    precision = 2 * max_rank + slack_bits
    scale = 1 << precision
    real_lower = scale // 2
    real_upper = real_lower

    # At d=1 the selected support is empty and the endpoint-2 target is 2.
    residual = 2
    mismatch_events: list[dict[str, int]] = []
    dangerous_take_events: list[dict[str, int]] = []
    direct_failures: list[dict[str, int]] = []
    minimum_take_square_clearance: tuple[int, int, int] | None = None
    minimum_late_take_square_clearance: tuple[int, int, int] | None = None
    minimum_skip_coin_gap: tuple[int, int, int] | None = None
    minimum_late_skip_coin_gap: tuple[int, int, int] | None = None
    minimum_post_take_residual: tuple[int, int] | None = None
    maximum_candidate_phase_ceiling: tuple[int, int] | None = None
    maximum_take_candidate_phase_ceiling: tuple[int, int] | None = None
    maximum_skip_candidate_phase_ceiling: tuple[int, int] | None = None
    minimum_take_phase_clearance: tuple[int, int, int] | None = None
    minimum_late_take_phase_clearance: tuple[int, int, int] | None = None
    phase_decision_failures: list[dict[str, int]] = []
    backward_residue_dangers: list[dict[str, int]] = []
    positive_finite_certificate_events: list[dict[str, int]] = []
    zero_residual_quotient_takes: list[dict[str, int]] = []
    maximum_finite_lookahead: tuple[int, int] | None = None
    maximum_take_certificate_surplus: tuple[int, int, int, int] | None = None
    maximum_late_take_certificate_surplus: tuple[int, int, int, int] | None = None
    take_count = 0
    skip_count = 0

    for d in range(1, max_rank):
        next_rank = d + 1
        g1 = selected_divisor_pulse(2 * d + 1, d, bits, spf)
        g2 = selected_divisor_pulse(2 * d + 2, d, bits, spf)
        pre_midpoint_residual = 4 * residual - 2 * g1 - g2
        midpoint_coin = (1 << next_rank) + 1
        quotient_margin = pre_midpoint_residual - midpoint_coin
        quotient_take = midpoint_coin <= pre_midpoint_residual
        real_take = bool(bits[next_rank])

        finite_lookahead = minimal_sqrt_tail_lookahead(2 * next_rank)
        if 2 * next_rank + finite_lookahead >= len(spf):
            raise AssertionError("smallest-prime-factor table is too short")
        finite_window_numerator = candidate_finite_window_numerator(
            bits, next_rank, finite_lookahead, spf
        )
        lookahead_candidate = (finite_lookahead, next_rank)
        if (
            maximum_finite_lookahead is None
            or lookahead_candidate > maximum_finite_lookahead
        ):
            maximum_finite_lookahead = lookahead_candidate
        if quotient_take:
            if quotient_margin == 0:
                zero_residual_quotient_takes.append(
                    {
                        "rank": next_rank,
                        "lookahead": finite_lookahead,
                        "finite_window_numerator": finite_window_numerator,
                    }
                )
            else:
                certificate_surplus = finite_window_numerator - (
                    (quotient_margin - 1) << finite_lookahead
                )
                surplus_candidate = (
                    certificate_surplus,
                    next_rank,
                    quotient_margin,
                    finite_window_numerator,
                )
                if (
                    maximum_take_certificate_surplus is None
                    or surplus_candidate > maximum_take_certificate_surplus
                ):
                    maximum_take_certificate_surplus = surplus_candidate
                if next_rank >= 8 and (
                    maximum_late_take_certificate_surplus is None
                    or surplus_candidate > maximum_late_take_certificate_surplus
                ):
                    maximum_late_take_certificate_surplus = surplus_candidate
                if certificate_surplus > 0:
                    positive_finite_certificate_events.append(
                        {
                            "rank": next_rank,
                            "residual": quotient_margin,
                            "lookahead": finite_lookahead,
                            "finite_window_numerator": finite_window_numerator,
                            "certificate_surplus": certificate_surplus,
                            "real_bit": int(real_take),
                        }
                    )

        phase_scale = 1 << (precision - 2 * next_rank)
        phase_denominator = (1 << next_rank) - 1
        phase_fraction_floor = phase_scale // phase_denominator
        phase_fraction_ceil = ceil_div(phase_scale, phase_denominator)
        candidate_phase_lower = (
            pre_midpoint_residual * phase_scale
            - real_upper
            + phase_fraction_floor
        )
        candidate_phase_upper = (
            pre_midpoint_residual * phase_scale
            - real_lower
            + phase_fraction_ceil
        )
        phase_ceiling = ceil_div(candidate_phase_upper, phase_scale)
        phase_candidate = (phase_ceiling, next_rank)
        if (
            maximum_candidate_phase_ceiling is None
            or phase_candidate > maximum_candidate_phase_ceiling
        ):
            maximum_candidate_phase_ceiling = phase_candidate
        if real_take:
            if (
                maximum_take_candidate_phase_ceiling is None
                or phase_candidate > maximum_take_candidate_phase_ceiling
            ):
                maximum_take_candidate_phase_ceiling = phase_candidate
        elif (
            maximum_skip_candidate_phase_ceiling is None
            or phase_candidate > maximum_skip_candidate_phase_ceiling
        ):
            maximum_skip_candidate_phase_ceiling = phase_candidate

        analytic_phase_bound = 2 * math.isqrt(2 * next_rank) + 6
        backward_modulus = 1
        backward_lookback = 0
        while backward_modulus <= analytic_phase_bound:
            backward_modulus *= 4
            backward_lookback += 1
        backward_residue = quotient_margin % backward_modulus
        if backward_residue * phase_scale < candidate_phase_upper:
            backward_residue_dangers.append(
                {
                    "rank": next_rank,
                    "residue": backward_residue,
                    "modulus": backward_modulus,
                    "lookback": backward_lookback,
                    "candidate_phase_ceiling": phase_ceiling,
                    "quotient_margin": quotient_margin,
                    "real_bit": int(real_take),
                }
            )

        if real_take:
            # A positive value certifies J_m-Phi_m by an integer margin.
            clearance = quotient_margin - phase_ceiling
            clearance_candidate = (clearance, next_rank, quotient_margin)
            if (
                minimum_take_phase_clearance is None
                or clearance_candidate < minimum_take_phase_clearance
            ):
                minimum_take_phase_clearance = clearance_candidate
            if next_rank >= 8 and (
                minimum_late_take_phase_clearance is None
                or clearance_candidate < minimum_late_take_phase_clearance
            ):
                minimum_late_take_phase_clearance = clearance_candidate
            if quotient_margin * phase_scale < candidate_phase_lower:
                phase_decision_failures.append(
                    {
                        "rank": next_rank,
                        "real_bit": 1,
                        "quotient_margin": quotient_margin,
                        "candidate_phase_ceiling": phase_ceiling,
                    }
                )
        elif quotient_margin * phase_scale >= candidate_phase_upper:
            phase_decision_failures.append(
                {
                    "rank": next_rank,
                    "real_bit": 0,
                    "quotient_margin": quotient_margin,
                    "candidate_phase_ceiling": phase_ceiling,
                }
            )

        if quotient_take != real_take:
            mismatch_events.append(
                {
                    "rank": next_rank,
                    "pre_midpoint_residual": pre_midpoint_residual,
                    "midpoint_coin": midpoint_coin,
                    "quotient_take": int(quotient_take),
                    "real_take": int(real_take),
                }
            )

        if real_take:
            take_count += 1
            residual = pre_midpoint_residual - midpoint_coin
            if residual < 0:
                raise AssertionError(
                    f"certified real take has negative quotient residual at {next_rank}"
                )
            if in_sqrt_crossing_window(residual, next_rank):
                dangerous_take_events.append(
                    {"rank": next_rank, "post_take_residual": residual}
                )
            square_clearance = (
                -8 * next_rank if residual < 4
                else (residual - 4) ** 2 - 8 * next_rank
            )
            candidate_clearance = (square_clearance, next_rank, residual)
            if (
                minimum_take_square_clearance is None
                or candidate_clearance < minimum_take_square_clearance
            ):
                minimum_take_square_clearance = candidate_clearance
            if next_rank >= 8 and (
                minimum_late_take_square_clearance is None
                or candidate_clearance < minimum_late_take_square_clearance
            ):
                minimum_late_take_square_clearance = candidate_clearance
            candidate_residual = (residual, next_rank)
            if (
                minimum_post_take_residual is None
                or candidate_residual < minimum_post_take_residual
            ):
                minimum_post_take_residual = candidate_residual
            weight_quotient = scale // phase_denominator
            real_lower -= weight_quotient + 1
            real_upper -= weight_quotient
        else:
            skip_count += 1
            residual = pre_midpoint_residual
            candidate_gap = (
                midpoint_coin - pre_midpoint_residual,
                next_rank,
                pre_midpoint_residual,
            )
            if minimum_skip_coin_gap is None or candidate_gap < minimum_skip_coin_gap:
                minimum_skip_coin_gap = candidate_gap
            if next_rank >= 8 and (
                minimum_late_skip_coin_gap is None
                or candidate_gap < minimum_late_skip_coin_gap
            ):
                minimum_late_skip_coin_gap = candidate_gap

        if next_rank <= direct_check_through:
            direct = direct_even_residual(bits, next_rank)
            if direct != residual:
                direct_failures.append(
                    {
                        "rank": next_rank,
                        "recurrence_residual": residual,
                        "direct_residual": direct,
                    }
                )

    assert minimum_take_square_clearance is not None
    assert minimum_late_take_square_clearance is not None
    assert minimum_skip_coin_gap is not None
    assert minimum_late_skip_coin_gap is not None
    assert minimum_post_take_residual is not None
    assert maximum_candidate_phase_ceiling is not None
    assert maximum_take_candidate_phase_ceiling is not None
    assert maximum_skip_candidate_phase_ceiling is not None
    assert minimum_take_phase_clearance is not None
    assert minimum_late_take_phase_clearance is not None
    assert maximum_finite_lookahead is not None
    assert maximum_take_certificate_surplus is not None
    assert maximum_late_take_certificate_surplus is not None
    return {
        "schema": "erdos257_half_midpoint_tail_bridge_lab_v1",
        "ranks_checked": [2, max_rank],
        "rank_count": max_rank - 1,
        "real_take_count": take_count,
        "real_skip_count": skip_count,
        "quotient_real_mismatch_count": len(mismatch_events),
        "first_quotient_real_mismatches": mismatch_events[:8],
        "sqrt_window_take_count": len(dangerous_take_events),
        "first_sqrt_window_takes": dangerous_take_events[:8],
        "minimum_take_square_clearance": {
            "value": minimum_take_square_clearance[0],
            "rank": minimum_take_square_clearance[1],
            "post_take_residual": minimum_take_square_clearance[2],
            "meaning": "(R-4)^2-8d; nonnegative is outside R<2*sqrt(2d)+4",
        },
        "minimum_take_square_clearance_from_rank_8": {
            "value": minimum_late_take_square_clearance[0],
            "rank": minimum_late_take_square_clearance[1],
            "post_take_residual": minimum_late_take_square_clearance[2],
            "meaning": "(R-4)^2-8d; nonnegative is outside R<2*sqrt(2d)+4",
        },
        "minimum_post_take_residual": {
            "value": minimum_post_take_residual[0],
            "rank": minimum_post_take_residual[1],
        },
        "maximum_candidate_phase_ceiling": {
            "value": maximum_candidate_phase_ceiling[0],
            "rank": maximum_candidate_phase_ceiling[1],
            "meaning": "rigorous dyadic upper ceiling for Phi_m",
        },
        "maximum_take_candidate_phase_ceiling": {
            "value": maximum_take_candidate_phase_ceiling[0],
            "rank": maximum_take_candidate_phase_ceiling[1],
        },
        "maximum_skip_candidate_phase_ceiling": {
            "value": maximum_skip_candidate_phase_ceiling[0],
            "rank": maximum_skip_candidate_phase_ceiling[1],
        },
        "minimum_take_phase_clearance": {
            "value": minimum_take_phase_clearance[0],
            "rank": minimum_take_phase_clearance[1],
            "quotient_margin": minimum_take_phase_clearance[2],
            "meaning": "J_m-ceil(Phi_m); nonnegative certifies a real take",
        },
        "minimum_take_phase_clearance_from_rank_8": {
            "value": minimum_late_take_phase_clearance[0],
            "rank": minimum_late_take_phase_clearance[1],
            "quotient_margin": minimum_late_take_phase_clearance[2],
            "meaning": "J_m-ceil(Phi_m) on mature real takes",
        },
        "phase_decision_failure_count": len(phase_decision_failures),
        "first_phase_decision_failures": phase_decision_failures[:8],
        "backward_residue_danger_count": len(backward_residue_dangers),
        "first_backward_residue_dangers": backward_residue_dangers[:8],
        "maximum_sqrt_tail_lookahead": {
            "value": maximum_finite_lookahead[0],
            "rank": maximum_finite_lookahead[1],
            "meaning": "least L with 2*isqrt(2d+L)+3 <= 2^L",
        },
        "positive_finite_certificate_count": len(
            positive_finite_certificate_events
        ),
        "first_positive_finite_certificates": positive_finite_certificate_events[:8],
        "zero_residual_quotient_take_count": len(zero_residual_quotient_takes),
        "first_zero_residual_quotient_takes": zero_residual_quotient_takes[:8],
        "maximum_take_finite_certificate_surplus": {
            "value": maximum_take_certificate_surplus[0],
            "rank": maximum_take_certificate_surplus[1],
            "residual": maximum_take_certificate_surplus[2],
            "finite_window_numerator": maximum_take_certificate_surplus[3],
            "meaning": "N_L-(R-1)2^L; a positive-residual crossing requires this to be positive",
        },
        "maximum_take_finite_certificate_surplus_from_rank_8": {
            "value": maximum_late_take_certificate_surplus[0],
            "rank": maximum_late_take_certificate_surplus[1],
            "residual": maximum_late_take_certificate_surplus[2],
            "finite_window_numerator": maximum_late_take_certificate_surplus[3],
            "meaning": "closest mature quotient take to the necessary finite-window crossing inequality",
        },
        "minimum_skip_coin_gap": {
            "value": minimum_skip_coin_gap[0],
            "rank": minimum_skip_coin_gap[1],
            "pre_midpoint_residual": minimum_skip_coin_gap[2],
        },
        "minimum_skip_coin_gap_from_rank_8": {
            "value": minimum_late_skip_coin_gap[0],
            "rank": minimum_late_skip_coin_gap[1],
            "pre_midpoint_residual": minimum_late_skip_coin_gap[2],
        },
        "direct_check_through": min(direct_check_through, max_rank),
        "direct_recurrence_failure_count": len(direct_failures),
        "first_direct_recurrence_failures": direct_failures[:8],
        "terminal_even_residual_bit_length": residual.bit_length(),
        "terminal_even_residual_sha256": hashlib.sha256(
            residual.to_bytes((residual.bit_length() + 7) // 8, "big")
        ).hexdigest(),
        "real_half_bits_sha256": packed_sha256(bits, max_rank),
        "decision_arithmetic": "exact dyadic enclosure plus exact integer recurrence",
        "claim_ceiling": (
            "finite mechanism probe only; all-depth quotient/real midpoint "
            "agreement remains open"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-rank", type=int, default=5000)
    parser.add_argument("--slack-bits", type=int, default=256)
    parser.add_argument("--direct-check-through", type=int, default=200)
    parser.add_argument("--seam-word-max-rank", type=int, default=0)
    parser.add_argument("--include-pullback-events", action="store_true")
    args = parser.parse_args()
    result = audit(args.max_rank, args.slack_bits, args.direct_check_through)
    if args.seam_word_max_rank:
        result["forced_seam_second_shell"] = audit_forced_seam_words(
            args.seam_word_max_rank,
            include_pullback_events=args.include_pullback_events,
        )
    print(json.dumps(result, indent=2, sort_keys=True))
    if result["quotient_real_mismatch_count"]:
        raise SystemExit("quotient/real midpoint mismatch found")
    if result["direct_recurrence_failure_count"]:
        raise SystemExit("even-endpoint recurrence disagrees with direct evaluation")


if __name__ == "__main__":
    main()
