#!/usr/bin/env python3
"""Exact receipts for the moving negacyclic saturation modulus."""

from __future__ import annotations

import json
from fractions import Fraction
from math import gcd


REDUCED_SOCKET_140 = [
    5, 7, 8, 9, 10, 11, 13, 16, 18, 20, 22, 24, 28, 32, 34, 37, 39,
    42, 45, 46, 47, 49, 50, 51, 53, 54, 57, 58, 59, 60, 61, 67, 71,
    73, 77, 78, 79, 82, 83, 84, 86, 91, 93, 105, 107, 109, 111, 115,
    117, 118, 119, 123, 124, 131, 132, 133, 134, 139, 140,
]


def quotient(depth: int, denominator_rank: int) -> int:
    return (1 << depth) // ((1 << denominator_rank) - 1)


def residue_formula(rank: int, denominator_rank: int) -> int:
    height_count, remainder = divmod(rank, denominator_rank)
    half = sum(
        1 << (rank - index * denominator_rank)
        for index in range(1, height_count + 1)
    )
    residue = ((1 << remainder) - 1) * half
    if 2 * remainder >= denominator_rank:
        residue += 1 << (2 * remainder - denominator_rank)
    return residue


def quotient_receipt(maximum_rank: int = 180) -> int:
    checks = 0
    for rank in range(2, maximum_rank + 1):
        modulus = (1 << rank) + 1
        for denominator_rank in range(2, rank + 1):
            full = quotient(2 * rank, denominator_rank)
            half = quotient(rank, denominator_rank)
            residue = residue_formula(rank, denominator_rank)
            assert 0 <= residue < (1 << rank)
            assert full == modulus * half + residue
            assert (residue == 0) == (rank % denominator_rank == 0)
            checks += 1
    return checks


def target_split(rank: int) -> tuple[int, int, int]:
    assert rank % 3 == 2
    modulus = (1 << rank) + 1
    full_target = (1 << (2 * rank)) // 21
    half_target = (1 << rank) // 21
    if rank % 6 == 2:
        residue = (modulus + 2) // 7
    else:
        residue = (10 * modulus + 6) // 21
    assert full_target - (1 << rank) == modulus * (half_target - 1) + residue
    return modulus, half_target, residue


def reduced_equation_receipt(maximum_rank: int = 17) -> int:
    checks = 0
    for rank in range(2, maximum_rank + 1, 3):
        modulus, half_target, target_residue = target_split(rank)
        terms = list(range(2, rank + 1))
        for mask in range(1 << len(terms)):
            support = [
                denominator_rank
                for index, denominator_rank in enumerate(terms)
                if mask & (1 << index)
            ]
            full_sum = sum(quotient(2 * rank, d) for d in support)
            visible = [d for d in support if rank % d != 0]
            blind = [d for d in support if rank % d == 0]
            visible_residue_sum = sum(residue_formula(rank, d) for d in visible)
            delta = visible_residue_sum - target_residue
            congruent = delta % modulus == 0
            if congruent:
                winding = delta // modulus
                reduced_sum = sum(quotient(rank, d) for d in visible)
                reduced_sum += sum(
                    ((1 << rank) - 1) // ((1 << d) - 1) for d in blind
                )
                assert (full_sum == (1 << (2 * rank)) // 21 - (1 << rank)) == (
                    reduced_sum == half_target - 1 - winding
                )
            checks += 1
    return checks


def blind_kernel_receipt(maximum_rank: int = 300) -> int:
    checks = 0
    for rank in range(3, maximum_rank + 1):
        for denominator_rank in range(3, rank + 1):
            if rank % denominator_rank != 0:
                continue
            assert residue_formula(rank, denominator_rank) == 0
            assert (2 * rank + 1) % denominator_rank != 0
            assert (2 * rank + 2) % denominator_rank != 0
            if denominator_rank > 4:
                assert (2 * rank + 3) % denominator_rank != 0
                assert (2 * rank + 4) % denominator_rank != 0
            checks += 1
    return checks


def half_depth_small_remainder_receipt(maximum_rank: int = 300) -> int:
    checks = 0
    for rank in range(8, maximum_rank + 1, 3):
        target = (1 << rank) // 21
        for denominator_rank in (2, 3, 4):
            assert quotient(rank, denominator_rank) > target
            checks += 1
    return checks


def valuation(number: int, prime: int) -> int:
    exponent = 0
    while number % prime == 0:
        exponent += 1
        number //= prime
    return exponent


def descending_greedy_support(rank: int) -> list[int]:
    remainder = (1 << rank) // 21
    support: list[int] = []
    for denominator_rank in range(5, rank + 1):
        coin = quotient(rank, denominator_rank)
        if coin <= remainder:
            support.append(denominator_rank)
            remainder -= coin
    assert remainder == 0
    return support


def primitive_prime_power_receipt() -> dict[str, object]:
    # The apparent mod-31 kernel for L_5(155t) disappears at the full
    # 31-adic exponent.  The even phase example t=4 has R == 2 mod 6.
    rank = 620
    period = 5
    prime = 31
    mersenne = (1 << rank) - 1
    coin = mersenne // ((1 << period) - 1)
    full_exponent = valuation(mersenne, prime)
    coin_exponent = valuation(coin, prime)
    assert rank % 6 == 2
    assert coin_exponent == valuation(rank // period, prime)
    assert coin_exponent + valuation((1 << period) - 1, prime) == full_exponent
    assert coin % prime == 0
    assert coin % (prime**full_exponent) != 0
    return {
        "rank": rank,
        "period": period,
        "prime": prime,
        "mod_prime_zero": True,
        "coin_valuation": coin_exponent,
        "full_valuation": full_exponent,
        "full_prime_power_nonzero": True,
    }


def reduced_socket_counterexample_receipt() -> dict[str, object]:
    rank = 140
    target = (1 << rank) // 21
    support = REDUCED_SOCKET_140
    assert descending_greedy_support(rank) == support
    assert sum(quotient(rank, d) for d in support) == target
    assert support[-1] == rank
    reduced_support = support[:-1]
    assert quotient(rank, rank) == 1
    assert sum(quotient(rank, d) for d in reduced_support) == target - 1

    pulse = 2 * sum((2 * rank + 1) % d == 0 for d in reduced_support)
    pulse += sum((2 * rank + 2) % d == 0 for d in reduced_support)
    next_pulse = 2 * sum((2 * rank + 3) % d == 0 for d in reduced_support)
    next_pulse += sum((2 * rank + 4) % d == 0 for d in reduced_support)
    assert pulse == 1
    assert next_pulse == 1

    blind = [d for d in reduced_support if rank % d == 0]
    assert blind == [5, 7, 10, 20, 28]

    modulus, _, target_residue = target_split(rank)
    visible_residue_sum = sum(
        residue_formula(rank, d) for d in reduced_support if rank % d != 0
    )
    visible_equation_holds = (visible_residue_sum - target_residue) % modulus == 0
    assert not visible_equation_holds
    return {
        "rank": rank,
        "small_remainder": 1,
        "support_size": len(reduced_support),
        "blind_support": blind,
        "pulse": pulse,
        "next_pulse": next_pulse,
        "all_descended_congruences_hold": True,
        "visible_negacyclic_equation_holds": visible_equation_holds,
    }


def equal_leading_cohort_receipt() -> dict[str, object]:
    # U=6 gives A=9 and N=5.  The listed primes and R are one CRT instance
    # of R == 2 (mod 6), R == -(U-1) (mod d).
    width = 6
    target_prefix = (1 << width) // 7
    seam_distance = width - 1
    denominator_ranks = [11, 13, 17, 19, 23]
    rank = 5_311_730
    assert rank % 6 == 2
    assert len(denominator_ranks) == (target_prefix + 1) // 2
    assert all(rank % d == d - seam_distance for d in denominator_ranks)
    assert all(d > 2 * seam_distance for d in denominator_ranks)

    cutoff = 1 << (rank - width)
    residue_sum = 0
    deficits = []
    for denominator_rank in denominator_ranks:
        remainder = rank % denominator_rank
        half_quotient = quotient(rank, denominator_rank)
        residue = ((1 << remainder) - 1) * half_quotient
        if 2 * remainder >= denominator_rank:
            residue += 1 << (2 * remainder - denominator_rank)
        deficit = (1 << (rank - seam_distance)) - residue
        assert 0 < deficit < (1 << (rank - denominator_rank))
        residue_sum += residue
        deficits.append(deficit)

    assert 0 < sum(deficits) < cutoff
    assert residue_sum // cutoff == target_prefix
    target_residue = ((1 << rank) + 3) // 7
    assert target_residue // cutoff == target_prefix
    pulse_counts = [
        sum((2 * rank + offset) % d == 0 for d in denominator_ranks)
        for offset in range(1, 5)
    ]
    assert pulse_counts == [0, 0, 0, 0]
    return {
        "rank": rank,
        "window_width": width,
        "seam_distance": seam_distance,
        "cohort_size": len(denominator_ranks),
        "target_prefix": target_prefix,
        "residue_sum_prefix": residue_sum // cutoff,
        "endpoint_divisor_counts": pulse_counts,
    }


def single_cohort_lower_carry_receipt() -> dict[str, object]:
    identity_checks = 0
    greedy_checks = 0
    critical_rows = []
    for seam_distance in range(5, 51, 3):
        rank = 5 * seam_distance + 20
        while rank % 6 != 2:
            rank += 1
        common_height = rank + seam_distance
        leading_scale = 1 << (rank - seam_distance)
        mersenne_t = (1 << seam_distance) - 1
        cohort = [
            d
            for d in range(seam_distance + 1, rank + 1)
            if common_height % d == 0
        ]
        for denominator_rank in cohort:
            remainder = rank % denominator_rank
            assert remainder == denominator_rank - seam_distance
            half_quotient = quotient(rank, denominator_rank)
            residue = ((1 << remainder) - 1) * half_quotient
            if 2 * remainder >= denominator_rank:
                residue += 1 << (2 * remainder - denominator_rank)
            deficit = leading_scale - residue
            assert 0 < deficit < (1 << (rank - denominator_rank))
            mersenne_d = (1 << denominator_rank) - 1
            if denominator_rank < 2 * seam_distance:
                correction = (1 << (denominator_rank - seam_distance))
                correction *= (1 << (denominator_rank - seam_distance)) - 1
                expected = leading_scale * mersenne_t + correction
            else:
                expected = mersenne_t * (
                    leading_scale - (1 << (denominator_rank - 2 * seam_distance))
                )
            assert deficit * mersenne_d == expected
            identity_checks += 1

        target = Fraction(3, 7 * mersenne_t)
        remainder_target = target
        support = []
        for denominator_rank in range(seam_distance + 1, 2 * seam_distance):
            weight = Fraction(1, (1 << denominator_rank) - 1)
            if weight <= remainder_target:
                support.append(denominator_rank)
                remainder_target -= weight
            greedy_checks += 1
        critical = [
            2 * seam_distance - 3,
            2 * seam_distance - 2,
            2 * seam_distance - 1,
        ]
        assert all(d in support for d in critical)
        perturbation_bound = Fraction(3, leading_scale)
        perturbation_bound += Fraction(
            rank, leading_scale * (1 << (seam_distance - 1))
        )
        assert perturbation_bound < Fraction(1, 1 << (3 * seam_distance))
        critical_rows.append(
            {
                "seam_distance": seam_distance,
                "rank": rank,
                "critical_offsets": [d - seam_distance for d in critical],
            }
        )
    return {
        "deficit_identity_checks": identity_checks,
        "ideal_greedy_decision_checks": greedy_checks,
        "tested_seam_distances": len(critical_rows),
        "first_critical_row": critical_rows[0],
        "last_critical_row": critical_rows[-1],
        "theorem_boundary": "single equal-t cohorts only; mixed t remains open",
    }


def safe_migration_common_height_receipt() -> dict[str, object]:
    forced_labels = {
        0: [1, 2, 4],
        1: [1, 3, 4],
        2: [1, 2, 3],
    }

    # The compatibility test depends only on j' modulo 6.  Sum the six
    # residue classes starting at j'=5; later representatives have common
    # ratio 2^-6.
    matrix = [[Fraction() for _ in range(6)] for _ in range(6)]
    edge_residue_checks = 0
    for source_phase in range(6):
        for source_label in forced_labels[source_phase % 3]:
            for child_label in range(5, 11):
                child_phase = source_phase - source_label + child_label
                rank_residue = 2 * source_phase - 2 * source_label + child_label
                divisor = gcd(rank_residue, 6)
                compatible = (child_phase + 2) % divisor == 0

                # Compare with the simultaneous-congruence criterion at a
                # positive representative of this source phase.
                source = source_phase + 60
                child = source - source_label + child_label
                rank = 2 * source - 2 * source_label + child_label
                assert compatible == ((child + 2) % gcd(rank, 6) == 0)
                edge_residue_checks += 1

                if compatible:
                    geometric_weight = Fraction(64, 63) * Fraction(
                        1, 1 << (child_label - source_label)
                    )
                    matrix[source_phase][child_phase % 6] += geometric_weight

    expected = [
        [Fraction(1, 21), Fraction(65, 126), Fraction(65, 252),
         Fraction(16, 63), Fraction(4, 21), Fraction(2, 63)],
        [Fraction(2, 63), Fraction(2, 63), Fraction(65, 126),
         Fraction(16, 63), Fraction(43, 168), Fraction(4, 63)],
        [Fraction(8, 63), Fraction(2, 63), Fraction(2, 63),
         Fraction(), Fraction(11, 42), Fraction(8, 63)],
        [Fraction(43, 168), Fraction(4, 63), Fraction(4, 63),
         Fraction(1, 63), Fraction(11, 21), Fraction(1, 252)],
        [Fraction(16, 63), Fraction(8, 63), Fraction(8, 63),
         Fraction(), Fraction(1, 21), Fraction(32, 63)],
        [Fraction(1, 63), Fraction(65, 252), Fraction(16, 63),
         Fraction(8, 63), Fraction(2, 21), Fraction(1, 63)],
    ]
    assert matrix == expected

    phase_weight = [100, 78, 47, 80, 78, 55]
    contraction = Fraction(19, 20)
    weighted_children = [
        sum(matrix[row][column] * phase_weight[column] for column in range(6))
        for row in range(6)
    ]
    slacks = [
        contraction * phase_weight[row] - weighted_children[row]
        for row in range(6)
    ]
    expected_slacks = [
        Fraction(241, 252),
        Fraction(541, 1260),
        Fraction(719, 1260),
        Fraction(31, 252),
        Fraction(743, 630),
        Fraction(37, 252),
    ]
    assert slacks == expected_slacks
    assert all(slack > 0 for slack in slacks)

    # The finite M7 graph is a subgraph of this infinite safe graph, so the
    # same strict contraction rules out every proposed finite recycling
    # multiset, irrespective of how mod-3 populations split by parity.
    return {
        "edge_residue_checks": edge_residue_checks,
        "source_phases": 6,
        "first_safe_label": 5,
        "all_safe_labels_summed": True,
        "phase_weight": phase_weight,
        "contraction": str(contraction),
        "slacks": [str(slack) for slack in slacks],
        "same_rank_conflicts_ignored": (
            "yes: the matrix is an upper bound, so contraction is stronger"
        ),
        "theorem_boundary": (
            "requires a nonduplicating assignment of mixed-cohort target "
            "pivots to valuation-preserving safe descendants"
        ),
    }


def lower_valuation_carry_receipt() -> dict[str, object]:
    rank = 44
    source_cohort = 8
    source_label = 3
    source_rank = 2 * source_cohort - source_label
    safe_pair = [12, 28]
    prefix_support = [8, 9, 12, 17, 21, 25, 28, 35, 37]

    def cohort(denominator_rank: int) -> int:
        remainder = rank % denominator_rank
        assert remainder != 0
        return denominator_rank - remainder

    def deficit(denominator_rank: int) -> int:
        seam_distance = cohort(denominator_rank)
        return (1 << (rank - seam_distance)) - residue_formula(
            rank, denominator_rank
        )

    def endpoint_pulses(denominator_rank: int) -> tuple[int, int]:
        pulse = 2 * ((2 * rank + 1) % denominator_rank == 0)
        pulse += (2 * rank + 2) % denominator_rank == 0
        next_pulse = 2 * ((2 * rank + 3) % denominator_rank == 0)
        next_pulse += (2 * rank + 4) % denominator_rank == 0
        return int(pulse), int(next_pulse)

    source_deficit = deficit(source_rank)
    pair_deficits = [deficit(d) for d in safe_pair]
    assert source_rank == 13
    assert endpoint_pulses(source_rank) == (0, 2)
    assert all(endpoint_pulses(d) == (0, 0) for d in safe_pair)
    assert [valuation(value, 2) for value in pair_deficits] == [4, 4]
    assert valuation(source_deficit, 2) == 5
    assert valuation(sum(pair_deficits), 2) == 5
    assert sum(pair_deficits) % 64 == source_deficit % 64 == 32

    target = ((1 << rank) + 3) // 7
    prefix_modulus = 1 << 17
    residue_sum = sum(residue_formula(rank, d) for d in prefix_support)
    pulse_pair = tuple(
        sum(endpoint_pulses(d)[index] for d in prefix_support)
        for index in range(2)
    )
    assert residue_sum % prefix_modulus == target % prefix_modulus
    assert pulse_pair == (1, 0)
    return {
        "rank": rank,
        "forbidden_source": {
            "cohort": source_cohort,
            "label": source_label,
            "denominator_rank": source_rank,
            "valuation": valuation(source_deficit, 2),
        },
        "safe_pair": safe_pair,
        "safe_pair_valuations": [valuation(value, 2) for value in pair_deficits],
        "carried_valuation": valuation(sum(pair_deficits), 2),
        "matched_low_bits": 6,
        "target_prefix_bits": 17,
        "prefix_support": prefix_support,
        "prefix_pulse_pair": pulse_pair,
        "full_negacyclic_equation_claimed": False,
    }


def deep_carry_impostor_receipt() -> dict[str, object]:
    block_identity_checks = 0
    for rank in range(8, 181):
        for denominator_rank in range(5, rank + 1):
            height_count, remainder = divmod(rank, denominator_rank)
            if remainder == 0:
                continue
            seam_distance = denominator_rank - remainder
            deficit = (1 << (rank - seam_distance)) - residue_formula(
                rank, denominator_rank
            )
            if remainder < seam_distance:
                expected = 1 << remainder
                expected += ((1 << seam_distance) - 1) * sum(
                    1 << (2 * remainder + index * denominator_rank)
                    for index in range(height_count - 1)
                )
                expected_popcount = (height_count - 1) * seam_distance + 1
            else:
                expected = ((1 << seam_distance) - 1) * sum(
                    1 << (
                        remainder
                        - seam_distance
                        + index * denominator_rank
                    )
                    for index in range(height_count)
                )
                expected_popcount = height_count * seam_distance
            assert deficit == expected
            assert deficit.bit_count() == expected_popcount
            block_identity_checks += 1

    family_rows = []
    for seam_distance in range(6, 61, 6):
        rank = 7 * seam_distance - 4
        source_rank = 2 * seam_distance - 1
        provider_ranks = [3 * seam_distance - 1, 6 * seam_distance - 2]
        four_atom_ranks = [
            3 * seam_distance - 1,
            4 * seam_distance - 2,
            5 * seam_distance,
            6 * seam_distance - 2,
        ]

        def cohort(denominator_rank: int) -> int:
            return denominator_rank - rank % denominator_rank

        def deficit(denominator_rank: int) -> int:
            return (1 << (rank - cohort(denominator_rank))) - residue_formula(
                rank, denominator_rank
            )

        source_deficit = deficit(source_rank)
        provider_deficits = [deficit(d) for d in provider_ranks]
        mismatch = sum(provider_deficits) - source_deficit
        assert cohort(source_rank) == seam_distance
        assert [cohort(d) for d in provider_ranks] == [
            2 * seam_distance + 1,
            5 * seam_distance,
        ]
        assert (2 * rank + 1) % source_rank == 0
        assert all(
            all((2 * rank + offset) % d != 0 for offset in range(1, 5))
            for d in provider_ranks
        )
        assert valuation(source_deficit, 2) == seam_distance - 1
        assert [valuation(value, 2) for value in provider_deficits] == [
            seam_distance - 2,
            seam_distance - 2,
        ]
        assert valuation(mismatch, 2) == 2 * seam_distance - 4
        four_atom_mismatch = sum(deficit(d) for d in four_atom_ranks)
        four_atom_mismatch -= source_deficit
        expected_four_atom_mismatch = -(1 << (4 * seam_distance - 2))
        expected_four_atom_mismatch *= (1 << (seam_distance - 1)) - 1
        assert four_atom_mismatch == expected_four_atom_mismatch
        assert all(
            all((2 * rank + offset) % d != 0 for offset in range(1, 5))
            for d in four_atom_ranks
        )
        assert not any(
            valuation(deficit(d), 2) == 4 * seam_distance - 2
            for d in range(5, rank + 1)
            if rank % d != 0
        )
        later_upper_capacity = (1 << (5 * seam_distance - 3)) - 1
        forced_gap_rank = (rank + 1) // 3
        assert 3 * forced_gap_rank == rank + 1
        forced_gap_deficit = deficit(forced_gap_rank)
        forced_gap = (1 << (rank - forced_gap_rank)) - forced_gap_deficit
        assert forced_gap == (1 << (forced_gap_rank - 2)) * (
            (1 << forced_gap_rank) - 1
        )
        assert forced_gap > (1 << (4 * seam_distance - 3))
        upper_minus_source = later_upper_capacity - source_deficit
        assert upper_minus_source == (
            (1 << (4 * seam_distance - 3))
            - (1 << (3 * seam_distance - 2))
            + (1 << (2 * seam_distance - 2))
            - (1 << (seam_distance - 1))
            - 1
        )
        assert upper_minus_source < (1 << (4 * seam_distance - 3))
        actual_later_mass = sum(
            deficit(d)
            for d in range(source_rank + 1, rank + 1)
            if rank % d != 0
        )
        assert actual_later_mass <= later_upper_capacity - forced_gap
        assert actual_later_mass < source_deficit
        family_rows.append(
            {
                "seam_distance": seam_distance,
                "rank": rank,
                "source_rank": source_rank,
                "provider_ranks": provider_ranks,
                "normalized_unit_agreement_bits": seam_distance - 3,
                "four_atom_ranks": four_atom_ranks,
                "four_atom_agreement_valuation": 4 * seam_distance - 2,
                "forward_visible_mass_strictly_below_source": True,
                "forced_gap_rank": forced_gap_rank,
            }
        )

    # At the first family member, a meet-in-the-middle audit proves that no
    # endpoint-safe subset agrees one bit beyond the four-atom recut.
    first = family_rows[0]
    first_rank = int(first["rank"])
    first_seam = int(first["seam_distance"])
    first_source = int(first["source_rank"])

    def first_cohort(denominator_rank: int) -> int:
        return denominator_rank - first_rank % denominator_rank

    def first_deficit(denominator_rank: int) -> int:
        return (
            (1 << (first_rank - first_cohort(denominator_rank)))
            - residue_formula(first_rank, denominator_rank)
        )

    safe_ranks = [
        d
        for d in range(5, first_rank + 1)
        if first_rank % d != 0
        and all((2 * first_rank + offset) % d != 0 for offset in range(1, 5))
    ]
    assert len(safe_ranks) == 22
    modulus = 1 << (4 * first_seam - 1)
    left = safe_ranks[: len(safe_ranks) // 2]
    right = safe_ranks[len(safe_ranks) // 2 :]
    left_residues = {
        sum(
            first_deficit(d)
            for index, d in enumerate(left)
            if mask & (1 << index)
        )
        % modulus
        for mask in range(1 << len(left))
    }
    target_residue = first_deficit(first_source) % modulus
    one_more_bit_solution = False
    for mask in range(1 << len(right)):
        right_residue = sum(
            first_deficit(d)
            for index, d in enumerate(right)
            if mask & (1 << index)
        )
        right_residue %= modulus
        if (target_residue - right_residue) % modulus in left_residues:
            one_more_bit_solution = True
            break
    assert not one_more_bit_solution

    return {
        "block_identity_and_popcount_checks": block_identity_checks,
        "family_rows_checked": len(family_rows),
        "first_family_row": family_rows[0],
        "last_family_row": family_rows[-1],
        "first_row_safe_subset_count": 1 << len(safe_ranks),
        "first_row_maximal_agreement_valuation": 4 * first_seam - 2,
        "fixed_unit_depth_invariant": "excluded by unbounded agreement depth",
    }


def main() -> None:
    even_modulus, even_half, even_residue = target_split(20)
    odd_modulus, odd_half, odd_residue = target_split(23)
    print(
        json.dumps(
            {
                "quotient_identity_checks": quotient_receipt(),
                "reduced_equation_exhaustive_support_checks": reduced_equation_receipt(),
                "blind_kernel_checks": blind_kernel_receipt(),
                "half_depth_large_early_term_checks": half_depth_small_remainder_receipt(),
                "primitive_prime_power_lift": primitive_prime_power_receipt(),
                "reduced_socket_counterexample": reduced_socket_counterexample_receipt(),
                "equal_leading_cohort": equal_leading_cohort_receipt(),
                "single_cohort_lower_carry": single_cohort_lower_carry_receipt(),
                "safe_migration_common_height": safe_migration_common_height_receipt(),
                "lower_valuation_carry": lower_valuation_carry_receipt(),
                "deep_carry_impostor": deep_carry_impostor_receipt(),
                "even_phase_example": {
                    "rank": 20,
                    "modulus": even_modulus,
                    "half_depth_target": even_half,
                    "target_residue": even_residue,
                },
                "odd_phase_example": {
                    "rank": 23,
                    "modulus": odd_modulus,
                    "half_depth_target": odd_half,
                    "target_residue": odd_residue,
                },
                "boundary": (
                    "The moving residue descends exactly to a half-depth "
                    "denominator-21 achievement equation. Full primitive "
                    "prime-power charges encode the divisor terms injectively, "
                    "but do not make the reduced small-remainder and sparse-"
                    "pulse conditions contradictory; the visible folded "
                    "equation remains essential."
                ),
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
