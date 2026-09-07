#!/usr/bin/env python3
"""Exact receipts for the first fatal cohort in the LCM-lift rewrite grammar."""

from __future__ import annotations

import json
from collections import Counter
from fractions import Fraction
from math import gcd, lcm, log2


def weight(rank: int) -> Fraction:
    return Fraction(1, (1 << rank) - 1)


def cylinder(a: int, b: int) -> Fraction:
    return weight(a) * weight(b)


def canonical_cylinder(a: int, b: int) -> tuple[int, int]:
    return (a, b) if a <= b else (b, a)


def split_children(a: int, b: int) -> list[tuple[int, int]]:
    stop = a + b
    return [canonical_cylinder(stop, b), canonical_cylinder(a, stop)]


def first_collision_receipt() -> dict[str, object]:
    """Process the primitive frontier by increasing stop through its first tie."""
    frontier: Counter[tuple[int, int]] = Counter({(2, 3): 1})
    emitted: list[int] = []
    while True:
        stop = min(a + b for a, b in frontier)
        cohort = [
            (pair, multiplicity)
            for pair, multiplicity in frontier.items()
            if sum(pair) == stop
        ]
        total = sum(multiplicity for _, multiplicity in cohort)
        if total >= 2:
            assert stop == 11
            assert Counter(dict(cohort)) == Counter({(3, 8): 1, (2, 9): 1})
            return {
                "ordinary_atoms_before_first_collision": emitted,
                "first_collision_stop": stop,
                "first_collision_cylinders": ["M(8,3)", "M(2,9)"],
            }
        assert total == 1
        pair = cohort[0][0]
        del frontier[pair]
        emitted.append(stop)
        for child in split_children(*pair):
            frontier[child] += 1


def lift_data(endpoint: int, stop: int) -> tuple[int, int]:
    if not 2 <= endpoint < stop - 1:
        raise ValueError("need 2 <= endpoint < stop-1")
    lifted_rank = lcm(endpoint, stop - 1)
    coefficient = (
        ((1 << lifted_rank) - 1) // ((1 << endpoint) - 1)
        - ((1 << lifted_rank) - 1) // ((1 << (stop - 1)) - 1)
    )
    assert coefficient > 0
    assert coefficient * weight(lifted_rank) == (
        weight(endpoint) - weight(stop - 1)
    )
    assert coefficient * cylinder(stop, lifted_rank) == (
        cylinder(endpoint, stop) - cylinder(stop - 1, stop)
    )
    return lifted_rank, coefficient


def remove_chosen_child(
    children: list[tuple[int, int]], endpoint: int, stop: int
) -> list[tuple[int, int]]:
    chosen = canonical_cylinder(endpoint, stop)
    remaining = children.copy()
    remaining.remove(chosen)
    return remaining


def collision_lift_receipts() -> list[dict[str, object]]:
    parents = [(8, 3), (2, 9)]
    stop = 11
    children = [child for parent in parents for child in split_children(*parent)]
    parent_mass = sum((cylinder(*parent) for parent in parents), Fraction())
    receipts: list[dict[str, object]] = []

    for endpoint in (2, 3, 8, 9):
        lifted_rank, coefficient = lift_data(endpoint, stop)
        remaining = remove_chosen_child(children, endpoint, stop)
        rhs = (
            weight(stop - 1)
            + coefficient * cylinder(stop, lifted_rank)
            + sum((cylinder(*child) for child in remaining), Fraction())
        )
        assert rhs == parent_mass

        lifted_stop = stop + lifted_rank
        digital_height = lifted_stop - log2(coefficient)
        assert stop + endpoint - 1 < digital_height < stop + endpoint + 2

        # With Boolean atoms, one pair rewrite and one ordinary split can
        # consume at most three members of a fixed-stop cohort.
        maximum_boolean_consumption = max(
            2 * pair_rewrites + ordinary_splits
            for pair_rewrites in range(2)
            for ordinary_splits in range(2)
        )
        assert maximum_boolean_consumption == 3
        assert coefficient > maximum_boolean_consumption
        residual_mass = (
            coefficient - maximum_boolean_consumption
        ) * cylinder(stop, lifted_rank)
        assert residual_mass > 0

        receipts.append(
            {
                "endpoint": endpoint,
                "lifted_rank_L": lifted_rank,
                "lifted_cylinder": f"M({stop},{lifted_rank})",
                "lifted_stop": lifted_stop,
                "coefficient_A": coefficient,
                "atom_rank_if_pair_processed": lifted_stop - 1,
                "digital_height": digital_height,
                "maximum_cohort_members_consumable_with_boolean_atoms": (
                    maximum_boolean_consumption
                ),
                "minimum_unresolved_members": (
                    coefficient - maximum_boolean_consumption
                ),
                "minimum_unresolved_mass": str(residual_mass),
            }
        )
    return receipts


def fixed_stop_capacity_receipt(limit: int = 12) -> dict[str, object]:
    feasible: dict[int, list[tuple[int, int]]] = {}
    for cohort_size in range(limit + 1):
        schedules = []
        for pair_rewrites in range(2):
            for ordinary_splits in range(2):
                if 2 * pair_rewrites + ordinary_splits == cohort_size:
                    schedules.append((pair_rewrites, ordinary_splits))
        feasible[cohort_size] = schedules
    assert [size for size, schedules in feasible.items() if schedules] == [0, 1, 2, 3]
    return {
        "equation": "2*x+y=C with Booleanity x<=1 and y<=1",
        "cohort_sizes_admitting_complete_boolean_consumption": [0, 1, 2, 3],
        "first_impossible_cohort_size": 4,
    }


def modified_ordinary_frontier(
    chosen_endpoint: int, limit: int
) -> dict[int, list[tuple[int, int]]]:
    """Ordinary frontier after replacing one child of the first collision."""
    frontier: Counter[tuple[int, int]] = Counter({(2, 3): 1})
    by_stop: dict[int, list[tuple[int, int]]] = {}
    for stop in range(5, 10):
        cohort: list[tuple[int, int]] = []
        for pair, multiplicity in list(frontier.items()):
            if sum(pair) == stop:
                cohort.extend([pair] * multiplicity)
                del frontier[pair]
        by_stop[stop] = cohort
        for pair in cohort:
            for child in split_children(*pair):
                frontier[child] += 1

    parents: list[tuple[int, int]] = []
    for pair, multiplicity in list(frontier.items()):
        if sum(pair) == 11:
            parents.extend([pair] * multiplicity)
            del frontier[pair]
    assert Counter(parents) == Counter({(3, 8): 1, (2, 9): 1})
    children = [child for parent in parents for child in split_children(*parent)]
    children.remove(canonical_cylinder(chosen_endpoint, 11))
    for child in children:
        frontier[child] += 1

    # The lifted cohort starts above every fatal rank audited below except its
    # own stop.  It is kept separate from this independent ordinary frontier.
    for stop in range(10, limit + 1):
        cohort = []
        for pair, multiplicity in list(frontier.items()):
            if sum(pair) == stop:
                cohort.extend([pair] * multiplicity)
                del frontier[pair]
        if cohort:
            by_stop[stop] = cohort
            for pair in cohort:
                for child in split_children(*pair):
                    frontier[child] += 1
    return by_stop


def coordinate_lift_sources(target: int) -> list[tuple[int, int]]:
    """All earlier (stop,endpoint) parameters whose LCM lift has coordinate target."""
    return [
        (stop, endpoint)
        for stop in range(5, target)
        for endpoint in range(2, stop - 1)
        if lcm(endpoint, stop - 1) == target
    ]


def stop_lift_sources(target: int) -> list[tuple[int, int]]:
    """All earlier parameters whose lifted cylinder has first emission target."""
    return [
        (stop, endpoint)
        for stop in range(5, target)
        for endpoint in range(2, stop - 1)
        if stop + lcm(endpoint, stop - 1) == target
    ]


def primitive_emission_count(a: int, b: int, target: int) -> int:
    return sum(
        1
        for p in range(1, target // a + 1)
        for q in range(1, target // b + 1)
        if a * p + b * q == target and gcd(p, q) == 1
    )


def lower_lift_descendant_sources(
    target: int,
) -> list[tuple[int, int, int, int]]:
    """Return (stop,e,L,count) for lower lifts with emissions at target."""
    rows = []
    for stop in range(5, target):
        for endpoint in range(2, stop - 1):
            lifted_rank = lcm(endpoint, stop - 1)
            if stop + lifted_rank >= target:
                continue
            count = primitive_emission_count(stop, lifted_rank, target)
            if count:
                rows.append((stop, endpoint, lifted_rank, count))
    return rows


def adjacent_credit_multiplicity(endpoint: int, rank: int) -> int:
    """Credits M(rank-1,rank) extractable from one M(endpoint,rank) lineage."""
    if (rank - 1) % endpoint == 0:
        quotient = ((1 << (rank - 1)) - 1) // ((1 << endpoint) - 1)
        assert cylinder(endpoint, rank) == quotient * cylinder(rank - 1, rank)
        return quotient
    lifted_rank, coefficient = lift_data(endpoint, rank)
    assert lifted_rank > rank
    assert cylinder(endpoint, rank) == (
        cylinder(rank - 1, rank)
        + coefficient * cylinder(rank, lifted_rank)
    )
    return 1


def direct_credit_capacity(
    parents: list[tuple[int, int]], rank: int
) -> int:
    return sum(
        adjacent_credit_multiplicity(endpoint, rank)
        for parent in parents
        for endpoint in parent
    )


def recursive_carry_receipt() -> dict[str, object]:
    first_coefficients = {
        endpoint: lift_data(endpoint, 11)[1]
        for endpoint in (2, 3, 8, 9)
    }


def ordinary_emissions(
    starts: list[tuple[int, int]], limit: int
) -> dict[int, list[tuple[int, int]]]:
    frontier: Counter[tuple[int, int]] = Counter(
        canonical_cylinder(*pair) for pair in starts
    )
    emissions: dict[int, list[tuple[int, int]]] = {}
    for stop in range(1, limit + 1):
        cohort = []
        for pair, multiplicity in list(frontier.items()):
            if sum(pair) == stop:
                cohort.extend([pair] * multiplicity)
                del frontier[pair]
        if cohort:
            emissions[stop] = cohort
            for pair in cohort:
                for child in split_children(*pair):
                    frontier[child] += 1
    return emissions


def first_binary_block_receipt() -> dict[str, object]:
    a, b = 11, 10
    coefficient = 340
    exponents = [8, 6, 4, 2]
    atom_ranks = [a + b - exponent for exponent in exponents]
    assert atom_ranks == [13, 15, 17, 19]

    remainders = []
    remainder_cutoffs = []
    for exponent, rank in zip(exponents, atom_ranks, strict=True):
        assert (1 << a) + (1 << b) > (1 << exponent) + 1
        remainder = (1 << exponent) * cylinder(a, b) - weight(rank)
        assert remainder > 0
        cutoff = next(test for test in range(rank + 1, 100) if weight(test) <= remainder)
        remainders.append(remainder)
        remainder_cutoffs.append(cutoff)
    assert remainder_cutoffs == [23, 25, 27, 29]

    aggregate_remainder = sum(remainders, Fraction())
    assert aggregate_remainder == (
        coefficient * cylinder(a, b)
        - sum((weight(rank) for rank in atom_ranks), Fraction())
    )
    assert weight(23) <= aggregate_remainder < weight(22)

    collision_children = ordinary_emissions([(11, 3), (8, 11), (11, 9)], 21)
    untouched = ordinary_emissions([(5, 7), (5, 8), (7, 9)], 21)
    ordinary_counts = {
        rank: len(collision_children.get(rank, [])) + len(untouched.get(rank, []))
        for rank in atom_ranks
    }
    assert ordinary_counts == {13: 1, 15: 0, 17: 2, 19: 2}
    total_counts = {rank: 1 + ordinary_counts[rank] for rank in atom_ranks}
    assert total_counts == {13: 2, 15: 1, 17: 3, 19: 3}

    prefix = [5, 7, 8, 9, 10]
    prefix_remainder = Fraction(1, 21) - sum(
        (weight(rank) for rank in prefix), Fraction()
    )
    assert prefix_remainder > weight(11)
    post_block_remainder = prefix_remainder - sum(
        (weight(rank) for rank in atom_ranks), Fraction()
    )
    assert weight(12) < post_block_remainder < weight(11)

    return {
        "cohort": "340*M(11,10)",
        "binary_exponents": exponents,
        "proposed_atom_ranks": atom_ranks,
        "individual_remainder_cutoffs": remainder_cutoffs,
        "aggregate_remainder_cutoff": 23,
        "ordinary_frontier_counts_at_block_ranks": ordinary_counts,
        "combined_counts_before_recut": total_counts,
        "forced_prefix_next_rank": 11,
        "post_block_global_remainder_interval": "w_12 < remainder < w_11",
        "conclusion": (
            "The four block atoms cannot be irrevocable; a successful "
            "whole-cohort grammar must recut them with the ordinary frontier."
        ),
    }

    fatal_ranks = {2: 20, 8: 50, 9: 100}
    direct_deficits = []
    expected = {
        2: (2, 4, 164),
        8: (4, 8, 1_618_509_428),
        9: (6, 12, 606_237_840_924_982_449_405_678),
    }
    for endpoint, rank in fatal_ranks.items():
        frontier = modified_ordinary_frontier(endpoint, rank)
        parents = frontier[rank]
        credits = direct_credit_capacity(parents, rank)
        incoming_atoms = first_coefficients[endpoint] // 2
        atoms_left = incoming_atoms + len(parents) - 2 * credits
        assert (len(parents), credits, atoms_left) == expected[endpoint]
        direct_deficits.append(
            {
                "first_endpoint": endpoint,
                "fatal_atom_rank": rank,
                "incoming_atoms": incoming_atoms,
                "independent_stop_rank_parents": parents,
                "adjacent_credit_capacity": credits,
                "atoms_left_after_all_direct_credits": atoms_left,
                "coordinate_lift_sources": coordinate_lift_sources(rank),
                "stop_lift_sources": stop_lift_sources(rank),
            }
        )

    # Source exclusions used in the note.
    assert coordinate_lift_sources(20) == [(6, 4), (11, 4)]
    assert stop_lift_sources(20) == []
    assert coordinate_lift_sources(50) == [(26, 2), (26, 10)]
    assert stop_lift_sources(50) == [(8, 6)]
    assert coordinate_lift_sources(100) == [
        (26, 4), (26, 20), (51, 4), (51, 20)
    ]
    assert stop_lift_sources(100) == [
        (12, 8), (34, 2), (34, 6), (34, 22)
    ]

    # Endpoint 3: a coordinate-40 pulse and an endpoint-2 divisor pulse fund
    # two layers before the coordinate-38 potential is exhausted.
    frontier3 = modified_ordinary_frontier(3, 40)
    assert frontier3[21] == [(8, 13), (2, 19)]
    lift40, pulse40 = lift_data(8, 21)
    assert (lift40, pulse40) == (40, 4_310_761_728)
    incoming40 = first_coefficients[3] // 2
    needed40 = incoming40 // 2
    assert needed40 == 38_085_522 < pulse40

    assert (2, 37) in frontier3[39]
    pulse39 = adjacent_credit_multiplicity(2, 39)
    assert pulse39 == 91_625_968_981
    incoming39 = needed40 + 1  # splitting M(2,37) emits one local w_39
    needed39 = (incoming39 - 1) // 2
    assert needed39 == 19_042_761 < pulse39

    frontier38 = modified_ordinary_frontier(3, 38)
    assert frontier38[38] == [(9, 29), (5, 33)]
    credits38 = direct_credit_capacity(frontier38[38], 38)
    assert credits38 == 4
    assert coordinate_lift_sources(38) == [(20, 2)]
    assert stop_lift_sources(38) == []
    assert frontier38[20] == [(9, 11)]
    atoms_left38 = needed39 + len(frontier38[38]) - 2 * credits38
    assert atoms_left38 == 19_042_755

    assert coordinate_lift_sources(40) == [(9, 5), (11, 8), (21, 8)]
    assert lower_lift_descendant_sources(40) == [
        (5, 2, 4, 1),
        (6, 2, 10, 1),
        (7, 4, 12, 1),
    ]
    sources38 = lower_lift_descendant_sources(38)
    assert {row[0] for row in sources38 if row[0] < 11} == {5, 6, 8, 10}
    assert (13, 2, 12, 1) in sources38
    assert lift_data(2, 13) == (12, 1364)

    return {
        "direct_first_backward_rank_deficits": direct_deficits,
        "endpoint_3_resonance_chain": {
            "rank_40_incoming_atoms": incoming40,
            "rank_40_credits_needed": needed40,
            "rank_40_lcm_pulse_credits": pulse40,
            "rank_39_atoms_after_carry_and_local_split": incoming39,
            "rank_39_divisor_pulse_credits": pulse39,
            "rank_38_incoming_atoms": needed39,
            "rank_38_parents": frontier38[38],
            "rank_38_credit_capacity": credits38,
            "rank_38_atoms_left": atoms_left38,
            "lower_lift_descendant_sources_at_38": sources38,
        },
        "potential_statement": (
            "Coordinate-r credit can originate only at a stop-r split or an "
            "earlier LCM lift with L=r; later forward rewrites cannot create it."
        ),
    }


def main() -> None:
    first = first_collision_receipt()
    lifts = collision_lift_receipts()
    capacity = fixed_stop_capacity_receipt()
    recursive = recursive_carry_receipt()
    binary_block = first_binary_block_receipt()
    assert min(item["coefficient_A"] for item in lifts) == 340
    print(
        json.dumps(
            {
                "claim": (
                    "No fair schedule using only ordinary cylinder splits and "
                    "pairwise LCM lifts can have both Boolean irrevocable atoms "
                    "and vanishing unresolved cylinder mass from M(2,3)."
                ),
                "first_frontier": first,
                "fixed_stop_capacity": capacity,
                "first_lift_choices": lifts,
                "recursive_adjacent_credit_audit": recursive,
                "first_binary_block_audit": binary_block,
                "boundary": (
                    "This does not exclude a larger rewrite system which can "
                    "close the lower-lift ancestral audit for endpoints 8 and "
                    "9, assemble non-adjacent aggregate credit, or normalize "
                    "whole cohorts without the literal adjacent-credit cascade."
                ),
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
