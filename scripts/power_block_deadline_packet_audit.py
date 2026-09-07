#!/usr/bin/env python3
"""Exact deadline-packet receipts for the first M(2,3) LCM lift."""

from __future__ import annotations

import json
from collections import defaultdict
from fractions import Fraction


def weight(rank: int) -> Fraction:
    return Fraction(1, (1 << rank) - 1)


def cylinder(a: int, b: int) -> Fraction:
    return weight(a) * weight(b)


def packet(rank: int, capacity: int) -> Fraction:
    if not 0 <= capacity < rank:
        raise ValueError("need 0 <= capacity < rank")
    return weight(rank - capacity) / (1 << capacity)


def theta(rank: int, capacity: int) -> Fraction:
    return sum(
        (
            Fraction(1, 1 << step)
            * cylinder(rank - step, rank - step + 1)
            for step in range(1, capacity + 1)
        ),
        Fraction(),
    )


def first_affordable(value: Fraction, limit: int = 1000) -> int | None:
    return next((rank for rank in range(1, limit + 1) if weight(rank) <= value), None)


def power_block_receipt(a: int, b: int, exponent: int) -> dict[str, object]:
    if a > b:
        a, b = b, a
    capacity = b - exponent
    rank = a + b - exponent
    deadline = a
    if capacity < 1:
        raise ValueError("the audited packet needs positive capacity")
    block = (1 << exponent) * cylinder(a, b)
    surplus = block - weight(rank)
    kappa = surplus / cylinder(rank - 1, rank)
    bound = Fraction(1 << (capacity - 1), 1) - Fraction(1, 2)
    assert kappa > bound
    assert packet(rank, capacity) == weight(rank) + theta(rank, capacity)
    assert block == packet(rank, capacity) + Fraction(1, 1 << capacity) * cylinder(a, b)
    return {
        "a": a,
        "b": b,
        "exponent": exponent,
        "rank": rank,
        "capacity": capacity,
        "deadline": deadline,
        "kappa": str(kappa),
        "strict_lower_bound": str(bound),
    }


def verify_surplus_bound(maximum: int = 28) -> int:
    checks = 0
    for a in range(2, maximum + 1):
        for b in range(a, maximum + 1):
            for exponent in range(0, b):
                power_block_receipt(a, b, exponent)
                checks += 1
    return checks


def kraft_load(state: dict[int, list[int]]) -> Fraction:
    return sum(
        (Fraction(1, 1 << capacity) for values in state.values() for capacity in values),
        Fraction(),
    )


def normalize_collisions(
    state: dict[int, list[int]], excess: Fraction, log: list[dict[str, object]]
) -> tuple[Fraction, dict[str, int] | None]:
    while True:
        rank = next((item for item in sorted(state) if len(state[item]) >= 2), None)
        if rank is None:
            return excess, None
        capacities = sorted(state[rank])
        first, second = capacities[:2]
        state[rank] = capacities[2:]
        if first == 0:
            return excess, {"rank": rank, "first": first, "second": second}
        excess += packet(rank, second) - packet(rank, first)
        state[rank - 1].append(first - 1)
        log.append(
            {
                "operation": "carry",
                "rank": rank,
                "capacities": [first, second],
                "output": [rank - 1, first - 1],
                "deadline": rank - first,
                "kraft_load": str(kraft_load(state)),
            }
        )


def maximum_packet_capacity(value: Fraction, rank: int) -> int:
    choices = [capacity for capacity in range(1, rank) if packet(rank, capacity) <= value]
    return max(choices) if choices else 0


def first_lift_packet_receipt() -> dict[str, object]:
    prefix = [5, 7, 8, 9, 10]
    frontier_value = Fraction(1, 21) - sum(
        (weight(rank) for rank in prefix), Fraction()
    )

    sources = [
        ("256*M(10,11)", 13, 3),
        ("64*M(10,11)", 15, 5),
        ("16*M(10,11)", 17, 7),
        ("4*M(10,11)", 19, 9),
        ("M(5,7)", 12, 7),
        ("M(5,8)", 13, 8),
        ("M(7,9)", 16, 9),
        ("M(3,11)", 14, 11),
        ("M(8,11)", 19, 11),
        ("M(9,11)", 20, 11),
    ]
    actual_source_value = (
        340 * cylinder(10, 11)
        + cylinder(5, 7)
        + cylinder(5, 8)
        + cylinder(7, 9)
        + cylinder(3, 11)
        + cylinder(8, 11)
        + cylinder(9, 11)
    )
    assert frontier_value == actual_source_value
    state: dict[int, list[int]] = defaultdict(list)
    for _, rank, capacity in sources:
        state[rank].append(capacity)
    excess = frontier_value - sum(
        (packet(rank, capacity) for _, rank, capacity in sources), Fraction()
    )
    assert excess > 0
    initial_load = kraft_load(state)
    assert initial_load == Fraction(371, 2048)

    log: list[dict[str, object]] = []
    excess, overload = normalize_collisions(state, excess, log)
    assert overload is None
    assert [(row["rank"], row["output"]) for row in log[:3]] == [
        (12, [11, 1]),
        (13, [12, 2]),
        (19, [18, 8]),
    ] or [(row["rank"], row["output"]) for row in log[:3]] == [
        (13, [12, 2]),
        (12, [11, 1]),
        (19, [18, 8]),
    ]
    assert state[11] == [1]
    root_load = kraft_load(state)
    assert root_load == Fraction(559, 1024)
    assert first_affordable(excess) == 17
    assert maximum_packet_capacity(excess, 17) == 15

    # Continue only through the first rank at which this deterministic parking
    # rule differs from the exact greedy prefix.
    while True:
        rank = first_affordable(excess)
        assert rank is not None
        if rank > 20:
            break
        capacity = maximum_packet_capacity(excess, rank)
        assert capacity > 0
        excess -= packet(rank, capacity)
        state[rank].append(capacity)
        log.append(
            {
                "operation": "extract",
                "rank": rank,
                "capacity": capacity,
                "deadline": rank - capacity,
                "kraft_load": str(kraft_load(state)),
            }
        )
        excess, overload = normalize_collisions(state, excess, log)
        assert overload is None

    heads_through_20 = sorted(
        rank for rank, capacities in state.items() if rank <= 20 and capacities
    )
    assert heads_through_20 == [11, 13, 16, 18]
    assert first_affordable(excess) == 21
    final_load = kraft_load(state)
    assert final_load == Fraction(329, 512)

    remainder = Fraction(1, 21)
    greedy = []
    for rank in range(1, 21):
        if weight(rank) <= remainder:
            greedy.append(rank)
            remainder -= weight(rank)
    assert greedy == [5, 7, 8, 9, 10, 11, 13, 16, 18, 20]

    endpoint_crossings = [
        row for row in log
        if row["operation"] == "carry" and row["output"][1] < 0
    ]
    assert endpoint_crossings == []
    return {
        "initial_sources": [
            {"source": source, "rank": rank, "capacity": capacity, "deadline": rank - capacity}
            for source, rank, capacity in sources
        ],
        "initial_kraft_load": str(initial_load),
        "root_recut_kraft_load": str(root_load),
        "forced_rank_11_packet": {"rank": 11, "capacity": 1, "deadline": 10},
        "heads_after_processing_excess_through_20": heads_through_20,
        "exact_greedy_support_through_20": greedy,
        "first_unrecovered_forced_rank": 20,
        "next_excess_rank": 21,
        "kraft_load_at_first_hole": str(final_load),
        "endpoint_crossings": endpoint_crossings,
        "operation_log": log,
    }


def main() -> None:
    displayed_blocks = [
        power_block_receipt(10, 11, exponent)
        for exponent in (8, 6, 4, 2)
    ]
    output = {
        "theorem": (
            "Every positive-capacity power block contains the exact deadline "
            "packet P_(r,c)=w_(r-c)/2^c and has kappa>2^(c-1)-1/2."
        ),
        "algebraic_parameter_checks": verify_surplus_bound(),
        "first_lift_power_blocks": displayed_blocks,
        "first_lift_deadline_parking": first_lift_packet_receipt(),
        "boundary": (
            "The packet law certifies legal carries and endpoint safety. It "
            "does not by itself decide when a forced rank must remain parked."
        ),
    }
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
