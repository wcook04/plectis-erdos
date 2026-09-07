#!/usr/bin/env python3
"""Exact first counterexample to uniform eight-step defect payment for 1/465."""

from __future__ import annotations

import json


DENOMINATOR = 465
FIRST_MIDPOINT = 20
FIRST_FAILURE = 1298
DEPTH = FIRST_FAILURE + 10


def target_bit(rank: int) -> int:
    return (1 << rank) // DENOMINATOR - 2 * (
        (1 << (rank - 1)) // DENOMINATOR
    )


def exact_greedy_state(depth: int) -> tuple[list[int], list[int], list[int], list[int]]:
    """Certify the real-greedy word by a dyadic integer enclosure."""
    precision = 2 * depth + 64
    scale = 1 << precision
    lower = scale // DENOMINATOR
    upper = (scale + DENOMINATOR - 1) // DENOMINATOR
    bits = [0] * (depth + 1)
    divisor_load = [0] * (depth + 1)
    defect = [0] * (depth + 1)
    prefix = [0] * (depth + 1)
    for rank in range(1, depth + 1):
        weight_floor = scale // ((1 << rank) - 1)
        if lower >= weight_floor + 1:
            lower -= weight_floor + 1
            upper -= weight_floor
            bits[rank] = 1
            for multiple in range(rank, depth + 1, rank):
                divisor_load[multiple] += 1
        elif upper <= weight_floor:
            pass
        else:
            raise AssertionError(f"ambiguous real-greedy branch at rank {rank}")
        prefix[rank] = prefix[rank - 1] + bits[rank]
        defect[rank] = (
            2 * defect[rank - 1]
            + target_bit(rank)
            - divisor_load[rank]
        )
    return bits, divisor_load, defect, prefix


def payment_row(
    midpoint: int,
    width: int,
    bits: list[int],
    divisor_load: list[int],
    defect: list[int],
) -> tuple[int, int, list[dict[str, int]]]:
    """Return (D_width,J_width,rows) for the directed payment recurrence."""
    directed = -defect[midpoint]
    holes = 0
    rows: list[dict[str, int]] = []
    for offset in range(1, width + 1):
        rank = midpoint + offset
        proper_load = divisor_load[rank] - bits[rank]
        holes = 2 * holes + 1 - bits[rank]
        directed = (
            2 * directed
            + 1
            - target_bit(rank)
            + proper_load
        )
        assert directed == holes - defect[rank]
        rows.append(
            {
                "offset": offset,
                "rank": rank,
                "b": bits[rank],
                "t": target_bit(rank),
                "f": divisor_load[rank],
                "s": proper_load,
                "Q": defect[rank],
                "J": holes,
                "D": directed,
            }
        )
    return directed, holes, rows


def main() -> None:
    bits, divisor_load, defect, prefix = exact_greedy_state(DEPTH)

    first_unpaid: int | None = None
    for midpoint in range(FIRST_MIDPOINT, FIRST_FAILURE + 1):
        directed = -defect[midpoint]
        paid = False
        for offset in range(1, 9):
            rank = midpoint + offset
            directed = (
                2 * directed
                + 1
                - target_bit(rank)
                + divisor_load[rank]
                - bits[rank]
            )
            if directed >= 0:
                paid = True
                break
        if not paid:
            first_unpaid = midpoint
            break

    assert first_unpaid == FIRST_FAILURE
    d8, j8, rows8 = payment_row(
        FIRST_FAILURE, 8, bits, divisor_load, defect
    )
    d10, j10, rows10 = payment_row(
        FIRST_FAILURE, 10, bits, divisor_load, defect
    )
    assert prefix[FIRST_FAILURE] == 610
    assert defect[FIRST_FAILURE] == 2
    assert j8 == 1 and defect[FIRST_FAILURE + 8] == 2 and d8 == -1
    assert all(row["D"] < 0 for row in rows8)
    assert rows10[8]["D"] == -1
    assert d10 == 2 and j10 == 5 and defect[FIRST_FAILURE + 10] == 3

    print(
        json.dumps(
            {
                "method": "exact dyadic enclosure and integer defect recurrence",
                "first_midpoint_checked": FIRST_MIDPOINT,
                "first_eight_step_failure": FIRST_FAILURE,
                "P_M": prefix[FIRST_FAILURE],
                "Q_M": defect[FIRST_FAILURE],
                "D_8": d8,
                "J_8": j8,
                "Q_M_plus_8": defect[FIRST_FAILURE + 8],
                "first_payment_offset": 10,
                "D_10": d10,
                "rows_through_payment": rows10,
                "claim": "uniform eight-step directed solvency is false",
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
