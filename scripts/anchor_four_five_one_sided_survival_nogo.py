#!/usr/bin/env python3
"""Exact symbolic countermodel to one-sided survival from local seam laws."""

from __future__ import annotations

import json


START_RANK = 500
COMMON_ONES = {4, 5, 11, 13, 22, 23, 39, 46, 169}
SEAM_THRESHOLDS = {502: 1, 504: 2, 506: 3}
EXPECTED_ENDPOINTS = {
    501: tuple(range(26)),
    502: (0, 1, *range(3, 26)),
    503: (0, 1, 2, *range(5, 26)),
    504: (0, 1, 2, *range(8, 26)),
    505: (0, 1, 2, 3, *range(14, 26)),
    506: (0, 1, 23, 24, 25),
    507: (),
}


def source_bit(rank: int) -> int:
    return (1 << rank) // 465 - 2 * ((1 << (rank - 1)) // 465)


def lower_load(rank: int) -> int:
    return sum(
        int(divisor in COMMON_ONES)
        for divisor in range(1, rank // 2 + 1)
        if divisor < rank / 2 and rank % divisor == 0
    )


def raw_multiplicity(rank: int) -> int:
    return sum(
        1
        for i in range(1, rank // 4 + 1)
        for j in range(1, rank // 5 + 1)
        if 4 * i + 5 * j == rank
    )


def main() -> None:
    states: set[tuple[int, str]] = {
        (endpoint, "U") for endpoint in range(START_RANK // 20 + 1)
    }
    rows: list[dict[str, object]] = []

    for rank in range(START_RANK + 1, 508):
        digit = source_bit(rank)
        load = lower_load(rank)
        threshold = SEAM_THRESHOLDS.get(rank)
        next_states: set[tuple[int, str]] = set()

        for endpoint, ancestry in states:
            half_bit = int(
                threshold is not None and endpoint <= threshold
            )
            next_ancestry = ancestry
            if rank == 502:
                next_ancestry = "L" if half_bit else "R"
            for new_bit in (0, 1):
                child = 2 * endpoint + digit - load - half_bit - new_bit
                if 0 <= child <= rank // 20:
                    next_states.add((child, next_ancestry))

        states = next_states
        endpoints = tuple(sorted({endpoint for endpoint, _ in states}))
        assert endpoints == EXPECTED_ENDPOINTS[rank]
        assert load + 2 <= raw_multiplicity(rank)
        rows.append(
            {
                "rank": rank,
                "source_bit": digit,
                "lower_load": load,
                "seam_threshold": threshold,
                "endpoints": endpoints,
                "left_endpoints": tuple(
                    sorted(q for q, label in states if label == "L")
                ),
                "right_endpoints": tuple(
                    sorted(q for q, label in states if label == "R")
                ),
            }
        )

    assert all(row["source_bit"] == 0 for row in rows)
    assert rows[-2]["left_endpoints"] == (0, 1)
    assert rows[-2]["right_endpoints"] == (23, 24, 25)
    assert not states

    print(
        json.dumps(
            {
                "status": "PASS",
                "claim": (
                    "local monotone seam laws plus source digits and "
                    "tau<=r do not force one-sided survival"
                ),
                "common_selected_bits": sorted(COMMON_ONES),
                "rows": rows,
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
