#!/usr/bin/env python3
"""Exact countermodel to a one-third-prefix endpoint-set induction."""

from __future__ import annotations

from math import isqrt


DENOMINATOR = 465
COMMON_SUPPORT = {
    9, 13, 14, 17, 19, 21, 22, 23,
    24, 25, 28, 29, 34, 35, 36, 37,
}


def proper_divisors(n: int) -> tuple[int, ...]:
    result: list[int] = []
    for divisor in range(1, isqrt(n) + 1):
        if n % divisor:
            continue
        other = n // divisor
        if divisor < n:
            result.append(divisor)
        if other != divisor and other < n:
            result.append(other)
    return tuple(result)


def target_bits(horizon: int) -> list[int]:
    remainder = 1
    result = [0]
    for _ in range(horizon):
        remainder *= 2
        bit, remainder = divmod(remainder, DENOMINATOR)
        result.append(bit)
    return result


def endpoint_step(
    endpoints: tuple[int, ...],
    rank: int,
    source_bit: int,
    common_load: int,
    half_bits: tuple[int, ...],
) -> tuple[int, ...]:
    assert len(endpoints) == len(half_bits)
    ceiling = rank // 20
    children: set[int] = set()
    for endpoint, half_bit in zip(endpoints, half_bits):
        for terminal_bit in (0, 1):
            child = (
                2 * endpoint + source_bit
                - common_load - half_bit - terminal_bit
            )
            if 0 <= child <= ceiling:
                children.add(child)
    return tuple(sorted(children))


def full_prefix_states(horizon: int) -> list[tuple[int, int]]:
    bits = target_bits(horizon)
    states: list[tuple[int, int]] = [(0, 0)]
    for rank in range(1, horizon + 1):
        ceiling = rank // 20
        divisors = proper_divisors(rank)
        next_states: list[tuple[int, int]] = []
        for word, defect in states:
            load = sum((word >> (d - 1)) & 1 for d in divisors)
            before_bit = 2 * defect + bits[rank] - load
            for selected in (0, 1):
                child = before_bit - selected
                if 0 <= child <= ceiling:
                    next_states.append(
                        (word | (selected << (rank - 1)), child)
                    )
        states = next_states
    return states


def main() -> None:
    bits = target_bits(116)
    expected_rows = {
        112: (0, (14, 28)),
        113: (1, ()),
        114: (1, (19,)),
        115: (0, (23,)),
        116: (0, (29,)),
    }
    loads: dict[int, int] = {}
    for rank, (expected_bit, selected_divisors) in expected_rows.items():
        actual = tuple(
            divisor for divisor in sorted(COMMON_SUPPORT)
            if divisor <= rank // 3 and rank % divisor == 0
        )
        assert bits[rank] == expected_bit
        assert actual == selected_divisors
        loads[rank] = len(actual)
        assert rank // 20 == 5

    endpoints = tuple(range(6))
    endpoints = endpoint_step(
        endpoints, 112, bits[112], loads[112], (0, 1, 0, 1, 0, 0)
    )
    assert endpoints == (1, 2, 3, 5)
    endpoints = endpoint_step(
        endpoints, 113, bits[113], loads[113], (0,) * len(endpoints)
    )
    assert endpoints == (2, 3, 4, 5)
    endpoints = endpoint_step(
        endpoints, 114, bits[114], loads[114], (0,) * len(endpoints)
    )
    assert endpoints == (3, 4, 5)
    endpoints = endpoint_step(
        endpoints, 115, bits[115], loads[115], (0,) * len(endpoints)
    )
    assert endpoints == (4, 5)
    endpoints = endpoint_step(
        endpoints, 116, bits[116], loads[116], (0,) * len(endpoints)
    )
    assert endpoints == ()

    actual_states = full_prefix_states(111)
    assert sorted(defect for _, defect in actual_states) == list(range(6))
    assert all(
        ((word >> 55) & 1, (word >> 56) & 1, (word >> 57) & 1)
        == (0, 0, 0)
        for word, _ in actual_states
    )

    print("hole-tolerant endpoint-set countermodel: PASS")
    print("ranks: 112..116")
    print("endpoint counts: 6 -> 4 -> 4 -> 3 -> 2 -> 0")
    print("source digits and common divisor loads: exact for 1/465")
    print("boundary: half-rank labels are not those of the real corridor")


if __name__ == "__main__":
    main()
