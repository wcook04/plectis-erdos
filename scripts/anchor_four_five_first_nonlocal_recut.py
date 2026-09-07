#!/usr/bin/env python3
"""Exact first nonlocal recut for M(4,5)."""

from collections import defaultdict
from fractions import Fraction


def weight(rank: int) -> Fraction:
    return Fraction(1, 2**rank - 1)


def cylinder(a: int, b: int) -> Fraction:
    return weight(a) * weight(b)


def packet(rank: int, capacity: int) -> Fraction:
    return weight(rank - capacity) / 2**capacity


def theta(rank: int, capacity: int) -> Fraction:
    return packet(rank, capacity) - weight(rank)


def main() -> None:
    a, b = 4, 5
    collision = a * b + a + b
    assert collision == 29
    scale = (collision - 1) // a
    coefficient = sum(2 ** (i * a) for i in range(1, scale))
    assert coefficient == (2 ** (collision - 1) - 1) // (2**a - 1) - 1

    outer_atoms = {9, 13, 14, 17, 19, 21, 24, 25, 28}
    sources: list[tuple[str, int, int, int]] = []
    for step in range(1, b):
        sources.append(
            (f"a_side_{step}", b + step * a, b + (step + 1) * a, 0)
        )
    for step in range(1, a):
        sources.append(
            (f"b_side_{step}", a + step * b, a + (step + 1) * b, 0)
        )
    sources.extend(
        [
            ("child_n_minus_a", collision - a, collision, 0),
            ("child_b", b, collision, 0),
            ("child_n_minus_b", collision - b, collision, 0),
        ]
    )
    for i in range(1, scale):
        sources.append((f"lift_bit_{i}", collision - 1, collision, i * a))

    source_value = sum(
        (2**exponent * cylinder(x, y) for _, x, y, exponent in sources),
        Fraction(),
    )
    target = cylinder(a, b)
    assert target == sum((weight(rank) for rank in outer_atoms), Fraction()) + source_value

    state: dict[int, list[tuple[int, str]]] = defaultdict(list)
    for name, x, y, exponent in sources:
        if x > y:
            x, y = y, x
        rank = x + y - exponent
        capacity = y - exponent
        state[rank].append((capacity, name))

    packet_value = sum(
        (packet(rank, capacity) for rank, rows in state.items() for capacity, _ in rows),
        Fraction(),
    )
    excess = source_value - packet_value
    assert excess > 0

    carry_receipts = []
    for rank in (33, 53):
        rows = sorted(state[rank])
        (first, first_name), (second, second_name) = rows[:2]
        state[rank] = rows[2:]
        excess += packet(rank, second) - packet(rank, first)
        state[rank - 1].append((first - 1, f"carry({first_name},{second_name})"))
        carry_receipts.append((rank, first, second, rank - 1, first - 1))
    assert carry_receipts == [(33, 5, 19, 32, 4), (53, 25, 29, 52, 24)]

    for rank, name in ((22, "a_side_1"), (23, "b_side_1")):
        row = next(item for item in state[rank] if item[1] == name)
        state[rank].remove(row)
        excess += theta(rank, row[0])
        outer_atoms.add(rank)

    residual = target - sum((weight(rank) for rank in outer_atoms), Fraction())
    remaining_packet_value = sum(
        (packet(rank, capacity) for rank, rows in state.items() for capacity, _ in rows),
        Fraction(),
    )
    assert residual == excess + remaining_packet_value
    assert weight(29) < residual < 2 * weight(29)
    assert weight(34) < residual - weight(29) < weight(33)

    packet_30 = next(capacity for capacity, _ in state[30])
    packet_32 = next(capacity for capacity, _ in state[32])
    assert packet_30 == 17
    assert packet_32 == 4

    residual_22 = cylinder(9, 13) - weight(22)
    residual_23 = cylinder(9, 14) - weight(23)
    assert residual_22 == cylinder(9, 22) + cylinder(13, 22)
    assert residual_23 == cylinder(9, 23) + cylinder(14, 23)

    packet_source_30 = cylinder(13, 17)
    packet_source_32 = cylinder(14, 19) + 2**24 * cylinder(28, 29)
    source_core = packet_source_30 + packet_source_32
    assert source_core + residual_22 < weight(29)
    assert source_core + residual_23 < weight(29)

    physical_pool = source_core + residual_22 + residual_23
    assert weight(29) < physical_pool < 2 * weight(29)
    post_recut = physical_pool - weight(29)
    assert post_recut.denominator % 2 == 1
    assert weight(35) < post_recut < weight(34)

    assert state[34] == [(29, "child_b")]
    print(f"target: {target}")
    print(f"first-collision coefficient: {coefficient}")
    print(f"carry receipts: {carry_receipts}")
    print(
        "rank-29 ownership pool: residuals(22,23) + "
        "source(30) + joint-source(32)"
    )
    print(f"post-recut residual: {post_recut}")
    print("anchor M(4,5) first nonlocal recut: PASS")


if __name__ == "__main__":
    main()
