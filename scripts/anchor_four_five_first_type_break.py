#!/usr/bin/env python3
"""Exact first renormalized type break after the (83,84) state of M(4,5)."""

from fractions import Fraction


def weight(rank: int) -> Fraction:
    return Fraction(1, 2**rank - 1)


def cylinder(a: int, b: int) -> Fraction:
    return weight(a) * weight(b)


def front(value: Fraction) -> int:
    assert value > 0
    rank = 2
    while weight(rank) > value:
        rank += 1
    return rank


def normalized_mass(value: Fraction) -> Fraction:
    rank = front(value)
    return (2**rank - 1) * value


def main() -> None:
    prefix79 = {
        9, 13, 14, 17, 19, 21, 22, 23, 24, 25, 28, 29,
        34, 35, 36, 37, 42, 43, 47, 48, 52, 54, 55, 59,
        61, 63, 64, 68, 70, 72, 74, 76, 77, 79,
    }

    # The owner-one cohort is the exact two-head tail of the untouched
    # physical source M(25,29).  The other cohort owns the remaining fifteen
    # first-front sources.
    c83 = cylinder(25, 29) - weight(54) - weight(79)
    r84 = cylinder(4, 5) - sum(
        (weight(rank) for rank in prefix79), Fraction()
    ) - c83
    assert front(c83) == 83
    assert front(r84) == 84
    assert c83.denominator % 2 == r84.denominator % 2 == 1

    # Exact cylinder-forest forms for the owner-one lineage.
    assert c83 == (
        cylinder(29, 54) + cylinder(25, 79) + cylinder(54, 79)
    )
    c104 = c83 - weight(83)
    assert c104 == (
        cylinder(29, 83)
        + cylinder(54, 83)
        + cylinder(25, 79)
        + cylinder(54, 79)
    )
    assert front(c104) == 104

    # The owner-fifteen lineage supplies every intervening global head.
    r_heads = (84, 88, 92, 94, 98, 99, 100)
    state = [c83, r84]
    assert front(sum(state, Fraction())) == 83
    state[0] -= weight(83)
    for rank in r_heads:
        assert front(sum(state, Fraction())) == rank
        assert front(state[1]) == rank
        state[1] -= weight(rank)
        assert state[1] > 0
    r103 = state[1]
    assert state[0] == c104
    assert front(r103) == 103

    # This is not the earlier equal-front synchronized predecessor.  The
    # fronts are staggered (103,104), but their union has front 102.
    pool = c104 + r103
    assert c104 < weight(102)
    assert r103 < weight(102)
    assert front(pool) == 102
    assert weight(102) + weight(105) <= pool
    assert pool < weight(102) + weight(104)

    h105 = pool - weight(102)
    assert front(h105) == 105
    assert h105.denominator % 2 == 1

    # Under the exact front-normalization mu(X)=(2^f(X)-1)X, the new
    # owner-sixteen singleton is not any component type occurring in this
    # transition.  More decisively, the ownership partition has changed from
    # (1,15) to (16), so no ownership-preserving scaling maps the states.
    component_types = {
        normalized_mass(c83),
        normalized_mass(r84),
        normalized_mass(c104),
        normalized_mass(r103),
    }
    assert normalized_mass(h105) not in component_types

    complete_prefix = prefix79 | {83, *r_heads, 102}
    assert cylinder(4, 5) == sum(
        (weight(rank) for rank in complete_prefix), Fraction()
    ) + h105

    print("initial renormalized state: fronts/owners [(83,1),(84,15)]")
    print("separate evolution: fronts/owners [(104,1),(103,15)]")
    print("first new recut type: staggered fronts (103,104) emit 102")
    print("post-recut state: one cohort at front 105 owning all 16 sources")
    print("M(4,5) first renormalized type break: PASS")


if __name__ == "__main__":
    main()
