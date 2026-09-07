#!/usr/bin/env python3
"""Exact audit for AnchorFourFiveDynamicOwnershipFlow.md.

This verifies the source-clock recut, anchor-25 demand word, common-height
integer transition, and a few named orbit states.  It is not an all-depth
proof of absence of 25 leading ones.
"""

from fractions import Fraction
from math import gcd


def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b


def w(n: int) -> Fraction:
    return Fraction(1, (1 << n) - 1)


def mersenne_packet(a: int, b: int) -> Fraction:
    return Fraction(1, ((1 << a) - 1) * ((1 << b) - 1))


def binary_digits(x: Fraction, count: int) -> list[int]:
    assert 0 <= x < 1
    digits: list[int] = []
    for _ in range(count):
        x *= 2
        if x >= 1:
            digits.append(1)
            x -= 1
        else:
            digits.append(0)
    return digits


def leading_one_data(x: Fraction, limit: int = 10000) -> tuple[int, int]:
    digits = binary_digits(x, limit)
    first = digits.index(1) + 1
    run = 0
    for bit in digits[first - 1 :]:
        if bit == 0:
            break
        run += 1
    return first, run


def scalar_front(x: Fraction) -> int:
    n = 1
    while w(n) > x:
        n += 1
    return n


PREFIX_79 = {
    9, 13, 14, 17, 19, 21, 22, 23, 24, 25, 28, 29, 34, 35, 36, 37,
    42, 43, 47, 48, 52, 54, 55, 59, 61, 63, 64, 68, 70, 72, 74, 76,
    77, 79,
}

PREFIX_102 = PREFIX_79 | {83, 84, 88, 92, 94, 98, 99, 100, 102}


def audit_rank_102_recut() -> Fraction:
    c83 = mersenne_packet(25, 29) - w(54) - w(79)
    r84 = mersenne_packet(4, 5) - sum((w(n) for n in PREFIX_79), Fraction()) - c83
    c104 = c83 - w(83)
    r103 = r84 - sum((w(n) for n in (84, 88, 92, 94, 98, 99, 100)), Fraction())
    h105 = c104 + r103 - w(102)
    p = w(102) - r103

    assert 0 < c104 < w(102)
    assert 0 < r103 < w(102)
    assert c104 + r103 > w(102)
    assert scalar_front(c104) == 104
    assert scalar_front(r103) == 103
    assert scalar_front(h105) == 105
    assert 0 < p < c104
    assert r103 + p == w(102)
    assert c104 == p + h105

    x = Fraction(1, 465)
    assert x - sum((w(n) for n in PREFIX_102), Fraction()) == h105
    return h105


def audit_anchor_demand() -> None:
    n = 105
    beta = Fraction((1 << 25) - 1, (1 << n) - 1)
    doubled = binary_digits(2 * beta, 2 * n)
    k = n - 25
    assert doubled[: k - 1] == [0] * (k - 1)
    assert doubled[k - 1 : k + 24] == [1] * 25

    beta_digits = binary_digits(beta, 2 * n + 2)
    expected_ones = set(range(n - 24, n + 1)) | set(range(2 * n - 24, 2 * n + 1))
    actual_ones = {j for j, bit in enumerate(beta_digits, start=1) if bit}
    assert actual_ones == expected_ones


def audit_common_height_update() -> None:
    x = Fraction(1, 465)
    height = 20
    coefficient = ((1 << height) - 1) * x
    assert coefficient.denominator == 1
    r = coefficient.numerator

    for n, take in ((9, True), (10, False), (13, True)):
        new_height = lcm(height, n)
        lift = ((1 << new_height) - 1) // ((1 << height) - 1)
        mask = ((1 << new_height) - 1) // ((1 << n) - 1)
        if take:
            assert lift * r >= mask
            r = lift * r - mask
            x -= w(n)
        else:
            assert lift * r < mask
            r = lift * r
        height = new_height
        assert Fraction(r, (1 << height) - 1) == x


def greedy_residuals(last: int) -> dict[int, Fraction]:
    residual = Fraction(1, 465)
    states: dict[int, Fraction] = {}
    support: set[int] = set()
    for n in range(1, last + 1):
        if residual >= w(n):
            residual -= w(n)
            support.add(n)
        states[n] = residual
    assert support & set(range(1, 103)) == PREFIX_102
    return states


def audit_named_states(h105: Fraction) -> None:
    states = greedy_residuals(240)
    assert states[102] == h105
    expected = {
        102: (80, 2, 105),
        114: (93, 4, 118),
        240: (218, 6, 243),
    }
    anchor = (1 << 25) - 1
    for n, (first, run, packet_front) in expected.items():
        c = anchor * states[n]
        got_first, got_run = leading_one_data(c)
        assert (got_first, got_run) == (first, run)
        assert packet_front == 25 + got_first
        assert scalar_front(states[n]) in (packet_front - 1, packet_front)


def main() -> None:
    h105 = audit_rank_102_recut()
    audit_anchor_demand()
    audit_common_height_update()
    audit_named_states(h105)
    print("anchor-four-five dynamic ownership audit: PASS")
    print("certified: rank-102 recut; periodic demand; exact coefficient update")
    print("finite diagnostics: leading-one runs 2, 4, 6 at ranks 102, 114, 240")
    print("not certified: all-depth exclusion of a 25-leading-one state")


if __name__ == "__main__":
    main()
