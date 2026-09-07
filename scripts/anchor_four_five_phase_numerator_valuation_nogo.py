#!/usr/bin/env python3
"""Exact checks for the phase-numerator valuation no-go at x = 1/465."""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations


def v2(value: int) -> int:
    assert value
    return (abs(value) & -abs(value)).bit_length() - 1


def prefix_data(depth: int, support: set[int]) -> tuple[int, int, int, int]:
    power = 1 << (2 * depth)
    remainder = power // 465
    product = 1
    for rank in support:
        remainder -= power // ((1 << rank) - 1)
        product *= (1 << rank) - 1

    numerator = product - 465 * sum(
        product // ((1 << rank) - 1) for rank in support
    )
    phase_numerator = pow(4, depth, 465) * product
    for rank in support:
        denominator = (1 << rank) - 1
        phase_numerator -= (
            465
            * pow(4, depth, denominator)
            * (product // denominator)
        )
    assert 465 * product * remainder == power * numerator - phase_numerator
    return remainder, product, numerator, phase_numerator


def prime_factors(value: int) -> set[int]:
    factors: set[int] = set()
    divisor = 2
    while divisor * divisor <= value:
        while value % divisor == 0:
            factors.add(divisor)
            value //= divisor
        divisor += 1
    if value > 1:
        factors.add(value)
    return factors


def audit_valuation_collapse() -> None:
    # Exhaust all prefixes through depth 8, then a reproducible sample at
    # depths 9..12.  The proof is equation (2); this is only an exact audit.
    for depth in range(2, 13):
        ranks = list(range(1, depth + 1))
        supports: list[set[int]] = []
        if depth <= 8:
            for size in range(depth + 1):
                supports.extend(set(chosen) for chosen in combinations(ranks, size))
        else:
            supports.extend(
                [
                    set(),
                    set(ranks[::2]),
                    set(ranks[1::2]),
                    set(ranks[-5:]),
                    {rank for rank in ranks if depth % rank == 0},
                ]
            )
        for support in supports:
            remainder, product, _, phase_numerator = prefix_data(depth, support)
            assert product & 1
            if remainder and v2(remainder) < 2 * depth:
                assert v2(phase_numerator) == v2(remainder)


def audit_fixed_target_nongate_falsifier() -> None:
    depth = 9
    support = {2, 3, 4, 6, 7}
    remainder, _, _, phase_numerator = prefix_data(depth, support)
    assert remainder == -147_968 == -289 * (1 << depth)
    assert v2(phase_numerator) == v2(remainder) == depth
    assert remainder != (1 << depth)


def audit_isolated_odd_prime_collapse() -> None:
    for depth, support in [
        (9, {2, 3, 4, 6, 7}),
        (12, {5, 7, 8, 9, 11}),
        (15, {6, 9, 10, 13, 14}),
    ]:
        _, product, numerator, phase_numerator = prefix_data(depth, support)
        denominators = {rank: (1 << rank) - 1 for rank in support}
        multiplicity: dict[int, int] = {}
        for denominator in denominators.values():
            for prime in prime_factors(denominator):
                multiplicity[prime] = multiplicity.get(prime, 0) + 1
        hypothetical_gate_rhs = (1 << depth) * (
            (1 << depth) * numerator - 465 * product
        )
        for denominator in denominators.values():
            cofactor = product // denominator
            for prime in prime_factors(denominator):
                if 465 % prime == 0 or multiplicity[prime] != 1:
                    continue
                expected = -465 * pow(4, depth, denominator) * cofactor
                assert phase_numerator % prime == expected % prime
                assert hypothetical_gate_rhs % prime == expected % prime


def audit_suffix_carry() -> None:
    # Use arbitrary integral pulse strings: (8) and the carry test are purely
    # algebraic and do not assert that these pulses are fixed-orbit reachable.
    samples = [
        [0, 0, 0, 0, 0, 0],
        [-7, 3, -4, 8, 0, -12, 4, 1],
        [5, -2, 9, -6, 3, 0, -1, 4, -8],
    ]
    for pulses in samples:
        depth = len(pulses)
        suffix = pulses[depth // 2 :]
        suffix_sum = sum(
            (4 ** (len(suffix) - 1 - index)) * pulse
            for index, pulse in enumerate(suffix)
        )
        if depth % 2 == 0:
            carry = 0
            exists = True
            for pulse in reversed(suffix):
                if (pulse + carry) % 4:
                    exists = False
                    break
                carry = (pulse + carry) // 4
            assert exists == (suffix_sum % (1 << depth) == 0)
        else:
            carry = 0
            exists = True
            for pulse in reversed(suffix[1:]):
                if (pulse + carry) % 4:
                    exists = False
                    break
                carry = (pulse + carry) // 4
            if exists:
                exists = (suffix[0] + carry) % 2 == 0
            assert exists == (suffix_sum % (1 << depth) == 0)


def audit_rank_twenty_four_countermodel_rejection() -> None:
    support = {9, 13, 14, 17, 19, 21, 22, 23}

    def load(rank: int) -> int:
        odd = sum(
            selected < rank and (2 * rank - 1) % selected == 0
            for selected in support
        )
        even = sum(
            selected < rank and (2 * rank) % selected == 0
            for selected in support
        )
        return 2 * odd + even

    # Fixed source pulses u_23 = u_24 = 0.  Rank 23 is selected in the
    # actual prefix; rank 24 is hypothetically forced to skip at the gate.
    h_24 = 0 - load(24) - 0
    h_23 = 0 - load(23) - 1
    assert (load(24), h_24) == (0, 0)
    assert (load(23), h_23) == (2, -3)
    first_carry = h_24 // 4
    assert h_24 % 4 == 0
    assert (h_23 + first_carry) % 4 != 0


def audit_recut_identity() -> None:
    depth = 100
    source_pairs = {
        0: 3,
        1: 0,
        2: 0,
        3: 0,
        4: 0,
        5: 2,
        6: 0,
        7: 3,
        8: 0,
        9: 3,
    }
    loads = [0] * (2 * depth + 1)
    remainders = [0]
    bits = [0]
    divisor_pulses = [0]
    for rank in range(1, depth + 1):
        source = source_pairs[rank % 10]
        divisor_pulse = 2 * loads[2 * rank - 1] + loads[2 * rank]
        pre_remainder = 4 * remainders[-1] + source - divisor_pulse
        weight = (1 << (2 * rank)) // ((1 << rank) - 1)
        bit = int(pre_remainder >= weight)
        remainder = pre_remainder - bit * weight
        bits.append(bit)
        divisor_pulses.append(divisor_pulse)
        remainders.append(remainder)
        if bit:
            for multiple in range(2 * rank, 2 * depth + 1, rank):
                loads[multiple] += 1

    for rank in range(4, depth + 1):
        cut = (rank + 1) // 2
        quotient = rank - cut
        binary_suffix = sum(
            bits[index] * (1 << (2 * cut - index))
            for index in range(cut + 1, rank + 1)
        )
        correction = sum(
            Fraction(
                divisor_pulses[index]
                + bits[index]
                - source_pairs[index % 10],
                4 ** (index - cut),
            )
            for index in range(cut + 1, rank + 1)
        )
        assert remainders[cut] == (
            Fraction(remainders[rank], 4**quotient)
            + binary_suffix
            + correction
        )


def main() -> None:
    audit_valuation_collapse()
    audit_fixed_target_nongate_falsifier()
    audit_isolated_odd_prime_collapse()
    audit_suffix_carry()
    audit_rank_twenty_four_countermodel_rejection()
    audit_recut_identity()
    print(
        "phase-numerator valuation no-go PASS: valuation collapse, fixed-target "
        "nongate falsifier, isolated odd-prime collapse, and suffix-carry "
        "equivalence; rank-24 synthetic gate rejected; recut identity checked"
    )


if __name__ == "__main__":
    main()
