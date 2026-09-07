#!/usr/bin/env python3
"""Exact witness against a terminal-congruence exclusion of fatal zero.

This checker rebuilds the deterministic half seam words at rows 1419--1422
directly from their integer-greedy definition.  The endpoint at row 1422 has
all of the scalar conditions left by the fatal-zero transfer (phase zero and
pulse one), follows an upper reset by two right steps, and satisfies every
``-1`` suffix congruence through that complete two-step run.  Its seam
remainder is nevertheless enormous rather than one.

The witness only refutes a proof using those bounded endpoint congruences as
a sufficient unit-state discriminator.  It does not satisfy, and does not
refute, the analytic fatality or midpoint-row hypotheses.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class SeamState:
    rank: int
    remainder: int
    support: frozenset[int]
    pulse: int


def row_pulse(rank: int, divisor: int) -> int:
    return 2 * int((2 * rank + 1) % divisor == 0) + int(
        (2 * rank + 2) % divisor == 0
    )


def seam_state(rank: int) -> SeamState:
    scale = 1 << (2 * rank)
    remainder = (1 << (2 * rank - 1)) - (1 << rank)
    support: set[int] = set()
    for divisor in range(2, rank):
        coin = scale // ((1 << divisor) - 1)
        if coin <= remainder:
            support.add(divisor)
            remainder -= coin
    pulse = sum(row_pulse(rank, divisor) for divisor in support)
    return SeamState(rank, remainder, frozenset(support), pulse)


def branch(previous: SeamState, current: SeamState) -> str:
    if current.support == previous.support | {previous.rank}:
        return "right"
    if current.support == previous.support:
        return "middle"
    return "upper"


def affine_charge(pulses: list[int]) -> int:
    charge = 0
    for pulse in pulses:
        charge = 4 * charge + pulse + 4
    return charge


def main() -> None:
    states = {rank: seam_state(rank) for rank in range(1419, 1423)}

    assert branch(states[1419], states[1420]) == "upper"
    assert branch(states[1420], states[1421]) == "right"
    assert branch(states[1421], states[1422]) == "right"

    endpoint = states[1422]
    assert endpoint.rank % 3 == 0
    assert endpoint.pulse == 1
    assert len(endpoint.support) == 692
    assert endpoint.remainder != 1

    # The two pulse digits of the realized right run start at rows 1420,1421.
    pulses = [states[1420].pulse, states[1421].pulse]
    assert pulses == [9, 7]

    # Every terminal suffix obeys the exact necessary unit-state residue.
    for depth in (1, 2):
        suffix_charge = affine_charge(pulses[-depth:])
        assert (1 + suffix_charge) % (4**depth) == 0

    full_charge = affine_charge(pulses)
    assert full_charge == 63
    assert endpoint.remainder % 16 == 1
    assert (endpoint.remainder + full_charge) % 16 == 0

    # The collision is deeper than the realized run: E is 1 modulo 2^8.
    assert endpoint.remainder % 256 == 1
    assert endpoint.remainder % 512 != 1

    print("fatal-zero endpoint valuation no-go: exact witness verified")
    print(
        {
            "endpoint_rank": endpoint.rank,
            "endpoint_phase_mod_3": endpoint.rank % 3,
            "endpoint_pulse": endpoint.pulse,
            "endpoint_support_card": len(endpoint.support),
            "right_run_length": 2,
            "right_run_pulses": pulses,
            "full_affine_charge": full_charge,
            "endpoint_remainder_mod_256": endpoint.remainder % 256,
            "endpoint_remainder_bit_length": endpoint.remainder.bit_length(),
        }
    )


if __name__ == "__main__":
    main()
