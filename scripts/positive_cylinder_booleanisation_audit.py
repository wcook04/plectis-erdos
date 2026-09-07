#!/usr/bin/env python3
"""Exact audit for positive Stern--Brocot cylinder Booleanisation.

The script distinguishes three coefficient systems for

    M(a,b) = 1 / ((2^a-1)(2^b-1)).

* c(n) counts primitive positive solutions of a*p+b*q=n;
* r(n) counts all positive solutions and equals sum_{d|n} c(d);
* t(n) is the binary digit stream of M(a,b).

The carry K(n)=2*K(n-1)+t(n)-r(n) normalises the lattice coefficients to
binary digits.  For (a,b)=(2,3), K(n)=floor(n/6).  If B is a Boolean
Mersenne support with quotient defect Q, then E=K-Q satisfies

    E(n)=2*E(n-1)+h_B(n)-r(n).

All arithmetic used for the reported identities and greedy decisions is
integer or Fraction arithmetic.  Finite scans remain finite evidence.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import gcd, lcm


def weight(rank: int) -> Fraction:
    return Fraction(1, (1 << rank) - 1)


def cylinder(left: int, right: int) -> Fraction:
    return weight(left) * weight(right)


def primitive_count(left: int, right: int, rank: int) -> int:
    return sum(
        1
        for p in range(1, rank // left + 1)
        for q in range(1, rank // right + 1)
        if left * p + right * q == rank and gcd(p, q) == 1
    )


def lattice_count(left: int, right: int, rank: int) -> int:
    return sum(
        1
        for p in range(1, rank // left + 1)
        if rank - left * p > 0 and (rank - left * p) % right == 0
    )


def coefficient_arrays(
    left: int,
    right: int,
    depth: int,
) -> tuple[list[int], list[int]]:
    """Return primitive and unrestricted lattice counts through `depth`."""
    primitive = [0] * (depth + 1)
    lattice = [0] * (depth + 1)
    for p in range(1, depth // left + 1):
        for q in range(1, (depth - left * p) // right + 1):
            rank = left * p + right * q
            lattice[rank] += 1
            if gcd(p, q) == 1:
                primitive[rank] += 1
    return primitive, lattice


def divisors(rank: int) -> list[int]:
    return [d for d in range(1, rank + 1) if rank % d == 0]


def binary_digits(numerator: int, denominator: int, depth: int) -> list[int]:
    remainder = numerator
    digits = [0] * (depth + 1)
    for rank in range(1, depth + 1):
        remainder *= 2
        digits[rank], remainder = divmod(remainder, denominator)
        if digits[rank] not in (0, 1):
            raise AssertionError("target is not in [0,1)")
    return digits


def exact_greedy_bits(
    numerator: int,
    denominator: int,
    depth: int,
) -> list[int]:
    """Certify decisions by directed dyadic intervals."""
    precision = 2 * depth + 64
    scale = 1 << precision
    lower = scale * numerator // denominator
    upper = (scale * numerator + denominator - 1) // denominator
    bits = [0] * (depth + 1)
    for rank in range(1, depth + 1):
        weight_floor = scale // ((1 << rank) - 1)
        if lower >= weight_floor + 1:
            lower -= weight_floor + 1
            upper -= weight_floor
            bits[rank] = 1
        elif upper <= weight_floor:
            continue
        else:
            raise AssertionError(
                f"undecided directed interval at rank {rank}"
            )
    return bits


def quotient_defects(
    digits: list[int],
    bits: list[int],
) -> list[int]:
    depth = len(bits) - 1
    divisor_load = [0] * (depth + 1)
    for rank in range(1, depth + 1):
        if bits[rank]:
            for multiple in range(rank, depth + 1, rank):
                divisor_load[multiple] += 1
    defects = [0] * (depth + 1)
    for rank in range(1, depth + 1):
        defects[rank] = (
            2 * defects[rank - 1] + digits[rank] - divisor_load[rank]
        )
        if defects[rank] < 0:
            raise AssertionError(f"negative quotient defect at rank {rank}")
    return defects


def primitive_lattice_receipt(depth: int) -> dict[str, object]:
    primitive, lattice = coefficient_arrays(2, 3, depth)
    for rank in range(1, depth + 1):
        assert lattice[rank] == sum(
            primitive[d] for d in divisors(rank)
        )

    digits = binary_digits(1, 21, depth)
    carry = [0] * (depth + 1)
    for rank in range(1, depth + 1):
        carry[rank] = (
            2 * carry[rank - 1] + digits[rank] - lattice[rank]
        )
        assert carry[rank] == rank // 6

    assert primitive[10] == 0
    assert primitive[11] == 2
    return {
        "checked_through": depth,
        "divisor_sum_identity_checked": True,
        "raw_carry_equals_floor_rank_div_six_checked": True,
        "primitive_rank_10": primitive[10],
        "primitive_rank_11": primitive[11],
        "claim_status": (
            "the formulas are proved separately in the note; this is an "
            "exact finite audit"
        ),
    }


def forced_anticipation_receipt() -> dict[str, object]:
    target = Fraction(1, 21)
    residual = target
    decisions: list[dict[str, object]] = []
    selected: list[int] = []
    for rank in range(1, 11):
        before = residual
        take = before >= weight(rank)
        if take:
            residual -= weight(rank)
            selected.append(rank)
        decisions.append(
            {
                "rank": rank,
                "take": take,
                "residual_before": str(before),
                "weight": str(weight(rank)),
                "residual_after": str(residual),
            }
        )
    assert selected == [5, 7, 8, 9, 10]
    assert primitive_count(2, 3, 10) == 0
    assert primitive_count(2, 3, 11) == 2

    carry_checks = []
    for rank in range(2, 65):
        assert 2 * weight(rank) + cylinder(rank - 1, rank) == weight(rank - 1)
        carry_checks.append(rank)

    aggregate_credit_remainder = (
        cylinder(11, 3)
        + cylinder(8, 11)
        + cylinder(11, 9)
        + cylinder(2, 11)
        - cylinder(10, 11)
    )
    assert aggregate_credit_remainder == Fraction(3481, 14811335)
    assert aggregate_credit_remainder > 0

    # The aggregate remainder is already an integer cylinder cone element.
    assert weight(2) == 341 * weight(10)
    first_cylinder_decomposition = (
        cylinder(11, 3)
        + cylinder(8, 11)
        + cylinder(11, 9)
        + 340 * cylinder(10, 11)
    )
    assert first_cylinder_decomposition == aggregate_credit_remainder

    return {
        "target": "1/21",
        "greedy_selected_through_10": selected,
        "decisions": decisions,
        "rank_10_has_no_primitive_emission": True,
        "rank_11_has_two_primitive_emissions": True,
        "positive_carry_identity": "2*w_n + M(n-1,n) = w_(n-1)",
        "positive_carry_identity_checked_for": [
            min(carry_checks),
            max(carry_checks),
        ],
        "first_aggregate_credit_remainder": str(
            aggregate_credit_remainder
        ),
        "first_positive_cylinder_decomposition": (
            "M(11,3)+M(8,11)+M(11,9)+340*M(10,11)"
        ),
        "claim_status": "exact rational computation",
    }


def lcm_lift_coefficient(endpoint: int, stop: int) -> tuple[int, int]:
    """Return L,A with M(endpoint,stop)-M(stop-1,stop)=A*M(stop,L)."""
    if not 2 <= endpoint < stop - 1:
        raise ValueError("need 2 <= endpoint < stop-1")
    lifted_rank = lcm(endpoint, stop - 1)
    coefficient = (
        ((1 << lifted_rank) - 1) // ((1 << endpoint) - 1)
        - ((1 << lifted_rank) - 1) // ((1 << (stop - 1)) - 1)
    )
    assert coefficient > 0
    assert (
        cylinder(endpoint, stop) - cylinder(stop - 1, stop)
        == coefficient * cylinder(stop, lifted_rank)
    )
    return lifted_rank, coefficient


def lcm_collision_receipt() -> dict[str, object]:
    """Audit the general LCM lift and the first even primitive collision."""
    checks = []
    for stop in range(5, 80):
        for endpoint in range(2, stop - 1):
            lifted_rank, coefficient = lcm_lift_coefficient(endpoint, stop)
            checks.append((endpoint, stop, lifted_rank, coefficient))

    # The first collision is the special divisibility case L=10, A=340.
    first_lift = lcm_lift_coefficient(2, 11)
    assert first_lift == (10, 340)

    # At the first even primitive collision the direct endpoint-divisibility
    # shortcut fails, but the LCM lift remains an exact integer cylinder.
    even_lift = lcm_lift_coefficient(3, 20)
    assert even_lift == (57, 20587609132405320)
    even_pair_surplus = cylinder(11, 9) + cylinder(17, 3) - weight(19)
    even_decomposition = (
        cylinder(20, 9)
        + cylinder(11, 20)
        + cylinder(17, 20)
        + even_lift[1] * cylinder(20, even_lift[0])
    )
    assert even_pair_surplus == even_decomposition
    assert 0 < even_pair_surplus < weight(20)

    return {
        "general_identity": (
            "M(e,n)-M(n-1,n)=A*M(n,lcm(e,n-1))"
        ),
        "parameter_pairs_checked": len(checks),
        "stop_range_checked": [5, 79],
        "first_collision_lift": {
            "endpoint": 2,
            "stop": 11,
            "lifted_rank": first_lift[0],
            "coefficient": first_lift[1],
        },
        "first_even_collision_lift": {
            "primitive_cylinders": ["M(11,9)", "M(17,3)"],
            "endpoint": 3,
            "stop": 20,
            "lifted_rank": even_lift[0],
            "coefficient": even_lift[1],
            "positive_surplus": str(even_pair_surplus),
            "surplus_is_below_w_20": True,
        },
        "claim_status": (
            "the general identity is proved algebraically in the note; "
            "the stated finite range and rank-20 decomposition are exact "
            "integer/rational checks"
        ),
    }


def greedy_surplus_receipt(depth: int) -> dict[str, object]:
    digits = binary_digits(1, 21, depth)
    bits = exact_greedy_bits(1, 21, depth)
    defects = quotient_defects(digits, bits)
    _, lattice = coefficient_arrays(2, 3, depth)
    raw_carry = 0
    minimum_surplus = depth
    zero_surplus_ranks: list[int] = []
    first_negative = None
    for rank in range(1, depth + 1):
        raw_carry = (
            2 * raw_carry
            + digits[rank]
            - lattice[rank]
        )
        surplus = raw_carry - defects[rank]
        minimum_surplus = min(minimum_surplus, surplus)
        if surplus == 0:
            zero_surplus_ranks.append(rank)
        if surplus < 0 and first_negative is None:
            first_negative = rank
    assert raw_carry == depth // 6
    return {
        "checked_through": depth,
        "minimum_booleanisation_surplus": minimum_surplus,
        "first_negative_surplus_rank": first_negative,
        "zero_surplus_ranks": zero_surplus_ranks,
        "selected": sum(bits),
        "skipped": depth - sum(bits),
        "maximum_quotient_defect": max(defects),
        "claim_status": "exact finite directed-interval computation only",
    }


def scaled_adjacent_cylinder_receipt(depth: int) -> dict[str, object]:
    # The residual in x_5 = w_5 + w_10 + x_5*w_10 is
    # x_5*w_10 = 17*M(9,10).
    numerator = 17
    denominator = ((1 << 9) - 1) * ((1 << 10) - 1)
    bits = exact_greedy_bits(numerator, denominator, depth)
    selected = [rank for rank in range(1, depth + 1) if bits[rank]]
    assert selected[:2] == [15, 19]
    assert numerator * weight(19) > weight(15)
    return {
        "target": f"{numerator}/{denominator}",
        "identity": "x_5*w_10 = 17*M(9,10)",
        "first_selected_ranks": selected[:20],
        "multiplicity_17_stop_rank": 19,
        "anticipatory_selected_rank": 15,
        "inequality": "17*w_19 > w_15",
        "checked_through": depth,
        "claim_status": (
            "the displayed identities and inequality are exact; the greedy "
            "prefix beyond the asserted first two ranks is a finite audit"
        ),
    }


def resolvent_comparison_receipt() -> dict[str, object]:
    """Disprove direct actual-versus-primitive resolvent domination."""
    cut = 20
    boundary = 2 * cut
    lookahead = 100
    bits = exact_greedy_bits(1, 21, boundary + lookahead)
    primitive, lattice = coefficient_arrays(2, 3, boundary + lookahead)
    digits = binary_digits(1, 21, boundary + lookahead)
    defects = quotient_defects(digits, bits)

    raw_carry = [0] * (boundary + 1)
    for rank in range(1, boundary + 1):
        raw_carry[rank] = (
            2 * raw_carry[rank - 1] + digits[rank] - lattice[rank]
        )
    surplus_at_boundary = raw_carry[boundary] - defects[boundary]

    actual_resolvent = sum(
        (
            Fraction(
                pow(2, boundary, (1 << rank) - 1),
                (1 << rank) - 1,
            )
            for rank in range(1, cut + 1)
            if bits[rank]
        ),
        Fraction(),
    )
    primitive_resolvent = sum(
        (
            primitive[rank]
            * Fraction(
                pow(2, boundary, (1 << rank) - 1),
                (1 << rank) - 1,
            )
            for rank in range(1, cut + 1)
        ),
        Fraction(),
    )
    difference = actual_resolvent - primitive_resolvent
    assert difference < 0

    first_coefficient_failure = None
    for offset in range(1, lookahead + 1):
        actual_coefficient = sum(
            bits[rank]
            for rank in range(1, cut + 1)
            if (boundary + offset) % rank == 0
        )
        primitive_coefficient = sum(
            primitive[rank]
            for rank in range(1, cut + 1)
            if (boundary + offset) % rank == 0
        )
        if actual_coefficient < primitive_coefficient:
            first_coefficient_failure = {
                "offset": offset,
                "actual": actual_coefficient,
                "primitive": primitive_coefficient,
            }
            break
    assert first_coefficient_failure == {
        "offset": 2,
        "actual": 1,
        "primitive": 2,
    }
    assert surplus_at_boundary > 0
    return {
        "cut": cut,
        "boundary": boundary,
        "actual_resolvent": str(actual_resolvent),
        "primitive_resolvent": str(primitive_resolvent),
        "actual_minus_primitive": str(difference),
        "first_coefficientwise_domination_failure": (
            first_coefficient_failure
        ),
        "booleanisation_surplus_at_boundary": surplus_at_boundary,
        "claim_status": "exact rational counterexample",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=5000)
    args = parser.parse_args()
    if args.depth < 64:
        raise SystemExit("--depth must be at least 64")
    report = {
        "primitive_lattice": primitive_lattice_receipt(args.depth),
        "forced_anticipation": forced_anticipation_receipt(),
        "lcm_collision_lift": lcm_collision_receipt(),
        "greedy_surplus": greedy_surplus_receipt(args.depth),
        "scaled_adjacent_cylinder": scaled_adjacent_cylinder_receipt(
            min(args.depth, 5000)
        ),
        "resolvent_comparison": resolvent_comparison_receipt(),
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
