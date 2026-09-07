#!/usr/bin/env python3
"""Exact receipts for deadline capacity and anchored cylinder contraction."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import lcm


def weight(rank: int) -> Fraction:
    if rank < 1:
        raise ValueError("rank must be positive")
    return Fraction(1, (1 << rank) - 1)


def cylinder(a: int, b: int) -> Fraction:
    return weight(a) * weight(b)


def theta(rank: int, capacity: int) -> Fraction:
    if capacity < 0 or rank - capacity < 1:
        raise ValueError("invalid capacity")
    return sum(
        (
            Fraction(1, 1 << step)
            * cylinder(rank - step, rank - step + 1)
        )
        for step in range(1, capacity + 1)
    )


def protected_packet(rank: int, deadline: int) -> Fraction:
    if not 2 <= deadline <= rank:
        raise ValueError("need 2 <= deadline <= rank")
    return Fraction(1 << deadline, 1 << rank) * weight(deadline)


def residual_lift(a: int, b: int, exponent: int) -> dict[str, object]:
    if not (2 <= a <= b and 0 <= exponent <= b):
        raise ValueError("need 2 <= a <= b and 0 <= exponent <= b")
    capacity = b - exponent
    rank = a + capacity
    block = (1 << exponent) * cylinder(a, b)
    residual = block - weight(rank)
    if residual <= 0:
        raise AssertionError("the first-rank residual must be positive")

    lifted_rank = lcm(b, rank)
    coefficient = residual * ((1 << a) - 1) * ((1 << lifted_rank) - 1)
    if coefficient.denominator != 1:
        raise AssertionError("residual lift coefficient is not integral")
    integer_coefficient = coefficient.numerator
    assert residual == integer_coefficient * cylinder(a, lifted_rank)

    load = Fraction(integer_coefficient, 1 << lifted_rank)
    parent_load = Fraction(1, 1 << capacity)
    ratio = load / parent_load
    proxy = residual * ((1 << a) - 1) * (1 << capacity)
    assert ratio < proxy
    assert proxy == Fraction(
        ((1 << a) + (1 << b) - (1 << exponent) - 1)
        * (1 << capacity),
        ((1 << b) - 1) * ((1 << rank) - 1),
    )
    assert proxy <= Fraction(8, 15)
    assert load < parent_load

    bit_exponents = [
        bit
        for bit in range(integer_coefficient.bit_length())
        if (integer_coefficient >> bit) & 1
    ]
    child_arrivals = [a + lifted_rank - bit for bit in bit_exponents]
    assert all(child_rank > rank for child_rank in child_arrivals)
    assert sum(Fraction(1 << bit, 1 << lifted_rank) for bit in bit_exponents) == load

    return {
        "a": a,
        "b": b,
        "j": exponent,
        "first_rank": rank,
        "capacity": capacity,
        "deadline": a,
        "residual_lift_rank": lifted_rank,
        "residual_coefficient": integer_coefficient,
        "parent_load": str(parent_load),
        "child_load": str(load),
        "exact_proxy": str(proxy),
        "minimum_child_rank": min(child_arrivals) if child_arrivals else None,
        "binary_child_count": len(bit_exponents),
    }


def packet_law_checks(maximum_endpoint: int) -> dict[str, object]:
    checks = 0
    merge_checks = 0
    maximum_proxy = Fraction(0)
    maximum_proxy_case = None
    slowest_load_ratio = Fraction(0)
    slowest_load_case = None

    for a in range(2, maximum_endpoint + 1):
        for b in range(a, maximum_endpoint + 1):
            for exponent in range(0, b + 1):
                capacity = b - exponent
                rank = a + capacity
                block = (1 << exponent) * cylinder(a, b)
                assert weight(rank) + theta(rank, capacity) == Fraction(
                    weight(a), 1 << capacity
                )
                assert protected_packet(rank, a) == (
                    weight(rank) + theta(rank, capacity)
                )
                contracted_copy = Fraction(1, 1 << capacity) * cylinder(a, b)
                assert block == protected_packet(rank, a) + contracted_copy
                assert contracted_copy / block == Fraction(1, 1 << b)
                for depth in range(capacity + 1):
                    assert block > weight(rank) + theta(rank, depth)
                assert block <= Fraction(weight(a - 1), 1 << (capacity + 1))

                receipt = residual_lift(a, b, exponent)
                proxy = Fraction(receipt["exact_proxy"])
                ratio = Fraction(receipt["child_load"]) / Fraction(
                    receipt["parent_load"]
                )
                if proxy > maximum_proxy:
                    maximum_proxy = proxy
                    maximum_proxy_case = (a, b, exponent)
                if ratio > slowest_load_ratio:
                    slowest_load_ratio = ratio
                    slowest_load_case = (a, b, exponent)
                checks += 1

    assert maximum_proxy == Fraction(8, 15)
    assert maximum_proxy_case == (2, 2, 0)
    assert slowest_load_ratio < Fraction(8, 15)

    for rank in range(5, 2 * maximum_endpoint + 1):
        for first_capacity in range(1, rank - 1):
            for second_capacity in range(1, rank - 1):
                first_reserve = theta(rank, first_capacity)
                second_reserve = theta(rank, second_capacity)
                carried_reserve = (
                    first_reserve
                    + second_reserve
                    - cylinder(rank - 1, rank)
                )
                guaranteed = theta(
                    rank - 1,
                    min(first_capacity, second_capacity) - 1,
                )
                assert carried_reserve >= guaranteed
                merge_checks += 1

    return {
        "maximum_endpoint": maximum_endpoint,
        "power_packet_checks": checks,
        "carry_pair_checks": merge_checks,
        "maximum_proxy": str(maximum_proxy),
        "maximum_proxy_case": maximum_proxy_case,
        "slowest_exact_lift_ratio": str(slowest_load_ratio),
        "slowest_exact_lift_case": slowest_load_case,
    }


def protected_carry_checks(maximum_rank: int) -> dict[str, object]:
    checks = 0
    positive_excess_checks = 0
    future_recode_terms = 0
    for rank in range(4, maximum_rank + 1):
        for first_deadline in range(2, rank):
            for second_deadline in range(first_deadline, rank):
                first = protected_packet(rank, first_deadline)
                second = protected_packet(rank, second_deadline)
                carried = protected_packet(rank - 1, second_deadline)
                excess = first + second - carried
                expected = Fraction(1, 1 << rank) * (
                    weight(first_deadline) - weight(second_deadline)
                )
                assert excess == expected
                assert excess >= 0
                if first_deadline == second_deadline:
                    assert excess == 0
                else:
                    lifted_rank = lcm(first_deadline, second_deadline)
                    coefficient = (
                        ((1 << lifted_rank) - 1)
                        // ((1 << first_deadline) - 1)
                        - ((1 << lifted_rank) - 1)
                        // ((1 << second_deadline) - 1)
                    )
                    assert excess == (
                        Fraction(coefficient, 1 << rank)
                        * weight(lifted_rank)
                    )
                    recoded_terms = []
                    recoded_residual = Fraction(0)
                    for exponent_numerator in range(
                        first_deadline,
                        second_deadline,
                    ):
                        term = (
                            Fraction(1 << exponent_numerator, 1 << rank)
                            * cylinder(first_deadline, second_deadline)
                        )
                        dyadic_exponent = exponent_numerator - rank
                        front_rank = (
                            first_deadline
                            + second_deadline
                            - dyadic_exponent
                        )
                        assert front_rank > rank
                        protected = protected_packet(
                            front_rank,
                            first_deadline,
                        )
                        residual = term / (1 << second_deadline)
                        assert term == protected + residual
                        recoded_terms.append(term)
                        recoded_residual += residual
                        future_recode_terms += 1
                    assert sum(recoded_terms, Fraction(0)) == excess
                    assert recoded_residual == excess / (1 << second_deadline)
                    positive_excess_checks += 1
                checks += 1
    return {
        "maximum_rank": maximum_rank,
        "checks": checks,
        "strictly_positive_heterogeneous_excess_checks": positive_excess_checks,
        "future_recode_term_checks": future_recode_terms,
        "law": (
            "P(r,d1)+P(r,d2)=P(r-1,max(d1,d2))"
            "+2^-r*(w_min(d1,d2)-w_max(d1,d2))"
        ),
    }


def collision_kraft_checks(maximum_stop: int) -> dict[str, object]:
    checks = 0
    maximum_required = Fraction(0)
    maximum_case = None
    for stop in range(4, maximum_stop + 1):
        for a in range(2, stop - 1):
            b = stop - a
            if b < 2:
                continue
            for c in range(2, stop - 1):
                d = stop - c
                if d < 2:
                    continue
                endpoints = [a, b, c, d]
                for chosen_index, endpoint in enumerate(endpoints):
                    lifted_rank = lcm(endpoint, stop - 1)
                    coefficient = (
                        ((1 << lifted_rank) - 1) // ((1 << endpoint) - 1)
                        - ((1 << lifted_rank) - 1) // ((1 << (stop - 1)) - 1)
                    )
                    remaining = endpoints[:chosen_index] + endpoints[chosen_index + 1 :]
                    required = Fraction(coefficient, 1 << lifted_rank) + sum(
                        Fraction(1, 1 << item) for item in remaining
                    )
                    assert required < 1
                    if required > maximum_required:
                        maximum_required = required
                        maximum_case = {
                            "stop": stop,
                            "parents": [[a, b], [c, d]],
                            "chosen_endpoint": endpoint,
                            "L": lifted_rank,
                            "A": coefficient,
                        }
                    checks += 1
    return {
        "maximum_stop": maximum_stop,
        "checks": checks,
        "maximum_required_fraction": str(maximum_required),
        "maximum_case": maximum_case,
    }


def hall_condition(deadlines: list[int], arrival: int) -> bool:
    count = len(deadlines)
    for threshold in range(min(deadlines) - 1, arrival + 1):
        restrictive = sum(deadline > threshold for deadline in deadlines)
        shallow_capacity = count % (1 << (arrival - threshold)) if threshold < arrival else 0
        if restrictive > shallow_capacity:
            return False
    return True


def homogeneous_hall_checks(maximum_count: int, maximum_capacity: int) -> dict[str, object]:
    checks = 0
    for capacity in range(maximum_capacity + 1):
        arrival = capacity + 2
        deadline = 2
        for count in range(1, maximum_count + 1):
            expected = count < (1 << (capacity + 1))
            assert hall_condition([deadline] * count, arrival) == expected
            checks += 1
    return {
        "checks": checks,
        "homogeneous_law": "N packets of capacity c are parkable iff N < 2^(c+1)",
    }


def root_receipt() -> dict[str, object]:
    receipt = residual_lift(2, 3, 0)
    assert receipt["first_rank"] == 5
    assert receipt["residual_lift_rank"] == 15
    assert receipt["residual_coefficient"] == 1510
    root_load = Fraction(1, 8)
    geometric_bound = root_load / (1 - Fraction(8, 15))
    assert geometric_bound == Fraction(15, 56)
    return {
        "identity": "M(2,3)-w_5 = 1510*M(2,15)",
        "root_load": str(root_load),
        "first_residual_load": receipt["child_load"],
        "first_residual_minimum_rank": receipt["minimum_child_rank"],
        "formal_geometric_atom_load_bound": str(geometric_bound),
        "boundary": (
            "the geometric bound applies to independently expanded packet fronts; "
            "protected packets solve local reserve ownership, but a global proof "
            "still needs escrow release and fixed-rank stabilization under returning carries"
        ),
    }


def escrow_potential_nogo_checks(series_terms: int = 12) -> dict[str, object]:
    root = cylinder(2, 3)
    protected_sum = sum(
        protected_packet(2 + 3 * index, 2)
        for index in range(1, series_terms + 1)
    )
    exact_tail = Fraction(1, 1 << (3 * series_terms)) * root
    assert root == protected_sum + exact_tail

    carry_checks = 0
    for rank in range(4, 40):
        for first_deadline in range(2, rank):
            for second_deadline in range(first_deadline, rank):
                first_escrow_load = Fraction(
                    rank - first_deadline,
                    1 << (rank + 1),
                )
                second_escrow_load = Fraction(
                    rank - second_deadline,
                    1 << (rank + 1),
                )
                output_escrow_load = Fraction(
                    rank - 1 - second_deadline,
                    1 << rank,
                )
                if first_deadline == second_deadline:
                    active_excess_load = Fraction(0)
                else:
                    active_excess_load = Fraction(1, 1 << rank) * (
                        1
                        - Fraction(
                            1,
                            1 << (second_deadline - first_deadline),
                        )
                    )
                assert (
                    output_escrow_load + active_excess_load
                    <= first_escrow_load + second_escrow_load
                )
                carry_checks += 1

    a, b, exponent = 2, 9, 0
    capacity = b - exponent
    rank = a + capacity
    active_before = Fraction(1, 1 << capacity)
    active_after = Fraction(1, 1 << (capacity + b))
    escrow_load = Fraction(capacity, 1 << (rank + 1))
    alpha_upper = (active_before - active_after) / escrow_load
    assert alpha_upper == Fraction(511, 576)
    assert alpha_upper < 1
    return {
        "root_protected_series_terms": series_terms,
        "root_partial_sum_identity": (
            "M(2,3)=sum_(k=1..K) P(2+3k,2)+2^(-3K)M(2,3)"
        ),
        "active_plus_escrow_carry_checks": carry_checks,
        "reachable_counterexample_path": (
            "M(2,3)->M(2,5)->M(2,7)->M(2,9)"
        ),
        "release_requires_alpha_at_least": "1",
        "parking_M_2_9_requires_alpha_at_most": str(alpha_upper),
        "gamma_disjoint_label_no_go": {
            "root_front_required_label": "1",
            "root_residual_required_label": "1/8",
            "disjoint_total_required": "9/8",
            "heterogeneous_carry_boundary": (
                "two sharp parent labels are exhausted by the carried front; "
                "positive excess requires overlap or loses Gamma>=5"
            ),
        },
        "conclusion": (
            "no constant alpha makes natural active-load plus releasable-escrow "
            "load nonincreasing under both park and release"
        ),
    }


def exact_bank_depth(endpoint: int, stop: int) -> int:
    depth = 0
    while stop - depth - 1 >= 2:
        candidate = depth + 1
        if cylinder(endpoint, stop) <= cylinder(
            stop - candidate,
            stop - candidate + 1,
        ):
            break
        depth = candidate
    return depth


def banked_batch_checks(maximum_stop: int) -> dict[str, object]:
    domination_checks = 0
    height_checks = 0
    for a in range(2, maximum_stop + 1):
        for b in range(2, maximum_stop + 1):
            for c in range(a, maximum_stop + 1):
                for d in range(b, maximum_stop + 1):
                    if (a, b) == (c, d):
                        continue
                    larger = cylinder(a, b)
                    smaller = cylinder(c, d)
                    if larger <= smaller:
                        continue
                    first_lift = lcm(a, c)
                    second_lift = lcm(b, d)
                    coefficient = (
                        ((1 << first_lift) - 1) // ((1 << a) - 1)
                        * ((1 << second_lift) - 1) // ((1 << b) - 1)
                        - ((1 << first_lift) - 1) // ((1 << c) - 1)
                        * ((1 << second_lift) - 1) // ((1 << d) - 1)
                    )
                    assert coefficient > 0
                    assert larger - smaller == (
                        coefficient * cylinder(first_lift, second_lift)
                    )
                    effective_height = (
                        first_lift
                        + second_lift
                        - (coefficient.bit_length() - 1)
                    )
                    assert effective_height >= a + b
                    domination_checks += 1
                    height_checks += 1

    sufficient_depth_checks = 0
    for stop in range(5, 2 * maximum_stop + 1):
        for endpoint in range(2, stop - 1):
            for tax_depth in range(1, stop - 1):
                if 2 * tax_depth <= stop - endpoint - 1:
                    assert cylinder(endpoint, stop) > cylinder(
                        stop - tax_depth,
                        stop - tax_depth + 1,
                    )
                    sufficient_depth_checks += 1

    pooled_checks = 0
    maximum_pooled_ratio = Fraction(0)
    maximum_pooled_case = None
    for a in range(2, maximum_stop + 1):
        for b in range(a, maximum_stop + 1):
            stop = a + b
            for exponent in range(0, b + 1):
                front_rank = stop - exponent
                tax = weight(front_rank) - (1 << exponent) * weight(stop)
                assert tax >= 0
                pooled_bank_residual = (
                    (1 << exponent) * cylinder(a, stop) - tax
                )
                assert pooled_bank_residual == (
                    (1 << (a + exponent)) * cylinder(a, stop)
                    - weight(front_rank)
                )
                assert pooled_bank_residual > 0
                assert (
                    (1 << exponent) * cylinder(a, b)
                    == weight(front_rank)
                    + pooled_bank_residual
                    + (1 << exponent) * cylinder(stop, b)
                )

                residual_receipt = residual_lift(
                    a,
                    stop,
                    a + exponent,
                )
                assert residual_receipt["first_rank"] == front_rank
                parent_load = Fraction(1, 1 << (b - exponent))
                residual_load = Fraction(residual_receipt["child_load"])
                other_load = Fraction(1, 1 << (stop - exponent))
                ratio = (residual_load + other_load) / parent_load
                assert ratio < Fraction(8, 15) + Fraction(1, 1 << a)
                assert ratio < Fraction(47, 60)
                assert residual_receipt["minimum_child_rank"] > front_rank
                assert b + stop - exponent > front_rank
                if ratio > maximum_pooled_ratio:
                    maximum_pooled_ratio = ratio
                    maximum_pooled_case = (a, b, exponent)
                pooled_checks += 1

    generated_depth = exact_bank_depth(10, 21)
    assert generated_depth == 6
    assert generated_depth < 8
    generated_parent = (1 << 8) * cylinder(10, 11)
    generated_tax = weight(13) - (1 << 8) * weight(21)
    generated_pooled_residual = (1 << 8) * cylinder(10, 21) - generated_tax
    assert generated_pooled_residual > 0
    assert generated_parent == (
        weight(13)
        + generated_pooled_residual
        + (1 << 8) * cylinder(21, 11)
    )
    return {
        "maximum_endpoint": maximum_stop,
        "general_cylinder_difference_checks": domination_checks,
        "future_height_checks": height_checks,
        "sufficient_depth_checks": sufficient_depth_checks,
        "pooled_power_packet_checks": pooled_checks,
        "maximum_pooled_residual_load_ratio": str(maximum_pooled_ratio),
        "maximum_pooled_ratio_case": maximum_pooled_case,
        "generated_340_cohort": {
            "cylinder": "M(10,11)",
            "stop": 21,
            "multiplicity": 340,
            "exact_bank_depth": generated_depth,
            "largest_single_power_batch": 1 << generated_depth,
            "full_256_batch_depth_needed": 8,
            "individual_bank_assignment_supports_full_batch": False,
            "pooled_bank_tax_is_positive": True,
            "pooled_full_rewrite": (
                "256*M(10,11)=w_13+D_(10,21,18)+256*M(21,11)"
            ),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--maximum-endpoint", type=int, default=24)
    parser.add_argument("--maximum-count", type=int, default=300)
    parser.add_argument("--maximum-capacity", type=int, default=12)
    args = parser.parse_args()
    if args.maximum_endpoint < 3:
        raise SystemExit("maximum endpoint must be at least 3")
    output = {
        "theta_identity": "w_(r-c)/2^c = w_r + Theta_(r,c)",
        "capacity_law": (
            "for 2^j*M(a,b), a<=b, the exact maximum certified depth is "
            "c=b-j and the deadline is a"
        ),
        "checks": packet_law_checks(args.maximum_endpoint),
        "collision_kraft_allocation": collision_kraft_checks(
            2 * args.maximum_endpoint
        ),
        "protected_packet_carries": protected_carry_checks(
            2 * args.maximum_endpoint
        ),
        "fixed_rank_hall": homogeneous_hall_checks(
            args.maximum_count,
            args.maximum_capacity,
        ),
        "root": root_receipt(),
        "escrow_potential_no_go": escrow_potential_nogo_checks(),
        "literal_banked_batches": banked_batch_checks(
            min(args.maximum_endpoint, 14)
        ),
        "claim_status": (
            "theta, packet capacity, exact anchored residual lift, and the 8/15 "
            "proxy bound are algebraic; the protected packet split, heterogeneous "
            "carry excess, future-directed excess recoding, and pooled bank rewrite "
            "are exact. Finite loops audit instances and fixed-rank Hall. Escrow "
            "release and global rank stabilization remain open."
        ),
    }
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
