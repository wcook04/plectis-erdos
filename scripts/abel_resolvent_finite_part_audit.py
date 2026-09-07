#!/usr/bin/env python3
"""Exact audit of the Abel finite part of the future-divisor resolvent."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction


def fraction_receipt(value: Fraction) -> dict[str, object]:
    numerator_text = str(abs(value.numerator))
    denominator_text = str(value.denominator)
    if len(numerator_text) + len(denominator_text) > 300:
        return {
            "sign": -1 if value < 0 else (1 if value > 0 else 0),
            "numerator_decimal_digits": len(numerator_text),
            "denominator_decimal_digits": len(denominator_text),
            "exact_omitted_from_display": True,
        }
    return {
        "exact": str(value),
        "approx": float(value),
    }


def integer_receipt(value: int) -> int | dict[str, object]:
    text = str(abs(value))
    if len(text) <= 120:
        return value
    return {
        "sign": -1 if value < 0 else (1 if value > 0 else 0),
        "decimal_digits": len(text),
        "exact_omitted_from_display": True,
    }


def source_digits(target: Fraction, depth: int) -> list[int]:
    residue = target.numerator % target.denominator
    digits = [0] * (depth + 1)
    for rank in range(1, depth + 1):
        residue *= 2
        digits[rank] = residue // target.denominator
        residue %= target.denominator
    return digits


def directed_greedy_bits(target: Fraction, depth: int) -> list[int]:
    precision = 2 * depth + 128
    scale = 1 << precision
    lower = scale * target.numerator // target.denominator
    upper = (
        scale * target.numerator + target.denominator - 1
    ) // target.denominator
    bits = [0] * (depth + 1)
    for rank in range(1, depth + 1):
        weight_floor = scale // ((1 << rank) - 1)
        if lower >= weight_floor + 1:
            bits[rank] = 1
            lower -= weight_floor + 1
            upper -= weight_floor
        elif upper <= weight_floor:
            continue
        else:
            raise AssertionError(f"ambiguous greedy decision at rank {rank}")
    return bits


def orbit_states(
    bits: list[int],
    source: list[int],
    allowance: int,
) -> dict[str, list[int]]:
    depth = len(bits) - 1
    prefix = [0] * (depth + 1)
    source_prefix = [0] * (depth + 1)
    divisor_load = [0] * (depth + 1)
    for rank in range(1, depth + 1):
        prefix[rank] = prefix[rank - 1] + bits[rank]
        source_prefix[rank] = source_prefix[rank - 1] + source[rank]
        if bits[rank]:
            for multiple in range(rank, depth + 1, rank):
                divisor_load[multiple] += 1
    defect = [0] * (depth + 1)
    energy = [allowance] * (depth + 1)
    for rank in range(1, depth + 1):
        defect[rank] = (
            2 * defect[rank - 1] + source[rank] - divisor_load[rank]
        )
        endpoint_count = (
            source_prefix[rank]
            + prefix[rank // 2]
            - prefix[rank]
        )
        energy[rank] = endpoint_count + allowance - 2 * defect[rank]
    return {
        "prefix": prefix,
        "source_prefix": source_prefix,
        "divisor_load": divisor_load,
        "defect": defect,
        "energy": energy,
    }


def direct_finite_part(bits: list[int], radius: int) -> Fraction:
    value = Fraction()
    for rank in range(1, radius + 1):
        if not bits[rank]:
            continue
        residue = (2 * radius) % rank
        value += (
            Fraction(residue, rank)
            - Fraction(1, 2)
            - Fraction(1, 2 * rank)
        )
    return value


def divisor_capacity(bits: list[int], radius: int) -> int:
    return sum(
        bits[rank] * ((2 * radius) // rank)
        for rank in range(1, radius + 1)
    )


def future_count(bits: list[int], radius: int, offset: int) -> int:
    return sum(
        bits[rank]
        for rank in range(1, radius + 1)
        if (2 * radius + offset) % rank == 0
    )


def row_receipt(row: dict[str, object]) -> dict[str, object]:
    return {
        "R": row["R"],
        "even_horizon": 2 * row["R"],
        "F_even": integer_receipt(row["F"]),
        "selected_count": row["count"],
        "A_R": fraction_receipt(row["A"]),
        "finite_part_B_R": fraction_receipt(row["B"]),
        "smooth_service_C_R": fraction_receipt(row["C"]),
        "J_R": fraction_receipt(row["J"]),
        "cumulative_Q": integer_receipt(row["sum_Q"]),
    }


def analyse_support(
    name: str,
    bits: list[int],
    source: list[int],
    allowance: int,
    direct_check_radius: int,
    support_status: str,
) -> dict[str, object]:
    depth = len(bits) - 1
    states = orbit_states(bits, source, allowance)
    defect = states["defect"]
    energy = states["energy"]
    maximum_radius = depth // 2

    rows: list[dict[str, object]] = [
        {
            "R": 0,
            "A": Fraction(),
            "count": 0,
            "C": Fraction(),
            "D": 0,
            "B": Fraction(),
            "sum_Q": 0,
            "J": Fraction(allowance),
            "K": Fraction(allowance),
            "upper_B": Fraction(),
            "F": allowance,
        }
    ]
    reciprocal_mass = Fraction()
    selected_count = 0
    cumulative_defect = 0
    direct_checks = 0
    floor_reconstruction_checks = 0
    potential_identity_checks = 0
    capacity = 0

    for radius in range(1, maximum_radius + 1):
        if bits[radius]:
            reciprocal_mass += Fraction(1, radius)
            selected_count += 1
        cumulative_defect += defect[2 * radius - 1] + defect[2 * radius]
        smooth_service = (
            Fraction(4 * radius - 1, 2) * reciprocal_mass
            - Fraction(selected_count, 2)
        )
        odd_horizon = 2 * radius - 1
        even_horizon = 2 * radius
        nu_previous_one = (
            states["divisor_load"][odd_horizon] - bits[odd_horizon]
        )
        nu_previous_two = (
            states["divisor_load"][even_horizon]
            - bits[even_horizon]
            - bits[radius]
        )
        capacity += nu_previous_one + nu_previous_two + 2 * bits[radius]
        if (
            radius <= direct_check_radius
            and capacity != divisor_capacity(bits, radius)
        ):
            raise AssertionError(f"direct capacity identity failed for {name}")
        finite_part = smooth_service - capacity
        upper_finite_part = (
            Fraction(selected_count, 2)
            - Fraction(3, 2) * reciprocal_mass
        )
        if finite_part > upper_finite_part:
            raise AssertionError(f"finite-part upper bound failed for {name}")
        if radius <= direct_check_radius:
            if direct_finite_part(bits, radius) != finite_part:
                raise AssertionError(
                    f"direct finite-part identity failed for {name} at R={radius}"
                )
            direct_checks += 1

        # Per-clock Abel finite part plus pole mass reconstructs the floor.
        if radius <= direct_check_radius:
            for rank in range(1, radius + 1):
                if not bits[rank]:
                    continue
                residue = (2 * radius) % rank
                clock_finite_part = (
                    Fraction(residue, rank)
                    - Fraction(1, 2)
                    - Fraction(1, 2 * rank)
                )
                clock_smooth_service = (
                    Fraction(4 * radius - 1, 2 * rank)
                    - Fraction(1, 2)
                )
                if (
                    clock_smooth_service - clock_finite_part
                    != (2 * radius) // rank
                ):
                    raise AssertionError("per-clock floor reconstruction failed")
                floor_reconstruction_checks += 1

        potential = Fraction(allowance) + smooth_service - cumulative_defect
        if potential != energy[2 * radius] + finite_part:
            raise AssertionError(f"potential identity failed for {name}")
        if (
            potential - smooth_service
            != Fraction(allowance - cumulative_defect)
        ):
            raise AssertionError(f"centred potential identity failed for {name}")
        potential_identity_checks += 1
        rows.append(
            {
                "R": radius,
                "A": reciprocal_mass,
                "count": selected_count,
                "C": smooth_service,
                "D": capacity,
                "B": finite_part,
                "sum_Q": cumulative_defect,
                "J": potential,
                "K": potential - smooth_service,
                "upper_B": upper_finite_part,
                "F": energy[2 * radius],
            }
        )

    transport_checks = 0
    first_negative_drift: dict[str, object] | None = None
    for radius in range(0, maximum_radius):
        current = rows[radius]
        following = rows[radius + 1]
        nu_one = (
            states["divisor_load"][2 * radius + 1]
            - bits[2 * radius + 1]
        )
        nu_two = (
            states["divisor_load"][2 * radius + 2]
            - bits[2 * radius + 2]
            - bits[radius + 1]
        )
        insertion = bits[radius + 1]
        expected_finite_difference = (
            2 * current["A"]
            - nu_one
            - nu_two
            - Fraction(
                insertion * (radius + 2),
                2 * (radius + 1),
            )
        )
        if following["B"] - current["B"] != expected_finite_difference:
            raise AssertionError(f"finite-part transport failed for {name}")

        gamma = Fraction(3 * radius + 2, 2 * (radius + 1))
        quotient_demand = defect[2 * radius + 1] + defect[2 * radius + 2]
        expected_potential_difference = (
            2 * current["A"] + gamma * insertion - quotient_demand
        )
        actual_potential_difference = following["J"] - current["J"]
        if actual_potential_difference != expected_potential_difference:
            raise AssertionError(f"potential transport failed for {name}")
        if first_negative_drift is None and actual_potential_difference < 0:
            first_negative_drift = {
                "from_R": radius,
                "to_R": radius + 1,
                "quotient_demand": quotient_demand,
                "nu_R_1": nu_one,
                "nu_R_2": nu_two,
                "inserted_bit": insertion,
                "drift": fraction_receipt(actual_potential_difference),
            }
        transport_checks += 1

    first_negative_energy = next(
        (
            {"rank": rank, "F": energy[rank], "Q": defect[rank]}
            for rank in range(depth + 1)
            if energy[rank] < 0
        ),
        None,
    )
    first_negative_potential = next(
        (row_receipt(row) for row in rows if row["J"] < 0),
        None,
    )
    first_positive_finite_part = next(
        (row_receipt(row) for row in rows if row["B"] > 0),
        None,
    )
    first_failure_of_mass_only_sufficient_bound = next(
        (
            {
                **row_receipt(row),
                "upper_bound_for_B_R": fraction_receipt(row["upper_B"]),
                "J_minus_upper_bound": fraction_receipt(
                    row["J"] - row["upper_B"]
                ),
            }
            for row in rows
            if row["J"] < row["upper_B"]
        ),
        None,
    )
    minimum_potential_row = min(rows, key=lambda row: (row["J"], row["R"]))
    minimum_energy = min((value, rank) for rank, value in enumerate(energy))

    harmonic_mass = Fraction()
    harmonic_count = 0
    cumulative_defect_all = 0
    previous_mass_potential = Fraction(allowance)
    minimum_mass_potential: tuple[Fraction, int, Fraction, int, int] = (
        previous_mass_potential,
        0,
        harmonic_mass,
        harmonic_count,
        cumulative_defect_all,
    )
    first_negative_mass_potential: dict[str, object] | None = None
    first_negative_mass_drift: dict[str, object] | None = None
    minimum_positive_mass_potential: tuple[Fraction, dict[str, object]] | None = None
    mass_potential_zero_ranks: list[int] = [0] if allowance == 0 else []
    mass_potential_values: list[Fraction] = [Fraction(allowance)]
    mass_potential_checks = 0
    for rank in range(1, depth + 1):
        previous_harmonic_mass = harmonic_mass
        if rank % 2 == 0:
            radius = rank // 2
            if bits[radius]:
                harmonic_mass += Fraction(1, radius)
                harmonic_count += 1
        else:
            radius = rank // 2
        cumulative_defect_all += defect[rank]
        mass_potential = (
            Fraction(allowance)
            + (rank + 1) * harmonic_mass
            - harmonic_count
            - cumulative_defect_all
        )
        if rank % 2:
            expected_drift = harmonic_mass - defect[rank]
        else:
            expected_drift = (
                previous_harmonic_mass
                + bits[radius] * (1 + Fraction(1, radius))
                - defect[rank]
            )
        if mass_potential - previous_mass_potential != expected_drift:
            raise AssertionError(f"mass-potential recurrence failed for {name}")
        if mass_potential > energy[rank]:
            raise AssertionError(f"mass potential exceeded energy for {name}")
        if rank % 2 == 0:
            even_row = rows[rank // 2]
            if mass_potential != even_row["J"] - even_row["upper_B"]:
                raise AssertionError(
                    f"even Abel/mass potential identity failed for {name}"
                )
        if rank <= 2 * direct_check_radius:
            direct_capacity = sum(
                bits[divisor] * (rank // divisor)
                for divisor in range(1, rank // 2 + 1)
            )
            lower_capacity = (rank + 1) * harmonic_mass - harmonic_count
            if direct_capacity - lower_capacity != energy[rank] - mass_potential:
                raise AssertionError(
                    f"direct mass-potential slack failed for {name}"
                )
        if mass_potential == 0:
            mass_potential_zero_ranks.append(rank)
        receipt = {
            "rank": rank,
            "F": integer_receipt(energy[rank]),
            "Q": integer_receipt(defect[rank]),
            "A_floor_half": fraction_receipt(harmonic_mass),
            "selected_count_floor_half": harmonic_count,
            "cumulative_Q": integer_receipt(cumulative_defect_all),
            "mass_potential": fraction_receipt(mass_potential),
        }
        if first_negative_mass_potential is None and mass_potential < 0:
            first_negative_mass_potential = receipt
        if first_negative_mass_drift is None and expected_drift < 0:
            first_negative_mass_drift = {
                **receipt,
                "drift": fraction_receipt(expected_drift),
            }
        if mass_potential > 0 and (
            minimum_positive_mass_potential is None
            or mass_potential < minimum_positive_mass_potential[0]
        ):
            minimum_positive_mass_potential = (mass_potential, receipt)
        candidate = (
            mass_potential,
            rank,
            harmonic_mass,
            harmonic_count,
            cumulative_defect_all,
        )
        if candidate[:2] < minimum_mass_potential[:2]:
            minimum_mass_potential = candidate
        previous_mass_potential = mass_potential
        mass_potential_values.append(mass_potential)
        mass_potential_checks += 1

    minimum_mass_receipt = {
        "rank": minimum_mass_potential[1],
        "A_floor_half": fraction_receipt(minimum_mass_potential[2]),
        "selected_count_floor_half": minimum_mass_potential[3],
        "cumulative_Q": integer_receipt(minimum_mass_potential[4]),
        "mass_potential": fraction_receipt(minimum_mass_potential[0]),
    }
    first_negative_nine_step_drift = next(
        (
            {
                "from_rank": rank - 9,
                "to_rank": rank,
                "drift": fraction_receipt(
                    mass_potential_values[rank]
                    - mass_potential_values[rank - 9]
                ),
            }
            for rank in range(9, depth + 1)
            if mass_potential_values[rank] < mass_potential_values[rank - 9]
        ),
        None,
    )

    return {
        "name": name,
        "depth": depth,
        "allowance": allowance,
        "support_status": support_status,
        "first_negative_energy": first_negative_energy,
        "minimum_energy": {
            "F": integer_receipt(minimum_energy[0]),
            "rank": minimum_energy[1],
        },
        "first_negative_Abel_potential": first_negative_potential,
        "minimum_Abel_potential": row_receipt(minimum_potential_row),
        "first_positive_finite_part": first_positive_finite_part,
        "first_failure_of_mass_only_sufficient_bound": (
            first_failure_of_mass_only_sufficient_bound
        ),
        "first_negative_Abel_drift": first_negative_drift,
        "harmonic_mass_sufficient_potential": {
            "formula": (
                "allowance+(N+1)*A_floor(N/2)-Bcount(floor(N/2))"
                "-sum_(j<=N)Q_j"
            ),
            "first_negative": first_negative_mass_potential,
            "minimum": minimum_mass_receipt,
            "minimum_positive": (
                minimum_positive_mass_potential[1]
                if minimum_positive_mass_potential is not None
                else None
            ),
            "zero_ranks": mass_potential_zero_ranks,
            "first_negative_one_step_drift": first_negative_mass_drift,
            "first_negative_nine_step_drift": first_negative_nine_step_drift,
            "implication": "nonnegative potential implies nonnegative F_N",
            "claim_status": "finite audit only",
        },
        "checks": {
            "direct_finite_part": direct_checks,
            "per_clock_floor_reconstruction": floor_reconstruction_checks,
            "potential_identity": potential_identity_checks,
            "transport": transport_checks,
            "mass_potential": mass_potential_checks,
        },
    }


def directed_mass_potential_certificate(
    target: Fraction,
    depth: int,
    allowance: int,
    precision: int = 160,
) -> dict[str, object]:
    bits = directed_greedy_bits(target, depth)
    source = source_digits(target, depth)
    states = orbit_states(bits, source, allowance)
    defect = states["defect"]
    scale = 1 << precision
    lower_harmonic_mass = 0
    selected_count = 0
    cumulative_defect = 0
    zero_ranks: list[int] = []
    first_uncertified: dict[str, object] | None = None
    for rank in range(1, depth + 1):
        if rank % 2 == 0:
            radius = rank // 2
            if bits[radius]:
                lower_harmonic_mass += scale // radius
                selected_count += 1
        cumulative_defect += defect[rank]
        lower_numerator = (
            allowance * scale
            + (rank + 1) * lower_harmonic_mass
            - scale * (selected_count + cumulative_defect)
        )
        if lower_numerator == 0:
            zero_ranks.append(rank)
        elif lower_numerator < 0 and first_uncertified is None:
            # A negative directed lower bound need not mean that the exact
            # potential is negative.  Record it rather than promoting it.
            first_uncertified = {
                "rank": rank,
                "lower_numerator": lower_numerator,
            }
    return {
        "depth": depth,
        "dyadic_precision_bits": precision,
        "zero_lower_bound_ranks": zero_ranks,
        "first_uncertified_rank": first_uncertified,
        "strictly_positive_lower_bound_after_rank_5": (
            first_uncertified is None
            and all(rank <= 5 for rank in zero_ranks)
        ),
        "claim_status": (
            "directed dyadic lower bound on harmonic mass; finite range only"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=1000)
    parser.add_argument("--direct-check-radius", type=int, default=80)
    parser.add_argument("--deep-90-depth", type=int, default=0)
    args = parser.parse_args()
    if args.depth < 128:
        raise SystemExit("--depth must be at least 128")

    one_twenty_one = Fraction(1, 21)
    perturbed = one_twenty_one - Fraction(1, 3 * (1 << 63))
    ninety = Fraction(90, 511)
    seventeen = Fraction(17, 511)

    cases: list[dict[str, object]] = []
    for name, target, allowance in (
        ("actual_1_over_21", one_twenty_one, 4),
        ("same_cylinder_x_minus", perturbed, 4),
        ("actual_90_over_511", ninety, 0),
        ("recut_tail_17_over_511", seventeen, 0),
    ):
        cases.append(
            analyse_support(
                name=name,
                bits=directed_greedy_bits(target, args.depth),
                source=source_digits(target, args.depth),
                allowance=allowance,
                direct_check_radius=args.direct_check_radius,
                support_status="certified greedy prefix by directed dyadic enclosure",
            )
        )

    cofinite_bits = [0] * (args.depth + 1)
    for rank in range(6, args.depth + 1):
        cofinite_bits[rank] = 1
    cases.append(
        analyse_support(
            name="fixed_source_cofinite_A6",
            bits=cofinite_bits,
            source=source_digits(one_twenty_one, args.depth),
            allowance=4,
            direct_check_radius=args.direct_check_radius,
            support_status=(
                "quotient-admissible cofinite countermodel for the 1/21 source; "
                "not its greedy support"
            ),
        )
    )

    output = {
        "finite_part_per_clock": (
            "FP[z^rho/(1-z^d)] = (d-1-2*rho)/(2d) "
            "= ((2R mod d)/d)-1/2-1/(2d)"
        ),
        "finite_part_transport": (
            "B_(R+1)-B_R = 2*A_R-nu_R(1)-nu_R(2) "
            "-b_(R+1)*(R+2)/(2*(R+1))"
        ),
        "equal_weight_result": (
            "the two consumed coefficients enter the finite-part transport "
            "with equal coefficient -1"
        ),
        "collapse_identity": (
            "C_R-B_R=D_(2R), where "
            "C_R=((4R-1)/2)*A_R-Bcount(R)/2"
        ),
        "claim_status": (
            "exact identities and finite adversarial audits; "
            "no all-depth endpoint-energy proof"
        ),
        "cases": cases,
    }
    if args.deep_90_depth:
        if args.deep_90_depth < args.depth:
            raise SystemExit("--deep-90-depth must be at least --depth")
        output["deep_90_harmonic_mass_certificate"] = (
            directed_mass_potential_certificate(
                target=ninety,
                depth=args.deep_90_depth,
                allowance=0,
            )
        )
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
