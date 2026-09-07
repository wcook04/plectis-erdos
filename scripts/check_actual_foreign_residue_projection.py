#!/usr/bin/env python3
"""Exact-arithmetic fixtures for the actual foreign-residue projection.

This is a research receipt generator, not Lean proof authority.  It checks the
finite algebra behind docs/formal_math/
erdos249_actual_foreign_residue_projection_receipt_2026_07_11.md using only
fractions and emits a machine-readable separation certificate candidate.
"""

from __future__ import annotations

problem_id = "erdos_249"

import argparse
import hashlib
import json
import math
import random
import sys
from functools import lru_cache
from fractions import Fraction

try:
    import sympy
except ImportError:  # Optional: only the large LCM mode needs fast factoring.
    sympy = None

sys.set_int_max_str_digits(0)


@lru_cache(maxsize=None)
def moebius(n: int) -> int:
    if n <= 0:
        raise ValueError("moebius expects a positive integer")
    value = n
    parity = 0
    prime = 2
    while prime * prime <= value:
        if value % prime == 0:
            value //= prime
            parity += 1
            if value % prime == 0:
                return 0
            while value % prime == 0:
                value //= prime
        prime += 1
    if value > 1:
        parity += 1
    return -1 if parity % 2 else 1


@lru_cache(maxsize=None)
def totient(n: int) -> int:
    if n == 0:
        return 0
    result = n
    value = n
    prime = 2
    while prime * prime <= value:
        if value % prime == 0:
            result -= result // prime
            while value % prime == 0:
                value //= prime
        prime += 1
    if value > 1:
        result -= result // value
    return result


def residue_offset(d: int, n: int) -> int:
    """The representative a_d(N) in {1, ..., d}."""
    return d - n % d


def kappa(d: int, n: int) -> Fraction:
    a = residue_offset(d, n)
    mersenne = 2**d - 1
    return (
        moebius(d)
        * 2 ** (d - a)
        * (Fraction(n + a, d * mersenne) + Fraction(1, mersenne**2))
    )


def residue_increment(d: int, height: int) -> Fraction:
    return kappa(d, 2 * height) - kappa(d, height)


def explicit_shadow(height: int) -> Fraction:
    return sum(
        (
            Fraction(height * moebius(d), d * (2**d - 1))
            for d in range(1, height + 1)
            if height % d == 0
        ),
        Fraction(),
    )


def projected_foreign_defect(height: int, cutoff: int) -> Fraction:
    return sum(
        (
            residue_increment(d, height)
            for d in range(1, cutoff + 1)
            if height % d != 0
        ),
        Fraction(),
    )


def complement_bound(height: int, cutoff: int) -> Fraction:
    if cutoff < 2 * height:
        raise ValueError("the closed complement bound requires cutoff >= 2 * height")
    coefficient = 2**height * (2**height - 1)
    return coefficient * (
        Fraction(2, 2**cutoff) + Fraction(4, 3 * 4**cutoff)
    )


def diagonal_coefficient(height: int) -> int:
    return 2**height * (2**height - 1)


@lru_cache(maxsize=None)
def totient_prefix(n: int) -> int:
    if n == 0:
        return totient(0)
    return 2 * totient_prefix(n - 1) + totient(n)


def diagonal_prefix_correction(height: int) -> int:
    return totient_prefix(height) - totient_prefix(2 * height)


@lru_cache(maxsize=None)
def mobius_linear_partial(cutoff: int) -> Fraction:
    if cutoff == 0:
        return Fraction()
    return mobius_linear_partial(cutoff - 1) + Fraction(
        moebius(cutoff), 2**cutoff - 1
    )


@lru_cache(maxsize=None)
def mobius_square_partial(cutoff: int) -> Fraction:
    if cutoff == 0:
        return Fraction(1, 2)
    return mobius_square_partial(cutoff - 1) + Fraction(
        moebius(cutoff), (2**cutoff - 1) ** 2
    )


def lambert_projected_diagonal(height: int, cutoff: int) -> Fraction:
    return diagonal_prefix_correction(height) + diagonal_coefficient(height) * (
        mobius_square_partial(cutoff)
    )


def first_lambert_tail_correction(cutoff: int) -> Fraction:
    return Fraction(1, 2) - mobius_linear_partial(cutoff)


def crude_square_bound(height: int, cutoff: int) -> Fraction:
    return Fraction(4 * diagonal_coefficient(height), 3 * 4**cutoff)


def sharp_square_bound(height: int, cutoff: int) -> Fraction:
    return Fraction(
        4 * diagonal_coefficient(height), 3 * (2 ** (cutoff + 1) - 1) ** 2
    )


def truncated_tail(n: int, terms: int) -> Fraction:
    return sum(
        (Fraction(totient(n + j), 2**j) for j in range(1, terms + 1)),
        Fraction(),
    )


def direct_diagonal_error_bound(height: int, terms: int) -> Fraction:
    # Sum of the two standard totient-tail remainder bounds.
    return Fraction((2 * height + terms + 2) + (height + terms + 2), 2**terms)


def distance_to_integer(value: Fraction) -> Fraction:
    floor_value = value.numerator // value.denominator
    return min(value - floor_value, floor_value + 1 - value)


def fraction_json(value: Fraction) -> dict[str, object]:
    try:
        decimal: float | None = float(value)
    except OverflowError:
        decimal = None
    return {
        "numerator": value.numerator,
        "denominator": value.denominator,
        "decimal": decimal,
    }


def build_receipt(height: int, cutoff: int, terms: int) -> dict[str, object]:
    if height <= 0:
        raise ValueError("height must be positive")
    if terms <= cutoff:
        raise ValueError("terms must exceed cutoff")

    shadow = explicit_shadow(height)
    projection = projected_foreign_defect(height, cutoff)
    epsilon = complement_bound(height, cutoff)
    projected_diagonal = shadow + projection
    separation = distance_to_integer(projected_diagonal)

    divisor_increment = sum(
        (
            residue_increment(d, height)
            for d in range(1, height + 1)
            if height % d == 0
        ),
        Fraction(),
    )
    large_channel_checks = []
    coefficient = 2**height * (2**height - 1)
    for d in range(cutoff + 1, cutoff + 17):
        mersenne = 2**d - 1
        closed_form = Fraction(
            moebius(d) * coefficient * (mersenne + 1), mersenne**2
        )
        large_channel_checks.append(residue_increment(d, height) == closed_form)

    diagonal_truncated = truncated_tail(2 * height, terms) - truncated_tail(height, terms)
    foreign_truncated = diagonal_truncated - shadow
    observed_complement = foreign_truncated - projection
    direct_error = direct_diagonal_error_bound(height, terms)
    consistency_bound = epsilon + direct_error

    return {
        "schema": "actual_foreign_residue_projection_fixture_v0",
        "proof_authority": "exact_fixture_not_lean_proof_authority",
        "height": height,
        "cutoff": cutoff,
        "tail_terms": terms,
        "preconditions": {
            "height_positive": height > 0,
            "cutoff_ge_twice_height": cutoff >= 2 * height,
            "tail_terms_gt_cutoff": terms > cutoff,
        },
        "exact_checks": {
            "divisor_channels_sum_to_explicit_shadow": divisor_increment == shadow,
            "large_channel_closed_form_all": all(large_channel_checks),
            "truncated_consistency_within_proved_bounds": abs(observed_complement)
            <= consistency_bound,
        },
        "values": {
            "explicit_shadow": fraction_json(shadow),
            "projected_foreign_defect": fraction_json(projection),
            "projected_diagonal": fraction_json(projected_diagonal),
            "distance_to_integer": fraction_json(separation),
            "foreign_complement_bound": fraction_json(epsilon),
            "direct_tail_error_bound": fraction_json(direct_error),
            "observed_truncated_complement": fraction_json(observed_complement),
        },
        "finite_nonintegrality_certificate": separation > epsilon,
        "lean_reentry_target":
            "Erdos257PeriodNoncollapse.ActualForeignResidueProjection",
    }


def build_resummed_receipt(height: int, cutoff: int) -> dict[str, object]:
    if height <= 0:
        raise ValueError("height must be positive")
    if cutoff < 2 * height:
        raise ValueError("resummed residue comparison requires cutoff >= 2 * height")
    coefficient = diagonal_coefficient(height)
    raw_diagonal = explicit_shadow(height) + projected_foreign_defect(height, cutoff)
    corrected_diagonal = raw_diagonal + coefficient * first_lambert_tail_correction(
        cutoff
    )
    direct_diagonal = lambert_projected_diagonal(height, cutoff)
    raw_radius = complement_bound(height, cutoff)
    crude_radius = crude_square_bound(height, cutoff)
    sharp_radius = sharp_square_bound(height, cutoff)
    return {
        "schema": "erdos249_resummed_residue_fixture_v0",
        "proof_authority": "exact_fixture_not_lean_proof_authority",
        "height": height,
        "cutoff": cutoff,
        "exact_checks": {
            "resummed_residue_equals_direct_lambert": corrected_diagonal
            == direct_diagonal,
            "sharp_radius_le_crude_radius": sharp_radius <= crude_radius,
            "crude_radius_lt_raw_radius": crude_radius < raw_radius,
        },
        "values": {
            "raw_residue_diagonal": fraction_json(raw_diagonal),
            "first_lambert_tail_correction": fraction_json(
                first_lambert_tail_correction(cutoff)
            ),
            "corrected_residue_diagonal": fraction_json(corrected_diagonal),
            "direct_lambert_diagonal": fraction_json(direct_diagonal),
            "distance_to_integer": fraction_json(
                distance_to_integer(direct_diagonal)
            ),
            "raw_radius": fraction_json(raw_radius),
            "crude_square_radius": fraction_json(crude_radius),
            "sharp_square_radius": fraction_json(sharp_radius),
        },
        "finite_nonintegrality_certificate": distance_to_integer(direct_diagonal)
        > sharp_radius,
        "lean_reentry_target": (
            "Erdos257PeriodNoncollapse.SquaredMersenneDiagonalEnclosure"
        ),
    }


def nearest_integer_gap(value: Fraction) -> tuple[int, Fraction]:
    floor_value = value.numerator // value.denominator
    candidates = (floor_value, floor_value + 1)
    nearest = min(candidates, key=lambda z: abs(value - z))
    return nearest, abs(value - nearest)


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    divisor = 3
    while divisor * divisor <= n:
        if n % divisor == 0:
            return False
        divisor += 2
    return True


def square_centre_diagnostics(
    height: int, cutoff: int, centre: Fraction, radius: Fraction
) -> dict[str, object]:
    """Exact central-gap, reduction, wide-prime, and directed-tail ledger."""
    coefficient = diagonal_coefficient(height)
    nearest, gap = nearest_integer_gap(centre)
    numerator_gap = abs(centre.numerator - nearest * centre.denominator)
    partial = mobius_square_partial(cutoff)
    reduction_gcd = math.gcd(partial.denominator, coefficient)
    expected_denominator = partial.denominator // reduction_gcd

    wide_primes = [
        p for p in range(cutoff // 2 + 1, cutoff + 1) if is_prime(p)
    ]
    wide_block = math.prod((2**p - 1) ** 2 for p in wide_primes)
    raw_block_divides = partial.denominator % wide_block == 0
    final_block_divides = centre.denominator % wide_block == 0

    first_nonzero = cutoff + 1
    while moebius(first_nonzero) == 0:
        first_nonzero += 1
    first_sign = moebius(first_nonzero)
    first_displacement = Fraction(
        coefficient, (2**first_nonzero - 1) ** 2
    )
    directed_remainder = sharp_square_bound(height, first_nonzero)
    directed_lower = first_displacement - directed_remainder
    directed_upper = first_displacement + directed_remainder
    if first_sign == 1:
        interval_lower = centre + directed_lower
        interval_upper = centre + directed_upper
    else:
        interval_lower = centre - directed_upper
        interval_upper = centre - directed_lower
    first_integer = math.ceil(interval_lower)
    last_integer = math.floor(interval_upper)
    obstructing_integers = (
        list(range(first_integer, last_integer + 1))
        if first_integer <= last_integer
        else []
    )

    leave_one_out = []
    for prime in wide_primes:
        channel = Fraction(
            coefficient * moebius(prime), (2**prime - 1) ** 2
        )
        reduced = centre - channel
        reduced_nearest, reduced_gap = nearest_integer_gap(reduced)
        leave_one_out.append(
            {
                "prime": prime,
                "channel": fraction_json(channel),
                "nearest_integer": reduced_nearest,
                "distance_to_integer": fraction_json(reduced_gap),
            }
        )

    return {
        "reduced_centre": {
            "numerator": centre.numerator,
            "denominator": centre.denominator,
        },
        "central_gap": {
            "nearest_integer": nearest,
            "numerator_gap": numerator_gap,
            "normalized_gap": fraction_json(gap),
            "radius_times_denominator": fraction_json(
                radius * centre.denominator
            ),
        },
        "reduction": {
            "mobius_square_partial_denominator": partial.denominator,
            "coefficient_gcd": reduction_gcd,
            "expected_scaled_denominator": expected_denominator,
            "matches_reduced_centre": expected_denominator
            == centre.denominator,
        },
        "wide_prime_block": {
            "primes": wide_primes,
            "bit_length": wide_block.bit_length(),
            "divides_partial_denominator": raw_block_divides,
            "divides_scaled_centre_denominator": final_block_divides,
            "scaled_cofactor_bit_length": (
                (centre.denominator // wide_block).bit_length()
                if final_block_divides
                else None
            ),
        },
        "directed_tail": {
            "first_nonzero_mobius_channel": first_nonzero,
            "sign": first_sign,
            "oriented_displacement_lower": fraction_json(directed_lower),
            "oriented_displacement_upper": fraction_json(directed_upper),
            "actual_interval_lower": fraction_json(interval_lower),
            "actual_interval_upper": fraction_json(interval_upper),
            "obstructing_integers": obstructing_integers,
            "certified": not obstructing_integers,
        },
        "leave_one_wide_prime_out": leave_one_out,
    }


def build_square_centre_receipt(height: int, cutoff: int) -> dict[str, object]:
    if height <= 0:
        raise ValueError("height must be positive")
    if cutoff < 0:
        raise ValueError("cutoff must be nonnegative")
    centre = lambert_projected_diagonal(height, cutoff)
    radius = sharp_square_bound(height, cutoff)
    nearest, gap = nearest_integer_gap(centre)
    diagnostics = square_centre_diagnostics(height, cutoff, centre, radius)
    directed_certified = bool(diagnostics["directed_tail"]["certified"])
    symmetric_certified = gap > radius
    return {
        "schema": "erdos249_square_centre_ledger_v1",
        "proof_authority": "exact_fixture_not_lean_proof_authority",
        "height": height,
        "cutoff": cutoff,
        "certificate_kind": (
            "symmetric"
            if symmetric_certified
            else "directed_first_support"
            if directed_certified
            else None
        ),
        "symmetric_certified": symmetric_certified,
        "directed_certified": directed_certified,
        "finite_nonintegrality_certificate": (
            symmetric_certified or directed_certified
        ),
        "distance": fraction_json(gap),
        "radius": fraction_json(radius),
        "nearest_integer": nearest,
        **diagnostics,
    }


def build_offset_adversary(max_height: int, max_offset: int) -> dict[str, object]:
    if max_height <= 0 or max_offset < 0:
        raise ValueError("max-height must be positive and max-offset nonnegative")
    rows: list[dict[str, object]] = []
    for height in range(1, max_height + 1):
        first_success: dict[str, object] | None = None
        largest_failed_offset: int | None = None
        for offset in range(max_offset + 1):
            cutoff = height + offset
            centre = lambert_projected_diagonal(height, cutoff)
            radius = sharp_square_bound(height, cutoff)
            nearest, gap = nearest_integer_gap(centre)
            diagnostics = square_centre_diagnostics(
                height, cutoff, centre, radius
            )
            directed_certified = bool(
                diagnostics["directed_tail"]["certified"]
            )
            symmetric_certified = gap > radius
            row = {
                "height": height,
                "offset": offset,
                "cutoff": cutoff,
                "certified": symmetric_certified or directed_certified,
                "certificate_kind": (
                    "symmetric"
                    if symmetric_certified
                    else "directed_first_support"
                    if directed_certified
                    else None
                ),
                "symmetric_certified": symmetric_certified,
                "directed_certified": directed_certified,
                "distance": fraction_json(gap),
                "radius": fraction_json(radius),
                "normalized_margin": float((gap - radius) / radius),
                "denominator_bits": centre.denominator.bit_length(),
                "nearest_integer": nearest,
                "exact_numerator_gap": abs(
                    centre.numerator - nearest * centre.denominator
                ),
                **diagnostics,
            }
            if row["certified"] and first_success is None:
                first_success = row
                break
            if not row["certified"]:
                largest_failed_offset = offset
        rows.append(
            first_success
            or {
                "height": height,
                "certified": False,
                "largest_failed_offset": largest_failed_offset,
            }
        )
    rows.sort(
        key=lambda row: (
            row.get("certified", False),
            row.get("normalized_margin", float("-inf")),
        )
    )
    return {
        "schema": "erdos249_offset_adversary_v1",
        "proof_authority": "exact_fixture_not_lean_proof_authority",
        "max_height": max_height,
        "max_offset": max_offset,
        "all_heights_certified": all(row.get("certified", False) for row in rows),
        "max_minimal_successful_offset": max(
            (int(row["offset"]) for row in rows if row.get("certified", False)),
            default=None,
        ),
        "rows": rows,
    }


def controlled_square_partial(cutoff: int, signs: dict[int, int]) -> Fraction:
    return Fraction(1, 2) + sum(
        (
            Fraction(signs[d], (2**d - 1) ** 2)
            for d in range(1, cutoff + 1)
        ),
        Fraction(),
    )


def controlled_offset_summary(
    max_height: int, max_offset: int, signs: dict[int, int]
) -> dict[str, object]:
    first_offsets: list[int | None] = []
    for height in range(1, max_height + 1):
        first_offset = None
        for offset in range(max_offset + 1):
            cutoff = height + offset
            centre = diagonal_prefix_correction(height) + diagonal_coefficient(
                height
            ) * controlled_square_partial(cutoff, signs)
            if distance_to_integer(centre) > sharp_square_bound(height, cutoff):
                first_offset = offset
                break
        first_offsets.append(first_offset)
    successful = [offset for offset in first_offsets if offset is not None]
    return {
        "all_heights_certified": len(successful) == max_height,
        "max_minimal_successful_offset": max(successful, default=None),
        "offset_counts": {
            str(offset): first_offsets.count(offset)
            for offset in sorted(set(successful))
        },
        "uncertified_heights": [
            height
            for height, offset in enumerate(first_offsets, start=1)
            if offset is None
        ],
    }


def build_square_controls(
    max_height: int, max_offset: int, control_seeds: int
) -> dict[str, object]:
    if max_height <= 0 or max_offset < 0 or control_seeds < 0:
        raise ValueError("control bounds must be nonnegative and height positive")
    max_channel = max_height + max_offset
    support = {
        d: moebius(d) != 0 for d in range(1, max_channel + 1)
    }
    all_positive = {
        d: 1 if support[d] else 0 for d in range(1, max_channel + 1)
    }
    random_controls = []
    for seed in range(control_seeds):
        generator = random.Random(seed)
        signs = {
            d: generator.choice((-1, 1)) if support[d] else 0
            for d in range(1, max_channel + 1)
        }
        random_controls.append(
            {
                "seed": seed,
                **controlled_offset_summary(max_height, max_offset, signs),
            }
        )
    return {
        "schema": "erdos249_square_sign_controls_v1",
        "proof_authority": "disconfirming_exact_fixture_not_lean_proof_authority",
        "max_height": max_height,
        "max_offset": max_offset,
        "support": "actual_squarefree_support",
        "all_positive": controlled_offset_summary(
            max_height, max_offset, all_positive
        ),
        "random_signs": random_controls,
    }


@lru_cache(maxsize=None)
def totient_factored(n: int) -> tuple[int, dict[int, int]]:
    if sympy is None:
        raise RuntimeError("lcm_diagonal mode requires sympy")
    factors = {int(p): int(e) for p, e in sympy.factorint(n).items()}
    value = n
    for prime in factors:
        value -= value // prime
    return value, factors


def build_lcm_diagonal(max_t: int, max_extra_depth: int) -> dict[str, object]:
    if max_t <= 0 or max_extra_depth < 0:
        raise ValueError("lcm-max-t must be positive and max-extra-depth nonnegative")
    height = 1
    rows: list[dict[str, object]] = []
    for t in range(1, max_t + 1):
        previous_height = height
        height = math.lcm(height, t)
        start_depth = height.bit_length() + 4
        accumulator = 0
        factor_receipts: dict[int, dict[str, object]] = {}
        success: dict[str, object] | None = None
        for depth in range(1, start_depth + max_extra_depth + 1):
            phi_2h, factors_2h = totient_factored(2 * height + depth)
            phi_h, factors_h = totient_factored(height + depth)
            accumulator = 2 * accumulator + phi_2h - phi_h
            if depth < start_depth:
                continue
            modulus = 2**depth
            residue = accumulator % modulus
            distance_numerator = min(residue, modulus - residue)
            tail_numerator = 3 * height + 2 * depth + 4
            factor_receipts[depth] = {
                "height_plus_depth": factors_h,
                "twice_height_plus_depth": factors_2h,
            }
            if distance_numerator > tail_numerator:
                success = {
                    "t": t,
                    "height": height,
                    "depth": depth,
                    "residue_distance_numerator": distance_numerator,
                    "tail_numerator": tail_numerator,
                    "normalized_margin": Fraction(
                        distance_numerator - tail_numerator, tail_numerator
                    ).__float__(),
                    "height_changed": height != previous_height,
                    "responsible_prime_power": t if height != previous_height else None,
                    "factor_receipt": factor_receipts[depth],
                }
                break
        rows.append(
            success
            or {
                "t": t,
                "height": height,
                "certified": False,
                "searched_through_depth": start_depth + max_extra_depth,
                "height_changed": height != previous_height,
                "responsible_prime_power": t if height != previous_height else None,
            }
        )
    return {
        "schema": "erdos249_lcm_diagonal_adversary_v0",
        "proof_authority": "exact_integer_fixture_not_lean_proof_authority",
        "max_t": max_t,
        "all_t_certified": all(row.get("certified", True) for row in rows),
        "rows": rows,
    }


def build_power_two_adjacent_suffix_slack(
    min_exponent: int, max_exponent: int
) -> dict[str, object]:
    """Evaluate the exact canonical adjacent-suffix slack at ``t = 2^a``.

    This is the executable counterpart of the parity-complete
    ``CanonicalAdjacentSuffixPenultimateMarginSupply``.  It is finite evidence
    only: every totient is computed from a checked prime factorization, but a
    successful bounded range is not promoted to the cofinal Lean producer.
    """

    if min_exponent < 2 or max_exponent < min_exponent:
        raise ValueError("require 2 <= min-exponent <= max-exponent")
    if sympy is None:
        raise RuntimeError("power_two_adjacent_suffix_slack mode requires sympy")

    rows: list[dict[str, object]] = []
    all_factorizations_verified = True
    for exponent in range(min_exponent, max_exponent + 1):
        endpoint = 2**exponent
        height = math.lcm(*range(1, endpoint + 1))
        depth = height.bit_length() - 1 + 10
        accumulator = 0
        penultimate_raw = None
        target_previous_increment = None
        target_terminal_increment = None
        factor_lines: list[str] = []
        factorization_verified = True

        for offset in range(1, depth + 2):
            phi_twice, factors_twice = totient_factored(2 * height + offset)
            phi_once, factors_once = totient_factored(height + offset)
            for value, factors in (
                (2 * height + offset, factors_twice),
                (height + offset, factors_once),
            ):
                reconstructed = math.prod(
                    prime**multiplicity
                    for prime, multiplicity in factors.items()
                )
                verified = reconstructed == value and all(
                    bool(sympy.isprime(prime)) for prime in factors
                )
                factorization_verified &= verified
                factor_lines.append(
                    f"{value}:"
                    + ",".join(
                        f"{prime}^{multiplicity}"
                        for prime, multiplicity in sorted(factors.items())
                    )
                )
            increment = phi_twice - phi_once
            if offset <= depth:
                if offset == depth:
                    penultimate_raw = accumulator + increment
                    target_previous_increment = increment
                accumulator = 2 * accumulator + increment
            else:
                target_terminal_increment = increment
                accumulator += increment

        assert penultimate_raw is not None
        assert target_previous_increment is not None
        assert target_terminal_increment is not None
        modulus = 2**depth
        residue = accumulator % modulus
        edge = 2 ** (depth - 5)
        slack = min(residue - edge, (modulus - edge) - residue)
        penultimate_modulus = 2 ** (depth - 1)
        penultimate_residue = penultimate_raw % penultimate_modulus
        penultimate_strong_slack = min(
            penultimate_residue - edge,
            (penultimate_modulus - edge) - penultimate_residue,
        )
        target_correction = target_terminal_increment - target_previous_increment
        correction_abs_lt_edge = abs(target_correction) < edge
        target_unwrapped = 2 * penultimate_residue + target_correction
        penultimate_exact_left = target_unwrapped - edge
        penultimate_exact_right = (modulus - edge) - target_unwrapped
        penultimate_exact_slack = min(
            penultimate_exact_left, penultimate_exact_right
        )
        one_step_recurrence_verified = (
            target_unwrapped % modulus == residue
        )
        exact_centrality_iff_verified = (slack >= 0) == (
            penultimate_exact_slack >= 0
        )
        correction_envelope = 3 * height + 2 * depth + 1
        penultimate_margin_left = (
            2 * penultimate_residue - (edge + correction_envelope)
        )
        penultimate_margin_right = (
            (modulus - edge) - (2 * penultimate_residue + correction_envelope)
        )
        penultimate_margin_slack = min(
            penultimate_margin_left, penultimate_margin_right
        )
        digest = hashlib.sha256("\n".join(factor_lines).encode()).hexdigest()
        all_factorizations_verified &= factorization_verified
        rows.append(
            {
                "exponent": exponent,
                "endpoint": endpoint,
                "period_lcm": height,
                "canonical_depth": depth,
                "raw_block_residue": residue,
                "central_edge": edge,
                "central_slack": slack,
                "slack_nonnegative": slack >= 0,
                "normalized_residue": residue / modulus,
                "penultimate_depth": depth - 1,
                "penultimate_raw_block_residue": penultimate_residue,
                "penultimate_strong_edge": edge,
                "penultimate_strong_slack": penultimate_strong_slack,
                "penultimate_strong_band_satisfied": penultimate_strong_slack >= 0,
                "target_depth_correction": target_correction,
                "correction_envelope": correction_envelope,
                "correction_abs_lt_edge": correction_abs_lt_edge,
                "target_unwrapped": target_unwrapped,
                "penultimate_exact_left": penultimate_exact_left,
                "penultimate_exact_right": penultimate_exact_right,
                "penultimate_exact_slack": penultimate_exact_slack,
                "penultimate_exact_satisfied": penultimate_exact_slack >= 0,
                "one_step_recurrence_verified": one_step_recurrence_verified,
                "exact_centrality_iff_verified": exact_centrality_iff_verified,
                "penultimate_margin_left": penultimate_margin_left,
                "penultimate_margin_right": penultimate_margin_right,
                "penultimate_margin_slack": penultimate_margin_slack,
                "penultimate_margin_satisfied": penultimate_margin_slack >= 0,
                "factorization_count": 2 * (depth + 1),
                "factorizations_verified": factorization_verified,
                "factorization_receipt_sha256": digest,
            }
        )

    return {
        "schema": "erdos249_power_two_adjacent_suffix_slack_fixture_v1",
        "proof_authority": "exact_finite_fixture_not_cofinal_lean_proof_authority",
        "exponent_range": [min_exponent, max_exponent],
        "exact_checks": {
            "all_factorizations_verified": all_factorizations_verified,
            "all_tested_slacks_nonnegative": all(
                bool(row["slack_nonnegative"]) for row in rows
            ),
            "all_penultimate_strong_bands_satisfied": all(
                bool(row["penultimate_strong_band_satisfied"]) for row in rows
            ),
            "all_corrections_inside_edge": all(
                bool(row["correction_abs_lt_edge"]) for row in rows
            ),
            "all_one_step_recurrences_verified": all(
                bool(row["one_step_recurrence_verified"]) for row in rows
            ),
            "all_exact_centrality_iffs_verified": all(
                bool(row["exact_centrality_iff_verified"]) for row in rows
            ),
            "all_penultimate_exact_conditions_satisfied": all(
                bool(row["penultimate_exact_satisfied"]) for row in rows
            ),
            "all_penultimate_margins_satisfied": all(
                bool(row["penultimate_margin_satisfied"]) for row in rows
            ),
        },
        "rows": rows,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--mode",
        choices=(
            "raw_residue",
            "resummed_residue",
            "square_centre",
            "square_controls",
            "offset_adversary",
            "lcm_diagonal",
            "power_two_adjacent_suffix_slack",
        ),
        default="raw_residue",
    )
    parser.add_argument("--height", type=int, default=7)
    parser.add_argument("--cutoff", type=int, default=64)
    parser.add_argument("--tail-terms", type=int, default=256)
    parser.add_argument("--max-height", type=int, default=100)
    parser.add_argument("--max-offset", type=int, default=8)
    parser.add_argument("--control-seeds", type=int, default=10)
    parser.add_argument("--lcm-max-t", type=int, default=20)
    parser.add_argument("--max-extra-depth", type=int, default=32)
    parser.add_argument("--min-exponent", type=int, default=2)
    parser.add_argument("--max-exponent", type=int, default=6)
    args = parser.parse_args()
    if args.mode == "raw_residue":
        receipt = build_receipt(args.height, args.cutoff, args.tail_terms)
    elif args.mode == "resummed_residue":
        receipt = build_resummed_receipt(args.height, args.cutoff)
    elif args.mode == "square_centre":
        receipt = build_square_centre_receipt(args.height, args.cutoff)
    elif args.mode == "square_controls":
        receipt = build_square_controls(
            args.max_height, args.max_offset, args.control_seeds
        )
    elif args.mode == "offset_adversary":
        receipt = build_offset_adversary(args.max_height, args.max_offset)
    elif args.mode == "lcm_diagonal":
        receipt = build_lcm_diagonal(args.lcm_max_t, args.max_extra_depth)
    else:
        receipt = build_power_two_adjacent_suffix_slack(
            args.min_exponent, args.max_exponent
        )
    print(json.dumps(receipt, indent=2, sort_keys=True))
    checks = receipt.get("exact_checks")
    return 0 if checks is None or all(checks.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
