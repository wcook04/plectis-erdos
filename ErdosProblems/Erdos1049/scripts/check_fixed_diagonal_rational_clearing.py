#!/usr/bin/env python3
"""Exact scalar moving-diagonal rational-clearing probe for Erdős #1049.

Van Assche's little-q-Legendre Padé construction evaluates P_n(x|q) on the
moving diagonal x=p^n, q=p^-1.  The q-Apéry denominator is the neighbouring
fixed diagonal x=p^(n+1).  For every fixed offset delta >= 0, the denominator
polynomial has degree

    D_(n,delta) = (3 n^2 + (2 delta - 1)n) / 2

and unit leading coefficient.  At p=3/2 its reduced denominator is therefore
exactly 2^D.  The cyclotomic clearing polynomial is monic as well and adds
E_n = sum_{k<=n} phi(k), so the product has exact denominator 2^(D+E).

Combining that forced homogeneous clearing cost with Van Assche's displayed Padé error
asymptotic gives the quadratic logarithmic exponent

    (3/2 + 3/pi^2) log 2 + (3/pi^2 - 3/2) log(3/2)
      = (3/2) log(4/3) + (3/pi^2) log 3 > 0.

More generally, evaluation at x=p^m with m>=n has exact degree

    D_(n,m) = n m + n(n-1)/2.

The target tail forces a cyclotomic cutoff m+O(1).  Composing the source error
with the unavoidable denominator of the P-coefficient gives the finite-scale
main term

    (n m+n^2/2) log(4/3) + (3/pi^2)m^2 log 3,

which is positive for every outward scalar diagonal before division by common
odd row content.  The script replays exact
polynomial degrees, leading coefficients, reduced denominators, and Van
Assche's exact error bounds for fixed, linearly moving, and superlinear sample
diagonals, constructs the exact associated coefficient, and primitively
normalizes the displayed integer pairs.  It also reconstructs the adjacent
second-kind determinant, verifies the resulting coprime-content divisor
reduction, and stores exact counterexamples to an order-at-most-2n shortcut.
The all-index forced-clearing
conclusion uses the primary source's analytic formulas plus the elementary
degree proof; primitive common content is finite evidence only.  The script is
not a Lean formalization of the source asymptotics and does not decide
irrationality at 3/2.
"""

from __future__ import annotations

import argparse
from functools import cache
from fractions import Fraction
import importlib.util
import json
import math
from pathlib import Path
import sys
from typing import Any

import sympy as sp


REPO_ROOT = Path(__file__).resolve().parents[5]
SCRIPT_DIR = Path(__file__).resolve().parent
DIAGONAL_SOURCE = SCRIPT_DIR / "verify_qapery_diagonal_nonequivalence.py"
spec = importlib.util.spec_from_file_location("qapery_diagonal", DIAGONAL_SOURCE)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load the q-Apéry diagonal checker")
diagonal = importlib.util.module_from_spec(spec)
spec.loader.exec_module(diagonal)

sys.path.insert(0, str(REPO_ROOT))
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


P = diagonal.P
Z = sp.symbols("z")
OFFSETS = (0, 1, 2, 3)
N_MAX = 7
OUTWARD_MULTIPLIERS = (1, 2, 3)
OUTWARD_N_MAX = 6
SUPERLINEAR_N = (2, 3, 4, 5)
CONTENT_ORDER_FALSIFIERS = ((4, 32), (5, 40), (7, 28), (8, 64))
SOURCE_REF = str(Path(__file__).resolve().relative_to(REPO_ROOT))
DIAGONAL_REF = str(DIAGONAL_SOURCE.relative_to(REPO_ROOT))
LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "FixedDiagonalRationalClearing.lean"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "FixedDiagonalRationalClearingLab.md"
)
PACKET_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "research_packet.json"
)
PRIMARY_SOURCE_REF = (
    "annexes/arxiv-math0101187-van-assche-little-q-legendre-lambert/source.tex"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_fixed_diagonal_rational_clearing_receipt.json"
)


def as_fraction(value: Any) -> Fraction:
    value = sp.cancel(value)
    return Fraction(int(sp.numer(value)), int(sp.denom(value)))


@cache
def moving_diagonal(n: int, evaluation_exponent: int):
    return sp.expand(diagonal.little_q_legendre(n, P**evaluation_exponent))


def moving_diagonal_degree(n: int, evaluation_exponent: int) -> int:
    return n * evaluation_exponent + n * (n - 1) // 2


def fixed_diagonal(n: int, offset: int):
    return moving_diagonal(n, n + offset)


def fixed_diagonal_degree(n: int, offset: int) -> int:
    return moving_diagonal_degree(n, n + offset)


@cache
def cyclotomic_clearing(cutoff: int):
    return sp.expand(sp.prod(sp.cyclotomic_poly(k, P) for k in range(1, cutoff + 1)))


def homogeneous_numerator(poly, width: int) -> int:
    coefficients = {e: int(c) for (e,), c in sp.Poly(poly, P).terms()}
    return sum(c * 3**e * 2 ** (width - e) for e, c in coefficients.items())


def encode_fraction(value: Fraction) -> dict[str, Any]:
    return {
        "numerator": str(value.numerator),
        "denominator": str(value.denominator),
        "numerator_bit_length": abs(value.numerator).bit_length(),
        "denominator_bit_length": value.denominator.bit_length(),
    }


@cache
def q_binomial_fraction(n: int, k: int, p: Fraction) -> Fraction:
    if k < 0 or k > n:
        return Fraction(0)
    value = Fraction(1)
    for j in range(1, k + 1):
        value *= (1 - p ** (n - k + j)) / (1 - p**j)
    return value


@cache
def little_q_legendre_coefficients_fraction(
    n: int, p: Fraction
) -> tuple[Fraction, ...]:
    return tuple(
        (-1) ** k
        * q_binomial_fraction(n, k, p)
        * q_binomial_fraction(n + k, k, p)
        * p ** (-k * n + k * (k - 1) // 2)
        for k in range(n + 1)
    )


@cache
def associated_q_value_fraction(
    n: int, evaluation_exponent: int, p: Fraction
) -> Fraction:
    """Evaluate Van Assche's associated polynomial from its moment definition."""

    z = p**evaluation_exponent
    coefficients = little_q_legendre_coefficients_fraction(n, p)
    total = Fraction(0)
    for degree in range(1, n + 1):
        coefficient = coefficients[degree]
        for moment_index in range(degree):
            moment = p ** (moment_index + 1) / (p ** (moment_index + 1) - 1)
            total += coefficient * z ** (degree - 1 - moment_index) * moment
    return total


@cache
def little_q_legendre_polynomial_fraction(n: int, p: Fraction):
    coefficients = little_q_legendre_coefficients_fraction(n, p)
    return sp.Poly(
        sum(
            sp.Rational(coefficient.numerator, coefficient.denominator) * Z**degree
            for degree, coefficient in enumerate(coefficients)
        ),
        Z,
    )


@cache
def associated_q_polynomial_fraction(n: int, p: Fraction):
    """Materialize Q_n from the same moment definition used at p^m."""

    coefficients = little_q_legendre_coefficients_fraction(n, p)
    expression = sp.Integer(0)
    for degree in range(1, n + 1):
        coefficient = coefficients[degree]
        for moment_index in range(degree):
            moment = p ** (moment_index + 1) / (p ** (moment_index + 1) - 1)
            expression += (
                sp.Rational(coefficient.numerator, coefficient.denominator)
                * Z ** (degree - 1 - moment_index)
                * sp.Rational(moment.numerator, moment.denominator)
            )
    return sp.Poly(expression, Z)


def adjacent_second_kind_determinant_records() -> list[dict[str, Any]]:
    """Replay the all-index adjacent P/Q determinant at p=3/2.

    Orthogonality gives

      Q_n P_(n-1) - P_n Q_(n-1)
        = (kappa_n/kappa_(n-1)) ||P_(n-1)||^2
        = -(p^n+1)/(p^n-1).

    The exact finite replay guards the coefficient and sign conventions used
    in the primitive-content divisor consequence.
    """

    p = Fraction(3, 2)
    records: list[dict[str, Any]] = []
    for n in range(1, N_MAX + 1):
        polynomial = little_q_legendre_polynomial_fraction(n, p)
        previous_polynomial = little_q_legendre_polynomial_fraction(n - 1, p)
        associated = associated_q_polynomial_fraction(n, p)
        previous_associated = associated_q_polynomial_fraction(n - 1, p)
        determinant = sp.Poly(
            associated.as_expr() * previous_polynomial.as_expr()
            - polynomial.as_expr() * previous_associated.as_expr(),
            Z,
        )
        expected = -(p**n + 1) / (p**n - 1)
        determinant_value = as_fraction(determinant.as_expr())
        assert determinant.degree() == 0
        assert determinant_value == expected
        records.append(
            {
                "n": n,
                "determinant": encode_fraction(determinant_value),
                "expected_numerator": str(-(3**n + 2**n)),
                "expected_denominator": str(3**n - 2**n),
                "identity_holds": True,
            }
        )
    return records


def valuation_int(value: int, prime: int) -> int | None:
    if value == 0:
        return None
    value = abs(value)
    order = 0
    while value % prime == 0:
        value //= prime
        order += 1
    return order


def rational_base_order_mod_prime(prime: int) -> int:
    assert prime not in (2, 3)
    return int(sp.n_order((3 * pow(2, -1, prime)) % prime, prime))


def diagonal_records() -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    p = sp.Rational(3, 2)
    for offset in OFFSETS:
        for n in range(1, N_MAX + 1):
            poly = sp.Poly(fixed_diagonal(n, offset), P)
            degree = int(poly.degree())
            expected_degree = fixed_diagonal_degree(n, offset)
            leading = int(poly.LC())
            value = as_fraction(poly.eval(p))
            numerator = homogeneous_numerator(poly.as_expr(), degree)

            # Q_n has denominators p^ell-1 through ell=n.  Moving the Markov
            # evaluation by a fixed offset also exposes the finite target tail
            # through n+offset-1.  Their common cyclotomic cutoff is the max.
            cutoff = max(n, n + offset - 1)
            clearing = sp.Poly(cyclotomic_clearing(cutoff), P)
            clearing_degree = int(clearing.degree())
            combined = sp.Poly(sp.expand(poly.as_expr() * clearing.as_expr()), P)
            combined_degree = int(combined.degree())
            combined_value = as_fraction(combined.eval(p))
            combined_numerator = homogeneous_numerator(
                combined.as_expr(), combined_degree
            )

            assert degree == expected_degree
            assert leading == (-1) ** n
            assert numerator % 2 != 0
            assert value.denominator == 2**degree
            assert combined_degree == degree + clearing_degree
            assert int(clearing.LC()) == 1
            assert int(combined.LC()) == (-1) ** n
            assert combined_numerator % 2 != 0
            assert combined_value.denominator == 2**combined_degree

            records.append(
                {
                    "offset": offset,
                    "n": n,
                    "degree": degree,
                    "expected_degree": expected_degree,
                    "leading_coefficient": leading,
                    "homogeneous_numerator_mod_2": numerator % 2,
                    "reduced_denominator": str(value.denominator),
                    "reduced_denominator_is_exact_two_power": True,
                    "cyclotomic_cutoff": cutoff,
                    "cyclotomic_degree": clearing_degree,
                    "combined_degree": combined_degree,
                    "combined_homogeneous_numerator_mod_2": combined_numerator % 2,
                    "combined_reduced_denominator": str(combined_value.denominator),
                    "minimal_combined_two_clearing_exponent": combined_degree,
                }
            )
    return records


def outward_diagonal_records() -> list[dict[str, Any]]:
    """Exact endpoint and denominator checks beyond fixed offsets."""

    cases = [
        ("linear_ratio", multiplier, n, multiplier * n)
        for multiplier in OUTWARD_MULTIPLIERS
        for n in range(1, OUTWARD_N_MAX + 1)
    ] + [
        ("superlinear_square", None, n, n * n) for n in SUPERLINEAR_N
    ]
    records: list[dict[str, Any]] = []
    p = sp.Rational(3, 2)
    for family, multiplier, n, evaluation_exponent in cases:
        poly = sp.Poly(moving_diagonal(n, evaluation_exponent), P)
        degree = int(poly.degree())
        expected_degree = moving_diagonal_degree(n, evaluation_exponent)
        leading = int(poly.LC())
        value = as_fraction(poly.eval(p))
        numerator = homogeneous_numerator(poly.as_expr(), degree)

        cutoff = max(n, evaluation_exponent - 1)
        clearing = sp.Poly(cyclotomic_clearing(cutoff), P)
        clearing_degree = int(clearing.degree())
        combined = sp.Poly(sp.expand(poly.as_expr() * clearing.as_expr()), P)
        combined_degree = int(combined.degree())
        combined_value = as_fraction(combined.eval(p))
        combined_numerator = homogeneous_numerator(
            combined.as_expr(), combined_degree
        )

        assert evaluation_exponent >= n
        assert degree == expected_degree
        assert leading == (-1) ** n
        assert numerator % 2 != 0
        assert value.denominator == 2**degree
        assert combined_degree == degree + clearing_degree
        assert int(clearing.LC()) == 1
        assert int(combined.LC()) == (-1) ** n
        assert combined_numerator % 2 != 0
        assert combined_value.denominator == 2**combined_degree

        records.append(
            {
                "family": family,
                "multiplier": multiplier,
                "n": n,
                "evaluation_exponent": evaluation_exponent,
                "degree": degree,
                "expected_degree": expected_degree,
                "leading_coefficient": leading,
                "homogeneous_numerator_mod_2": numerator % 2,
                "reduced_denominator": str(value.denominator),
                "cyclotomic_cutoff": cutoff,
                "cyclotomic_degree": clearing_degree,
                "combined_degree": combined_degree,
                "combined_homogeneous_numerator_mod_2": combined_numerator % 2,
                "combined_reduced_denominator": str(combined_value.denominator),
                "minimal_required_two_clearing_exponent": combined_degree,
            }
        )
    return records


def cleared_error_bound_record(n: int, evaluation_exponent: int) -> dict[str, Any]:
    """Source lower/upper bounds after the forced P-coefficient clearing."""

    p = Fraction(3, 2)
    poly = sp.Poly(moving_diagonal(n, evaluation_exponent), P)
    cutoff = max(n, evaluation_exponent - 1)
    clearing = sp.Poly(cyclotomic_clearing(cutoff), P)
    p_value = as_fraction(poly.eval(sp.Rational(3, 2)))
    d_value = as_fraction(clearing.eval(sp.Rational(3, 2)))
    forced_clearing = 2 ** (int(poly.degree()) + int(clearing.degree()))

    # The exact squared norm is p^(n+1)/(p^(2n+1)-1), while
    # p^m-1 <= p^m-q^k <= p^m.  This is Van Assche's positivity argument
    # with the evaluation exponent m left free.
    norm_lower = p ** (n + 1 - evaluation_exponent) / (p ** (2 * n + 1) - 1)
    norm_upper = p ** (n + 1) / (
        (p**evaluation_exponent - 1) * (p ** (2 * n + 1) - 1)
    )
    common = forced_clearing * abs(d_value / p_value)
    cleared_lower = common * norm_lower
    cleared_upper = common * norm_upper
    return {
        "n": n,
        "evaluation_exponent": evaluation_exponent,
        "cyclotomic_cutoff": cutoff,
        "forced_two_clearing_exponent": int(poly.degree())
        + int(clearing.degree()),
        "cleared_error_lower": encode_fraction(cleared_lower),
        "cleared_error_upper": encode_fraction(cleared_upper),
        "exact_lower_bound_exceeds_one": cleared_lower > 1,
    }


def primitive_row_record(n: int, evaluation_exponent: int) -> dict[str, Any]:
    """Construct the exact cleared coefficient pair and divide its full gcd."""

    p = Fraction(3, 2)
    cutoff = max(n, evaluation_exponent - 1)
    poly = sp.Poly(moving_diagonal(n, evaluation_exponent), P)
    clearing = sp.Poly(cyclotomic_clearing(cutoff), P)
    p_value = as_fraction(poly.eval(sp.Rational(3, 2)))
    d_value = as_fraction(clearing.eval(sp.Rational(3, 2)))
    q_value = associated_q_value_fraction(n, evaluation_exponent, p)
    target_prefix = sum(
        (Fraction(1, 1) / (p**j - 1) for j in range(1, evaluation_exponent)),
        Fraction(0),
    )

    denominator_coefficient = d_value * p_value
    numerator_coefficient = d_value * q_value + denominator_coefficient * target_prefix
    common_denominator = math.lcm(
        numerator_coefficient.denominator, denominator_coefficient.denominator
    )
    numerator_integer = int(numerator_coefficient * common_denominator)
    denominator_integer = int(denominator_coefficient * common_denominator)
    content = math.gcd(abs(numerator_integer), abs(denominator_integer)) or 1
    primitive_numerator = numerator_integer // content
    primitive_denominator = denominator_integer // content

    clearing_numerator = d_value.numerator
    content_factorization = sp.factorint(content)
    content_prime_orders = {
        str(prime): rational_base_order_mod_prime(prime)
        for prime in content_factorization
    }
    content_coprime_to_clearing = 1
    for prime, exponent in content_factorization.items():
        if clearing_numerator % prime != 0:
            content_coprime_to_clearing *= prime**exponent
    adjacent_determinant_numerator = 3**n + 2**n

    forced_exponent = int(poly.degree()) + int(clearing.degree())
    assert common_denominator == 2**forced_exponent
    assert content % 2 == 1
    assert math.gcd(abs(primitive_numerator), abs(primitive_denominator)) == 1
    # If an odd prime does not divide the cyclotomic clearing value, all
    # moments and target-prefix denominators are units locally.  Common row
    # divisibility then gives common divisibility of P_n and Q_n, and the
    # adjacent second-kind determinant forces the full prime power into
    # 3^n+2^n.
    assert adjacent_determinant_numerator % content_coprime_to_clearing == 0

    source_bounds = cleared_error_bound_record(n, evaluation_exponent)
    cleared_lower = Fraction(
        int(source_bounds["cleared_error_lower"]["numerator"]),
        int(source_bounds["cleared_error_lower"]["denominator"]),
    )
    cleared_upper = Fraction(
        int(source_bounds["cleared_error_upper"]["numerator"]),
        int(source_bounds["cleared_error_upper"]["denominator"]),
    )
    primitive_lower = cleared_lower / content
    primitive_upper = cleared_upper / content
    return {
        "n": n,
        "evaluation_exponent": evaluation_exponent,
        "cyclotomic_cutoff": cutoff,
        "common_denominator": str(common_denominator),
        "common_denominator_is_forced_two_power": True,
        "row_content": str(content),
        "row_content_factorization": {
            str(prime): exponent for prime, exponent in content_factorization.items()
        },
        "row_content_prime_orders_of_3_over_2": content_prime_orders,
        "clearing_homogeneous_numerator": str(clearing_numerator),
        "content_coprime_to_clearing": str(content_coprime_to_clearing),
        "content_coprime_to_clearing_divides_3n_plus_2n": True,
        "row_content_bit_length": content.bit_length(),
        "row_content_v2": valuation_int(content, 2),
        "row_content_v3": valuation_int(content, 3),
        "primitive_numerator_bit_length": abs(primitive_numerator).bit_length(),
        "primitive_denominator_bit_length": abs(primitive_denominator).bit_length(),
        "primitive_error_lower": encode_fraction(primitive_lower),
        "primitive_error_upper": encode_fraction(primitive_upper),
        "primitive_lower_exceeds_one": primitive_lower > 1,
        "primitive_upper_below_one": primitive_upper < 1,
    }


def van_assche_error_bounds() -> list[dict[str, Any]]:
    """Exact lower/upper bounds for the minimally cleared offset-zero form."""

    records: list[dict[str, Any]] = []
    for n in range(1, N_MAX + 1):
        record = cleared_error_bound_record(n, n)
        if n >= 2:
            assert record["exact_lower_bound_exceeds_one"]
        record["minimal_clearing_exponent"] = record.pop(
            "forced_two_clearing_exponent"
        )
        records.append(record)
    return records


def outward_moving_error_bounds() -> list[dict[str, Any]]:
    cases = [
        ("linear_ratio", multiplier, n, multiplier * n)
        for multiplier in OUTWARD_MULTIPLIERS
        for n in range(1, OUTWARD_N_MAX + 1)
    ] + [
        ("superlinear_square", None, n, n * n) for n in SUPERLINEAR_N
    ]
    records: list[dict[str, Any]] = []
    for family, multiplier, n, evaluation_exponent in cases:
        record = cleared_error_bound_record(n, evaluation_exponent)
        record["family"] = family
        record["multiplier"] = multiplier
        if n >= 2:
            assert record["exact_lower_bound_exceeds_one"]
        records.append(record)
    return records


def outward_primitive_content_records() -> list[dict[str, Any]]:
    cases = [
        ("linear_ratio", multiplier, n, multiplier * n)
        for multiplier in OUTWARD_MULTIPLIERS
        for n in range(1, OUTWARD_N_MAX + 1)
    ] + [
        ("superlinear_square", None, n, n * n) for n in SUPERLINEAR_N
    ]
    records: list[dict[str, Any]] = []
    for family, multiplier, n, evaluation_exponent in cases:
        record = primitive_row_record(n, evaluation_exponent)
        record["family"] = family
        record["multiplier"] = multiplier
        records.append(record)
    return records


def content_order_falsifier_records() -> list[dict[str, Any]]:
    """Exact counterexamples to the tempting order <= 2n support guess."""

    records: list[dict[str, Any]] = []
    for n, evaluation_exponent in CONTENT_ORDER_FALSIFIERS:
        record = primitive_row_record(n, evaluation_exponent)
        order_witnesses = [
            {
                "prime": prime,
                "exponent": exponent,
                "order": rational_base_order_mod_prime(prime),
            }
            for prime, exponent in sp.factorint(int(record["row_content"])).items()
            if rational_base_order_mod_prime(prime) > 2 * n
        ]
        assert order_witnesses
        record["order_exceeds_twice_n_witnesses"] = order_witnesses
        records.append(record)
    return records


def build_payload() -> dict[str, Any]:
    diagonals = diagonal_records()
    adjacent_determinants = adjacent_second_kind_determinant_records()
    errors = van_assche_error_bounds()
    outward_diagonals = outward_diagonal_records()
    outward_errors = outward_moving_error_bounds()
    primitive_records = outward_primitive_content_records()
    order_falsifiers = content_order_falsifier_records()
    positive_exponent = (
        Fraction(3, 2) * math.log(Fraction(4, 3))
        + 3 / math.pi**2 * math.log(3)
    )
    result = {
        "fixed_offset_records": diagonals,
        "adjacent_second_kind_determinant_records": adjacent_determinants,
        "van_assche_offset_zero_error_bounds": errors,
        "outward_moving_diagonal_records": outward_diagonals,
        "outward_moving_diagonal_error_bounds": outward_errors,
        "outward_primitive_content_records": primitive_records,
        "content_order_at_most_twice_n_falsifier_records": order_falsifiers,
        "all_displayed_fixed_offsets_have_exact_minimal_two_power_clearing": all(
            row["reduced_denominator_is_exact_two_power"] for row in diagonals
        ),
        "offset_zero_cleared_error_lower_bound_exceeds_one_for_n_ge_2": all(
            row["exact_lower_bound_exceeds_one"]
            for row in errors
            if row["n"] >= 2
        ),
        "outward_cleared_error_lower_bound_exceeds_one_for_n_ge_2": all(
            row["exact_lower_bound_exceeds_one"]
            for row in outward_errors
            if row["n"] >= 2
        ),
        "outward_primitive_error_lower_bound_exceeds_one_for_all_displayed_n_ge_2": all(
            row["primitive_lower_exceeds_one"]
            for row in primitive_records
            if row["n"] >= 2
        ),
        "outward_primitive_error_upper_bound_below_one_in_any_displayed_case": any(
            row["primitive_upper_below_one"] for row in primitive_records
        ),
        "quadratic_exponent": {
            "source_balance": (
                "(3/2 + 3/pi^2) log 2 + "
                "(3/pi^2 - 3/2) log(3/2)"
            ),
            "positive_decomposition": "(3/2) log(4/3) + (3/pi^2) log 3",
            "strictly_positive_by_exact_inequalities": ["4/3 > 1", "3 > 1"],
            "decimal_display_only": positive_exponent,
            "lean_theorems": [
                "fixedDiagonalRationalClearingExponent_eq_sourceBalance",
                "fixedDiagonalRationalClearingExponent_pos",
                "fixedDiagonalSourceBalance_pos",
                "not_tendsto_zero_of_eventually_one_le_abs",
            ],
        },
        "moving_diagonal_main_term": {
            "finite_scale_positive_form": (
                "(n*m+n^2/2) log(4/3) + (3/pi^2)m^2 log 3"
            ),
            "ratio_beta_positive_form": (
                "(beta+1/2) log(4/3) + (3/pi^2)beta^2 log 3"
            ),
            "domain": "integers m>=n>=1; beta>=1 on finite-ratio diagonals",
            "strictly_positive_by_exact_inequalities": [
                "n*m+n^2/2 > 0",
                "m^2 > 0",
                "4/3 > 1",
                "3 > 1",
            ],
            "lean_theorems": [
                "movingDiagonalRationalClearingMainTerm_eq_sourceBalance",
                "movingDiagonalRationalClearingMainTerm_pos",
                "movingDiagonalRatioExponent_one",
                "movingDiagonalRatioExponent_pos",
            ],
        },
        "primitive_content_divisor_reduction": {
            "adjacent_identity": (
                "Q_n(z)P_(n-1)(z)-P_n(z)Q_(n-1)(z)="
                "-(p^n+1)/(p^n-1)"
            ),
            "all_index_consequence": (
                "the largest divisor of G_(n,m) coprime to the homogeneous "
                "cyclotomic clearing value divides 3^n+2^n"
            ),
            "lean_arithmetic_consumer": (
                "commonDivisor_dvd_adjacentSecondKindNumerator"
            ),
            "remaining_content_support": (
                "prime powers supported on the homogeneous cyclotomic clearing "
                "value; their total multiplicity remains open"
            ),
            "false_shortcut": (
                "content primes need not have order at most 2n; the canonical "
                "receipt includes four exact counterexamples"
            ),
        },
        "mechanism_verdict": (
            "all_outward_forced_homogeneous_clearing_obstructed_"
            "primitive_content_open"
        ),
        "remaining_boundary": (
            "An all-index upper bound on primitive common odd content is still "
            "required before eliminating outward scalar rows.  The result also "
            "does not cover inward evaluations m<n, nonrectangular multiple-q-"
            "Jacobi systems, congruence-constrained combinations, or determinant/"
            "Hankel constructions."
        ),
    }
    contract = build_experiment_contract(
        problem_id="erdos_1049",
        target_statement="Prove irrationality of the Lambert value at q=3/2.",
        claim_ceiling=(
            "Exact displayed primitive-row arithmetic plus a source-derived "
            "all-index forced-homogeneous-clearing obstruction.  Primitive "
            "common content is not bounded all-index, the little-q-Legendre "
            "analytic asymptotics are not formalized in Lean, and no "
            "irrationality theorem at 3/2 is claimed."
        ),
        hypothesis_id="scalar_moving_evaluation_repairs_rational_height",
        hypothesis_statement=(
            "Changing the little-q-Legendre evaluation from p^n to any outward "
            "moving diagonal p^m can retain enough source decay to overcome "
            "the rational-base homogeneous clearing tax."
        ),
        probe_id="all_outward_degree_endpoint_and_source_exponent_composition",
        probe_question=(
            "Does any scalar evaluation exponent m>=n make the forced-cleared "
            "Van Assche forms tend to zero at p=3/2?"
        ),
        computation=(
            "Materialize fixed offsets, the linear diagonals m=n,2n,3n, and "
            "the superlinear diagonal m=n^2; verify degree n*m+n(n-1)/2, "
            "unit leading coefficient, odd homogeneous endpoint, and exact "
            "P-coefficient denominator; then compose the all-index degree law "
            "and cutoff m+O(1) with Van Assche's positive error identity."
        ),
        falsifier=(
            "An m>=n whose degree differs from n*m+n(n-1)/2, whose homogeneous "
            "P-coefficient numerator is even after cyclotomic multiplication, "
            "or whose source/clearing main term is nonpositive."
        ),
        stop_condition=(
            "Once the all-outward degree law and positive forced-clearing main "
            "term are exact, stop scanning evaluation exponents and test an "
            "explicit all-index primitive-content lemma."
        ),
        survival_consequence=(
            "A nonpositive main term would let the raw choice of outward "
            "evaluation repair rational-base height without another mechanism."
        ),
        falsification_consequence=(
            "Every outward scalar moving diagonal has positive forced-cleared "
            "main term, so only primitive common content can still repair the "
            "scalar row."
        ),
        consumer_ref=PACKET_REF,
        analysis_refs=[ANALYSIS_REF],
        source_refs=[SOURCE_REF, DIAGONAL_REF, PRIMARY_SOURCE_REF, LEAN_REF],
        input_receipt_refs=[],
        result_status="exact_one_way_result",
        result_summary=(
            "The primitively normalized Van Assche forms have exact lower bound "
            "greater than one for every displayed outward case with n>=2.  For every "
            "m>=n the P-coefficient has degree n*m+n(n-1)/2 and odd homogeneous "
            "numerator, while the source/clearing balance has strictly positive "
            "forced main term (n*m+n^2/2)log(4/3)+(3/pi^2)m^2 log 3.  The "
            "adjacent second-kind determinant additionally confines every "
            "content factor coprime to the clearing value to 3^n+2^n."
        ),
        progress_class="one_way_theorem",
        decision_basis=(
            "The exact P-coefficient endpoint numerator is odd for every m>=n, "
            "so no hidden power-of-two cancellation can reduce its mandatory "
            "clearing cost.  Exact primitive content is usually one in the "
            "displayed range, but an all-index odd-content bound remains open."
        ),
        next_analytic_target=(
            "Bound the common odd content of the two forced-cleared coefficients "
            "below the positive main term, or derive an explicit content factor "
            "large enough to reopen the scalar route."
        ),
        resource_bounds={
            "fixed_offset_count": len(OFFSETS),
            "fixed_offset_maximum": max(OFFSETS),
            "n_minimum": 1,
            "n_maximum": N_MAX,
            "outward_linear_multiplier_count": len(OUTWARD_MULTIPLIERS),
            "outward_linear_multiplier_maximum": max(OUTWARD_MULTIPLIERS),
            "outward_n_maximum": OUTWARD_N_MAX,
            "superlinear_case_count": len(SUPERLINEAR_N),
            "superlinear_evaluation_exponent_maximum": max(
                n * n for n in SUPERLINEAR_N
            ),
            "content_order_falsifier_count": len(CONTENT_ORDER_FALSIFIERS),
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos1049-fixed-diagonal-rational-clearing/1",
        "status": "exact_all_outward_forced_clearing_obstruction_primitive_content_open",
        "result": result,
        "experiment_contract": contract,
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [
                SOURCE_REF,
                DIAGONAL_REF,
                PRIMARY_SOURCE_REF,
                LEAN_REF,
                ANALYSIS_REF,
                PACKET_REF,
            ]
        ],
    }


def emit(payload: dict[str, Any], output: Path, check: bool) -> int:
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if check:
        if not output.exists() or output.read_text(encoding="utf-8") != rendered:
            print(f"stale receipt: {output}", file=sys.stderr)
            return 1
        print(json.dumps({"status": "current", "output": str(output)}))
        return 0
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(rendered, encoding="utf-8")
    print(json.dumps({"status": "written", "output": str(output)}))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    return emit(build_payload(), args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
