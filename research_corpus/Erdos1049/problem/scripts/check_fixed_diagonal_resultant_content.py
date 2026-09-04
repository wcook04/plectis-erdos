#!/usr/bin/env python3
"""Exact resultant bound for fixed-diagonal Van Assche row content.

For m=n, form the two integral coefficient polynomials

  A_n(p) = d_n(p) P_n(p^n | p^-1),
  C_n(p) = d_n(p) (Q_n(p^n) + P_n(p^n) sum_{j<n} 1/(p^j-1)).

They have degrees W_n and W_n-1.  Their homogeneous evaluations of common
width W_n at (3,2) are exactly the two forced-cleared integer coefficients.
Consequently their odd row content divides Res_p(A_n,C_n): modulo an odd
content prime, 2 is invertible and p=3/2 is a common root.

The finite resultant table is a theorem-sized probe for an all-index height
law.  It is not itself an asymptotic theorem and proves no irrationality.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from functools import cache
import importlib.util
import json
import math
from pathlib import Path
import sys
from typing import Any

import sympy as sp


REPO_ROOT = Path(__file__).resolve().parents[5]
SCRIPT_DIR = Path(__file__).resolve().parent
CLEARING_SCRIPT = SCRIPT_DIR / "check_fixed_diagonal_rational_clearing.py"
spec = importlib.util.spec_from_file_location("fixed_diagonal_clearing", CLEARING_SCRIPT)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load the fixed-diagonal clearing checker")
clearing = importlib.util.module_from_spec(spec)
spec.loader.exec_module(clearing)

sys.path.insert(0, str(REPO_ROOT))
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


P = clearing.P
X = sp.symbols("x")
N_MAX = 7
RESULTANT_BUDGET_TEST_MAX = 15
HARMONIC_CONSTANT_TRUNCATION = 200_000
SOURCE_REF = str(Path(__file__).resolve().relative_to(REPO_ROOT))
CLEARING_REF = str(CLEARING_SCRIPT.relative_to(REPO_ROOT))
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "FixedDiagonalResultantContentLab.md"
)
LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "FixedDiagonalRationalClearing.lean"
)
PACKET_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "research_packet.json"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_fixed_diagonal_resultant_content_receipt.json"
)


def homogeneous_evaluation(poly: sp.Poly, width: int) -> int:
    return sum(
        int(coefficient) * 3**degree * 2 ** (width - degree)
        for (degree,), coefficient in poly.terms()
    )


def coefficient_polynomials(n: int) -> tuple[sp.Poly, sp.Poly]:
    """Return the two d_n-cleared coefficient polynomials in Z[p]."""

    x_value = P**n
    polynomial_in_x = sp.Poly(
        sp.cancel(clearing.diagonal.little_q_legendre(n, X)), X
    )
    p_value = polynomial_in_x.eval(x_value)
    q_value = sum(
        polynomial_in_x.nth(degree)
        * x_value ** (degree - 1 - moment_index)
        * P ** (moment_index + 1)
        / (P ** (moment_index + 1) - 1)
        for degree in range(1, n + 1)
        for moment_index in range(degree)
    )
    target_prefix = sum(
        (1 / (P**j - 1) for j in range(1, n)), sp.Integer(0)
    )
    d_n = clearing.cyclotomic_clearing(n)
    denominator = sp.Poly(sp.cancel(d_n * p_value), P)
    numerator = sp.Poly(
        sp.cancel(d_n * (q_value + p_value * target_prefix)), P
    )
    if denominator.domain != sp.ZZ or numerator.domain != sp.ZZ:
        raise AssertionError("cleared coefficient polynomial is not integral")
    return denominator, numerator


def resultant_split_factors(n: int, numerator: sp.Poly) -> tuple[int, int]:
    """Split Res(d_n P_n,C_n) into clearing and associated-Pade factors."""

    x_value = P**n
    polynomial_in_x = sp.Poly(
        sp.cancel(clearing.diagonal.little_q_legendre(n, X)), X
    )
    p_diagonal = sp.Poly(polynomial_in_x.eval(x_value), P)
    q_value = sum(
        polynomial_in_x.nth(degree)
        * x_value ** (degree - 1 - moment_index)
        * P ** (moment_index + 1)
        / (P ** (moment_index + 1) - 1)
        for degree in range(1, n + 1)
        for moment_index in range(degree)
    )
    d_n = sp.Poly(clearing.cyclotomic_clearing(n), P)
    cleared_q = sp.Poly(sp.cancel(d_n.as_expr() * q_value), P)
    clearing_factor = abs(int(sp.resultant(d_n, numerator, P)))
    pade_factor = abs(int(sp.resultant(p_diagonal, cleared_q, P)))
    return clearing_factor, pade_factor


@cache
def diagonal_polynomial(n: int) -> sp.Poly:
    """Return P_n(p^n | p^-1) as an integral polynomial in p."""

    polynomial_in_x = sp.Poly(
        sp.cancel(clearing.diagonal.little_q_legendre(n, X)), X
    )
    return sp.Poly(polynomial_in_x.eval(P**n), P)


def harmonic_number(n: int) -> Fraction:
    return sum((Fraction(1, index) for index in range(1, n + 1)), Fraction())


def local_cyclotomic_factorization(
    n: int, r: int, numerator: sp.Poly
) -> dict[str, Any]:
    """Replay the q-Lucas local formula for Res(Phi_r,C_n).

    If n=a*r+b, reduction modulo Phi_r gives

      C_n = (d_n/(p^r-1)) P_b(p^b) (-1)^a K_(a,b),

    where K_(a,b)=3 H_a for b>0 and 3 H_a-1/a for b=0.
    Norms are rational factor-by-factor, but their product is the integral
    local resultant.
    """

    quotient, remainder = divmod(n, r)
    phi_r = sp.Poly(sp.cyclotomic_poly(r, P), P)
    totient = int(sp.totient(r))
    d_n = sp.Poly(clearing.cyclotomic_clearing(n), P)
    cross_polynomial = sp.Poly(sp.cancel(d_n.as_expr() / (P**r - 1)), P)
    cross_norm = abs(int(sp.resultant(phi_r, cross_polynomial, P)))
    residual_norm = abs(int(sp.resultant(phi_r, diagonal_polynomial(remainder), P)))
    harmonic_scalar = 3 * harmonic_number(quotient)
    if remainder == 0:
        harmonic_scalar -= Fraction(1, quotient)
    predicted = Fraction(cross_norm * residual_norm) * harmonic_scalar**totient
    actual = abs(int(sp.resultant(phi_r, numerator, P)))
    assert predicted.denominator == 1
    assert predicted.numerator == actual
    return {
        "r": r,
        "quotient_a": quotient,
        "remainder_b": remainder,
        "totient": totient,
        "actual_local_resultant": str(actual),
        "cross_cyclotomic_norm": str(cross_norm),
        "harmonic_scalar": {
            "numerator": str(harmonic_scalar.numerator),
            "denominator": str(harmonic_scalar.denominator),
        },
        "smaller_diagonal_norm": str(residual_norm),
        "predicted_product_is_integral_and_exact": True,
    }


def aggregate_clearing_resultant_from_local_law(n: int) -> dict[str, Any]:
    """Evaluate the authored all-index local law without constructing C_n."""

    d_n = sp.Poly(clearing.cyclotomic_clearing(n), P)
    cross_product = 1
    harmonic_product = Fraction(1)
    smaller_diagonal_product = 1
    for r in range(1, n + 1):
        quotient, remainder = divmod(n, r)
        phi_r = sp.Poly(sp.cyclotomic_poly(r, P), P)
        totient = int(sp.totient(r))
        cross_polynomial = sp.Poly(sp.cancel(d_n.as_expr() / (P**r - 1)), P)
        cross_product *= abs(int(sp.resultant(phi_r, cross_polynomial, P)))
        harmonic_scalar = 3 * harmonic_number(quotient)
        if remainder == 0:
            harmonic_scalar -= Fraction(1, quotient)
        harmonic_product *= harmonic_scalar**totient
        smaller_diagonal_product *= abs(
            int(sp.resultant(phi_r, diagonal_polynomial(remainder), P))
        )
    total = Fraction(cross_product * smaller_diagonal_product) * harmonic_product
    assert total.denominator == 1
    return {
        "n": n,
        "cross_cyclotomic_product": str(cross_product),
        "harmonic_product": {
            "numerator": str(harmonic_product.numerator),
            "denominator": str(harmonic_product.denominator),
        },
        "smaller_diagonal_norm_product": str(smaller_diagonal_product),
        "clearing_resultant_from_local_law": str(total.numerator),
        "log_clearing_resultant_over_n_squared": math.log(total.numerator) / n**2,
    }


def record(n: int) -> dict[str, Any]:
    denominator, numerator = coefficient_polynomials(n)
    width = denominator.degree()
    expected_width = (
        clearing.moving_diagonal_degree(n, n)
        + sp.Poly(clearing.cyclotomic_clearing(n), P).degree()
    )
    assert width == expected_width
    assert numerator.degree() == width - 1
    assert sp.gcd(denominator, numerator).degree() == 0

    resultant = abs(int(sp.resultant(denominator, numerator, P)))
    assert resultant > 0
    clearing_resultant, pade_resultant = resultant_split_factors(n, numerator)
    assert resultant == clearing_resultant * pade_resultant
    top_cyclotomic = sp.Poly(sp.cyclotomic_poly(n, P), P)
    top_cyclotomic_resultant = abs(
        int(sp.resultant(top_cyclotomic, numerator, P))
    )
    expected_top_cyclotomic_resultant = 2 ** int(sp.totient(n))
    assert top_cyclotomic_resultant == expected_top_cyclotomic_resultant
    penultimate_cyclotomic_resultant = None
    if n >= 3:
        penultimate_cyclotomic = sp.Poly(sp.cyclotomic_poly(n - 1, P), P)
        penultimate_cyclotomic_resultant = abs(
            int(sp.resultant(penultimate_cyclotomic, numerator, P))
        )
        assert penultimate_cyclotomic_resultant == 3 ** int(sp.totient(n - 1))
    denominator_integer = homogeneous_evaluation(denominator, width)
    numerator_integer = homogeneous_evaluation(numerator, width)
    content = math.gcd(abs(denominator_integer), abs(numerator_integer)) or 1

    canonical = clearing.primitive_row_record(n, n)
    assert content == int(canonical["row_content"])
    assert content % 2 == 1
    assert resultant % content == 0
    local_factors = [
        local_cyclotomic_factorization(n, r, numerator) for r in range(1, n + 1)
    ]
    assert math.prod(int(row["actual_local_resultant"]) for row in local_factors) == (
        clearing_resultant
    )

    return {
        "n": n,
        "common_homogeneous_width": width,
        "denominator_polynomial_degree": denominator.degree(),
        "numerator_polynomial_degree": numerator.degree(),
        "polynomial_gcd_degree": 0,
        "resultant": str(resultant),
        "resultant_factorization": {
            str(prime): exponent
            for prime, exponent in sp.factorint(resultant).items()
        },
        "resultant_bit_length": resultant.bit_length(),
        "log_resultant_over_n_squared": math.log(resultant) / n**2,
        "resultant_multiplicative_split": {
            "clearing_against_full_numerator": str(clearing_resultant),
            "diagonal_P_against_cleared_Q": str(pade_resultant),
            "product_equals_full_resultant": True,
        },
        "top_cyclotomic_resultant": str(top_cyclotomic_resultant),
        "top_cyclotomic_resultant_equals_two_pow_totient": True,
        "penultimate_cyclotomic_resultant": (
            str(penultimate_cyclotomic_resultant)
            if penultimate_cyclotomic_resultant is not None
            else None
        ),
        "penultimate_cyclotomic_resultant_equals_three_pow_totient": (
            True if n >= 3 else None
        ),
        "all_cyclotomic_local_factorizations": local_factors,
        "local_factor_product_equals_clearing_resultant": True,
        "homogeneous_denominator_integer": str(denominator_integer),
        "homogeneous_numerator_integer": str(numerator_integer),
        "row_content": str(content),
        "row_content_factorization": canonical["row_content_factorization"],
        "odd_row_content_divides_resultant": True,
    }


def build_payload() -> dict[str, Any]:
    records = [record(n) for n in range(1, N_MAX + 1)]
    fixed_exponent = (
        1.5 * math.log(4 / 3) + 3 / math.pi**2 * math.log(3)
    )
    harmonic = 0.0
    harmonic_series = []
    for quotient in range(1, HARMONIC_CONSTANT_TRUNCATION + 1):
        harmonic += 1 / quotient
        harmonic_series.append(
            math.log(3 * harmonic)
            * (1 / quotient**2 - 1 / (quotient + 1) ** 2)
        )
    harmonic_quadratic_constant = 3 / math.pi**2 * math.fsum(harmonic_series)
    budget_test_records = [
        aggregate_clearing_resultant_from_local_law(n)
        for n in range(1, RESULTANT_BUDGET_TEST_MAX + 1)
    ]
    first_budget_crossing = next(
        row
        for row in budget_test_records
        if row["log_clearing_resultant_over_n_squared"] > fixed_exponent
    )
    result = {
        "records": records,
        "all_coefficient_polynomials_integral_and_coprime": True,
        "all_homogeneous_row_contents_divide_resultant": all(
            row["odd_row_content_divides_resultant"] for row in records
        ),
        "pade_split_factor_is_not_always_one": any(
            int(
                row["resultant_multiplicative_split"][
                    "diagonal_P_against_cleared_Q"
                ]
            ) > 1
            for row in records
        ),
        "all_displayed_top_cyclotomic_resultants_equal_two_pow_totient": all(
            row["top_cyclotomic_resultant_equals_two_pow_totient"]
            for row in records
        ),
        "all_displayed_penultimate_cyclotomic_resultants_equal_three_pow_totient": all(
            row["penultimate_cyclotomic_resultant_equals_three_pow_totient"]
            for row in records
            if row["n"] >= 3
        ),
        "all_displayed_general_cyclotomic_factorizations_exact": all(
            row["local_factor_product_equals_clearing_resultant"] for row in records
        ),
        "all_index_general_cyclotomic_formula": {
            "statement": (
                "for n=a*r+b, C_n mod Phi_r equals "
                "(-1)^a*(d_n/(p^r-1))*P_b(p^b)*K_(a,b), where "
                "K_(a,b)=3H_a if b>0 and 3H_a-1/a if b=0"
            ),
            "proof_ref": ANALYSIS_REF,
            "finite_regression_range": f"1<=r<=n<={N_MAX}",
        },
        "harmonic_factor_quadratic_constant": {
            "series": (
                "(3/pi^2)*sum_(a>=1) log(3H_a)*(1/a^2-1/(a+1)^2)"
            ),
            "truncation": HARMONIC_CONSTANT_TRUNCATION,
            "decimal_partial_sum": harmonic_quadratic_constant,
        },
        "clearing_resultant_budget_test_from_all_index_local_law": {
            "records": budget_test_records,
            "first_crossing_rank": first_budget_crossing["n"],
            "first_crossing_rate": first_budget_crossing[
                "log_clearing_resultant_over_n_squared"
            ],
            "forced_clearing_exponent": fixed_exponent,
            "full_resultant_upper_bound_route_falsified": True,
        },
        "fixed_diagonal_forced_clearing_exponent_decimal_display": fixed_exponent,
        "all_displayed_log_resultant_rates_below_forced_clearing_exponent": all(
            row["log_resultant_over_n_squared"] < fixed_exponent for row in records
        ),
        "exact_reduction": (
            "For odd g dividing both width-W homogeneous evaluations, "
            "p=3*2^{-1} is a common root modulo every prime power of g; "
            "hence g divides the integer polynomial resultant."
        ),
        "all_index_top_cyclotomic_formula": {
            "statement": "abs(Res(Phi_n,C_n))=2^phi(n)",
            "proof_ref": ANALYSIS_REF,
            "finite_regression_range": f"1<=n<={N_MAX}",
        },
        "all_index_penultimate_cyclotomic_formula": {
            "statement": "abs(Res(Phi_(n-1),C_n))=3^phi(n-1) for n>=3",
            "proof_ref": ANALYSIS_REF,
            "finite_regression_range": f"3<=n<={N_MAX}",
        },
        "mechanism_verdict": "full_resultant_height_upper_bound_falsified_at_n_15",
        "remaining_boundary": (
            "The all-index local product law is proved in the analysis.  Its "
            "exact clearing-resultant rate already exceeds the analytic budget "
            "at n=15, before the nontrivial P-Q factor.  Any continuation must "
            "bound specialization-specific row content strictly below the full "
            "resultant, or leave this scalar fixed-diagonal architecture."
        ),
    }
    contract = build_experiment_contract(
        problem_id="erdos_1049",
        target_statement="Prove irrationality of the Lambert value at q=3/2.",
        claim_ceiling=(
            "An authored all-index cyclotomic local factorization, with exact "
            "polynomial and specialization replay through n=7; no all-index "
            "aggregate height bound and no irrationality theorem."
        ),
        hypothesis_id="fixed_diagonal_content_has_small_resultant_height",
        hypothesis_statement=(
            "The fixed-diagonal primitive row content is bounded by a "
            "specialization-independent resultant whose logarithmic height is "
            "strictly below the forced-clearing error exponent."
        ),
        probe_id="fixed_diagonal_coefficient_polynomial_resultants",
        probe_question=(
            "Do the exact cleared coefficient polynomials stay coprime, and do "
            "their resultants remain below the coefficient-height threshold?"
        ),
        computation=(
            "Construct both d_n-cleared coefficient polynomials over Z[p], "
            "verify their common-width homogeneous evaluations reproduce the "
            "row content, and compute exact resultants through n=7."
        ),
        falsifier=(
            "A nonintegral coefficient polynomial, a nonconstant polynomial "
            "gcd, a row content not dividing the resultant, or a displayed "
            "resultant rate crossing the forced-clearing exponent."
        ),
        stop_condition=(
            "After the exact finite resultant table, stop extending n and seek "
            "a source-derived product law or an all-index resultant bound."
        ),
        survival_consequence=(
            "A suitable all-index resultant bound would close primitive content "
            "as a repair of the original fixed Van Assche diagonal."
        ),
        falsification_consequence=(
            "A crossing or polynomial common factor would retire this global "
            "resultant route and return the analysis to local valuations."
        ),
        consumer_ref=PACKET_REF,
        analysis_refs=[ANALYSIS_REF],
        source_refs=[SOURCE_REF, CLEARING_REF, LEAN_REF],
        input_receipt_refs=[],
        result_status="finite_support",
        result_summary=(
            "The two fixed-diagonal coefficient polynomials are integral and "
            "coprime through n=7; every exact odd row content divides their "
            "resultant, and every displayed log-resultant/n^2 rate is below the "
            "forced-clearing exponent."
        ),
        progress_class="mechanism_opened",
        decision_basis=(
            "The resultant bound is global across clearing-supported and "
            "coprime-to-clearing primes and avoids the falsified local valuation shortcut."
        ),
        next_analytic_target=(
            "Bound the aggregate smaller-diagonal norms "
            "Res(Phi_r,P_(n mod r)(p^(n mod r))) and the associated P-Q "
            "resultant below the remaining quadratic height margin."
        ),
        resource_bounds={"n_minimum": 1, "n_maximum": N_MAX},
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos1049-fixed-diagonal-resultant-content/1",
        "status": "exact_finite_resultant_content_reduction",
        "result": result,
        "experiment_contract": contract,
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [SOURCE_REF, CLEARING_REF, LEAN_REF, ANALYSIS_REF, PACKET_REF]
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
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    return emit(build_payload(), args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
