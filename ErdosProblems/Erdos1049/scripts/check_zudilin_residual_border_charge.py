#!/usr/bin/env python3
"""Exact residual-border probe for Zudilin's #1049 Hankel determinant.

After extracting the source scalar factors H_i H_j, the Phi_d exponent in a
residual entry is e_d(i+j)-e_d(i)-e_d(j).  On the southeast block i,j >= d
this exponent is one plus three times a floor carry, hence is either 1 or 4.
The generic determinant lemma therefore forces Phi_d^(N-2d).  This checker
replays that exponent law, proves its valuation-assignment bound sharp by an
explicit residue-antitone permutation, records the strict charge no-go, and
uses exact specializations to certify rank-five content without a full
bivariate determinant expansion.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

import sympy as sp


REPO_ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(REPO_ROOT))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_zudilin_scalar_content import (  # noqa: E402
    cleared_row,
    content_signature,
    mu,
    p,
    polynomial_gcd,
    predicted_content,
    scalar_factor_degree,
)
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
)
from system.lib.formal_math_polynomial_content import (  # noqa: E402
    specialization_saturated_gcd,
)


SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "scripts/check_zudilin_residual_border_charge.py"
)
SCALAR_SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "scripts/check_zudilin_scalar_content.py"
)
PRIMARY_SOURCE_REF = "annexes/arxiv-1601-02688-zudilin-generalized-q-logarithm/extracted.md"
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "ZudilinResidualBorderChargeLab.md"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "AdelicHeightBridge.lean"
)
BLOCK_CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "SoutheastBlockDeterminant.lean"
)
POLYNOMIAL_CONTENT_REF = "system/lib/formal_math_polynomial_content.py"
CONSUMER_DECLARATIONS = [
    "zudilinScalarPlusBorder_ceiling_lt_required",
    "zudilinScalarPlusBorder_cannot_meet_required_charge",
]


def cyclotomic_exponent(d: int, n: int) -> int:
    return max(3 * (n // d) - 1, 0)


def residual_exponent(d: int, i: int, j: int) -> int:
    return (
        cyclotomic_exponent(d, i + j)
        - cyclotomic_exponent(d, i)
        - cyclotomic_exponent(d, j)
    )


def border_charge(rank: int) -> int:
    return sum(
        int(sp.totient(d)) * (rank - 2 * d)
        for d in range(1, (rank - 1) // 2 + 1)
    )


def residue_antitone_permutation(rank: int, d: int) -> list[int]:
    """Exhibit an assignment attaining the southeast lower bound ``N-2d``.

    Reverse the first ``2d`` columns.  On the remaining consecutive tail,
    match row residues in increasing order with column residues in decreasing
    order.  The tail residue multiset consists of complete residue cycles and
    one initial segment, so every matched residue sum is below ``d``.
    """

    if not 1 <= d or not 2 * d < rank:
        raise ValueError("the sharp border assignment requires 1 <= 2d < rank")
    permutation = [-1] * rank
    for index in range(2 * d):
        permutation[index] = 2 * d - 1 - index
    tail_rows = sorted(range(2 * d, rank), key=lambda index: (index % d, index))
    tail_columns = sorted(
        range(2 * d, rank), key=lambda index: (-(index % d), index)
    )
    for row, column in zip(tail_rows, tail_columns):
        permutation[row] = column
    if sorted(permutation) != list(range(rank)):
        raise AssertionError("constructed assignment is not a permutation")
    return permutation


def valuation_assignment_check(rank: int, d: int) -> dict[str, object]:
    permutation = residue_antitone_permutation(rank, d)
    entry_orders = [
        residual_exponent(d, row, permutation[row]) for row in range(rank)
    ]
    achieved = sum(entry_orders)
    lower_bound = rank - 2 * d
    return {
        "rank": rank,
        "d": d,
        "southeast_block_lower_bound": lower_bound,
        "explicit_assignment_order": achieved,
        "assignment_attains_lower_bound": achieved == lower_bound,
        "zero_order_entry_count": entry_orders.count(0),
        "unit_order_entry_count": entry_orders.count(1),
        "all_assignment_entries_have_order_zero_or_one": set(entry_orders) <= {0, 1},
        "permutation": permutation,
    }


def residual_determinant_check(rank: int) -> dict[str, object]:
    rows = [cleared_row(n) for n in range(2 * rank - 1)]
    moments = [a.as_expr() * mu - b.as_expr() - c.as_expr() for a, b, c in rows]
    h = [sp.cancel(predicted_content(n) / p ** (n + 1)) for n in range(rank)]
    matrix = sp.Matrix(
        rank,
        rank,
        lambda i, j: sp.cancel(moments[i + j] / (h[i] * h[j])),
    )
    determinant = sp.expand(matrix.det(method="domain-ge"))
    coefficients = [
        sp.Poly(coefficient, p)
        for coefficient in sp.Poly(determinant, mu).all_coeffs()
    ]
    gcd = polynomial_gcd(coefficients)
    signature = content_signature(gcd, 2 * rank - 2)
    expected_orders = {
        str(d): rank - 2 * d
        for d in range(1, (rank - 1) // 2 + 1)
    }
    observed_orders = signature["cyclotomic_orders"]
    return {
        "rank": rank,
        "mu_degree": sp.Poly(determinant, mu).degree(),
        "p_degree": int(sp.degree(determinant, p)),
        "content_degree": gcd.degree(),
        "content_signature": signature,
        "expected_forced_cyclotomic_orders": expected_orders,
        "no_extra_cyclotomic_or_unaccounted_factor": (
            observed_orders == expected_orders
            and signature["unaccounted_quotient"] == "1"
        ),
    }


def residual_specialization_sandwich(rank: int) -> dict[str, object]:
    """Upper-bound bivariate coefficient content by two exact evaluations."""

    rows = [cleared_row(n) for n in range(2 * rank - 1)]
    moments = [a.as_expr() * mu - b.as_expr() - c.as_expr() for a, b, c in rows]
    h = [sp.cancel(predicted_content(n) / p ** (n + 1)) for n in range(rank)]
    determinants: dict[int, sp.Poly] = {}
    for value in (0, 1):
        matrix = sp.Matrix(
            rank,
            rank,
            lambda i, j: sp.Poly(
                sp.cancel(moments[i + j].subs(mu, value) / (h[i] * h[j])), p
            ).as_expr(),
        )
        determinants[value] = sp.Poly(matrix.det(method="domain-ge"), p)
    profile, saturated_gcd, p_order = specialization_saturated_gcd(
        determinants, sp.Poly(p, p)
    )
    expected = sp.Poly(
        sp.prod(
            sp.cyclotomic_poly(d, p) ** (rank - 2 * d)
            for d in range(1, (rank - 1) // 2 + 1)
        ),
        p,
    ).monic()
    return {
        "rank": rank,
        "specialization_values": list(profile.labels),
        "specialized_determinant_degrees": list(profile.degrees),
        "specialization_gcd_degree": profile.gcd.degree(),
        "specialization_gcd_factorization": str(sp.factor(profile.gcd.as_expr())),
        "specialization_gcd_p_order": p_order,
        "p_saturated_specialization_gcd": str(sp.factor(saturated_gcd.as_expr())),
        "expected_forced_non_p_factor": str(sp.factor(expected.as_expr())),
        "p_saturated_gcd_equals_forced_factor": saturated_gcd == expected,
        "sandwich_consequence": (
            "Because the forced cyclotomic factor divides every mu coefficient "
            "and coefficient content divides every specialization, equality of "
            "the p-saturated specialization gcd proves exact non-p content."
        ),
    }
def compute(max_exact_rank: int, table_max_rank: int, exponent_grid_max: int) -> dict[str, object]:
    exponent_checks = []
    for d in range(1, exponent_grid_max + 1):
        values = {
            residual_exponent(d, i, j)
            for i in range(d, exponent_grid_max + 1)
            for j in range(d, exponent_grid_max + 1)
        }
        exponent_checks.append(
            {
                "d": d,
                "observed_southeast_residual_exponents": sorted(values),
                "all_are_one_or_four": values <= {1, 4},
                "block_is_divisible": min(values) >= 1,
            }
        )

    degree_table = []
    for rank in range(2, table_max_rank + 1):
        scalar = scalar_factor_degree(rank)
        border = border_charge(rank)
        coarse_combined = 2 * rank**3 - rank
        required_scaled = 39 * (4 * rank**3 - 3 * rank**2)
        degree_table.append(
            {
                "rank": rank,
                "exact_scalar_degree": scalar,
                "exact_border_charge": border,
                "exact_combined_degree": scalar + border,
                "coarse_combined_ceiling": coarse_combined,
                "coarse_ceiling_scaled_by_41": 41 * coarse_combined,
                "required_charge_scaled_by_41": required_scaled,
                "coarse_ceiling_is_below_required_charge": (
                    41 * coarse_combined < required_scaled
                ),
            }
        )

    determinants = [
        residual_determinant_check(rank)
        for rank in range(1, max_exact_rank + 1)
    ]
    assignment_checks = [
        valuation_assignment_check(rank, d)
        for rank in range(3, table_max_rank + 1)
        for d in range(1, (rank - 1) // 2 + 1)
    ]
    selected_assignment_checks = [
        row
        for row in assignment_checks
        if row["rank"] <= 8 or row["rank"] in {16, 32, table_max_rank}
    ]
    rank_five_sandwich = residual_specialization_sandwich(5)
    return {
        "all_rank_residual_exponent_identity": (
            "for i,j>=d, r_d(i,j)=1+3*"
            "(floor((i+j)/d)-floor(i/d)-floor(j/d)) in {1,4}"
        ),
        "forced_residual_factor": (
            "prod_{1<=d, 2d<N} Phi_d(p)^(N-2d) divides the primitive residual determinant"
        ),
        "border_charge_formula": "sum_{1<=d,2d<N} phi(d)(N-2d)",
        "border_charge_ceiling": "B_N <= N^3",
        "scalar_plus_border_ceiling": "degree <= 2N^3-N",
        "exponent_checks": exponent_checks,
        "all_exponent_checks_pass": all(
            row["all_are_one_or_four"] and row["block_is_divisible"]
            for row in exponent_checks
        ),
        "degree_table": degree_table,
        "all_charge_no_go_checks_pass": all(
            row["coarse_ceiling_is_below_required_charge"] for row in degree_table
        ),
        "residual_determinant_checks": determinants,
        "all_finite_determinants_have_only_forced_cyclotomic_content": all(
            row["no_extra_cyclotomic_or_unaccounted_factor"] for row in determinants
        ),
        "valuation_assignment_check_count": len(assignment_checks),
        "selected_valuation_assignment_witnesses": selected_assignment_checks,
        "all_explicit_assignments_attain_border_lower_bound": all(
            row["assignment_attains_lower_bound"]
            and row["all_assignment_entries_have_order_zero_or_one"]
            for row in assignment_checks
        ),
        "all_rank_tropical_sharpness": (
            "The southeast block forces order N-2d, and the explicit residue-"
            "antitone permutation has total order N-2d. Entrywise cyclotomic "
            "valuations alone therefore force no deeper determinant charge."
        ),
        "rank_five_specialization_content_sandwich": rank_five_sandwich,
    }


def emit(result: dict[str, object], output: Path | None, check: bool) -> int:
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if output is None:
        print(rendered, end="")
        return 0
    resolved = output.resolve()
    if check:
        if not resolved.exists() or resolved.read_text(encoding="utf-8") != rendered:
            print(f"stale receipt: {resolved}", file=sys.stderr)
            return 1
        print(json.dumps({"status": "current", "output": str(resolved)}))
        return 0
    resolved.parent.mkdir(parents=True, exist_ok=True)
    resolved.write_text(rendered, encoding="utf-8")
    print(json.dumps({"status": "written", "output": str(resolved)}))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-exact-rank", type=int, default=4)
    parser.add_argument("--table-max-rank", type=int, default=64)
    parser.add_argument("--exponent-grid-max", type=int, default=32)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if not 1 <= args.max_exact_rank <= 4:
        parser.error("--max-exact-rank must lie in [1,4]")
    if args.table_max_rank < 2 or args.exponent_grid_max < 1:
        parser.error("table rank must be at least 2 and exponent grid must be positive")
    if args.check and args.output is None:
        parser.error("--check requires --output")

    scan = compute(args.max_exact_rank, args.table_max_rank, args.exponent_grid_max)
    result = {
        "schema": "erdos1049-zudilin-residual-border-charge/1",
        "claim_ceiling": (
            "The source-natural primitive residual determinant has a new all-rank "
            "cyclotomic border factor, but its entry-valuation lower bound is exact "
            "and scalar plus border content is strictly insufficient for the 3/2 "
            "threshold. Genuine determinant cancellation remains open."
        ),
        "parameters": {
            "max_exact_rank": args.max_exact_rank,
            "table_max_rank": args.table_max_rank,
            "exponent_grid_max": args.exponent_grid_max,
        },
        "scan": scan,
        "experiment_contract": build_experiment_contract(
            problem_id="erdos_1049",
            target_statement="Prove irrationality of the rational-base Lambert value at p=3/2.",
            claim_ceiling=(
                "All-rank source algebra and the generic determinant lemma prove the "
                "border factor; Lean proves its coarse combined ceiling insufficient. "
                "Finite determinants are regression evidence only."
            ),
            hypothesis_id="zudilin_primitive_southeast_blocks_supply_required_charge",
            hypothesis_statement=(
                "After scalar extraction, the universally forced southeast cyclotomic "
                "blocks remove enough additional cubic charge at p=3/2."
            ),
            probe_id="residual_cyclotomic_floor_carry_and_border_charge",
            probe_question=(
                "Which Phi_d factors divide the primitive residual matrix at every "
                "rank, and can the forced determinant charge close the 39/41 deficit?"
            ),
            computation=(
                "Compute the exact residual exponent from the source H_n factors, "
                "sum the determinant block charges, construct an all-rank optimal "
                "valuation assignment, symbolically factor primitive Hankel "
                "determinants through rank four, and sandwich rank-five coefficient "
                "content between two exact specializations and the forced factor."
            ),
            falsifier=(
                "An all-rank scalar-plus-border ceiling below the required extraction "
                "eliminates first-order southeast-block content as sufficient; an "
                "assignment attaining the lower bound eliminates any stronger "
                "entry-valuation-only extraction."
            ),
            stop_condition=(
                "Once the all-rank border factor and strict combined no-go are proved, "
                "move to deeper residual valuations, cancellation, or another model."
            ),
            survival_consequence=(
                "Sufficient border charge would complete the missing arithmetic side "
                "of the normalized Hankel route."
            ),
            falsification_consequence=(
                "The factor is retained, but any successful residual route must use "
                "higher valuations or nontrivial determinant cancellation."
            ),
            consumer_ref=CONSUMER_REF,
            consumer_declarations=CONSUMER_DECLARATIONS,
            analysis_refs=[ANALYSIS_REF],
            source_refs=[
                SOURCE_REF,
                SCALAR_SOURCE_REF,
                PRIMARY_SOURCE_REF,
                BLOCK_CONSUMER_REF,
                POLYNOMIAL_CONTENT_REF,
            ],
            result_status="exact_one_way_result",
            result_summary=(
                "For every d, primitive residual entries with i,j>=d contain Phi_d "
                "to exponent 1 or 4, forcing product Phi_d^(N-2d). Its charge is at "
                "most N^3, and together with scalar content is at most 2N^3-N, still "
                "strictly below the required charge. An explicit all-rank assignment "
                "attains order N-2d, eliminating any stronger bound from entry "
                "valuations alone. A two-specialization sandwich proves that rank "
                "five has exactly Phi_1^3 Phi_2 after p-saturation and no extra "
                "primitive non-p factor."
            ),
            progress_class="mechanism_eliminated",
            decision_basis=(
                "The exact all-rank inequality eliminates the structurally distinct "
                "hypothesis that scalar content plus every universally forced "
                "first-order southeast block can supply the missing charge. The "
                "matching upper witness additionally eliminates nested entrywise "
                "valuation extraction beyond that border factor."
            ),
            next_analytic_target=(
                "Test genuine cancellation of the minimum-valuation determinant "
                "terms modulo Phi_d, or abandon this integral model for a "
                "congruence-constrained construction."
            ),
            resource_bounds={
                "maximum_exact_residual_hankel_rank": args.max_exact_rank,
                "maximum_specialization_sandwich_rank": 5,
                "maximum_exponent_grid_index": args.exponent_grid_max,
                "degree_table_max_rank": args.table_max_rank,
            },
        ),
        "sources": [
            source_record(REPO_ROOT, SOURCE_REF),
            source_record(REPO_ROOT, SCALAR_SOURCE_REF),
            source_record(REPO_ROOT, PRIMARY_SOURCE_REF),
            source_record(REPO_ROOT, CONSUMER_REF),
            source_record(REPO_ROOT, BLOCK_CONSUMER_REF),
            source_record(REPO_ROOT, POLYNOMIAL_CONTENT_REF),
            source_record(REPO_ROOT, ANALYSIS_REF),
        ],
    }
    return emit(result, args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
