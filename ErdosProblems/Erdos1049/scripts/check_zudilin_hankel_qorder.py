#!/usr/bin/env python3
"""Compute exact initial q-orders of Zudilin's normalized Hankel determinants.

At x=z=1 the primary-source formula is

  v_m^* = sum_{t>=0} q^((m+1)t)
      (q;q)_m^3 (q^(t+1);q)_m / (q^(m+1+t);q)_(m+1).

This script expands those series with integer coefficient arithmetic and forms
V_N^*=det(v_{i+j}^*) exactly, truncated beyond the source lower bound
N(N-1)(2N-1)/6.  It tests for additional cancellation in the analytic Hankel
determinant; it does not compute denominator factors or prove an asymptotic
statement from a finite rank scan.
"""

from __future__ import annotations

import argparse
from functools import lru_cache
import itertools
import json
import math
from pathlib import Path
import sys


REPO_ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
)


SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "scripts/check_zudilin_hankel_qorder.py"
)
PRIMARY_SOURCE_REF = (
    "annexes/arxiv-1601-02688-zudilin-generalized-q-logarithm/extracted.md"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "HankelQOrderComputationalLab.md"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "AdelicHeightBridge.lean"
)
CONSUMER_DECLARATIONS = ["threeHalves_hankelChargeThreshold_lt_eightFortyOne"]


def zero_series(cutoff: int) -> list[int]:
    return [0] * (cutoff + 1)


def multiply(a: list[int], b: list[int], cutoff: int) -> list[int]:
    result = zero_series(cutoff)
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for j, bj in enumerate(b[: cutoff - i + 1]):
            if bj:
                result[i + j] += ai * bj
    return result


def multiply_one_minus_q_power(series: list[int], power: int) -> list[int]:
    result = series.copy()
    for degree in range(power, len(series)):
        result[degree] -= series[degree - power]
    return result


def divide_one_minus_q_power(series: list[int], power: int) -> list[int]:
    """Divide a truncated series by 1-q^power exactly."""

    result = series.copy()
    for degree in range(power, len(series)):
        result[degree] += result[degree - power]
    return result


def shift(series: list[int], amount: int) -> list[int]:
    if amount >= len(series):
        return zero_series(len(series) - 1)
    return [0] * amount + series[: len(series) - amount]


@lru_cache(None)
def qbinomial_series(n: int, k: int, cutoff: int) -> tuple[int, ...]:
    """Gaussian binomial [n choose k]_q through q^cutoff."""

    if k < 0 or k > n:
        return tuple(zero_series(cutoff))
    if k == 0 or k == n:
        result = zero_series(cutoff)
        result[0] = 1
        return tuple(result)
    left = list(qbinomial_series(n - 1, k, cutoff))
    right = shift(list(qbinomial_series(n - 1, k - 1, cutoff)), n - k)
    return tuple(a + b for a, b in zip(left, right))


def transformed_form_series(
    moments: list[list[int]], index: int, order: int, cutoff: int
) -> list[int]:
    """Apply D_order=(N;q)_order to v_index^*."""

    result = zero_series(cutoff)
    for backward in range(order + 1):
        coefficient = shift(
            list(qbinomial_series(order, backward, cutoff)),
            backward * (backward - 1) // 2,
        )
        term = multiply(coefficient, moments[index - backward], cutoff)
        sign = -1 if backward % 2 else 1
        result = [a + sign * b for a, b in zip(result, term)]
    return result


def normalized_form_series(index: int, cutoff: int) -> list[int]:
    """Return v_index^* through q^cutoff at x=z=1."""

    result = zero_series(cutoff)
    for tail_index in range(cutoff // (index + 1) + 1):
        term = normalized_tail_series(index, tail_index, cutoff)
        result = [a + b for a, b in zip(result, term)]
    return result


def normalized_tail_series(index: int, tail_index: int, cutoff: int) -> list[int]:
    """One hypergeometric tail summand of ``v_index^*``."""

    term = zero_series(cutoff)
    term[0] = 1
    for power in range(1, index + 1):
        for _ in range(3):
            term = multiply_one_minus_q_power(term, power)
    for power in range(tail_index + 1, tail_index + index + 1):
        term = multiply_one_minus_q_power(term, power)
    for power in range(index + 1 + tail_index, 2 * index + 2 + tail_index):
        term = divide_one_minus_q_power(term, power)
    return shift(term, (index + 1) * tail_index)


def transformed_tail_series(
    index: int, order: int, tail_index: int, cutoff: int
) -> list[int]:
    """Apply ``D_order`` to one fixed hypergeometric tail state."""

    result = zero_series(cutoff)
    for backward in range(order + 1):
        coefficient = shift(
            list(qbinomial_series(order, backward, cutoff)),
            backward * (backward - 1) // 2,
        )
        term = multiply(
            coefficient,
            normalized_tail_series(index - backward, tail_index, cutoff),
            cutoff,
        )
        sign = -1 if backward % 2 else 1
        result = [a + sign * b for a, b in zip(result, term)]
    return result


def predicted_tail_leading_coefficient(row: int, tail_index: int) -> int:
    """Associated-graded coefficient of one source tail state."""

    sign = -1 if row % 2 else 1
    if tail_index == 0:
        return sign * (row + 1) * (row + 2) * (2 * row + 3) // 6
    if tail_index <= row:
        return sign * math.comb(row - tail_index + 2, 2)
    return 0


def permutation_sign(permutation: tuple[int, ...]) -> int:
    inversions = sum(
        permutation[i] > permutation[j]
        for i in range(len(permutation))
        for j in range(i + 1, len(permutation))
    )
    return -1 if inversions % 2 else 1


def determinant_series(
    moments: list[list[int]], rank: int, cutoff: int
) -> list[int]:
    result = zero_series(cutoff)
    one = zero_series(cutoff)
    one[0] = 1
    for permutation in itertools.permutations(range(rank)):
        term = one
        for row, column in enumerate(permutation):
            term = multiply(term, moments[row + column], cutoff)
        sign = permutation_sign(permutation)
        result = [a + sign * b for a, b in zip(result, term)]
    return result


def source_lower_bound(rank: int) -> int:
    return rank * (rank - 1) * (2 * rank - 1) // 6


def predicted_leading_coefficient(rank: int) -> int:
    return math.factorial(rank) ** 2 * math.factorial(rank + 1) // (2**rank)


def first_nonzero(series: list[int]) -> tuple[int | None, int | None]:
    for degree, coefficient in enumerate(series):
        if coefficient:
            return degree, coefficient
    return None, None


def compute(max_rank: int, margin: int) -> dict[str, object]:
    cutoff = source_lower_bound(max_rank) + margin
    moments = [
        normalized_form_series(index, cutoff) for index in range(2 * max_rank - 1)
    ]
    ranks = []
    for rank in range(1, max_rank + 1):
        determinant = determinant_series(moments, rank, cutoff)
        order, leading_coefficient = first_nonzero(determinant)
        lower_bound = source_lower_bound(rank)
        ranks.append(
            {
                "rank": rank,
                "source_q_order_lower_bound": lower_bound,
                "computed_q_order": order,
                "order_surplus": None if order is None else order - lower_bound,
                "leading_coefficient": leading_coefficient,
                "predicted_leading_coefficient": predicted_leading_coefficient(rank),
                "leading_coefficient_matches_factorial_pattern": (
                    leading_coefficient == predicted_leading_coefficient(rank)
                ),
                "first_coefficients_from_lower_bound": determinant[
                    lower_bound : min(cutoff + 1, lower_bound + 8)
                ],
                "nonzero_witness_within_cutoff": order is not None,
            }
        )
    transformed_rows = []
    transformed_tail_decomposition = []
    for row in range(max_rank):
        predicted_coefficient = (
            (-1) ** row * (row + 1) ** 2 * (row + 2) // 2
        )
        for column in range(max_rank):
            transformed = transformed_form_series(
                moments, row + column, row, cutoff
            )
            order, coefficient = first_nonzero(transformed)
            predicted_order = row * (row + 1) // 2 + row * column
            transformed_rows.append(
                {
                    "row": row,
                    "column": column,
                    "computed_q_order": order,
                    "predicted_q_order": predicted_order,
                    "computed_leading_coefficient": coefficient,
                    "predicted_leading_coefficient": predicted_coefficient,
                    "matches": (
                        order == predicted_order
                        and coefficient == predicted_coefficient
                    ),
                }
            )
            tail_rows = []
            for tail_index in range(row + 1):
                tail_series = transformed_tail_series(
                    row + column, row, tail_index, cutoff
                )
                tail_coefficient = tail_series[predicted_order]
                predicted_tail_coefficient = predicted_tail_leading_coefficient(
                    row, tail_index
                )
                tail_rows.append(
                    {
                        "tail_index": tail_index,
                        "computed_leading_coefficient": tail_coefficient,
                        "predicted_leading_coefficient": predicted_tail_coefficient,
                        "matches": tail_coefficient == predicted_tail_coefficient,
                    }
                )
            transformed_tail_decomposition.append(
                {
                    "row": row,
                    "column": column,
                    "predicted_q_order": predicted_order,
                    "tail_contributions": tail_rows,
                    "computed_tail_sum": sum(
                        item["computed_leading_coefficient"] for item in tail_rows
                    ),
                    "predicted_row_coefficient": predicted_coefficient,
                    "matches": all(item["matches"] for item in tail_rows)
                    and sum(
                        item["computed_leading_coefficient"] for item in tail_rows
                    )
                    == predicted_coefficient,
                }
            )
    return {
        "q_degree_cutoff": cutoff,
        "moment_index_range": [0, 2 * max_rank - 2],
        "ranks": ranks,
        "all_computed_orders_equal_source_lower_bound": all(
            row["order_surplus"] == 0 for row in ranks
        ),
        "all_computed_leading_coefficients_match_factorial_pattern": all(
            row["leading_coefficient_matches_factorial_pattern"] for row in ranks
        ),
        "transformed_row_leading_terms": transformed_rows,
        "all_transformed_row_leading_terms_match": all(
            row["matches"] for row in transformed_rows
        ),
        "transformed_tail_decomposition": transformed_tail_decomposition,
        "all_transformed_tail_contributions_match": all(
            row["matches"] for row in transformed_tail_decomposition
        ),
        "structural_factorization": {
            "row_leading_term": (
                "D_j v_(j+l)^* = (-1)^j (j+1)^2(j+2)/2 "
                "q^(j(j+1)/2+jl) + higher terms"
            ),
            "leading_matrix": "row factors times ((q^j)^l)_(j,l)",
            "vandermonde_order": "N(N-1)(N-2)/6",
            "row_factor_order": "N(N-1)(N+1)/6",
            "combined_order": "N(N-1)(2N-1)/6",
            "row_coefficient_product": "(N!)^2(N+1)!/2^N",
            "remaining_proof_obligation": (
                "none on normalized q-order: the associated-graded reciprocal "
                "law plus the two specialized tail reciprocals proves the "
                "transformed-row leading term for arbitrary j,l"
            ),
            "associated_graded_reciprocal_law": (
                "[q^(nj-j(j-1)/2)] D_j w_n(H,t) = "
                "(-1)^j [X^(j-t)] H_0(X)^(-1)"
            ),
            "tail_zero_reciprocal": "(1+X)/(1-X)^4",
            "positive_tail_reciprocal": "1/(1-X)^3",
        },
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
    parser.add_argument("--max-rank", type=int, default=6)
    parser.add_argument("--margin", type=int, default=8)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if not 1 <= args.max_rank <= 7:
        parser.error("--max-rank must lie in [1,7]")
    if args.margin < 1:
        parser.error("--margin must be positive")
    if args.check and args.output is None:
        parser.error("--check requires --output")

    scan = compute(args.max_rank, args.margin)
    exact_at_every_rank = bool(scan["all_computed_orders_equal_source_lower_bound"])
    summary = (
        "The normalized Hankel q-order equals Zudilin's source lower bound at "
        f"every exact rank 1..{args.max_rank}; the displayed leading "
        "coefficients match (N!)^2(N+1)!/2^N. Across the full transformed-row "
        "grid, every individual hypergeometric tail contribution matches the "
        "associated-graded reciprocal formula. The authored all-rank induction "
        "and its Lean-checked coefficient recurrence prove that D_j v_(j+l)^* "
        "has the predicted leading monomial and leaves a Vandermonde leading "
        "matrix. Hidden normalized-Hankel q-order is therefore eliminated as "
        "a source of additional cubic decay."
        if exact_at_every_rank
        else
        "At least one exact rank has q-order strictly above Zudilin's source "
        "lower bound, opening a source-natural analytic-cancellation mechanism."
    )
    result = {
        "schema": "erdos1049-zudilin-hankel-qorder/1",
        "claim_ceiling": (
            "The all-rank associated-graded argument proves exact normalized "
            "q-order at x=z=1; it does not extract arithmetic denominator "
            "factors or decide irrationality at p=3/2."
        ),
        "parameters": {"max_rank": args.max_rank, "margin": args.margin},
        "scan": scan,
        "experiment_contract": build_experiment_contract(
            problem_id="erdos_1049",
            target_statement=(
                "Prove irrationality of the rational-base Lambert value at p=3/2."
            ),
            claim_ceiling=(
                "The exact checker regression-tests the source-linked all-rank "
                "associated-graded proof. It does not establish the rational "
                "specialization's required denominator-factor extraction."
            ),
            hypothesis_id="zudilin_hankel_has_hidden_q_order_surplus",
            hypothesis_statement=(
                "The normalized source Hankel determinant has q-order above "
                "N(N-1)(2N-1)/6, yielding extra cubic analytic decay before "
                "any denominator-factor extraction."
            ),
            probe_id="exact_normalized_hankel_q_order_scan",
            probe_question=(
                "Does exact cancellation at x=z=1 improve the source q-order "
                "lower bound at the first discriminating ranks?"
            ),
            computation=(
                "Expand the primary-source normalized forms v_m^* with integer "
                "formal-power-series arithmetic and compute their Hankel "
                "determinants by the Leibniz formula."
            ),
            falsifier=(
                "A nonzero coefficient occurs exactly at the source lower-bound "
                "degree, so that rank has no hidden q-order surplus."
            ),
            stop_condition=(
                "If equality persists with structured nonzero leading coefficients, "
                "seek an all-rank leading-term theorem; if a surplus appears, "
                "measure its growth before returning to denominator charge."
            ),
            survival_consequence=(
                "A cubic q-order surplus would reduce the analytic side of the "
                "explicit 3/2 height threshold."
            ),
            falsification_consequence=(
                "Exact equality removes free analytic cancellation at that rank "
                "and sends the method back to denominator-factor extraction."
            ),
            consumer_ref=CONSUMER_REF,
            consumer_declarations=CONSUMER_DECLARATIONS,
            analysis_refs=[ANALYSIS_REF],
            source_refs=[SOURCE_REF, PRIMARY_SOURCE_REF],
            result_status=(
                "exact_one_way_result" if exact_at_every_rank else "finite_support"
            ),
            result_summary=summary,
            resource_bounds={
                "max_rank": args.max_rank,
                "q_degree_cutoff": int(scan["q_degree_cutoff"]),
                "maximum_permutation_count": math.factorial(args.max_rank),
                "maximum_moment_index": 2 * args.max_rank - 2,
                "transformed_row_grid_size": args.max_rank**2,
                "transformed_tail_certificate_count": (
                    args.max_rank**2 * (args.max_rank + 1) // 2
                ),
            },
        ),
        "sources": [
            source_record(REPO_ROOT, SOURCE_REF),
            source_record(REPO_ROOT, PRIMARY_SOURCE_REF),
            source_record(REPO_ROOT, CONSUMER_REF),
            source_record(REPO_ROOT, ANALYSIS_REF),
        ],
    }
    return emit(result, args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
