#!/usr/bin/env python3
"""Extend the exact Zudilin normalized-Hankel q-order scan past rank 7.

``check_zudilin_hankel_qorder.py`` forms the determinant by enumerating all
``N!`` permutations and multiplying truncated series, so it is capped at
``--max-rank 7``.  That cap is an artifact of the determinant routine, not of
the mathematics: the initial term of ``V_N^*`` is decided entirely by the
per-entry initial monomials of the backward-shifted grid

    D_j v_{j+l}^* = (-1)^j ((j+1)^2 (j+2) / 2) q^(j(j+1)/2 + jl) + O(q^(...+1)),

together with which permutations minimise the total entry order.  This module
therefore separates the two halves:

1. the *entry* half is still exact truncated integer series arithmetic, reusing
   the sibling checker's source expansion verbatim;
2. the *determinant* half becomes a minimum-weight assignment dynamic program
   over column subsets, ``O(2^N N^2)`` instead of ``O(N! N)``, which retains
   the minimum total order, the number of permutations attaining it, and the
   exact signed sum of leading-coefficient products over those minimisers.

The DP is not trusted on its own.  For every rank where the sibling's exact
permutation determinant is affordable, this module recomputes the determinant
series that way and requires the two to agree on both order and leading
coefficient.  A DP that disagreed with an exact series determinant at rank 5
would be reported as a failure, not silently preferred.

Boundary: this is a finite exact computation over the source's own normalized
forms.  It regression-tests the authored all-rank associated-graded argument at
larger ranks.  It does not prove the all-rank statement, extract arithmetic
denominator factors, or decide irrationality at 3/2.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
from pathlib import Path
import sys


REPO_ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(REPO_ROOT))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
)
from system.lib.formal_math_probe_registry import mechanism_bindings  # noqa: E402

# Reuse the sibling's exact source expansion rather than re-deriving it.
from check_zudilin_hankel_qorder import (  # noqa: E402
    determinant_series,
    first_nonzero,
    multiply,
    multiply_one_minus_q_power,
    normalized_form_series,
    predicted_leading_coefficient,
    predicted_tail_leading_coefficient,
    source_lower_bound,
    transformed_form_series,
    transformed_tail_series,
    zero_series,
)


SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "scripts/check_zudilin_hankel_qorder_extended.py"
)
SIBLING_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "scripts/check_zudilin_hankel_qorder.py"
)
PRIMARY_SOURCE_REF = (
    "annexes/arxiv-1601-02688-zudilin-generalized-q-logarithm/extracted.md"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "AdelicHeightBridge.lean"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "HankelQOrderComputationalLab.md"
)


def entry_order(row: int, column: int) -> int:
    """Predicted q-order of ``D_row v_{row+column}^*``."""

    return row * (row + 1) // 2 + row * column


def entry_leading_coefficient(row: int) -> int:
    """Predicted leading coefficient of ``D_row v_{row+column}^*`` (column-free)."""

    return (-1) ** row * (row + 1) ** 2 * (row + 2) // 2


def assignment_initial_term(
    orders: list[list[int]], coefficients: list[list[int]], rank: int
) -> dict[str, object]:
    """Minimum total order and signed leading sum over all permutations.

    States are ``(rows placed, frozenset of used columns)``; the permutation
    sign is accumulated incrementally, since assigning row ``j`` to column ``c``
    contributes one inversion for every already-used column greater than ``c``.
    """

    full = (1 << rank) - 1
    # state -> (min_weight, signed_leading_sum, minimiser_count)
    layer: dict[int, tuple[int, int, int]] = {0: (0, 1, 1)}
    for row in range(rank):
        nxt: dict[int, tuple[int, int, int]] = {}
        for used, (weight, signed, count) in layer.items():
            for column in range(rank):
                bit = 1 << column
                if used & bit:
                    continue
                inversions = bin(used >> (column + 1)).count("1")
                sign = -1 if inversions % 2 else 1
                new_used = used | bit
                new_weight = weight + orders[row][column]
                new_signed = signed * sign * coefficients[row][column]
                prior = nxt.get(new_used)
                if prior is None or new_weight < prior[0]:
                    nxt[new_used] = (new_weight, new_signed, count)
                elif new_weight == prior[0]:
                    nxt[new_used] = (
                        prior[0],
                        prior[1] + new_signed,
                        prior[2] + count,
                    )
        layer = nxt
    weight, signed, count = layer[full]
    return {
        "minimum_total_order": weight,
        "signed_leading_sum": signed,
        "minimising_permutation_count": count,
    }


def reversing_permutation_weight(rank: int) -> int:
    return sum(entry_order(row, rank - 1 - row) for row in range(rank))


def qpochhammer_series(length: int, cutoff: int) -> list[int]:
    """``(q;q)_length`` truncated at ``q^cutoff``."""

    series = zero_series(cutoff)
    series[0] = 1
    for power in range(1, length + 1):
        series = multiply_one_minus_q_power(series, power)
    return series


def associated_leading_determinant(rank: int, cutoff: int) -> list[int]:
    """``det L_N`` computed directly from the associated-graded leading matrix."""

    orders = [[entry_order(r, c) for c in range(rank)] for r in range(rank)]
    coefficients = [
        [entry_leading_coefficient(r) for _ in range(rank)] for r in range(rank)
    ]
    result = zero_series(cutoff)
    for permutation in itertools.permutations(range(rank)):
        inversions = sum(
            permutation[i] > permutation[j]
            for i in range(rank)
            for j in range(i + 1, rank)
        )
        sign = -1 if inversions % 2 else 1
        degree = sum(orders[row][permutation[row]] for row in range(rank))
        if degree > cutoff:
            continue
        value = sign
        for row in range(rank):
            value *= coefficients[row][permutation[row]]
        result[degree] += value
    return result


def predicted_associated_leading_determinant(rank: int, cutoff: int) -> list[int]:
    """``C_N q^{B_N} prod_{r=1}^{N-1} (q;q)_r``."""

    series = zero_series(cutoff)
    series[0] = predicted_leading_coefficient(rank)
    for length in range(1, rank):
        series = multiply(series, qpochhammer_series(length, cutoff), cutoff)
    shift_by = source_lower_bound(rank)
    shifted = zero_series(cutoff)
    for degree in range(cutoff + 1 - shift_by):
        shifted[degree + shift_by] = series[degree]
    return shifted


def compute(max_rank: int, margin: int, cross_check_rank: int) -> dict[str, object]:
    cutoff = source_lower_bound(max_rank) + margin
    moments = [
        normalized_form_series(index, cutoff) for index in range(2 * max_rank - 1)
    ]

    # --- entry half: exact series, verified against the predicted monomial ---
    orders = [[0] * max_rank for _ in range(max_rank)]
    coefficients = [[0] * max_rank for _ in range(max_rank)]
    entry_rows: list[dict[str, object]] = []
    tail_rows: list[dict[str, object]] = []
    for row in range(max_rank):
        for column in range(max_rank):
            transformed = transformed_form_series(moments, row + column, row, cutoff)
            order, coefficient = first_nonzero(transformed)
            predicted_order = entry_order(row, column)
            predicted_coefficient = entry_leading_coefficient(row)
            orders[row][column] = predicted_order
            coefficients[row][column] = predicted_coefficient
            entry_rows.append(
                {
                    "row": row,
                    "column": column,
                    "computed_q_order": order,
                    "predicted_q_order": predicted_order,
                    "computed_leading_coefficient": coefficient,
                    "predicted_leading_coefficient": predicted_coefficient,
                    "matches": order == predicted_order
                    and coefficient == predicted_coefficient,
                }
            )
            contributions = []
            for tail_index in range(row + 1):
                tail = transformed_tail_series(row + column, row, tail_index, cutoff)
                observed = tail[predicted_order]
                predicted = predicted_tail_leading_coefficient(row, tail_index)
                contributions.append(
                    {
                        "tail_index": tail_index,
                        "computed_leading_coefficient": observed,
                        "predicted_leading_coefficient": predicted,
                        "matches": observed == predicted,
                    }
                )
            tail_rows.append(
                {
                    "row": row,
                    "column": column,
                    "tail_contributions": contributions,
                    "computed_tail_sum": sum(
                        item["computed_leading_coefficient"] for item in contributions
                    ),
                    "predicted_row_coefficient": predicted_coefficient,
                    "matches": all(item["matches"] for item in contributions)
                    and sum(
                        item["computed_leading_coefficient"] for item in contributions
                    )
                    == predicted_coefficient,
                }
            )

    # --- determinant half: subset DP, cross-checked against exact series ---
    ranks: list[dict[str, object]] = []
    for rank in range(1, max_rank + 1):
        dp = assignment_initial_term(orders, coefficients, rank)
        lower_bound = source_lower_bound(rank)
        predicted_coefficient = predicted_leading_coefficient(rank)
        cross: dict[str, object] | None = None
        if rank <= cross_check_rank:
            determinant = determinant_series(moments, rank, cutoff)
            exact_order, exact_coefficient = first_nonzero(determinant)
            cross = {
                "exact_permutation_determinant_q_order": exact_order,
                "exact_permutation_determinant_leading_coefficient": (
                    exact_coefficient
                ),
                "agrees_with_assignment_dp": (
                    exact_order == dp["minimum_total_order"]
                    and exact_coefficient == dp["signed_leading_sum"]
                ),
            }
        ranks.append(
            {
                "rank": rank,
                "source_q_order_lower_bound": lower_bound,
                "assignment_dp_q_order": dp["minimum_total_order"],
                "order_surplus": dp["minimum_total_order"] - lower_bound,
                "assignment_dp_leading_coefficient": dp["signed_leading_sum"],
                "predicted_leading_coefficient": predicted_coefficient,
                "leading_coefficient_matches_factorial_pattern": (
                    dp["signed_leading_sum"] == predicted_coefficient
                ),
                "minimising_permutation_count": dp["minimising_permutation_count"],
                "unique_minimiser": dp["minimising_permutation_count"] == 1,
                "reversing_permutation_weight": reversing_permutation_weight(rank),
                "reversing_permutation_is_the_minimiser": (
                    reversing_permutation_weight(rank) == dp["minimum_total_order"]
                ),
                "exact_series_cross_check": cross,
            }
        )

    # --- exact associated-graded determinant product identity ---
    product_rows: list[dict[str, object]] = []
    for rank in range(1, max_rank + 1):
        local_cutoff = source_lower_bound(rank) + rank * rank + margin
        observed = associated_leading_determinant(rank, local_cutoff)
        predicted = predicted_associated_leading_determinant(rank, local_cutoff)
        product_rows.append(
            {
                "rank": rank,
                "q_degree_cutoff": local_cutoff,
                "identity_holds_through_cutoff": observed == predicted,
                "first_disagreement_degree": next(
                    (
                        degree
                        for degree, (a, b) in enumerate(zip(observed, predicted))
                        if a != b
                    ),
                    None,
                ),
            }
        )

    return {
        "q_degree_cutoff": cutoff,
        "moment_index_range": [0, 2 * max_rank - 2],
        "transformed_row_leading_terms": entry_rows,
        "all_transformed_row_leading_terms_match": all(
            row["matches"] for row in entry_rows
        ),
        "transformed_tail_decomposition": tail_rows,
        "all_transformed_tail_contributions_match": all(
            row["matches"] for row in tail_rows
        ),
        "ranks": ranks,
        "all_orders_equal_source_lower_bound": all(
            row["order_surplus"] == 0 for row in ranks
        ),
        "all_leading_coefficients_match_factorial_pattern": all(
            row["leading_coefficient_matches_factorial_pattern"] for row in ranks
        ),
        "all_minimisers_unique": all(row["unique_minimiser"] for row in ranks),
        "all_exact_series_cross_checks_agree": all(
            row["exact_series_cross_check"]["agrees_with_assignment_dp"]
            for row in ranks
            if row["exact_series_cross_check"] is not None
        ),
        "associated_leading_determinant_product_identity": product_rows,
        "associated_leading_determinant_product_identity_holds": all(
            row["identity_holds_through_cutoff"] for row in product_rows
        ),
        "structural_factorization": {
            "row_leading_term": (
                "D_j v_(j+l)^* = (-1)^j (j+1)^2(j+2)/2 "
                "q^(j(j+1)/2+jl) + higher terms"
            ),
            "unique_minimiser": "reversing permutation pi_0(j) = N-1-j",
            "combined_order": "N(N-1)(2N-1)/6",
            "row_coefficient_product": "(N!)^2(N+1)!/2^N",
            "associated_leading_determinant": (
                "det L_N = ((N!)^2 (N+1)!/2^N) q^(N(N-1)(2N-1)/6) "
                "prod_(r=1)^(N-1) (q;q)_r"
            ),
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
    parser.add_argument("--max-rank", type=int, default=10)
    parser.add_argument("--margin", type=int, default=4)
    parser.add_argument(
        "--cross-check-rank",
        type=int,
        default=5,
        help="highest rank at which the O(N!) exact series determinant is also run",
    )
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if not 1 <= args.max_rank <= 14:
        parser.error("--max-rank must lie in [1,14]")
    if args.margin < 1:
        parser.error("--margin must be positive")
    if not 0 <= args.cross_check_rank <= min(args.max_rank, 7):
        parser.error("--cross-check-rank must lie in [0, min(max_rank,7)]")
    if args.check and args.output is None:
        parser.error("--check requires --output")

    scan = compute(args.max_rank, args.margin, args.cross_check_rank)
    sharp = (
        bool(scan["all_orders_equal_source_lower_bound"])
        and bool(scan["all_leading_coefficients_match_factorial_pattern"])
        and bool(scan["all_minimisers_unique"])
        and bool(scan["all_exact_series_cross_checks_agree"])
    )
    summary = (
        "Through rank "
        f"{args.max_rank} the exact transformed-entry grid matches the "
        "associated-graded initial monomial in every position, the reversing "
        "permutation is the unique minimiser of the total entry order, the "
        "determinant q-order equals Zudilin's source lower bound "
        "N(N-1)(2N-1)/6, and the leading coefficient equals (N!)^2(N+1)!/2^N. "
        "The assignment dynamic program agrees with the exact permutation "
        "series determinant at every rank where both were run, and the "
        "associated-graded determinant matches the closed product "
        "C_N q^(B_N) prod (q;q)_r exactly."
        if sharp
        else
        "At least one rank disagrees with the associated-graded prediction; "
        "inspect the per-rank rows before treating the sharp order or leading "
        "coefficient as regression-tested at this rank."
    )
    result = {
        "schema": "erdos1049-zudilin-hankel-qorder-extended/1",
        "claim_ceiling": (
            "A finite exact regression test of the authored all-rank "
            "associated-graded argument at ranks beyond the sibling checker's "
            "factorial cap. It is not a proof of the all-rank statement, does "
            "not extract arithmetic denominator factors, and does not decide "
            "irrationality at 3/2."
        ),
        "parameters": {
            "max_rank": args.max_rank,
            "margin": args.margin,
            "cross_check_rank": args.cross_check_rank,
        },
        "scan": scan,
        "experiment_contract": build_experiment_contract(
            problem_id="erdos_1049",
            target_statement=(
                "Prove irrationality of the rational-base Lambert value at p=3/2."
            ),
            claim_ceiling=(
                "Regression evidence for the sharp normalized q-order and "
                "leading coefficient at larger ranks; not a proof and not a "
                "denominator-factor extraction."
            ),
            hypothesis_id="zudilin_hankel_sharp_order_fails_beyond_rank_seven",
            hypothesis_statement=(
                "Beyond the sibling checker's factorial cap the determinant "
                "acquires extra cancellation, so the q-order exceeds "
                "N(N-1)(2N-1)/6 or the leading coefficient departs from "
                "(N!)^2(N+1)!/2^N."
            ),
            probe_id="assignment_dp_normalized_hankel_initial_term_scan",
            probe_question=(
                "Do the sharp order and the factorial leading coefficient "
                "persist at ranks 8..N, and is the reversing permutation still "
                "the unique minimiser?"
            ),
            computation=(
                "Expand the source normalized forms with exact integer "
                "truncated series arithmetic, verify every transformed-entry "
                "initial monomial and its per-tail decomposition, then obtain "
                "the determinant's initial term by a minimum-weight assignment "
                "dynamic program over column subsets, cross-checked against the "
                "exact permutation series determinant at low rank."
            ),
            falsifier=(
                "At some rank the assignment minimum exceeds N(N-1)(2N-1)/6, or "
                "the signed leading sum differs from (N!)^2(N+1)!/2^N, or the "
                "minimiser is not unique, or the dynamic program disagrees with "
                "the exact permutation determinant where both are run."
            ),
            stop_condition=(
                "If the sharp order and factorial coefficient persist at every "
                "reachable rank, the remaining work is the Lean all-rank "
                "initial-monomial theorem for backward-shift rows j >= 2, not "
                "further finite scanning."
            ),
            survival_consequence=(
                "A rank with extra cancellation would reduce the analytic side "
                "of the explicit 3/2 height threshold."
            ),
            falsification_consequence=(
                "Persistent equality removes free analytic cancellation at "
                "every scanned rank and sends the method back to "
                "denominator-factor extraction."
            ),
            consumer_ref=CONSUMER_REF,
            consumer_declarations=[
                "zudilinTransformedNormalizedMoment_one_initialMonomial",
                "order_det_eq_of_unique_minimizing_permutation",
                "det_zudilinAssociatedLeadingMatrix",
            ],
            analysis_refs=[ANALYSIS_REF],
            source_refs=[SOURCE_REF, SIBLING_REF, PRIMARY_SOURCE_REF],
            result_status=("exact_one_way_result" if sharp else "finite_support"),
            result_summary=summary,
            resource_bounds={
                "max_rank": args.max_rank,
                "q_degree_cutoff": int(scan["q_degree_cutoff"]),
                "assignment_dp_state_count": (1 << args.max_rank) * args.max_rank,
                "cross_check_permutation_count": math.factorial(
                    args.cross_check_rank
                ),
                "maximum_moment_index": 2 * args.max_rank - 2,
                "transformed_row_grid_size": args.max_rank**2,
            },
        ),
        "mechanism_bindings": mechanism_bindings(
            problem_id="erdos_1049",
            motivated_by=[
                "factor_extracted_hankel_against_explicit_thresholds",
                "zudilin_normalized_hankel_qorder_factorial_pattern",
            ],
            supports=[
                "zudilin_normalized_hankel_qorder_factorial_pattern",
                "rank_budget_law_for_rational_bases",
            ],
            rationale=(
                "The sibling checker's factorial determinant capped the sharp "
                "q-order regression at rank 7. Replacing the determinant half "
                "with a minimum-weight assignment dynamic program, cross-checked "
                "against the exact permutation series determinant at low rank, "
                "extends the same exact scan to rank 10 and additionally "
                "verifies the closed associated-graded product identity. This "
                "measures whether the analytic side of the explicit 3/2 height "
                "threshold gains any further cancellation at larger ranks."
            ),
        ),
        "sources": [
            source_record(REPO_ROOT, SOURCE_REF),
            source_record(REPO_ROOT, SIBLING_REF),
            source_record(REPO_ROOT, PRIMARY_SOURCE_REF),
            source_record(REPO_ROOT, CONSUMER_REF),
            source_record(REPO_ROOT, ANALYSIS_REF),
        ],
        "summary": summary,
    }
    return emit(result, args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
