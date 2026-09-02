#!/usr/bin/env python3
"""Find exact moving-tail q-Apéry collisions escaping both nullspaces."""

from __future__ import annotations

import argparse
import json
import math
import sys
from fractions import Fraction
from pathlib import Path


if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


REPO_ROOT = Path(__file__).resolve().parents[5]
SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(REPO_ROOT))
sys.path.insert(0, str(SCRIPT_DIR))

from system.lib.formal_math_determinantal import (  # noqa: E402
    find_short_collinear_relation,
)
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
)
from verify_qapery_remainder_at_three_halves import (  # noqa: E402
    f_three_halves_bracket,
)


SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "scripts/check_qapery_selector_remainder_escape.py"
)
RECURRENCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "scripts/verify_qapery_transduction.py"
)
REMAINDER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "scripts/verify_qapery_remainder_at_three_halves.py"
)
DETERMINANTAL_REF = "system/lib/formal_math_determinantal.py"
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "PrimitivePluckerComputationalLab.md"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "BezoutPluckerJets.lean"
)
PRIOR_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_primitive_plucker_receipt.json"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_qapery_selector_remainder_escape_receipt.json"
)
STARTS = (0, 1, 2, 3)
LLL_DELTA = 0.99
LLL_LAST_COORDINATE_WEIGHT = 2**16
REMAINDER_BRACKET_TERMS = 8000
REMAINDER_BRACKET_BITS = 12000


def recurrence_coefficients(index: int) -> tuple[Fraction, Fraction, Fraction]:
    q = Fraction(3, 2)
    alpha = q ** (index + 1)
    y0 = q * (alpha - 1) * (q * alpha + 2)
    y2 = (q * alpha - 1) * (alpha + 2)
    y1 = (
        q**3 * alpha**5
        + 2 * q**2 * (q + 1) * alpha**4
        + q**2 * alpha**3
        - 4 * q * (q + 1) * alpha**2
        + (q**2 - 4 * q + 1) * alpha
        + 2 * (q + 1)
    )
    return y0, y1, y2


def primitive_pair(left: Fraction, right: Fraction) -> tuple[int, int]:
    denominator = math.lcm(left.denominator, right.denominator)
    first = left.numerator * (denominator // left.denominator)
    second = right.numerator * (denominator // right.denominator)
    content = math.gcd(abs(first), abs(second)) or 1
    first, second = first // content, second // content
    if second < 0:
        first, second = -first, -second
    return first, second


def primitive_rows(count: int) -> list[tuple[int, int]]:
    if count < 2:
        raise ValueError("at least two rows are required")
    left = [Fraction(0), Fraction(-21, 2)]
    right = [Fraction(1), Fraction(-11, 4)]
    for index in range(count - 2):
        y0, y1, y2 = recurrence_coefficients(index)
        left.append(-(y1 * left[-1] + y0 * left[-2]) / y2)
        right.append(-(y1 * right[-1] + y0 * right[-2]) / y2)
    return [primitive_pair(a, b) for a, b in zip(left, right)]


def encode_fraction(value: Fraction) -> dict[str, str]:
    return {"numerator": str(value.numerator), "denominator": str(value.denominator)}


def build_result() -> dict[str, object]:
    maximum_index = max(start + 3 * start * start + 5 * start + 3 for start in STARTS)
    rows = primitive_rows(maximum_index)
    prior = json.loads((REPO_ROOT / PRIOR_RECEIPT_REF).read_text())
    prior_rows = []
    for row in prior["scan"]["rows"]:
        first, second = int(row["A"]), int(row["B"])
        prior_rows.append((first, second) if second >= 0 else (-first, -second))
    if rows[: len(prior_rows)] != prior_rows:
        raise AssertionError("fast recurrence rows disagree with canonical symbolic rows")

    f_lower, f_upper = f_three_halves_bracket(
        terms=REMAINDER_BRACKET_TERMS, bits=REMAINDER_BRACKET_BITS
    )
    records = []
    for start in STARTS:
        two_depth = 3 * start * start + 3 * start + 1
        three_depth = start + 1
        width = two_depth + 2 * three_depth
        modulus = 2**two_depth * 3**three_depth
        family = rows[start : start + width]
        relation = find_short_collinear_relation(
            family,
            modulus,
            max_abs_coefficient=1,
            lll_delta=LLL_DELTA,
            lll_last_coordinate_weight=LLL_LAST_COORDINATE_WEIGHT,
        )
        if relation is None:
            raise AssertionError(f"no binary-selector relation found at start {start}")
        coefficients = relation.coefficients
        pair_a, pair_b = relation.row_sum
        if pair_a == 0 and pair_b == 0:
            raise AssertionError("selector remained in the exact polynomial-pair nullspace")
        remainder_lower = pair_b * f_lower - pair_a
        remainder_upper = pair_b * f_upper - pair_a
        if pair_b < 0:
            remainder_lower, remainder_upper = remainder_upper, remainder_lower
        sign = (
            "positive"
            if remainder_lower > 0
            else "negative"
            if remainder_upper < 0
            else None
        )
        if sign is None:
            raise AssertionError("analytic remainder bracket did not exclude zero")
        records.append(
            {
                "tail_start": start,
                "row_count": width,
                "row_indices": list(range(start, start + width)),
                "modulus": modulus,
                "modulus_v2": two_depth,
                "modulus_v3": three_depth,
                "coefficients": list(coefficients),
                "positive_selector_indices": [
                    start + i for i, value in enumerate(coefficients) if value == 1
                ],
                "negative_selector_indices": [
                    start + i for i, value in enumerate(coefficients) if value == -1
                ],
                "support_size": sum(value != 0 for value in coefficients),
                "combined_pair": {"A": str(pair_a), "B": str(pair_b)},
                "combined_pair_modulus_remainders": [pair_a % modulus, pair_b % modulus],
                "exact_pair_nonzero": True,
                "analytic_remainder_sign": sign,
                "analytic_remainder_lower": encode_fraction(remainder_lower),
                "analytic_remainder_upper": encode_fraction(remainder_upper),
                "analytic_remainder_zero_excluded": True,
            }
        )
    strongest = records[-1]
    summary = (
        "Exact recurrence rows and LLL-certified binary selectors produce moving-tail "
        "collisions at s=0,1,2,3 outside both the exact coefficient-pair and analytic "
        "remainder nullspaces. The first previously untested start s=3 requires a "
        "stronger exact LLL reduction than the earlier starts; its resulting binary "
        "selector is replayed in both integer channels and against a 12000-bit "
        "rational remainder bracket."
    )
    return {
        "schema": "erdos1049-qapery-selector-remainder-escape/1",
        "claim_ceiling": (
            "These exact finite selectors prove that the moving-tail congruence kernel "
            "is not structurally swallowed by either nullspace. They do not provide "
            "an all-start short selector, an asymptotic height gain, or irrationality."
        ),
        "parameters": {
            "tail_starts": list(STARTS),
            "lll_delta": LLL_DELTA,
            "lll_last_coordinate_weight": LLL_LAST_COORDINATE_WEIGHT,
            "remainder_bracket_terms": REMAINDER_BRACKET_TERMS,
            "remainder_bracket_bits": REMAINDER_BRACKET_BITS,
        },
        "fast_recurrence_crosscheck": {
            "canonical_symbolic_row_count": len(prior_rows),
            "all_rows_match": True,
        },
        "selector_records": records,
        "strongest_selector": strongest,
        "mechanism_effect": (
            "The polynomial-pair and analytic-remainder nullspaces do not contain the "
            "whole moving-tail modular collision kernel. The surviving asymptotic task "
            "is quantitative: control selector height/support and real remainder as s grows."
        ),
        "experiment_contract": build_experiment_contract(
            problem_id="erdos_1049",
            target_statement="Prove irrationality of the Lambert value at q=3/2.",
            claim_ceiling=(
                "Finite exact nullspace escape at starts 0,1,2,3; no all-start or "
                "irrationality theorem."
            ),
            hypothesis_id="moving_tail_collision_kernel_is_nullspace_trapped",
            hypothesis_statement=(
                "Every binary-selector collision supplied by moving-tail Plücker "
                "compression has zero exact coefficient pair or zero analytic remainder."
            ),
            probe_id="exact_recurrence_lll_selector_remainder_bracket",
            probe_question=(
                "Does the first genuinely wide moving-tail congruence kernel contain "
                "a collision escaping both nullspaces?"
            ),
            computation=(
                "Generate primitive q-Apéry rows from the exact source recurrence, "
                "reduce the rank-two image to one modular coordinate, use exact LLL "
                "to recover {-1,0,1} relations, and bracket F(3/2) rationally."
            ),
            falsifier=(
                "One modular collision with nonzero combined pair and a rational "
                "remainder bracket lying strictly on one side of zero."
            ),
            stop_condition=(
                "After a scale s>=2 collision escapes both nullspaces, stop finite "
                "start extension and target an all-start quantitative selector theorem."
            ),
            survival_consequence=(
                "If every collision were trapped, moving-tail Plücker compression "
                "would be analytically inert."
            ),
            falsification_consequence=(
                "Nullspace trapping is eliminated as a structural no-go; the remaining "
                "barrier is asymptotic selector height and remainder control."
            ),
            consumer_ref=CONSUMER_REF,
            analysis_refs=[ANALYSIS_REF],
            source_refs=[SOURCE_REF, RECURRENCE_REF, REMAINDER_REF, DETERMINANTAL_REF],
            input_receipt_refs=[PRIOR_RECEIPT_REF],
            result_status="exact_one_way_result",
            result_summary=summary,
            progress_class="mechanism_opened",
            decision_basis=(
                "The s=3 selector has coefficients in {-1,0,1}, both integer channels "
                "divisible by 2^37*3^4, a nonzero combined pair, and a certified "
                "analytic remainder bounded strictly away from zero."
            ),
            next_analytic_target=(
                "Prove an all-start bounded-coefficient selector with quantitative "
                "height and remainder control, or show its cost defeats local gain."
            ),
        ),
        "sources": [
            source_record(REPO_ROOT, ref)
            for ref in [SOURCE_REF, RECURRENCE_REF, REMAINDER_REF, DETERMINANTAL_REF, CONSUMER_REF]
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = json.dumps(build_result(), indent=2, sort_keys=True) + "\n"
    if args.check:
        if not args.output.exists() or args.output.read_text() != rendered:
            raise SystemExit("selector-remainder receipt is stale")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
