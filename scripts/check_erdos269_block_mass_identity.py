#!/usr/bin/env python3
"""Check the exact half-height block-mass identity for Erdős #269."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from bisect import bisect_left
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

import check_erdos269_dyadic_windows as dyadic  # noqa: E402
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
)


SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos269_block_mass_identity.py"
)
DYADIC_SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos269_dyadic_windows.py"
)
LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "DyadicBlockMassIdentity.lean"
)
THRESHOLD_LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "DyadicBlockThresholdPartition.lean"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "DyadicWindowComputationalLab.md"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos269_block_mass_identity_receipt.json"
)


def integer_log(base: int, value: int) -> int:
    exponent = 0
    power = 1
    while power * base <= value:
        power *= base
        exponent += 1
    return exponent


def height235(value: int) -> int:
    return (
        2 ** integer_log(2, value)
        * 3 ** integer_log(3, value)
        * 5 ** integer_log(5, value)
    )


def smooth_values_through(limit: int) -> list[int]:
    powers: dict[int, list[int]] = {}
    for base in (2, 3, 5):
        values = []
        value = 1
        while value <= limit:
            values.append(value)
            value *= base
        powers[base] = values
    smooth = set()
    for two_power in powers[2]:
        for three_power in powers[3]:
            partial = two_power * three_power
            if partial > limit:
                break
            for five_power in powers[5]:
                value = partial * five_power
                if value > limit:
                    break
                smooth.add(value)
    return sorted(smooth)


def build_receipt(max_a: int) -> dict[str, object]:
    if max_a < 1:
        raise ValueError("max-a must be positive")
    blocks = dyadic.build_dyadic_blocks(max_a)
    limit = 1 << (max_a + 1)
    smooth = smooth_values_through(limit)
    rows = []
    for a, (block_base, block_digit, ending_jump_index) in enumerate(blocks, 1):
        lower = 1 << a
        upper = 1 << (a + 1)
        left = bisect_left(smooth, lower)
        right = bisect_left(smooth, upper)
        endpoint_height = height235(upper)
        shell = smooth[left:right]
        cleared_mass = sum(endpoint_height // height235(value) for value in shell)
        threshold_three = 3 ** integer_log(3, upper)
        threshold_five = 5 ** integer_log(5, upper)
        before_three = sum(value < threshold_three for value in shell)
        before_five = sum(value < threshold_five for value in shell)
        before_both = sum(
            value < threshold_three and value < threshold_five for value in shell
        )
        threshold_partition_digit = (
            len(shell)
            + 2 * before_three
            + 4 * before_five
            + 8 * before_both
        )
        if threshold_three <= threshold_five:
            threshold_order = "three_then_five"
            ordered_threshold_digit = len(shell) + 10 * before_three + 4 * before_five
        else:
            threshold_order = "five_then_three"
            ordered_threshold_digit = len(shell) + 2 * before_three + 12 * before_five
        if cleared_mass != 2 * block_digit:
            raise AssertionError(
                ("block mass identity failed", a, block_base, block_digit, cleared_mass)
            )
        if not (
            cleared_mass // 2
            == threshold_partition_digit
            == ordered_threshold_digit
            == block_digit
        ):
            raise AssertionError(
                (
                    "threshold-ordered digit identity failed",
                    a,
                    cleared_mass // 2,
                    threshold_partition_digit,
                    ordered_threshold_digit,
                    block_digit,
                )
            )
        rows.append(
            {
                "a": a,
                "block_base": block_base,
                "block_digit": block_digit,
                "ending_jump_index": ending_jump_index,
                "shell_cardinality": len(shell),
                "height_cleared_shell_mass": cleared_mass,
                "threshold_order": threshold_order,
                "before_three_count": before_three,
                "before_five_count": before_five,
                "before_both_count": before_both,
                "ordered_threshold_digit": ordered_threshold_digit,
            }
        )
    row_bytes = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    summary = (
        f"For every 1<=a<={max_a}, exact enumeration verifies that the "
        "height-cleared mass of the half-open shell [2^a,2^(a+1)) is exactly "
        "twice the checker block digit. Lean proves at every scale that each "
        "source height quotient has a terminal factor 2 times an odd suffix "
        "product and sums it by the unique odd-channel thresholds. The same "
        "enumeration verifies the theorem's ordered coefficient formula against "
        "the independently constructed checker digit."
    )
    return {
        "schema": "erdos269-block-mass-identity/2",
        "problem_id": "erdos_269",
        "parameters": {"min_a": 1, "max_a": max_a},
        "checked_shell_count": len(rows),
        "smooth_value_count": len(smooth),
        "identity": (
            "sum_{x smooth, 2^a <= x < 2^(a+1)} "
            "H(2^(a+1))/H(x) = 2*block_digit(a)"
        ),
        "row_sha256": hashlib.sha256(row_bytes).hexdigest(),
        "first_rows": rows[:6],
        "last_rows": rows[-3:],
        "lean_declarations": [
            "mem_strictSmoothExponents235_iff",
            "mem_dyadicSmoothShell235_iff",
            "log_two_eq_of_mem_dyadicSmoothShell235",
            "threePrimeHeight_dyadicShell_factor_two",
            "halfClearedMassOne_eq_blockDigitOne",
            "halfClearedMassTwo_eq_blockDigitTwo",
            "halfOpenMass_eq_rightClosedMass_add",
            "clearedMassTwo_eq_two_mul_blockDigitTwo",
            "pow_log_dyadic_suffix_eq_if",
            "oddHeightSuffix235_eq_thresholdFactors",
            "dyadicHalfClearedMass235_eq_thresholdCounts",
            "dyadicBeforeBothThresholdsCount235_eq_three",
            "dyadicBeforeBothThresholdsCount235_eq_five",
            "dyadicHalfClearedMass235_eq_orderedBlockDigit235",
        ],
        "result_summary": summary,
        "experiment_contract": build_experiment_contract(
            problem_id="erdos_269",
            target_statement=(
                "Identify the actual ordered smooth-prefix block digit and derive "
                "its exact affine carry recurrence."
            ),
            claim_ceiling=(
                "Lean proves the all-scale terminal-two height factorization, local "
                "cell algebra, and the exact threshold-ordered summation formula. "
                "The actual affine carry recurrence and cofinal Farey-phase producer "
                "remain open."
            ),
            hypothesis_id="dyadic_block_digit_is_half_height_cleared_mass",
            hypothesis_statement=(
                "The checker digit equals one half of the height-cleared mass of "
                "the actual half-open dyadic smooth shell."
            ),
            probe_id="direct_smooth_shell_height_mass",
            probe_question=(
                "Does direct source enumeration agree exactly with the independently "
                "constructed block digit, including endpoint normalization?"
            ),
            computation=(
                "Enumerate all {2,3,5}-smooth values in each half-open dyadic shell, "
                "sum the exact integer height quotients, and compare with twice the "
                "block digit built from ordered prime-power jumps."
            ),
            falsifier="Any shell with cleared_mass != 2*block_digit.",
            stop_condition=(
                "The all-a threshold partition is Lean-certified; stop finite shell "
                "extension and move to the actual rationality carry recurrence."
            ),
            survival_consequence=(
                "Use the all-a threshold-ordered source identity to derive the actual "
                "affine rationality carry recurrence."
            ),
            falsification_consequence=(
                "Reject the checker digit as a source-faithful compression and repair "
                "the endpoint or height convention."
            ),
            consumer_ref=THRESHOLD_LEAN_REF,
            consumer_declarations=[
                "threePrimeHeight_dyadicShell_factor_two",
                "halfClearedMassOne_eq_blockDigitOne",
                "halfClearedMassTwo_eq_blockDigitTwo",
                "dyadicHalfClearedMass235_eq_thresholdCounts",
                "dyadicHalfClearedMass235_eq_orderedBlockDigit235",
            ],
            analysis_refs=[ANALYSIS_REF],
            source_refs=[SOURCE_REF, DYADIC_SOURCE_REF, LEAN_REF, THRESHOLD_LEAN_REF],
            result_status="exact_one_way_result",
            result_summary=summary,
            progress_class="mechanism_opened",
            decision_basis=(
                "Lean proves for every scale and every actual smooth shell point that "
                "the right-endpoint height factors as point-height times 2 and an odd "
                "suffix product and its all-scale threshold partition; direct "
                "enumeration independently verifies both ordered threshold formulas "
                "against the checker digit."
            ),
            next_analytic_target=(
                "Bind the threshold-ordered source digit into the actual rationality "
                "carry recurrence, then control its arithmetic Farey phase cofinally."
            ),
        ),
        "sources": [
            source_record(REPO_ROOT, ref)
            for ref in [SOURCE_REF, DYADIC_SOURCE_REF, LEAN_REF, THRESHOLD_LEAN_REF]
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-a", type=int, default=100)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = json.dumps(build_receipt(args.max_a), indent=2, sort_keys=True) + "\n"
    output = args.output.resolve()
    if args.check:
        if not output.exists() or output.read_text(encoding="utf-8") != rendered:
            print(f"stale or missing receipt: {output}", file=sys.stderr)
            return 1
        print(json.dumps({"status": "current", "output": str(output)}))
        return 0
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(rendered, encoding="utf-8")
    print(json.dumps({"status": "written", "output": str(output)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
