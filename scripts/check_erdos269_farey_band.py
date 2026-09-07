#!/usr/bin/env python3
"""Decide exact Farey occupancy of selected Erdős #269 cylinder bands."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

import check_erdos269_affine_cylinders as affine  # noqa: E402
import check_erdos269_dyadic_windows as dyadic  # noqa: E402
from system.lib.formal_math_affine_cylinder import (  # noqa: E402
    certify_rationals_in_denominator_band,
)
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
)


SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos269_farey_band.py"
)
LIBRARY_REF = "system/lib/formal_math_affine_cylinder.py"
AFFINE_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos269_affine_cylinders.py"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "DyadicWindowComputationalLab.md"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "ResidueEscape.lean"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos269_farey_band_receipt.json"
)

# Adjacent first-clear lengths chosen to test continuation, not horizon size.
CASES = (
    (8, 13),
    (16, 19), (16, 20),
    (24, 27), (24, 28),
    (32, 35), (32, 36),
    (40, 44), (40, 45),
    (50, 54), (50, 55),
    (64, 67), (64, 68), (64, 69), (64, 70),
    (80, 84), (80, 85),
)


def build_result() -> dict[str, object]:
    anchor = 100
    blocks = dyadic.build_dyadic_blocks(anchor + max(length + depth for depth, length in CASES) + 4)
    rows = []
    for depth, first_clear_length in CASES:
        interval, _, nesting = affine.cylinder_for_depth(
            blocks, anchor, first_clear_length, depth
        )
        minimum, maximum = affine.denominator_band(
            blocks, anchor, first_clear_length
        )
        certificate = certify_rationals_in_denominator_band(
            interval, minimum, maximum, coprime_to=30
        )
        rows.append(
            {
                "depth": depth,
                "first_clear_length": first_clear_length,
                "denominator_band_minimum": minimum,
                "denominator_band_maximum": maximum,
                "admissible_rational_count": certificate.count,
                "first_denominator": certificate.first_denominator,
                "first_witness_numerator": (
                    certificate.first_witness.numerator
                    if certificate.first_witness is not None else None
                ),
                "first_witness_reduced_denominator": (
                    certificate.first_witness.denominator
                    if certificate.first_witness is not None else None
                ),
                "nested": nesting.nested,
                "active_lower_label": interval.active_lower_label,
                "active_upper_label": interval.active_upper_label,
            }
        )
    by_pair = {(row["depth"], row["first_clear_length"]): row for row in rows}
    disappearing = [
        [16, 19, 20], [24, 27, 28], [50, 54, 55]
    ]
    appearing = [[32, 35, 36], [40, 44, 45], [64, 69, 70], [80, 84, 85]]
    for depth, occupied, empty in disappearing:
        assert by_pair[(depth, occupied)]["admissible_rational_count"] > 0
        assert by_pair[(depth, empty)]["admissible_rational_count"] == 0
    for depth, empty, occupied in appearing:
        assert by_pair[(depth, empty)]["admissible_rational_count"] == 0
        assert by_pair[(depth, occupied)]["admissible_rational_count"] > 0
    unique_pairs = [[8, 13], [24, 27], [32, 36], [40, 45], [50, 54], [80, 85]]
    for pair in unique_pairs:
        assert by_pair[tuple(pair)]["admissible_rational_count"] == 1
    summary = (
        "Exact floor-sum counts show both occupied-to-empty and empty-to-occupied "
        "adjacent first-clear shifts, with six singleton bands. Rational-point "
        "admissibility is sparse and nonmonotone even after exact cylinder nesting."
    )
    return {
        "schema": "erdos269-farey-band-occupancy/1",
        "claim_ceiling": (
            "This eliminates monotone continuation and width-only density arguments; "
            "it does not prove arbitrary-depth occupancy or irrationality."
        ),
        "parameters": {"anchor": anchor, "coprime_to": 30},
        "rows": rows,
        "structural_result": {
            "occupied_to_empty_adjacent_shifts": disappearing,
            "empty_to_occupied_adjacent_shifts": appearing,
            "singleton_bands": unique_pairs,
            "eliminated_mechanism": (
                "Neither exact interval nesting, increasing first-clear length, nor "
                "band width alone propagates an admissible rational witness."
            ),
            "opened_mechanism": (
                "An arbitrary-depth producer must control the arithmetic Farey phase "
                "of the actual endpoint, or rotate anchors; mere density is insufficient."
            ),
        },
        "experiment_contract": build_experiment_contract(
            problem_id="erdos_269",
            target_statement="Prove irrationality for prime support {2,3,5}.",
            claim_ceiling=(
                "Exact selected-band decisions do not establish arbitrary-depth "
                "admissibility or the universal denominator theorem."
            ),
            hypothesis_id="monotone_affine_cylinder_rational_continuation",
            hypothesis_statement=(
                "Once a nested affine cylinder contains a denominator-admissible "
                "rational, the next first-clear shift remains occupied, or occupancy "
                "follows from interval width alone."
            ),
            probe_id="exact_floor_sum_farey_band_decision",
            probe_question=(
                "Are adjacent exact first-clear bands monotonically occupied?"
            ),
            computation=(
                "Count floor(B*u)-floor(B*l) over the exact denominator band, with "
                "inclusion-exclusion for gcd(B,30)=1, using logarithmic floor sums."
            ),
            falsifier="One occupied-to-empty adjacent shift in the actual cylinders.",
            stop_condition=(
                "After both transition polarities and singleton bands are certified, "
                "stop extending depth and target arithmetic phase control."
            ),
            survival_consequence=(
                "Monotone occupancy would reduce arbitrary-depth construction to one seed."
            ),
            falsification_consequence=(
                "A producer must control endpoint arithmetic or rotate anchors; nesting "
                "and coarse density cannot carry the proof."
            ),
            consumer_ref=CONSUMER_REF,
            analysis_refs=[ANALYSIS_REF],
            source_refs=[SOURCE_REF, LIBRARY_REF, AFFINE_REF],
            result_status="exact_one_way_result",
            result_summary=summary,
            progress_class="mechanism_eliminated",
            decision_basis=(
                "Complete exact counts certify occupied-to-empty adjacent shifts at "
                "depths 16, 24, and 50, plus the reverse polarity and singleton bands."
            ),
            next_analytic_target=(
                "Control the Farey phase of the actual final endpoint across anchors "
                "or construct a cofinal anchor-selection law."
            ),
        ),
        "sources": [
            source_record(REPO_ROOT, SOURCE_REF),
            source_record(REPO_ROOT, LIBRARY_REF),
            source_record(REPO_ROOT, AFFINE_REF),
            source_record(REPO_ROOT, CONSUMER_REF),
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    payload = json.dumps(build_result(), indent=2, sort_keys=True) + "\n"
    if args.check:
        if not args.output.exists() or args.output.read_text() != payload:
            raise SystemExit("farey-band receipt is stale")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload)
    print(payload, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
