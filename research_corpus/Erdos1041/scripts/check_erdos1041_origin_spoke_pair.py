#!/usr/bin/env python3
"""Exact five-root counterexample to the two-safe-origin-spokes shortcut.

For a root ``z_i``, the proposed spoke is ``t z_i`` for ``0 <= t <= 1``.
The witness below has five distinct rational-complex roots in the open unit
disk.  Four of its five root spokes contain an explicit rational waypoint at
which ``|f| > 1``.  Hence at most one origin spoke is contained in the strict
unit lemniscate, so no pair can be joined through the origin by two such
spokes.  This eliminates that shortcut, not Erdős #1041.
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


SOURCE_REF = (
    "research_corpus/Erdos1041/"
    "scripts/check_erdos1041_origin_spoke_pair.py"
)
ANALYSIS_REF = (
    "research_corpus/Erdos1041/"
    "OriginSpokePairCounterexampleComputationalLab.md"
)
PACKET_REF = (
    "research_corpus/Erdos1041/"
    "research_packet.json"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "source-provenance://private-authoring-project/receipts/"
    "erdos1041_origin_spoke_pair_counterexample_receipt.json"
)

GaussianQ = tuple[Fraction, Fraction]


def qadd(left: GaussianQ, right: GaussianQ) -> GaussianQ:
    return left[0] + right[0], left[1] + right[1]


def qneg(value: GaussianQ) -> GaussianQ:
    return -value[0], -value[1]


def qsub(left: GaussianQ, right: GaussianQ) -> GaussianQ:
    return qadd(left, qneg(right))


def qmul(left: GaussianQ, right: GaussianQ) -> GaussianQ:
    return (
        left[0] * right[0] - left[1] * right[1],
        left[0] * right[1] + left[1] * right[0],
    )


def qscale(scale: Fraction, value: GaussianQ) -> GaussianQ:
    return scale * value[0], scale * value[1]


def norm_sq(value: GaussianQ) -> Fraction:
    return value[0] * value[0] + value[1] * value[1]


def encode_fraction(value: Fraction) -> dict[str, int | str]:
    return {
        "value": str(value),
        "numerator": value.numerator,
        "denominator": value.denominator,
    }


def encode_gaussian(value: GaussianQ) -> dict[str, str]:
    return {"real": str(value[0]), "imag": str(value[1])}


def polynomial_value(point: GaussianQ, roots: list[GaussianQ]) -> GaussianQ:
    value: GaussianQ = (Fraction(1), Fraction(0))
    for root in roots:
        value = qmul(value, qsub(point, root))
    return value


def build_witness() -> dict[str, Any]:
    radius = Fraction(99999, 100000)
    directions: list[GaussianQ] = [
        (Fraction(1), Fraction(0)),
        (Fraction(-20, 101), Fraction(99, 101)),
        (Fraction(-20, 101), Fraction(-99, 101)),
        (Fraction(-28, 197), Fraction(195, 197)),
        (Fraction(-28, 197), Fraction(-195, 197)),
    ]
    assert all(norm_sq(direction) == 1 for direction in directions)
    roots = [qscale(radius, direction) for direction in directions]
    assert len(set(roots)) == 5
    assert all(norm_sq(root) < 1 for root in roots)

    waypoint_by_index = {
        1: Fraction(3, 125),
        2: Fraction(3, 125),
        3: Fraction(17, 1000),
        4: Fraction(17, 1000),
    }
    unsafe_rows: list[dict[str, Any]] = []
    for index, parameter in waypoint_by_index.items():
        point = qscale(parameter, roots[index])
        value = polynomial_value(point, roots)
        value_norm_sq = norm_sq(value)
        margin = value_norm_sq - 1
        assert margin > 0
        unsafe_rows.append(
            {
                "root_index": index,
                "root": encode_gaussian(roots[index]),
                "waypoint_parameter": str(parameter),
                "waypoint": encode_gaussian(point),
                "polynomial_value": encode_gaussian(value),
                "polynomial_value_norm_sq": encode_fraction(value_norm_sq),
                "strict_unit_escape_margin_sq": encode_fraction(margin),
            }
        )

    return {
        "radius": str(radius),
        "directions": [encode_gaussian(value) for value in directions],
        "roots": [encode_gaussian(value) for value in roots],
        "all_roots_distinct": True,
        "all_root_norms_strictly_below_one": True,
        "unsafe_origin_spoke_count": len(unsafe_rows),
        "safe_origin_spoke_count_upper_bound": len(roots) - len(unsafe_rows),
        "unsafe_origin_spokes": unsafe_rows,
    }


def build_receipt() -> dict[str, Any]:
    witness = build_witness()
    contract = build_experiment_contract(
        problem_id="erdos_1041",
        target_statement=(
            "Join two roots by a curve of length less than two inside the "
            "strict unit lemniscate."
        ),
        claim_ceiling=(
            "Exact counterexample to selecting two root-to-origin straight "
            "spokes; not a counterexample to Erdős #1041."
        ),
        hypothesis_id="two_safe_root_to_origin_spokes",
        hypothesis_statement=(
            "Every monic polynomial with roots in the open unit disk has two "
            "distinct roots whose straight spokes to the origin remain in "
            "the strict unit lemniscate."
        ),
        probe_id="rational_boundary_cluster_origin_spoke_falsifier",
        probe_question=(
            "Can four of five distinct root spokes be forced outside |f|<1 "
            "by a rational boundary-near configuration?"
        ),
        computation=(
            "Evaluate the factored polynomial in Gaussian rational arithmetic "
            "at one explicit rational waypoint on each of four spokes."
        ),
        falsifier=(
            "A five-root polynomial for which four spokes have an exact "
            "waypoint satisfying |f|^2>1."
        ),
        stop_condition=(
            "Stop after four exact spoke escapes leave at most one safe spoke."
        ),
        survival_consequence=(
            "Two safe origin spokes would solve the metric and containment "
            "requirements simultaneously via a broken line of length below two."
        ),
        falsification_consequence=(
            "A fixed origin hub cannot replace critical-point selection; retain "
            "the all-critical inverse-ray aggregate or global Reeb route."
        ),
        consumer_ref=PACKET_REF,
        analysis_refs=[ANALYSIS_REF],
        source_refs=[SOURCE_REF, ANALYSIS_REF],
        result_status="finite_counterexample",
        result_summary=(
            "Four exact rational waypoints escape the unit lemniscate, leaving "
            "at most one safe origin spoke and eliminating the two-spoke shortcut."
        ),
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos1041-origin-spoke-pair-counterexample/1",
        "status": "verified_exact_mechanism_elimination",
        "experiment_contract": contract,
        "witness": witness,
        "consequence_decisions": [
            {
                "mechanism": "two_safe_root_to_origin_spokes",
                "decision": "eliminated",
            },
            {
                "mechanism": "all_critical_inverse_ray_hub_selection",
                "decision": "remains_open_and_not_touched_by_witness",
            },
            {
                "mechanism": "erdos_1041",
                "decision": "not_claimed",
            },
        ],
        "source_records": [
            source_record(REPO_ROOT, SOURCE_REF),
            source_record(REPO_ROOT, ANALYSIS_REF),
            source_record(REPO_ROOT, PACKET_REF),
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
    return emit(build_receipt(), args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
