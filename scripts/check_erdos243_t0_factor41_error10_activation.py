#!/usr/bin/env python3
"""Certify factor-41 cofinal activation on the #243 (31,-10) mode."""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from math import gcd
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)
from system.lib.formal_math_residue_cylinder import (  # noqa: E402
    centered_successor_signature,
    complete_unit_stride_residue_image,
)

from check_erdos243_t0_factor29_activation import (  # noqa: E402
    FACTOR29_SOURCE_MODULUS,
)
from check_erdos243_t0_factor31_41_field_activation import (  # noqa: E402
    _height29_multiplier_mod_prime,
    _transport_unit,
)


SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_t0_factor41_error10_activation.py"
)
PRIOR_SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_t0_factor31_41_field_activation.py"
)
PRIOR_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos243_t0_factor31_41_field_activation_receipt.json"
)
LIBRARY_REF = "system/lib/formal_math_residue_cylinder.py"
NOTE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/"
    "CleanRecoveryLengthComputationalLab.md"
)
PACKET_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/"
    "research_packet.json"
)
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "erdos243_t0_factor41_error10_activation_receipt.json"
)

PRIME = 41
SOURCE_STRIDE = FACTOR29_SOURCE_MODULUS * 30 * 31
EXPECTED_INPUT_PARENTS = 1_865_725_802_357_760_000
EXPECTED_VALUE_COUNTS = {
    0: 8,
    21: 9,
    24: 4,
    27: 4,
    30: 6,
    31: 8,
    37: 2,
}
EXPECTED_MODE_COUNTS = {
    (41, 1, 0): 8,
    (1, 41, -20): 4,
    (1, 41, -16): 8,
    (1, 41, 4): 2,
    (1, 41, 8): 4,
    (1, 41, 18): 9,
    (1, 41, 20): 6,
}


def _height31_multiplier_mod41(source_residue: int) -> int:
    multiplier29 = _height29_multiplier_mod_prime(
        source_residue,
        prime=PRIME,
        factor29_successor_error=-1,
    )
    multiplier30 = _transport_unit(
        29,
        -1,
        multiplier29,
        payment=1,
        successor_error=-1,
        modulus=PRIME,
    )
    return _transport_unit(
        30,
        -1,
        multiplier30,
        payment=1,
        successor_error=-10,
        modulus=PRIME,
    )


def complete_factor41_error10_census() -> dict[str, Any]:
    assert gcd(SOURCE_STRIDE, PRIME) == 1
    for divisor in range(21, 32):
        assert gcd(divisor, PRIME) == 1
    canonical = complete_unit_stride_residue_image(
        _height31_multiplier_mod41, modulus=PRIME
    )
    shifted = complete_unit_stride_residue_image(
        _height31_multiplier_mod41,
        modulus=PRIME,
        offset=23,
        stride=SOURCE_STRIDE,
    )
    assert Counter(shifted) == Counter(canonical)
    values = Counter(canonical)
    modes = Counter(
        centered_successor_signature(31, -10, multiplier)
        for multiplier in canonical
    )
    assert values == EXPECTED_VALUE_COUNTS
    assert modes == EXPECTED_MODE_COUNTS
    profile = (8, 21, 12)
    return {
        "incoming_state": {"height": 31, "error": -10},
        "next_raw_factor": 41,
        "source_stride": SOURCE_STRIDE,
        "source_stride_mod_41": SOURCE_STRIDE % PRIME,
        "prior_unit_divisors": list(range(21, 32)),
        "canonical_source_residue_table": canonical,
        "multiplier_counts_mod_41": {
            str(key): value for key, value in sorted(values.items())
        },
        "uniform_parent_profile": {
            "cofinal": profile[0],
            "positive": profile[1],
            "negative": profile[2],
        },
        "successor_mode_counts_per_parent": {
            f"payment={key[0]},height={key[1]},error={key[2]}": value
            for key, value in sorted(modes.items())
        },
        "logical_input_parent_count": EXPECTED_INPUT_PARENTS,
        "logical_child_count": EXPECTED_INPUT_PARENTS * PRIME,
        "weighted_cofinal_child_count": EXPECTED_INPUT_PARENTS * profile[0],
        "weighted_positive_child_count": EXPECTED_INPUT_PARENTS * profile[1],
        "weighted_negative_child_count": EXPECTED_INPUT_PARENTS * profile[2],
        "branch_negative_continuation": "12/41",
        "factor31_effective_negative_continuation_after_this_mode": "875/1271",
        "factor29_through_current_negative_continuation": "6125/36859",
        "formerly_inert_factor25_chain_continuation": "17500/479167",
        "universality_certificate": (
            "The complete next source lift permutes F_41 because its stride and "
            "all prior exact quotient divisors through 31 are units."
        ),
    }


def build_receipt() -> dict[str, Any]:
    previous = json.loads((REPO_ROOT / PRIOR_RECEIPT_REF).read_text())
    assert previous["status"] == "verified_uniform_factor31_41_field_activation"
    factor31 = previous["complete_factor31_41_census"]["factor31_branch"]
    assert factor31["logical_input_parent_count"] * 8 == EXPECTED_INPUT_PARENTS
    assert (
        factor31["successor_mode_counts_per_parent"]
        ["payment=1,height=31,error=-10"]
        == 8
    )
    census = complete_factor41_error10_census()
    contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Under a_(n+1)/a_n^2 -> 1 and rational reciprocal sum, force "
            "eventual Sylvester recurrence."
        ),
        claim_ceiling=(
            "Every actual (31,-10) parent has factor-41 profile (8,21,12), "
            "including eight cofinal children. Unrestricted #243 remains open."
        ),
        hypothesis_id="factor41_cofinally_activates_the_factor31_error10_mode",
        hypothesis_statement=(
            "The next prime field image on (31,-10) contains zero and removes a "
            "fixed share of negative support from every actual parent."
        ),
        probe_id="complete_factor41_unit_stride_image_on_error10",
        probe_question=(
            "Does the only prime next-factor among the seven new negative modes "
            "force a cofinal return?"
        ),
        computation=(
            "Propagate the exact cocycle over F_41 through the (31,-10) branch; "
            "use the unit source stride to transfer one 41-point table to every "
            "actual parent."
        ),
        falsifier=(
            "A nonunit prior divisor/stride, absence of zero, or any parent profile "
            "other than (8,21,12)."
        ),
        stop_condition=(
            "Stop after the complete prime-field profile and exact aggregate "
            "continuation are established."
        ),
        survival_consequence=(
            "Eight of 41 children return cofinally and 21 switch positive, leaving "
            "only 12 negative on every (31,-10) parent."
        ),
        falsification_consequence=(
            "A zero-free image would eliminate factor 41 as an immediate cofinal "
            "mechanism on this mode."
        ),
        consumer_ref=NOTE_REF,
        consumer_declarations=["factor-41 error-minus-ten cofinal consequence"],
        analysis_refs=[NOTE_REF, PACKET_REF, PRIOR_RECEIPT_REF],
        source_refs=[SCRIPT_REF, PRIOR_SCRIPT_REF, PRIOR_RECEIPT_REF, LIBRARY_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "The universal F_41 image contains multiplier zero eight times and has "
            "profile (8 cofinal,21 positive,12 negative)."
        ),
        progress_class="mechanism_opened",
        decision_basis=(
            "The complete field table is parent-independent by unit-stride "
            "permutation and contains eight full-payment residues."
        ),
        next_analytic_target=(
            "Probe successor raw factors 32,35,36,38,40,57,61. Factor 61 is "
            "prime; group the other six by shared-prime structure."
        ),
        resource_bounds={
            "canonical_field_evaluations": 41,
            "logical_input_parents": EXPECTED_INPUT_PARENTS,
            "avoided_materialized_refinements": EXPECTED_INPUT_PARENTS * PRIME,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos243-t0-factor41-error10-activation-receipt/1",
        "status": "verified_uniform_factor41_error10_cofinal_activation",
        "complete_factor41_error10_census": census,
        "mechanism_decision": {
            "factor41_profile": "cofinal=8,positive=21,negative=12",
            "factor31_effective_negative_continuation": "875/1271",
            "factor29_through_current_negative_continuation": "6125/36859",
            "formerly_inert_factor25_chain_continuation": "17500/479167",
            "next_step": contract["result"]["progress"]["next_analytic_target"],
        },
        "consequence_propagation": {
            "anchor": {
                "delta_class": "status_or_authority_changed",
                "strongest_authority": "exact_owner_checked_computation",
                "claim_ceiling": "source_conditioned_cofinal_mode_not_unrestricted_erdos243",
            },
            "decisions": [
                {
                    "surface": NOTE_REF,
                    "decision": "update_now",
                    "reason": "Binds the eight cofinal modes and exact continuation.",
                },
                {
                    "surface": PACKET_REF,
                    "decision": "update_now",
                    "reason": "Moves exact result, state-sensitive no-go, and producer.",
                },
                {
                    "surface": "corpus_computation_routes:erdos_243",
                    "decision": "update_now",
                    "reason": "Executable owner is explicitly linked and auto-discovered.",
                },
                {
                    "surface": PRIOR_SCRIPT_REF,
                    "decision": "verified_no_change",
                    "reason": "Its universal profiles remain exact inputs to this child branch.",
                },
                {
                    "surface": "four generic constant-name validator matches",
                    "decision": "outside_scope",
                    "reason": "Lexical collisions do not change their distinct residue cylinders.",
                },
                {
                    "surface": "Lean consumers and public projection",
                    "decision": "defer_with_reason",
                    "reason": "No Lean theorem changed and unrestricted #243 remains open.",
                    "reentry": "A selected Lean-bound or owner-approved public claim lands.",
                },
            ],
        },
        "experiment_contract": contract,
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [
                SCRIPT_REF,
                PRIOR_SCRIPT_REF,
                PRIOR_RECEIPT_REF,
                NOTE_REF,
                PACKET_REF,
                LIBRARY_REF,
            ]
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--explore", action="store_true")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    payload = complete_factor41_error10_census() if args.explore else build_receipt()
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.explore:
        print(rendered, end="")
        return 0
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
