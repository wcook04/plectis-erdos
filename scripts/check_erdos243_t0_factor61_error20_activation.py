#!/usr/bin/env python3
"""Certify the prime-61 profile on the #243 (41,-20) mode."""

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
    "check_erdos243_t0_factor61_error20_activation.py"
)
PRIOR_SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_t0_factor41_error10_activation.py"
)
PRIOR_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos243_t0_factor41_error10_activation_receipt.json"
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
    "erdos243_t0_factor61_error20_activation_receipt.json"
)

PRIME = 61
SOURCE_STRIDE = FACTOR29_SOURCE_MODULUS * 30 * 31 * 41
EXPECTED_INPUT_PARENTS = 7_462_903_209_431_040_000
EXPECTED_VALUE_COUNTS = {0: 4, 4: 9, 18: 10, 28: 6, 31: 14, 33: 2, 43: 10, 45: 6}
EXPECTED_MODE_COUNTS = {
    (61, 1, 0): 4,
    (1, 61, -15): 9,
    (1, 61, -14): 20,
    (1, 61, -5): 14,
    (1, 61, -3): 8,
    (1, 61, 4): 6,
}


def _height41_multiplier_mod61(source_residue: int) -> int:
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
    multiplier31 = _transport_unit(
        30,
        -1,
        multiplier30,
        payment=1,
        successor_error=-10,
        modulus=PRIME,
    )
    return _transport_unit(
        31,
        -10,
        multiplier31,
        payment=1,
        successor_error=-20,
        modulus=PRIME,
    )


def complete_factor61_error20_census() -> dict[str, Any]:
    assert gcd(SOURCE_STRIDE, PRIME) == 1
    prior_unit_divisors = [*range(21, 32), 41]
    for divisor in prior_unit_divisors:
        assert gcd(divisor, PRIME) == 1
    canonical = complete_unit_stride_residue_image(
        _height41_multiplier_mod61, modulus=PRIME
    )
    shifted = complete_unit_stride_residue_image(
        _height41_multiplier_mod61,
        modulus=PRIME,
        offset=23,
        stride=SOURCE_STRIDE,
    )
    assert Counter(shifted) == Counter(canonical)
    values = Counter(canonical)
    modes = Counter(
        centered_successor_signature(41, -20, multiplier)
        for multiplier in canonical
    )
    assert values == EXPECTED_VALUE_COUNTS
    assert modes == EXPECTED_MODE_COUNTS
    profile = (4, 6, 51)
    return {
        "incoming_state": {"height": 41, "error": -20},
        "next_raw_factor": PRIME,
        "source_stride": SOURCE_STRIDE,
        "source_stride_mod_61": SOURCE_STRIDE % PRIME,
        "prior_unit_divisors": prior_unit_divisors,
        "canonical_source_residue_table": canonical,
        "multiplier_counts_mod_61": {
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
        "branch_negative_continuation": "51/61",
        "factor41_error10_effective_negative_continuation": "692/2501",
        "factor31_effective_negative_continuation": "53055/77531",
        "factor29_through_current_negative_continuation": "371385/2248399",
        "formerly_inert_factor25_chain_continuation": "1061100/29229187",
        "universality_certificate": (
            "The complete next source lift permutes F_61 because its stride and "
            "all prior exact quotient divisors through 41 are units."
        ),
    }


def build_receipt() -> dict[str, Any]:
    previous = json.loads((REPO_ROOT / PRIOR_RECEIPT_REF).read_text())
    assert previous["status"] == "verified_uniform_factor41_error10_cofinal_activation"
    prior = previous["complete_factor41_error10_census"]
    assert (
        prior["logical_input_parent_count"]
        * prior["successor_mode_counts_per_parent"]["payment=1,height=41,error=-20"]
        == EXPECTED_INPUT_PARENTS
    )
    census = complete_factor61_error20_census()
    contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Under a_(n+1)/a_n^2 -> 1 and rational reciprocal sum, force "
            "eventual Sylvester recurrence."
        ),
        claim_ceiling=(
            "Every actual (41,-20) parent has factor-61 profile (4,6,51). "
            "Factor 61 forces four cofinal returns on this state; unrestricted "
            "#243 remains open."
        ),
        hypothesis_id="factor61_cofinally_activates_the_factor41_error20_mode",
        hypothesis_statement=(
            "The next prime field image on (41,-20) contains zero or removes a "
            "large fixed share of negative support from every actual parent."
        ),
        probe_id="complete_factor61_unit_stride_image_on_error20",
        probe_question=(
            "Does the newly exposed prime raw factor 61 force a cofinal return "
            "or a strong sign switch?"
        ),
        computation=(
            "Propagate the exact cocycle over F_61 through the (41,-20) branch; "
            "use the unit source stride to transfer one 61-point table to every "
            "actual parent."
        ),
        falsifier=(
            "Absence of zero, any nonunit prior divisor/stride, or any parent "
            "profile other than (4,6,51)."
        ),
        stop_condition=(
            "Stop after the complete prime-field profile and exact aggregate "
            "continuation are established."
        ),
        survival_consequence=(
            "A zero-containing image opens another exact cofinal-return mechanism "
            "on the actual negative cascade."
        ),
        falsification_consequence=(
            "A zero-free profile would eliminate immediate prime-field cofinal "
            "activation on this state."
        ),
        consumer_ref=NOTE_REF,
        consumer_declarations=["factor-61 error-minus-twenty cofinal consequence"],
        analysis_refs=[NOTE_REF, PACKET_REF, PRIOR_RECEIPT_REF],
        source_refs=[SCRIPT_REF, PRIOR_SCRIPT_REF, PRIOR_RECEIPT_REF, LIBRARY_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "The universal F_61 image contains zero four times and has profile "
            "(4 cofinal,6 positive,51 negative)."
        ),
        progress_class="mechanism_opened",
        decision_basis=(
            "The complete field table is parent-independent by unit-stride "
            "permutation and contains four full-payment residues."
        ),
        next_analytic_target=(
            "Probe composite raw factors 32,35,36,38,40,57,64,66,75,76 by "
            "shared-prime and nonunit-stride structure."
        ),
        resource_bounds={
            "canonical_field_evaluations": PRIME,
            "logical_input_parents": EXPECTED_INPUT_PARENTS,
            "avoided_materialized_refinements": EXPECTED_INPUT_PARENTS * PRIME,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos243-t0-factor61-error20-activation-receipt/1",
        "status": "verified_uniform_factor61_error20_cofinal_activation",
        "complete_factor61_error20_census": census,
        "mechanism_decision": {
            "factor61_profile": "cofinal=4,positive=6,negative=51",
            "factor41_error10_effective_negative_continuation": "692/2501",
            "factor31_effective_negative_continuation": "53055/77531",
            "factor29_through_current_negative_continuation": "371385/2248399",
            "formerly_inert_factor25_chain_continuation": "1061100/29229187",
            "next_step": contract["result"]["progress"]["next_analytic_target"],
        },
        "consequence_propagation": {
            "anchor": {
                "delta_class": "status_or_authority_changed",
                "strongest_authority": "exact_owner_checked_computation",
                "claim_ceiling": "source_conditioned_prime_mode_no_go_not_unrestricted_erdos243",
            },
            "decisions": [
                {
                    "surface": NOTE_REF,
                    "decision": "update_now",
                    "reason": "Binds the four cofinal modes and continuation update.",
                },
                {
                    "surface": PACKET_REF,
                    "decision": "update_now",
                    "reason": "Repairs the frontier and records the exact no-go.",
                },
                {
                    "surface": "corpus_computation_routes:erdos_243",
                    "decision": "update_now",
                    "reason": "Executable owner is auto-discovered by problem declaration.",
                },
                {
                    "surface": PRIOR_SCRIPT_REF,
                    "decision": "update_now",
                    "reason": "Its successor frontier omitted the two negative child states it created.",
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
    payload = complete_factor61_error20_census() if args.explore else build_receipt()
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
