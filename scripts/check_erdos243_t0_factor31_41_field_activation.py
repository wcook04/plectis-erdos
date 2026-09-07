#!/usr/bin/env python3
"""Certify universal factor-31/41 activation by complete field images."""

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
    centered_transport_next_multiplier_mod,
    complete_unit_stride_residue_image,
    invertible_quotient_value_mod,
)

from check_erdos243_t0_factor29_activation import (  # noqa: E402
    FACTOR29_SOURCE_MODULUS,
)
from check_erdos243_t0_factor30_35_split import (  # noqa: E402
    _negative_factor29_sources,
    _next_multiplier_mod,
)


SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_t0_factor31_41_field_activation.py"
)
SPLIT_SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_t0_factor30_35_split.py"
)
SPLIT_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos243_t0_factor30_35_split_receipt.json"
)
LIBRARY_REF = "system/lib/formal_math_residue_cylinder.py"
TEST_REF = "system/server/tests/test_formal_math_residue_cylinder.py"
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
    "erdos243_t0_factor31_41_field_activation_receipt.json"
)

EXPECTED_FACTOR31_INPUT_PARENTS = 233_215_725_294_720_000
EXPECTED_FACTOR41_INPUT_PARENTS = 133_266_128_739_840_000
EXPECTED_VALUE_COUNTS = {
    31: {0: 4, 1: 2, 6: 2, 14: 8, 21: 2, 28: 5, 29: 8},
    41: {0: 2, 9: 13, 14: 4, 15: 4, 28: 2, 30: 6, 36: 10},
}
EXPECTED_MODE_COUNTS = {
    31: {
        (31, 1, 0): 4,
        (1, 31, -10): 8,
        (1, 31, -9): 5,
        (1, 31, -7): 2,
        (1, 31, -5): 2,
        (1, 31, -4): 8,
        (1, 31, -1): 2,
    },
    41: {
        (41, 1, 0): 2,
        (1, 41, 3): 4,
        (1, 41, 6): 13,
        (1, 41, 11): 2,
        (1, 41, 12): 6,
        (1, 41, 13): 4,
        (1, 41, 14): 10,
    },
}


def _divide_unit(numerator: int, divisor: int, modulus: int) -> int:
    return invertible_quotient_value_mod(
        numerator, divisor=divisor, modulus=modulus
    )


def _transport_unit(
    height: int,
    centered_error: int,
    multiplier: int,
    *,
    payment: int,
    successor_error: int,
    modulus: int,
) -> int:
    """Transport a certified branch through an independent CRT modulus."""

    denominator = (multiplier - 1) * height + centered_error
    numerator = multiplier * denominator - payment * successor_error
    quotient = _divide_unit(numerator, height - centered_error, modulus)
    return (quotient + 1) % modulus


def _height29_multiplier_mod_prime(
    source_residue: int, *, prime: int, factor29_successor_error: int
) -> int:
    """Evaluate the already-certified exact cocycle modulo a new prime."""

    p = source_residue % prime
    multiplier20 = (380 * p * p + 18 * p + 1) % prime
    r = _divide_unit(multiplier20 - 1, 21, prime)
    multiplier21 = (420 * r * r + 19 * r + 1) % prime
    q = _divide_unit(multiplier21 - 1, 22, prime)
    multiplier22 = (462 * q * q + 20 * q + 1) % prime
    z = _divide_unit(multiplier22 - 1, 23, prime)
    multiplier23 = (506 * z * z + 21 * z + 1) % prime
    c = _divide_unit(multiplier23 - 1, 24, prime)
    multiplier24 = (552 * c * c + 22 * c + 1) % prime
    multiplier25 = _divide_unit(
        24 * multiplier24 * multiplier24 - 25 * multiplier24 + 26,
        25,
        prime,
    )
    multiplier26 = _divide_unit(
        25 * multiplier25 * multiplier25 - 26 * multiplier25 + 27,
        26,
        prime,
    )
    multiplier27 = _divide_unit(
        26 * multiplier26 * multiplier26 - 27 * multiplier26 + 28,
        27,
        prime,
    )
    multiplier28 = _transport_unit(
        27,
        -1,
        multiplier27,
        payment=1,
        successor_error=-1,
        modulus=prime,
    )
    return _transport_unit(
        28,
        -1,
        multiplier28,
        payment=1,
        successor_error=factor29_successor_error,
        modulus=prime,
    )


def _current_parent_multiplier_mod_prime(
    source_residue: int,
    *,
    prime: int,
    factor29_successor_error: int,
) -> int:
    """Transport the height-29 multiplier into the claimed parent state."""

    multiplier29 = _height29_multiplier_mod_prime(
        source_residue,
        prime=prime,
        factor29_successor_error=factor29_successor_error,
    )
    return _transport_unit(
        29,
        factor29_successor_error,
        multiplier29,
        payment=1,
        successor_error=factor29_successor_error,
        modulus=prime,
    )


def _branch_census(
    *,
    prime: int,
    current_height: int,
    current_error: int,
    preceding_raw_factor: int,
    input_parent_count: int,
) -> dict[str, Any]:
    source_stride = FACTOR29_SOURCE_MODULUS * preceding_raw_factor
    assert gcd(source_stride, prime) == 1
    for divisor in range(21, current_height + 1):
        assert gcd(divisor, prime) == 1

    canonical = complete_unit_stride_residue_image(
        lambda source: _current_parent_multiplier_mod_prime(
            source,
            prime=prime,
            factor29_successor_error=current_error,
        ),
        modulus=prime,
    )
    # An arbitrary actual source offset has the same multiset because the
    # declared source stride is a unit. This second table exercises the exact
    # source stride rather than merely quoting the permutation lemma.
    shifted = complete_unit_stride_residue_image(
        lambda source: _current_parent_multiplier_mod_prime(
            source,
            prime=prime,
            factor29_successor_error=current_error,
        ),
        modulus=prime,
        offset=17,
        stride=source_stride,
    )
    assert Counter(shifted) == Counter(canonical)

    # Independent exact-division regression: reconstruct one actual source
    # cylinder and compare the unit-field transport with pointwise quotient
    # recovery. This specifically catches an off-by-one multiplier that would
    # classify the height-29 value as though it already belonged to height
    # 30/35.
    refined29 = next(
        source
        for source, error, _ in _negative_factor29_sources()
        if error == current_error
    )
    actual_parent_source = next(
        candidate
        for lift in range(preceding_raw_factor)
        for candidate in [refined29 + FACTOR29_SOURCE_MODULUS * lift]
        if centered_successor_signature(
            29,
            current_error,
            _next_multiplier_mod(
                candidate, current_error, preceding_raw_factor
            ),
        )
        == (1, current_height, current_error)
    )
    inverse_stride = pow(source_stride, -1, prime)
    exact_parent_table: list[int] = []
    for source_residue in range(prime):
        lift = (
            (source_residue - actual_parent_source) * inverse_stride
        ) % prime
        source = actual_parent_source + source_stride * lift
        multiplier29 = _next_multiplier_mod(
            source,
            current_error,
            preceding_raw_factor * prime,
        )
        exact_parent = centered_transport_next_multiplier_mod(
            29,
            current_error,
            multiplier29,
            payment=1,
            successor_error=current_error,
            quotient_modulus=prime,
        )
        assert exact_parent == _current_parent_multiplier_mod_prime(
            source_residue,
            prime=prime,
            factor29_successor_error=current_error,
        )
        exact_parent_table.append(exact_parent)
    assert exact_parent_table == canonical
    value_counts = Counter(canonical)
    modes = Counter(
        centered_successor_signature(current_height, current_error, multiplier)
        for multiplier in canonical
    )
    assert value_counts == EXPECTED_VALUE_COUNTS[prime]
    assert modes == EXPECTED_MODE_COUNTS[prime]

    cofinal = sum(count for (_, height, _), count in modes.items() if height == 1)
    positive = sum(
        count
        for (_, height, error), count in modes.items()
        if height > 1 and error > 0
    )
    negative = sum(
        count
        for (_, height, error), count in modes.items()
        if height > 1 and error < 0
    )
    assert cofinal + positive + negative == prime

    return {
        "incoming_state": {"height": current_height, "error": current_error},
        "next_raw_factor": prime,
        "source_stride": source_stride,
        "source_stride_mod_prime": source_stride % prime,
        "prior_divisors_are_units": list(range(21, current_height + 1)),
        "canonical_source_residue_table": canonical,
        "exact_parent_transport_crosscheck_table": exact_parent_table,
        "current_multiplier_counts_mod_prime": {
            str(key): value for key, value in sorted(value_counts.items())
        },
        "uniform_parent_profile": {
            "cofinal": cofinal,
            "positive": positive,
            "negative": negative,
        },
        "successor_mode_counts_per_parent": {
            f"payment={key[0]},height={key[1]},error={key[2]}": value
            for key, value in sorted(modes.items())
        },
        "logical_input_parent_count": input_parent_count,
        "logical_child_count": input_parent_count * prime,
        "weighted_positive_child_count": input_parent_count * positive,
        "weighted_negative_child_count": input_parent_count * negative,
        "negative_continuation_ratio": f"{negative}/{prime}",
        "full_payment_residue_absent": 0 not in value_counts,
        "universality_certificate": (
            "Every actual next lift permutes all source residues modulo the new "
            "prime because the exact source stride and all prior quotient "
            "divisors are units. The height-29 multiplier is first transported "
            "through factor 30 or 35 into the declared parent state."
        ),
    }


def complete_factor31_41_field_census() -> dict[str, Any]:
    factor31 = _branch_census(
        prime=31,
        current_height=30,
        current_error=-1,
        preceding_raw_factor=30,
        input_parent_count=EXPECTED_FACTOR31_INPUT_PARENTS,
    )
    factor41 = _branch_census(
        prime=41,
        current_height=35,
        current_error=-6,
        preceding_raw_factor=35,
        input_parent_count=EXPECTED_FACTOR41_INPUT_PARENTS,
    )
    assert factor31["uniform_parent_profile"] == {
        "cofinal": 4,
        "positive": 0,
        "negative": 27,
    }
    assert factor41["uniform_parent_profile"] == {
        "cofinal": 2,
        "positive": 39,
        "negative": 0,
    }
    return {
        "factor31_branch": factor31,
        "factor41_branch": factor41,
        "aggregate_boundary_transfer": {
            "factor31_negative_continuation": "27/31",
            "factor41_negative_continuation": "0",
            "factor29_through_factor31_41_negative_continuation": "189/899",
            "formerly_inert_factor25_chain_continuation": "540/11687",
        },
        "avoided_materialized_refinement_count": (
            EXPECTED_FACTOR31_INPUT_PARENTS * 31
            + EXPECTED_FACTOR41_INPUT_PARENTS * 41
        ),
        "canonical_field_evaluation_count": 31 + 41,
    }


def build_receipt() -> dict[str, Any]:
    previous = json.loads((REPO_ROOT / SPLIT_RECEIPT_REF).read_text())
    assert previous["status"] == "verified_factor30_35_split"
    assert (
        previous["complete_factor30_35_census"]["branches"]["-1"]
        ["weighted_successor_mode_counts"]["payment=1,height=30,error=-1"]
        == EXPECTED_FACTOR31_INPUT_PARENTS
    )
    assert (
        previous["complete_factor30_35_census"]["branches"]["-6"]
        ["weighted_successor_mode_counts"]["payment=1,height=35,error=-6"]
        == EXPECTED_FACTOR41_INPUT_PARENTS
    )
    census = complete_factor31_41_field_census()
    contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Under a_(n+1)/a_n^2 -> 1 and rational reciprocal sum, force "
            "eventual Sylvester recurrence."
        ),
        claim_ceiling=(
            "Every actual surviving (30,-1) parent has factor-31 profile "
            "(4,0,27), and every surviving (35,-6) parent has factor-41 profile "
            "(2,39,0). Factor 41 kills all negative support on its branch; "
            "unrestricted #243 remains open."
        ),
        hypothesis_id="new_prime_field_images_uniformly_activate_both_split_modes",
        hypothesis_statement=(
            "After exact transport into the declared parent state, the next prime "
            "field forces cofinal return or sign change on actual support."
        ),
        probe_id="complete_factor31_41_unit_stride_field_images",
        probe_question=(
            "Can coprime source-stride permutation replace 889 million materialized "
            "refinements and prove a uniform next-factor profile?"
        ),
        computation=(
            "Propagate the exact quotient cocycle over F_31 and F_41 using modular "
            "inverses for all prior certified divisions. Since each next source "
            "stride is a unit, enumerate one canonical complete field image per "
            "branch and transfer its multiset to every actual parent."
        ),
        falsifier=(
            "A nonunit prior divisor or source stride, failure to transport the "
            "height-29 multiplier, or a profile other than (4,0,27)/(2,39,0)."
        ),
        stop_condition=(
            "Stop after both universal field images and exact weighted transfers "
            "are certified; do not materialize the parent-by-lift product."
        ),
        survival_consequence=(
            "Factor 31 forces four cofinal returns; factor 41 forces two cofinal "
            "returns and switches every other child positive, killing that branch."
        ),
        falsification_consequence=(
            "Failure of the unit-field image would require returning to source-"
            "stratified composite-cylinder enumeration."
        ),
        consumer_ref=NOTE_REF,
        consumer_declarations=["factor-31/factor-41 field-permutation consequence"],
        analysis_refs=[NOTE_REF, PACKET_REF, SPLIT_RECEIPT_REF],
        source_refs=[
            SCRIPT_REF,
            SPLIT_SCRIPT_REF,
            SPLIT_RECEIPT_REF,
            LIBRARY_REF,
            TEST_REF,
        ],
        result_status="exact_one_way_result",
        result_summary=(
            "The complete F_31 image has profile (4,0,27); the complete F_41 "
            "image has profile (2,39,0). Unit source strides make these profiles "
            "universal across all actual parents."
        ),
        progress_class="mechanism_opened",
        decision_basis=(
            "All prior divisors and both source strides are units in the new prime "
            "fields, so complete lift inputs are residue permutations."
        ),
        next_analytic_target=(
            "Resolve the six factor-31 negative errors with raw factors "
            "32,35,36,38,40,41; factor 41 is the only next prime."
        ),
        resource_bounds={
            "canonical_field_evaluations": 72,
            "avoided_materialized_refinements": census[
                "avoided_materialized_refinement_count"
            ],
            "factor31_logical_input_parents": EXPECTED_FACTOR31_INPUT_PARENTS,
            "factor41_logical_input_parents": EXPECTED_FACTOR41_INPUT_PARENTS,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos243-t0-factor31-41-field-activation-receipt/1",
        "status": "verified_uniform_factor31_41_field_activation",
        "complete_factor31_41_census": census,
        "mechanism_decision": {
            "factor31_profile": "cofinal=4,positive=0,negative=27",
            "factor41_profile": "cofinal=2,positive=39,negative=0",
            "factor29_through_factor31_41_negative_continuation": "189/899",
            "formerly_inert_factor25_chain_continuation": "540/11687",
            "next_step": contract["result"]["progress"]["next_analytic_target"],
        },
        "consequence_propagation": {
            "anchor": {
                "delta_class": "status_or_authority_changed",
                "strongest_authority": "exact_owner_checked_computation",
                "claim_ceiling": "source_conditioned_finite_cylinder_not_unrestricted_erdos243",
            },
            "decisions": [
                {
                    "surface": NOTE_REF,
                    "decision": "update_now",
                    "reason": (
                        "Records the unit-field proof, exact tables, continuation, "
                        "and next raw factors."
                    ),
                },
                {
                    "surface": PACKET_REF,
                    "decision": "update_now",
                    "reason": (
                        "Moves the exact result, negative mechanism, claim ceiling, "
                        "and open producer."
                    ),
                },
                {
                    "surface": "corpus_computation_routes:erdos_243",
                    "decision": "update_now",
                    "reason": (
                        "The executable owner is explicitly linked and auto-discovered."
                    ),
                },
                {
                    "surface": "three prior EXPECTED_MODE_COUNTS validators",
                    "decision": "outside_scope",
                    "reason": (
                        "Generic local constant-name collisions; their mathematics "
                        "is unchanged."
                    ),
                },
                {
                    "surface": "Lean consumers",
                    "decision": "verified_no_change",
                    "reason": (
                        "No Lean theorem authority changed; this is an exact "
                        "computation receipt."
                    ),
                },
                {
                    "surface": "public projection",
                    "decision": "defer_with_reason",
                    "reason": (
                        "Unrestricted #243 remains open and the release rule requires "
                        "human review."
                    ),
                    "reentry": (
                        "A selected Lean-bound theorem or owner-approved public "
                        "finite-cylinder claim lands."
                    ),
                },
            ],
            "cold_reader": {
                "status": "selected_result_and_open_boundary_visible",
                "query": "problem cockpit Erdos 243 factor 31 factor 41 field permutation",
            },
        },
        "experiment_contract": contract,
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [
                SCRIPT_REF,
                SPLIT_SCRIPT_REF,
                SPLIT_RECEIPT_REF,
                NOTE_REF,
                PACKET_REF,
                LIBRARY_REF,
                TEST_REF,
            ]
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--explore", action="store_true")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    payload = complete_factor31_41_field_census() if args.explore else build_receipt()
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
