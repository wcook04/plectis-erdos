#!/usr/bin/env python3
"""Certify the #243 height-22 centered-state split modulo twenty-three.

The height-21 certificate leaves 120931560 payment-one source classes modulo
16295479200.  Expanding all twenty-three lifts would create 2781425880
classes.  Instead, this checker evaluates the expensive degree-1024 source
polynomial only at lift zero and one modulo 23, tabulates the ten accepted
higher-coordinate residues for each actual source category, and uses exact
full-period affine preimage counts.  Nonzero slopes see each field residue
once; zero slopes contribute either all twenty-three lifts or none.

Exactly 2024012298 refined classes have multiplier residue zero, pay the full
factor twenty-three, and return cofinally.  Among the payment-one classes,
84115680 have multiplier residue fifteen and switch to centered error +5;
only 673297902 have residue one and reach height 23 with centered error -1.
No orbit-horizon evidence is used.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path
from typing import Any

import numpy as np


sys.set_int_max_str_digits(1_000_000)

REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)
from system.lib.formal_math_residue_cylinder import (  # noqa: E402
    affine_full_lift_acceptance_table,
    negative_unit_successor_signature,
)

from check_erdos243_height21_payment_split import (  # noqa: E402
    HEIGHT_TWENTY_ONE_MODULUS,
    PAYMENT_ONE_T_CLASSES,
    _affine_coordinates,
    _p_table,
    _source_cylinder,
)


SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_height22_mod23_split.py"
)
HEIGHT_TWENTY_ONE_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_height21_payment_split.py"
)
HEIGHT_TWENTY_ONE_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos243_height21_payment_split_receipt.json"
)
RESIDUE_CYLINDER_REF = "system/lib/formal_math_residue_cylinder.py"
LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/"
    "CleanRecoveryLengthCounterexample.lean"
)
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
    "erdos243_height22_mod23_split_receipt.json"
)

HEIGHT_TWENTY_TWO_MODULUS = HEIGHT_TWENTY_ONE_MODULUS * 23
COMMON_GLOBAL_MODULUS = 1_124_388_064_800
EXPECTED_HEIGHT_TWENTY_TWO_INPUTS = 120_931_560
EXPECTED_REFINED_CLASSES = 2_781_425_880
EXPECTED_FULL_PAYMENT = 2_024_012_298
EXPECTED_POSITIVE_SWITCH = 84_115_680
EXPECTED_NEGATIVE_SURVIVOR = 673_297_902
EXPECTED_SLOPE_COUNTS = {
    0: 99_902_640,
    7: 5_266_398,
    11: 5_250_828,
    12: 5_249_736,
    16: 5_261_958,
}
EXPECTED_COUNT_PER_FAMILY = {
    0: {0: 21_045_114, 10: 21_028_920, 23: 78_857_526},
    1: {0: 78_857_526, 9: 21_028_920, 23: 21_045_114},
    15: {0: 99_902_640, 4: 21_028_920},
}
EXPECTED_RESIDUE_COORDINATES = {
    (0, 0): {
        0: [1, 2, 6, 8, 9, 12, 14, 17, 18, 20],
        1: [0, 3, 4, 7, 11, 13, 15, 19, 22],
        15: [5, 10, 16, 21],
    },
    (0, 12): {
        0: [1, 2, 6, 8, 9, 12, 14, 17, 18, 20],
        1: [0, 3, 4, 7, 11, 13, 15, 19, 22],
        15: [5, 10, 16, 21],
    },
    (4, 0): {
        0: [1, 3, 4, 7, 9, 12, 13, 15, 19, 20],
        1: [2, 6, 8, 10, 14, 17, 18, 21, 22],
        15: [0, 5, 11, 16],
    },
    (4, 12): {
        0: [1, 3, 4, 7, 9, 12, 13, 15, 19, 20],
        1: [2, 6, 8, 10, 14, 17, 18, 21, 22],
        15: [0, 5, 11, 16],
    },
    (6, 0): {
        0: [1, 5, 6, 10, 12, 13, 16, 18, 21, 22],
        1: [0, 3, 4, 7, 8, 11, 15, 17, 19],
        15: [2, 9, 14, 20],
    },
    (6, 12): {
        0: [1, 5, 6, 10, 12, 13, 16, 18, 21, 22],
        1: [0, 3, 4, 7, 8, 11, 15, 17, 19],
        15: [2, 9, 14, 20],
    },
}


def _merge_counts(
    target: dict[int, int], values: np.ndarray[Any, np.dtype[np.int64]]
) -> None:
    unique, counts = np.unique(values, return_counts=True)
    for key, value in zip(unique, counts, strict=True):
        target[int(key)] = target.get(int(key), 0) + int(value)


def _multiplier_residue_lookup(
    p23_table: np.ndarray[Any, np.dtype[np.int64]],
) -> tuple[
    dict[int, np.ndarray[Any, np.dtype[np.int16]]],
    dict[tuple[int, int], dict[int, list[int]]],
]:
    lookups = {
        residue: np.zeros((10, 21, 23, 23), dtype=np.int16)
        for residue in (0, 1, 15)
    }
    coordinates: dict[tuple[int, int], dict[int, list[int]]] = {}
    inverse_21_mod_23 = pow(21, -1, 23)
    inverse_22_mod_23 = pow(22, -1, 23)
    for t_base in PAYMENT_ONE_T_CLASSES:
        for p21 in (0, 12):
            buckets = {residue: [] for residue in (0, 1, 15)}
            for coordinate in range(23):
                p23 = int(p23_table[t_base, coordinate])
                p483 = p21 + 21 * (
                    ((p23 - p21) * inverse_21_mod_23) % 23
                )
                height_twenty_multiplier = 380 * p483 * p483 + 18 * p483 + 1
                assert (height_twenty_multiplier - 1) % 21 == 0
                r23 = ((height_twenty_multiplier - 1) // 21) % 23
                s = (r23 * inverse_22_mod_23) % 23
                q = (9240 * s * s + 19 * s) % 23
                height_twenty_two_multiplier = (462 * q * q + 20 * q + 1) % 23
                assert (height_twenty_two_multiplier == 0) == (s in {11, 19})
                assert height_twenty_two_multiplier in buckets
                buckets[height_twenty_two_multiplier].append(coordinate)
            coordinates[(t_base, p21)] = buckets
            for residue, accepted in buckets.items():
                lookups[residue][t_base, p21] = np.array(
                    affine_full_lift_acceptance_table(
                        modulus=23, accepted_residues=accepted
                    ),
                    dtype=np.int16,
                )
    assert coordinates == EXPECTED_RESIDUE_COORDINATES
    return lookups, coordinates


def complete_height_twenty_two_split() -> dict[str, Any]:
    q10, source_classes, t_base = _source_cylinder()
    u21, slope21 = _affine_coordinates(q10, source_classes, t_base, 21)
    u22, slope22 = _affine_coordinates(q10, source_classes, t_base, 22)
    u23, slope23 = _affine_coordinates(q10, source_classes, t_base, 23)
    p21_table = _p_table(21)
    p22_table = _p_table(22)
    p23_table = _p_table(23)
    lookups, residue_coordinates = _multiplier_residue_lookup(p23_table)
    inverse_21_mod_22 = pow(21, -1, 22)

    height_twenty_two_inputs = 0
    refined_classes = 0
    residue_counts = {residue: 0 for residue in (0, 1, 15)}
    slope_counts: dict[int, int] = {}
    count_per_family = {residue: {} for residue in (0, 1, 15)}

    for lift21 in range(21):
        coordinate21 = (u21 + slope21 * lift21) % 21
        p21 = p21_table[t_base, coordinate21]
        survives_height_twenty = p21 != 18

        for lift22 in range(22):
            total_lift = lift21 + 21 * lift22
            coordinate22 = (u22 + slope22 * total_lift) % 22
            p22 = p22_table[t_base, coordinate22]
            p462 = p21 + 21 * (
                ((p22 - p21) * inverse_21_mod_22) % 22
            )
            height_twenty_multiplier = 380 * p462 * p462 + 18 * p462 + 1
            r22 = ((height_twenty_multiplier - 1) // 21) % 22
            height_twenty_two_mask = survives_height_twenty & (r22 == 0)
            family_count = int(np.sum(height_twenty_two_mask))
            height_twenty_two_inputs += family_count
            if family_count == 0:
                continue

            offset23 = (u23 + slope23 * total_lift) % 23
            lift23_slope = (slope23 * (21 * 22)) % 23
            refined_classes += family_count * 23
            _merge_counts(slope_counts, lift23_slope[height_twenty_two_mask])
            for residue in residue_counts:
                accepted_lift_counts = lookups[residue][
                    t_base, p21, offset23, lift23_slope
                ]
                live_acceptance = accepted_lift_counts[height_twenty_two_mask]
                residue_counts[residue] += int(np.sum(live_acceptance))
                _merge_counts(count_per_family[residue], live_acceptance)

    assert height_twenty_two_inputs == EXPECTED_HEIGHT_TWENTY_TWO_INPUTS
    assert refined_classes == EXPECTED_REFINED_CLASSES
    assert residue_counts == {
        0: EXPECTED_FULL_PAYMENT,
        1: EXPECTED_NEGATIVE_SURVIVOR,
        15: EXPECTED_POSITIVE_SWITCH,
    }
    assert sum(residue_counts.values()) == refined_classes
    assert slope_counts == EXPECTED_SLOPE_COUNTS
    assert count_per_family == EXPECTED_COUNT_PER_FAMILY
    return {
        "input_height_twenty_two_class_count_mod_16295479200": (
            height_twenty_two_inputs
        ),
        "height_twenty_two_refinement_modulus": HEIGHT_TWENTY_TWO_MODULUS,
        "complete_refined_class_count": refined_classes,
        "height_twenty_two_multiplier_image_mod_23": [0, 1, 15],
        "height_twenty_two_payment_image": [1, 23],
        "full_payment_twenty_three_class_count": residue_counts[0],
        "payment_one_positive_switch_class_count": residue_counts[15],
        "payment_one_to_height_twenty_three_negative_class_count": (
            residue_counts[1]
        ),
        "multiplier_residue_coordinates_by_source_category": {
            f"t={key[0]},p21={key[1]}": {
                str(residue): values for residue, values in sorted(value.items())
            }
            for key, value in sorted(residue_coordinates.items())
        },
        "lift23_slope_counts": {
            str(key): value for key, value in sorted(slope_counts.items())
        },
        "lift_count_per_source_family_by_multiplier_residue": {
            str(residue): {
                str(key): value
                for key, value in sorted(family_counts.items())
            }
            for residue, family_counts in sorted(count_per_family.items())
        },
        "compressed_root_counting": {
            "unexpanded_lift_class_count": refined_classes,
            "source_family_count": height_twenty_two_inputs,
            "coordinates_per_actual_category_by_multiplier_residue": {
                "0": 10,
                "1": 9,
                "15": 4,
            },
            "nonzero_slope_lifts_per_family_by_multiplier_residue": {
                "0": 10,
                "1": 9,
                "15": 4,
            },
            "zero_slope_lifts_per_family_by_multiplier_residue": [0, 23],
            "shared_primitive": (
                "system.lib.formal_math_residue_cylinder."
                "affine_full_lift_acceptance_table"
            ),
            "centered_transition_primitive": (
                "system.lib.formal_math_residue_cylinder."
                "negative_unit_successor_signature"
            ),
            "exactness": (
                "gcd fiber cardinality for complete affine periods; no sampling "
                "and no materialization of the 23-fold refined cylinder"
            ),
        },
    }


def symbolic_height_twenty_two_roots() -> dict[str, Any]:
    roots = []
    for s in range(23):
        q = (9240 * s * s + 19 * s) % 23
        multiplier = (462 * q * q + 20 * q + 1) % 23
        if multiplier == 0:
            roots.append(s)
            assert q == 12
    assert roots == [11, 19]
    for root in roots:
        for lift in range(40):
            s = root + 23 * lift
            q = 9240 * s * s + 19 * s
            multiplier = 462 * q * q + 20 * q + 1
            assert multiplier % 23 == 0
            assert math.gcd(multiplier * multiplier, 23) == 23
    centered_payment_one_errors = {}
    for residue in (1, 15):
        payment, next_height, centered_error = negative_unit_successor_signature(
            22, residue
        )
        assert (payment, next_height) == (1, 23)
        centered_payment_one_errors[str(residue)] = centered_error
    assert centered_payment_one_errors == {"1": -1, "15": 5}
    return {
        "height_twenty_two_full_payment_source_roots_mod_23": roots,
        "intermediate_parameter_residue_mod_23": 12,
        "centered_payment_one_errors_by_multiplier_residue": (
            centered_payment_one_errors
        ),
        "transitions": {
            "0": "(22,-1) --23--> (1,0 forever)",
            "1": "(22,-1) --1--> (23,-1)",
            "15": "(22,-1) --1--> (23,+5)",
        },
        "complete_symbolic_lifts_per_root": 40,
        "lean_declarations": [
            "ErdosProblems.Erdos243.heightTwentyTwo_transitionIdentity",
            "ErdosProblems.Erdos243.heightTwentyTwo_sourceRootIdentity",
            "ErdosProblems.Erdos243.heightTwentyTwo_multiplierAtTwelveIdentity",
            "ErdosProblems.Erdos243.heightTwentyTwo_fullPayment",
            "ErdosProblems.Erdos243.heightTwentyTwo_fullCollapse",
            "ErdosProblems.Erdos243.heightTwentyTwo_positiveSwitchIdentity",
            "ErdosProblems.Erdos243.heightTwentyTwo_negativeSurvivorIdentity",
        ],
    }


def build_receipt() -> dict[str, Any]:
    height_twenty_one = json.loads(
        (REPO_ROOT / HEIGHT_TWENTY_ONE_RECEIPT_REF).read_text(encoding="utf-8")
    )
    assert height_twenty_one["status"] == "verified_exact_height_twenty_one_payment_split"
    split = complete_height_twenty_two_split()
    roots = symbolic_height_twenty_two_roots()

    new_zero = split["full_payment_twenty_three_class_count"] * 3
    new_positive = split["payment_one_positive_switch_class_count"] * 3
    zero = 38_684_115_486 * 23 + new_zero
    positive = 9_839_527_434 * 23 + new_positive
    negative = (
        split["payment_one_to_height_twenty_three_negative_class_count"] * 3
    )
    assert (zero, positive, negative) == (
        895_806_693_072,
        226_561_478_022,
        2_019_893_706,
    )
    assert zero + positive + negative == COMMON_GLOBAL_MODULUS

    contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Under a_(n+1)/a_n^2 -> 1 and rational reciprocal sum, force "
            "eventual Sylvester recurrence."
        ),
        claim_ceiling=(
            "Exact cofinal return for 2024012298 height-22 full-payment classes "
            "and positive sign switch for 84115680 payment-one classes before the "
            "common factor-three lift, leaving 673297902 negative classes at "
            "height 23; unrestricted #243 remains open."
        ),
        hypothesis_id="height_twenty_two_payment_one_preserves_negative_error",
        hypothesis_statement=(
            "Every actual height-22 payment-one multiplier preserves centered "
            "error -1 after the transition to height 23."
        ),
        probe_id="compressed_affine_mod23_centered_residue_count",
        probe_question=(
            "Which multiplier residues modulo 23 occur on the complete height-22 "
            "source, and which cofinally return, switch positive, or retain "
            "negative centered error?"
        ),
        computation=(
            "Recover affine higher coordinates modulo 23, precompute the coordinate "
            "fibers for every actual multiplier residue, and count their preimages "
            "over complete affine periods using gcd fiber cardinality."
        ),
        falsifier=(
            "A nonzero exact count of payment-one lifts whose centered successor "
            "error is positive rather than -1."
        ),
        stop_condition=(
            "Stop after every height-22 lift is partitioned into cofinal, positive, "
            "or continuing-negative state; do not horizon-audit the true height-23 "
            "survivors."
        ),
        survival_consequence=(
            "If every payment-one residue gave centered error -1, all 757413582 "
            "payment-one lifts would remain in the expanding negative boundary mode."
        ),
        falsification_consequence=(
            "Multiplier residue 15 occurs on 84115680 exact lifts and forces centered "
            "error +5; only the 673297902 residue-one lifts remain negative."
        ),
        consumer_ref=LEAN_REF,
        consumer_declarations=roots["lean_declarations"],
        analysis_refs=[NOTE_REF, PACKET_REF, HEIGHT_TWENTY_ONE_RECEIPT_REF],
        source_refs=[
            SCRIPT_REF,
            HEIGHT_TWENTY_ONE_REF,
            HEIGHT_TWENTY_ONE_RECEIPT_REF,
            RESIDUE_CYLINDER_REF,
            LEAN_REF,
        ],
        result_status="exact_one_way_result",
        result_summary=(
            "The complete height-22 multiplier image modulo 23 is {0,1,15}. "
            "Exact compressed counting proves 2024012298 cofinal returns, "
            "84115680 positive switches, and 673297902 negative survivors."
        ),
        progress_class="one_way_theorem",
        decision_basis=(
            "Complete affine-period fiber counts replace a 2.78-billion-class "
            "expansion, while exact integer identities certify both the cofinal "
            "and centered-sign transitions."
        ),
        next_analytic_target=(
            "Discard every full-payment and residue-fifteen class; restrict the next "
            "exact probe to the 673297902 residue-one height-23 negative classes."
        ),
        resource_bounds={
            "source_polynomial_degree": 1024,
            "source_family_count": EXPECTED_HEIGHT_TWENTY_TWO_INPUTS,
            "logically_classified_lifts": EXPECTED_REFINED_CLASSES,
            "affine_lookup_entries": 333_270,
            "symbolic_root_checks": 80,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos243-height22-mod23-split-receipt/2",
        "status": "verified_exact_height_twenty_two_centered_split",
        "complete_height_twenty_two_split": split,
        "symbolic_height_twenty_two_roots": roots,
        "cumulative_source_class_partition": {
            "common_modulus": COMMON_GLOBAL_MODULUS,
            "new_cofinal_return_count": new_zero,
            "new_positive_switch_count": new_positive,
            "zero_centered_class_count": zero,
            "positive_centered_class_count": positive,
            "continuing_negative_candidate_class_count": negative,
            "height_twenty_three_negative_candidate_count": negative,
            "exact_partition": (
                "895806693072 zero + 226561478022 positive + "
                "2019893706 negative = 1124388064800"
            ),
        },
        "experiment_contract": contract,
        "consequence_reconciliation": {
            "height_twenty_two_full_payment_mode": {
                "decision": "update_now",
                "reason": "exact nonzero root count forces cofinal return",
                "authority_surface": PACKET_REF,
            },
            "height_twenty_two_positive_switch_mode": {
                "decision": "update_now",
                "reason": "multiplier residue fifteen forces centered error +5",
                "authority_surface": PACKET_REF,
            },
            "height_twenty_three_payment_one_branch": {
                "decision": "update_now",
                "reason": (
                    "only multiplier residue one preserves negative centered error; "
                    "residue fifteen must be removed as positive"
                ),
                "authority_surface": PACKET_REF,
            },
            "public_projection": {
                "decision": "defer_with_reason",
                "reason": "private exact result is not automatic publication authority",
                "reentry_condition": "explicit public release wave with owner review",
                "authority_surface": PACKET_REF,
            },
        },
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [
                SCRIPT_REF,
                HEIGHT_TWENTY_ONE_REF,
                HEIGHT_TWENTY_ONE_RECEIPT_REF,
                RESIDUE_CYLINDER_REF,
                LEAN_REF,
                NOTE_REF,
                PACKET_REF,
            ]
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = json.dumps(build_receipt(), indent=2, sort_keys=True) + "\n"
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
