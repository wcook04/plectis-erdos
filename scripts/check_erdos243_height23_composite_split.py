#!/usr/bin/env python3
"""Classify the actual #243 height-23 factor-twenty-four source modes.

The corrected height-22 certificate leaves 673297902 negative classes before
the common factor-three lift.  Refining them literally by twenty-four would
create more than sixteen billion classes.  This checker first quotients the
506880 source families by their joint affine coordinates modulo
21,22,23,16,9, leaving only 6699 weighted keys.  It then aggregates the
height-22 source state and uses exact generalized CRT across the overlapping
moduli 10626, 16, and 9 to recover the divided height-22 quotient modulo 24.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path
from typing import Any

import numpy as np


REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)
from system.lib.formal_math_residue_cylinder import (  # noqa: E402
    generalized_crt_pair,
    negative_unit_successor_signature,
)

from check_erdos243_height21_payment_split import (  # noqa: E402
    _affine_coordinates,
    _p_table,
    _source_cylinder,
)


SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_height23_composite_split.py"
)
HEIGHT_TWENTY_TWO_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_height22_mod23_split.py"
)
HEIGHT_TWENTY_TWO_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos243_height22_mod23_split_receipt.json"
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
    "erdos243_height23_composite_split_receipt.json"
)

EXPECTED_SOURCE_FAMILIES = 506_880
EXPECTED_AFFINE_KEYS = 6_699
EXPECTED_HEIGHT_TWENTY_TWO_FAMILIES = 120_931_560
EXPECTED_HEIGHT_TWENTY_THREE_INPUTS = 673_297_902
EXPECTED_REFINED_CLASSES = EXPECTED_HEIGHT_TWENTY_THREE_INPUTS * 24
EXPECTED_HEIGHT_TWENTY_TWO_KEYS = 570
EXPECTED_Z24_COUNTS = {0: EXPECTED_REFINED_CLASSES}
EXPECTED_MULTIPLIER_COUNTS = {1: EXPECTED_REFINED_CLASSES}
EXPECTED_MODE_COUNTS = {(1, 24, -1): EXPECTED_REFINED_CLASSES}
COMMON_GLOBAL_MODULUS = 26_985_313_555_200


def _weighted_affine_keys() -> tuple[np.ndarray[Any, Any], np.ndarray[Any, Any]]:
    q10, source_classes, t_base = _source_cylinder()
    columns = [t_base]
    for modulus in (21, 22, 23, 16, 9):
        offset, slope = _affine_coordinates(
            q10, source_classes, t_base, modulus
        )
        columns.extend([offset, slope])
    features = np.stack(columns, axis=1)
    keys, weights = np.unique(features, axis=0, return_counts=True)
    assert source_classes.size == EXPECTED_SOURCE_FAMILIES
    assert keys.shape == (EXPECTED_AFFINE_KEYS, 11)
    assert int(np.sum(weights)) == EXPECTED_SOURCE_FAMILIES
    return keys.astype(np.int64), weights.astype(np.int64)


def _pack_height_twenty_two_key(columns: list[np.ndarray[Any, Any]]) -> np.ndarray[Any, Any]:
    bases = (462, 23, 23, 16, 16, 9, 9)
    code = columns[0].astype(np.int64)
    for base, column in zip(bases, columns[1:], strict=True):
        code = code * base + column
    return code


def _decode_height_twenty_two_keys(codes: np.ndarray[Any, Any]) -> list[np.ndarray[Any, Any]]:
    values = codes.copy()
    reversed_columns = []
    for base in (9, 9, 16, 16, 23, 23, 462):
        reversed_columns.append(values % base)
        values //= base
    reversed_columns.append(values)
    return list(reversed(reversed_columns))


def _merge_weighted_codes(
    target: Counter[int], codes: np.ndarray[Any, Any], weights: np.ndarray[Any, Any]
) -> None:
    order = np.argsort(codes)
    ordered_codes = codes[order]
    ordered_weights = weights[order]
    starts = np.concatenate(
        [np.array([0]), np.flatnonzero(np.diff(ordered_codes)) + 1]
    )
    totals = np.add.reduceat(ordered_weights, starts)
    for code, weight in zip(ordered_codes[starts], totals, strict=True):
        target[int(code)] += int(weight)


def _height_twenty_two_keys() -> tuple[np.ndarray[Any, Any], np.ndarray[Any, Any]]:
    keys, weights = _weighted_affine_keys()
    (
        t_base,
        u21,
        slope21,
        u22,
        slope22,
        u23,
        slope23,
        u16,
        slope16,
        u9,
        slope9,
    ) = keys.T
    p21_table = _p_table(21)
    p22_table = _p_table(22)
    inverse_21_mod_22 = pow(21, -1, 22)
    aggregated: Counter[int] = Counter()
    weighted_family_count = 0

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
            multiplier20 = 380 * p462 * p462 + 18 * p462 + 1
            r22 = ((multiplier20 - 1) // 21) % 22
            live = survives_height_twenty & (r22 == 0)
            if not bool(np.any(live)):
                continue
            live_weights = weights[live]
            weighted_family_count += int(np.sum(live_weights))
            code = _pack_height_twenty_two_key(
                [
                    t_base[live],
                    p462[live],
                    (u23[live] + slope23[live] * total_lift) % 23,
                    (slope23[live] * (21 * 22)) % 23,
                    (u16[live] + slope16[live] * total_lift) % 16,
                    (slope16[live] * (21 * 22)) % 16,
                    (u9[live] + slope9[live] * total_lift) % 9,
                    (slope9[live] * (21 * 22)) % 9,
                ]
            )
            _merge_weighted_codes(aggregated, code, live_weights)

    assert weighted_family_count == EXPECTED_HEIGHT_TWENTY_TWO_FAMILIES
    codes = np.array(sorted(aggregated), dtype=np.int64)
    code_weights = np.array([aggregated[int(code)] for code in codes], dtype=np.int64)
    assert int(np.sum(code_weights)) == EXPECTED_HEIGHT_TWENTY_TWO_FAMILIES
    return codes, code_weights


def _combine_source_residues(
    p10626: np.ndarray[Any, Any],
    p16: np.ndarray[Any, Any],
    p9: np.ndarray[Any, Any],
) -> np.ndarray[Any, Any]:
    assert bool(np.all((p16 - p10626) % 2 == 0))
    step16 = ((p16 - p10626) // 2) % 8
    p85008 = p10626 + 10_626 * step16
    assert bool(np.all((p9 - p85008) % 3 == 0))
    step9 = ((p9 - p85008) // 3) % 3
    return p85008 + 85_008 * step9


def complete_height_twenty_three_split() -> dict[str, Any]:
    codes, weights = _height_twenty_two_keys()
    (
        t_base,
        p462,
        offset23,
        step23,
        offset16,
        step16,
        offset9,
        step9,
    ) = _decode_height_twenty_two_keys(codes)
    p23_table = _p_table(23)
    p16_table = _p_table(16)
    p9_table = _p_table(9)
    inverse_462_mod_23 = pow(462, -1, 23)
    mode_counts: Counter[tuple[int, int, int]] = Counter()
    z24_counts: Counter[int] = Counter()
    multiplier_residue_counts: Counter[int] = Counter()
    height_twenty_three_inputs = 0

    for lift23 in range(23):
        coordinate23 = (offset23 + step23 * lift23) % 23
        p23 = p23_table[t_base, coordinate23]
        p10626 = p462 + 462 * (
            ((p23 - p462) * inverse_462_mod_23) % 23
        )
        multiplier20 = 380 * p10626 * p10626 + 18 * p10626 + 1
        r506 = ((multiplier20 - 1) // 21) % 506
        assert bool(np.all(r506 % 22 == 0))
        s23 = (r506 // 22) % 23
        q23 = (9240 * s23 * s23 + 19 * s23) % 23
        multiplier22_mod23 = (462 * q23 * q23 + 20 * q23 + 1) % 23
        live = multiplier22_mod23 == 1
        height_twenty_three_inputs += int(np.sum(weights[live]))
        if not bool(np.any(live)):
            continue

        live_weights = weights[live]
        p10626_live = p10626[live]
        for lift24 in range(24):
            coordinate16 = (
                offset16[live]
                + step16[live] * lift23
                - step16[live] * lift24
            ) % 16
            coordinate9 = (
                offset9[live]
                + step9[live] * lift23
                - step9[live] * lift24
            ) % 9
            p16 = p16_table[t_base[live], coordinate16]
            p9 = p9_table[t_base[live], coordinate9]
            p255024 = _combine_source_residues(p10626_live, p16, p9)
            multiplier20_full = (
                380 * p255024 * p255024 + 18 * p255024 + 1
            ) % 255_024
            assert bool(np.all((multiplier20_full - 1) % 21 == 0))
            r12144 = ((multiplier20_full - 1) // 21) % 12_144
            multiplier21 = (420 * r12144 * r12144 + 19 * r12144 + 1) % 12_144
            assert bool(np.all((multiplier21 - 1) % 22 == 0))
            q552 = ((multiplier21 - 1) // 22) % 552
            multiplier22 = (462 * q552 * q552 + 20 * q552 + 1) % 552
            assert bool(np.all(multiplier22 % 23 == 1))
            z24 = ((multiplier22 - 1) // 23) % 24
            multiplier23 = (506 * z24 * z24 + 21 * z24 + 1) % 24
            unique_z, inverse_z = np.unique(z24, return_inverse=True)
            totals_z = np.bincount(inverse_z, weights=live_weights).astype(np.int64)
            for residue, count in zip(unique_z, totals_z, strict=True):
                z24_counts[int(residue)] += int(count)
            unique, inverse = np.unique(multiplier23, return_inverse=True)
            totals = np.bincount(inverse, weights=live_weights).astype(np.int64)
            for residue, count in zip(unique, totals, strict=True):
                signature = negative_unit_successor_signature(23, int(residue))
                mode_counts[signature] += int(count)
                multiplier_residue_counts[int(residue)] += int(count)

    assert height_twenty_three_inputs == EXPECTED_HEIGHT_TWENTY_THREE_INPUTS
    assert sum(mode_counts.values()) == EXPECTED_REFINED_CLASSES
    assert int(codes.size) == EXPECTED_HEIGHT_TWENTY_TWO_KEYS
    assert z24_counts == EXPECTED_Z24_COUNTS
    assert multiplier_residue_counts == EXPECTED_MULTIPLIER_COUNTS
    assert mode_counts == EXPECTED_MODE_COUNTS
    return {
        "height_twenty_two_weighted_key_count": int(codes.size),
        "height_twenty_three_input_count": height_twenty_three_inputs,
        "logical_refined_class_count": EXPECTED_REFINED_CLASSES,
        "divided_height_twenty_two_quotient_counts_mod_24": {
            str(key): value for key, value in sorted(z24_counts.items())
        },
        "multiplier_residue_counts_mod_24": {
            str(key): value for key, value in sorted(multiplier_residue_counts.items())
        },
        "successor_mode_counts": {
            f"payment={key[0]},height={key[1]},error={key[2]}": value
            for key, value in sorted(mode_counts.items())
        },
    }


def symbolic_height_twenty_three_modes() -> dict[str, Any]:
    modes: dict[tuple[int, int, int], list[int]] = {}
    for z in range(24):
        multiplier = 506 * z * z + 21 * z + 1
        signature = negative_unit_successor_signature(23, multiplier)
        modes.setdefault(signature, []).append(z)
    assert sum(map(len, modes.values())) == 24
    assert generalized_crt_pair(0, 10_626, 0, 16)[1] == 85_008
    assert generalized_crt_pair(0, 85_008, 0, 9)[1] == 255_024
    return {
        "height_twenty_three_multiplier": "506*z^2+21*z+1",
        "source_digits_by_successor_mode": {
            f"payment={key[0]},height={key[1]},error={key[2]}": value
            for key, value in sorted(modes.items())
        },
        "composite_crt_modulus": 255_024,
        "lean_declarations": [
            "ErdosProblems.Erdos243.heightTwentyThree_actualMultiplierOneIdentity",
            "ErdosProblems.Erdos243.heightTwentyThree_negativeSurvivorIdentity",
        ],
    }


def build_receipt() -> dict[str, Any]:
    height_twenty_two = json.loads(
        (REPO_ROOT / HEIGHT_TWENTY_TWO_RECEIPT_REF).read_text(encoding="utf-8")
    )
    assert height_twenty_two["status"] == "verified_exact_height_twenty_two_centered_split"
    split = complete_height_twenty_three_split()
    modes = symbolic_height_twenty_three_modes()
    zero = 895_806_693_072 * 24
    positive = 226_561_478_022 * 24
    negative = EXPECTED_REFINED_CLASSES * 3
    assert (zero, positive, negative) == (
        21_499_360_633_728,
        5_437_475_472_528,
        48_477_448_944,
    )
    assert zero + positive + negative == COMMON_GLOBAL_MODULUS
    contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Under a_(n+1)/a_n^2 -> 1 and rational reciprocal sum, force "
            "eventual Sylvester recurrence."
        ),
        claim_ceiling=(
            "Exact elimination of all five nontrivial generic height-23 modes "
            "on 16159149648 source refinements; every actual class has divided "
            "quotient zero and multiplier one modulo 24, reaches height 24 with "
            "error -1, and unrestricted #243 remains open."
        ),
        hypothesis_id="height_twenty_three_source_realizes_nontrivial_composite_mode",
        hypothesis_statement=(
            "Some actual height-23 source class realizes payment 3, 4, 8, 12, "
            "or 24 rather than the payment-one negative continuation."
        ),
        probe_id="weighted_affine_key_composite_crt_height23_split",
        probe_question=(
            "Which of the six generic factor-24 successor modes occur on the "
            "complete corrected height-23 source?"
        ),
        computation=(
            "Compress 506880 source families to 6699 joint affine keys, aggregate "
            "570 height-22 state keys, reconstruct the source parameter modulo "
            "255024 by generalized CRT, and classify every 24-adic lift exactly."
        ),
        falsifier=(
            "A nonzero exact source count in any mode other than payment one, "
            "height 24, centered error -1."
        ),
        stop_condition=(
            "Stop after the complete factor-24 source image is classified; do not "
            "horizon-audit the height-24 continuation."
        ),
        survival_consequence=(
            "Any nontrivial mode would either force a cofinal return, switch sign, "
            "or split negative support across a smaller primitive height."
        ),
        falsification_consequence=(
            "All 16159149648 lifts have z=0 and multiplier 1 modulo 24, eliminating "
            "full payment, positive switching, and payments 3, 4, and 12 on the "
            "actual source while isolating one rigid height-24 negative mode."
        ),
        consumer_ref=LEAN_REF,
        consumer_declarations=modes["lean_declarations"],
        analysis_refs=[NOTE_REF, PACKET_REF, HEIGHT_TWENTY_TWO_RECEIPT_REF],
        source_refs=[
            SCRIPT_REF,
            HEIGHT_TWENTY_TWO_REF,
            HEIGHT_TWENTY_TWO_RECEIPT_REF,
            RESIDUE_CYLINDER_REF,
            LEAN_REF,
        ],
        result_status="exact_one_way_result",
        result_summary=(
            "The actual height-23 source image is the singleton z=0 and multiplier "
            "1 modulo 24; every one of 16159149648 lifts reaches height 24 with "
            "centered error -1."
        ),
        progress_class="mechanism_eliminated",
        decision_basis=(
            "Complete weighted-key enumeration with exact overlapping-modulus CRT "
            "eliminates five structurally distinct generic successor modes."
        ),
        next_analytic_target=(
            "Restrict the next probe to the singleton height-24 payment-one mode and "
            "test the factor-25 full-payment-five/twenty-five mechanisms."
        ),
        resource_bounds={
            "source_family_count": EXPECTED_SOURCE_FAMILIES,
            "joint_affine_key_count": EXPECTED_AFFINE_KEYS,
            "height_twenty_two_weighted_key_count": EXPECTED_HEIGHT_TWENTY_TWO_KEYS,
            "logical_classified_lifts": EXPECTED_REFINED_CLASSES,
            "composite_crt_modulus": 255_024,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos243-height23-composite-split-receipt/1",
        "status": "verified_exact_height_twenty_three_singleton_mode",
        "complete_height_twenty_three_split": split,
        "symbolic_height_twenty_three_modes": modes,
        "cumulative_source_class_partition": {
            "common_modulus": COMMON_GLOBAL_MODULUS,
            "zero_centered_class_count": zero,
            "positive_centered_class_count": positive,
            "continuing_negative_candidate_class_count": negative,
            "height_twenty_four_negative_candidate_count": negative,
            "exact_partition": (
                "21499360633728 zero + 5437475472528 positive + "
                "48477448944 negative = 26985313555200"
            ),
        },
        "experiment_contract": contract,
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [
                SCRIPT_REF,
                HEIGHT_TWENTY_TWO_REF,
                HEIGHT_TWENTY_TWO_RECEIPT_REF,
                RESIDUE_CYLINDER_REF,
                LEAN_REF,
                NOTE_REF,
                PACKET_REF,
            ]
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--explore", action="store_true")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.explore:
        split = complete_height_twenty_three_split()
        modes = symbolic_height_twenty_three_modes()
        print(json.dumps({"split": split, "symbolic_modes": modes}, indent=2, sort_keys=True))
        return 0
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
