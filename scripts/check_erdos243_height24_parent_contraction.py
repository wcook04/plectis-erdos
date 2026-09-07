#!/usr/bin/env python3
"""Classify factor-25 outcomes parent-by-parent on the exact #243 source.

The aggregate height-24 census removes about one fifth of negative support,
but an analytic contraction route needs to know whether that loss is spread
across every actual parent or concentrated in a few fibers.  This checker
reuses the source-digest-bound weighted affine cache and records, for each
height-24 parent, how its complete set of 25 refinements divides among
cofinal return, positive switching, and continuing negative support.
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

from check_erdos243_height21_payment_split import _p_table  # noqa: E402
from check_erdos243_height23_composite_split import (  # noqa: E402
    _combine_source_residues,
)
from check_erdos243_height24_mod25_split import (  # noqa: E402
    EXPECTED_AFFINE_KEYS,
    EXPECTED_HEIGHT_TWENTY_FOUR_INPUTS,
    EXPECTED_HEIGHT_TWENTY_THREE_INPUTS,
    EXPECTED_HEIGHT_TWENTY_TWO_KEYS,
    EXPECTED_MODE_COUNTS,
    EXPECTED_REFINED_CLASSES,
    _decode,
    _height_twenty_two_keys_mod_25,
)


SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_height24_parent_contraction.py"
)
HEIGHT_TWENTY_FOUR_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_height24_mod25_split.py"
)
HEIGHT_TWENTY_FOUR_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos243_height24_mod25_split_receipt.json"
)
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
    "erdos243_height24_parent_contraction_receipt.json"
)
EXPECTED_PARENT_PROFILES = {
    (0, 0, 25): 10_282_880_304,
    (10, 4, 11): 5_876_269_344,
}
EXPECTED_INERT_NEGATIVE_CHILD_COUNT = 257_072_007_600


def _merge_parent_profiles(
    target: Counter[tuple[int, int, int]],
    cofinal: np.ndarray[Any, Any],
    positive: np.ndarray[Any, Any],
    negative: np.ndarray[Any, Any],
    weights: np.ndarray[Any, Any],
) -> None:
    profile_codes = cofinal * 26 * 26 + positive * 26 + negative
    order = np.argsort(profile_codes)
    codes = profile_codes[order]
    ordered_weights = weights[order]
    starts = np.concatenate([np.array([0]), np.flatnonzero(np.diff(codes)) + 1])
    totals = np.add.reduceat(ordered_weights, starts)
    for code, weight in zip(codes[starts], totals, strict=True):
        value = int(code)
        cofinal_count, remainder = divmod(value, 26 * 26)
        positive_count, negative_count = divmod(remainder, 26)
        target[(cofinal_count, positive_count, negative_count)] += int(weight)


def _merge_profile_slopes(
    target: Counter[tuple[int, int, int, int]],
    cofinal: np.ndarray[Any, Any],
    positive: np.ndarray[Any, Any],
    negative: np.ndarray[Any, Any],
    slopes: np.ndarray[Any, Any],
    weights: np.ndarray[Any, Any],
) -> None:
    profile_codes = cofinal * 26 * 26 + positive * 26 + negative
    joint_codes = profile_codes * 25 + slopes
    order = np.argsort(joint_codes)
    codes = joint_codes[order]
    ordered_weights = weights[order]
    starts = np.concatenate([np.array([0]), np.flatnonzero(np.diff(codes)) + 1])
    totals = np.add.reduceat(ordered_weights, starts)
    for code, weight in zip(codes[starts], totals, strict=True):
        profile_code, slope = divmod(int(code), 25)
        cofinal_count, remainder = divmod(profile_code, 26 * 26)
        positive_count, negative_count = divmod(remainder, 26)
        target[(cofinal_count, positive_count, negative_count, slope)] += int(weight)


def _merge_profile_source_digits(
    target: Counter[tuple[int, int, int, int, int]],
    cofinal: np.ndarray[Any, Any],
    positive: np.ndarray[Any, Any],
    negative: np.ndarray[Any, Any],
    source_digits: np.ndarray[Any, Any],
    slopes: np.ndarray[Any, Any],
    weights: np.ndarray[Any, Any],
) -> None:
    profile_codes = cofinal * 26 * 26 + positive * 26 + negative
    joint_codes = (profile_codes * 10 + source_digits) * 25 + slopes
    order = np.argsort(joint_codes)
    codes = joint_codes[order]
    ordered_weights = weights[order]
    starts = np.concatenate([np.array([0]), np.flatnonzero(np.diff(codes)) + 1])
    totals = np.add.reduceat(ordered_weights, starts)
    for code, weight in zip(codes[starts], totals, strict=True):
        profile_and_digit, slope = divmod(int(code), 25)
        profile_code, source_digit = divmod(profile_and_digit, 10)
        cofinal_count, remainder = divmod(profile_code, 26 * 26)
        positive_count, negative_count = divmod(remainder, 26)
        target[(cofinal_count, positive_count, negative_count, source_digit, slope)] += int(weight)


def _merge_negative_errors_by_source_digit(
    target: Counter[tuple[int, int]],
    source_digits: np.ndarray[Any, Any],
    errors: np.ndarray[Any, Any],
    negative_mask: np.ndarray[Any, Any],
    weights: np.ndarray[Any, Any],
) -> None:
    digits = source_digits[negative_mask]
    negative_errors = errors[negative_mask]
    negative_weights = weights[negative_mask]
    joint_codes = digits * 51 + (negative_errors + 25)
    order = np.argsort(joint_codes)
    codes = joint_codes[order]
    ordered_weights = negative_weights[order]
    starts = np.concatenate([np.array([0]), np.flatnonzero(np.diff(codes)) + 1])
    totals = np.add.reduceat(ordered_weights, starts)
    for code, weight in zip(codes[starts], totals, strict=True):
        source_digit, shifted_error = divmod(int(code), 51)
        target[(source_digit, shifted_error - 25)] += int(weight)


def complete_parent_contraction_census() -> dict[str, Any]:
    codes, weights, affine_key_count, cache_action = _height_twenty_two_keys_mod_25()
    assert affine_key_count == EXPECTED_AFFINE_KEYS
    assert int(codes.size) == EXPECTED_HEIGHT_TWENTY_TWO_KEYS
    (
        t_base,
        p462,
        offset23,
        step23,
        offset16,
        step16,
        offset9,
        step9,
        offset25,
        slope25,
    ) = _decode(codes)
    p23_table = _p_table(23)
    p16_table = _p_table(16)
    p9_table = _p_table(9)
    p25_table = _p_table(25)
    inverse_462_mod_23 = pow(462, -1, 23)
    inverse_255024_mod_25 = pow(255_024, -1, 25)
    parent_profiles: Counter[tuple[int, int, int]] = Counter()
    profile_slopes: Counter[tuple[int, int, int, int]] = Counter()
    profile_source_digits: Counter[tuple[int, int, int, int, int]] = Counter()
    negative_errors_by_source_digit: Counter[tuple[int, int]] = Counter()
    height_twenty_three_inputs = 0
    parent_count = 0

    for lift23 in range(23):
        coordinate23 = (offset23 + step23 * lift23) % 23
        p23 = p23_table[t_base, coordinate23]
        p10626 = p462 + 462 * (((p23 - p462) * inverse_462_mod_23) % 23)
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
                offset16[live] + step16[live] * lift23 - step16[live] * lift24
            ) % 16
            coordinate9 = (
                offset9[live] + step9[live] * lift23 - step9[live] * lift24
            ) % 9
            p16 = p16_table[t_base[live], coordinate16]
            p9 = p9_table[t_base[live], coordinate9]
            p255024 = _combine_source_residues(p10626_live, p16, p9)
            cofinal = np.zeros(live_weights.shape, dtype=np.int64)
            positive = np.zeros(live_weights.shape, dtype=np.int64)
            negative = np.zeros(live_weights.shape, dtype=np.int64)
            for lift25 in range(25):
                total_higher_lift = 462 * lift23 + 10_626 * lift24 + 255_024 * lift25
                coordinate25 = (
                    offset25[live] + slope25[live] * total_higher_lift
                ) % 25
                p25 = p25_table[t_base[live], coordinate25]
                p6375600 = p255024 + 255_024 * (
                    ((p25 - p255024) * inverse_255024_mod_25) % 25
                )
                multiplier20_full = (
                    380 * p6375600 * p6375600 + 18 * p6375600 + 1
                ) % 6_375_600
                assert bool(np.all((multiplier20_full - 1) % 21 == 0))
                r303600 = ((multiplier20_full - 1) // 21) % 303_600
                multiplier21 = (
                    420 * r303600 * r303600 + 19 * r303600 + 1
                ) % 303_600
                assert bool(np.all((multiplier21 - 1) % 22 == 0))
                q13800 = ((multiplier21 - 1) // 22) % 13_800
                multiplier22 = (
                    462 * q13800 * q13800 + 20 * q13800 + 1
                ) % 13_800
                assert bool(np.all((multiplier22 - 1) % 23 == 0))
                z600 = ((multiplier22 - 1) // 23) % 600
                assert bool(np.all(z600 % 24 == 0))
                multiplier23 = (506 * z600 * z600 + 21 * z600 + 1) % 600
                assert bool(np.all((multiplier23 - 1) % 24 == 0))
                c25 = ((multiplier23 - 1) // 24) % 25
                multiplier24 = (552 * c25 * c25 + 22 * c25 + 1) % 25
                full = multiplier24 % 5 == 0
                errors = (-(multiplier24 * multiplier24)) % 25
                errors = errors.copy()
                errors[2 * errors >= 25] -= 25
                cofinal += full
                positive += (~full) & (errors > 0)
                negative += (~full) & (errors < 0)
                _merge_negative_errors_by_source_digit(
                    negative_errors_by_source_digit,
                    t_base[live],
                    errors,
                    (~full) & (errors < 0),
                    live_weights,
                )
            assert bool(np.all(cofinal + positive + negative == 25))
            parent_count += int(np.sum(live_weights))
            _merge_parent_profiles(
                parent_profiles, cofinal, positive, negative, live_weights
            )
            _merge_profile_slopes(
                profile_slopes,
                cofinal,
                positive,
                negative,
                slope25[live],
                live_weights,
            )
            _merge_profile_source_digits(
                profile_source_digits,
                cofinal,
                positive,
                negative,
                t_base[live],
                slope25[live],
                live_weights,
            )

    assert height_twenty_three_inputs == EXPECTED_HEIGHT_TWENTY_THREE_INPUTS
    assert parent_count == EXPECTED_HEIGHT_TWENTY_FOUR_INPUTS
    assert sum(parent_profiles.values()) == EXPECTED_HEIGHT_TWENTY_FOUR_INPUTS
    child_cofinal = sum(key[0] * count for key, count in parent_profiles.items())
    child_positive = sum(key[1] * count for key, count in parent_profiles.items())
    child_negative = sum(key[2] * count for key, count in parent_profiles.items())
    assert child_cofinal == EXPECTED_MODE_COUNTS[(25, 1, 0)]
    assert child_positive == (
        EXPECTED_MODE_COUNTS[(1, 25, 4)] + EXPECTED_MODE_COUNTS[(1, 25, 9)]
    )
    assert child_negative == (
        EXPECTED_MODE_COUNTS[(1, 25, -1)]
        + EXPECTED_MODE_COUNTS[(1, 25, -6)]
        + EXPECTED_MODE_COUNTS[(1, 25, -11)]
    )
    assert child_cofinal + child_positive + child_negative == EXPECTED_REFINED_CLASSES
    assert parent_profiles == EXPECTED_PARENT_PROFILES
    inert_source_digits = sorted(
        {
            key[3]
            for key in profile_source_digits
            if key[:3] == (0, 0, 25)
        }
    )
    active_source_digits = sorted(
        {
            key[3]
            for key in profile_source_digits
            if key[:3] == (10, 4, 11)
        }
    )
    assert inert_source_digits == [0]
    assert active_source_digits == [4, 6]
    inert_error_counts = {
        error: count
        for (source_digit, error), count in negative_errors_by_source_digit.items()
        if source_digit == 0
    }
    assert inert_error_counts == {-1: EXPECTED_INERT_NEGATIVE_CHILD_COUNT}
    return {
        "compressed_affine_cache_action": cache_action,
        "height_twenty_four_parent_count": parent_count,
        "children_per_parent": 25,
        "parent_profile_counts": {
            f"cofinal={key[0]},positive={key[1]},negative={key[2]}": value
            for key, value in sorted(parent_profiles.items())
        },
        "parent_profile_counts_by_affine_slope_mod_25": {
            (
                f"cofinal={key[0]},positive={key[1]},negative={key[2]},"
                f"slope={key[3]}"
            ): value
            for key, value in sorted(profile_slopes.items())
        },
        "parent_profile_counts_by_source_digit_and_slope": {
            (
                f"cofinal={key[0]},positive={key[1]},negative={key[2]},"
                f"t={key[3]},slope={key[4]}"
            ): value
            for key, value in sorted(profile_source_digits.items())
        },
        "minimum_negative_children_per_parent": min(key[2] for key in parent_profiles),
        "maximum_negative_children_per_parent": max(key[2] for key in parent_profiles),
        "all_negative_parent_count": sum(
            count for key, count in parent_profiles.items() if key[2] == 25
        ),
        "activation_predicate": {
            "inert_source_digits_mod_10": inert_source_digits,
            "active_source_digits_mod_10": active_source_digits,
            "exact_separation": True,
            "affine_slope_alone_sufficient": False,
        },
        "inert_child_transition_target": {
            "centered_error_image": [-1],
            "negative_child_count": EXPECTED_INERT_NEGATIVE_CHILD_COUNT,
            "next_raw_height_factor": 26,
            "eliminated_raw_height_factors": [31, 36],
        },
        "negative_child_counts_by_source_digit_and_error": {
            f"t={key[0]},error={key[1]}": value
            for key, value in sorted(negative_errors_by_source_digit.items())
        },
        "child_outcome_totals": {
            "cofinal_return": child_cofinal,
            "positive_switch": child_positive,
            "continuing_negative": child_negative,
        },
    }


def build_receipt() -> dict[str, Any]:
    previous = json.loads(
        (REPO_ROOT / HEIGHT_TWENTY_FOUR_RECEIPT_REF).read_text(encoding="utf-8")
    )
    assert previous["status"] == "verified_exact_height_twenty_four_cofinal_opening"
    census = complete_parent_contraction_census()
    inert = EXPECTED_PARENT_PROFILES[(0, 0, 25)]
    active = EXPECTED_PARENT_PROFILES[(10, 4, 11)]
    contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Under a_(n+1)/a_n^2 -> 1 and rational reciprocal sum, force "
            "eventual Sylvester recurrence."
        ),
        claim_ceiling=(
            "Exact parent-local factor-25 classification: 10282880304 actual "
            "parents have 25 negative children, while 5876269344 have the rigid "
            "profile 10 cofinal, 4 positive, 11 negative.  The split is exactly "
            "t=0 mod 10 inert versus t in {4,6} active; unrestricted #243 remains "
            "open.  All 257072007600 inert children have error -1, eliminating "
            "the error-specific raw factors 31 and 36 from the inert frontier."
        ),
        hypothesis_id="uniform_factor25_negative_continuation_contraction",
        hypothesis_statement=(
            "Every actual height-24 parent loses at least one of its 25 children "
            "from negative support, giving a uniform continuation ratio below one."
        ),
        probe_id="exact_weighted_parent_local_factor25_outcome_histogram",
        probe_question=(
            "Is the aggregate factor-25 loss distributed across every actual "
            "parent, or concentrated in a proper subset of affine fibers?"
        ),
        computation=(
            "Reuse the source-current 32490-key affine cache, retain each complete "
            "height-24 parent, and count its 25 children separately as cofinal, "
            "positive, or continuing negative."
        ),
        falsifier=(
            "Any exact parent profile with 25 continuing-negative children."
        ),
        stop_condition=(
            "Stop after the complete weighted parent-profile histogram is exact; "
            "do not extend individual child orbits."
        ),
        survival_consequence=(
            "A maximum of at most 24 negative children would supply a uniform "
            "factor-25 contraction bound on every actual affine fiber."
        ),
        falsification_consequence=(
            "All-negative parents eliminate uniform one-step contraction.  A "
            "binary active/inert split instead makes recurrent activation of inert "
            "fibers the required analytic producer."
        ),
        consumer_ref=LEAN_REF,
        consumer_declarations=[
            "ErdosProblems.Erdos243.heightTwentyFour_fullPayment",
            "ErdosProblems.Erdos243.heightTwentyFour_fullCollapse",
        ],
        analysis_refs=[NOTE_REF, PACKET_REF, HEIGHT_TWENTY_FOUR_RECEIPT_REF],
        source_refs=[SCRIPT_REF, HEIGHT_TWENTY_FOUR_REF, HEIGHT_TWENTY_FOUR_RECEIPT_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "Exactly 10282880304 parents are inert with profile (0,0,25), and "
            "5876269344 are active with profile (10,4,11); source digit t mod 10 "
            "separates them exactly as 0 versus {4,6}; every inert child has "
            "error -1, so only raw factor 26 remains on that branch."
        ),
        progress_class="mechanism_eliminated",
        decision_basis=(
            "The complete exact parent-local histogram contains all-negative "
            "fibers, decisively refuting uniform one-step contraction while opening "
            "a binary activation mechanism."
        ),
        next_analytic_target=(
            "Restrict to the exact t=0 mod 10, error -1 inert subfamily and test "
            "factor 26 using only the new source coordinates modulo 32 and 13; do "
            "not build the eliminated factor-31 or factor-36 branches."
        ),
        resource_bounds={
            "weighted_affine_key_count": EXPECTED_HEIGHT_TWENTY_TWO_KEYS,
            "height_twenty_four_parent_count": EXPECTED_HEIGHT_TWENTY_FOUR_INPUTS,
            "children_per_parent": 25,
            "logical_child_count": EXPECTED_REFINED_CLASSES,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos243-height24-parent-contraction-receipt/1",
        "status": "verified_exact_binary_parent_fiber_split",
        "complete_parent_contraction_census": census,
        "mechanism_decision": {
            "uniform_one_step_contraction": "eliminated",
            "all_negative_parent_count": inert,
            "active_parent_count": active,
            "active_parent_profile": {
                "cofinal_children": 10,
                "positive_children": 4,
                "continuing_negative_children": 11,
            },
            "replacement_route": "bounded_gap_or_positive_density_activation",
            "exact_activation_predicate": {
                "inert_source_digits_mod_10": [0],
                "active_source_digits_mod_10": [4, 6],
                "slope_alone_sufficient": False,
            },
            "inert_child_error_image": [-1],
            "inert_next_raw_height_factor": 26,
            "eliminated_inert_raw_height_factors": [31, 36],
        },
        "experiment_contract": contract,
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [
                SCRIPT_REF,
                HEIGHT_TWENTY_FOUR_REF,
                HEIGHT_TWENTY_FOUR_RECEIPT_REF,
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
        census = complete_parent_contraction_census()
        print(json.dumps(census, indent=2, sort_keys=True))
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
