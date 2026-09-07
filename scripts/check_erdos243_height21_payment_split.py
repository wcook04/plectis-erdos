#!/usr/bin/env python3
"""Certify the #243 height-21 payment split and payment-eleven return.

The height-20 certificate leaves 8211456 payment-one cylinders modulo
740703600.  Two affine evaluations recover the next quotient coordinate on
all twenty-two lifts without evaluating the degree-1024 source polynomial on
all 180652032 refined classes.  The actual height-21 parameter image is only
``{0, 6}`` modulo 22, hence the payment image is only ``{1, 11}``.

The payment-eleven branch lands at height two with centered error -1.  A
further three-lift affine refinement is unexpectedly rigid: every actual class
pays one, not the full factor three, and reaches height three with centered
error -1.  The same residue forces an even height-three multiplier, hence full
payment four and a cofinal return.  No orbit horizon is used.
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
    affine_lift_coordinates_mod,
)

from check_erdos243_forced_excursion_split import (  # noqa: E402
    source_quotient_polynomials,
)
from check_erdos243_height20_payment_seven_cascade import (  # noqa: E402
    HEIGHT_EIGHTEEN_MODULUS,
    HEIGHT_EIGHTEEN_RECEIPT_REF,
    HEIGHT_NINETEEN_MODULUS,
    PAYMENT_ONE_T_CLASSES,
    Y_POLYNOMIAL_EXACT,
    _base_classes_mod_3527160,
    _integer_polynomial_value,
    _t_values,
)


SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_height21_payment_split.py"
)
HEIGHT_TWENTY_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_height20_payment_seven_cascade.py"
)
HEIGHT_TWENTY_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos243_height20_payment_seven_cascade_receipt.json"
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
    "erdos243_height21_payment_split_receipt.json"
)

HEIGHT_TWENTY_MODULUS = HEIGHT_NINETEEN_MODULUS * 21
HEIGHT_TWENTY_ONE_MODULUS = HEIGHT_TWENTY_MODULUS * 22
COMMON_MODULUS = HEIGHT_TWENTY_ONE_MODULUS * 3
EXPECTED_HEIGHT_TWENTY_SURVIVORS = 8_211_456
EXPECTED_HEIGHT_TWENTY_ONE_COUNTS = {1: 120_931_560, 11: 59_720_472}
EXPECTED_PAYMENT_ELEVEN_REFINED_COUNT = 179_161_416


def _p_table(modulus: int) -> np.ndarray[Any, np.dtype[np.int64]]:
    """Tabulate the height-19 quotient parameter from ``t mod 10*modulus``."""

    table = np.zeros((10, modulus), dtype=np.int64)
    for t_base in PAYMENT_ONE_T_CLASSES:
        for higher_coordinate in range(modulus):
            t = t_base + 10 * higher_coordinate
            e = 19 * t
            y = _integer_polynomial_value(Y_POLYNOMIAL_EXACT, e) // 19
            n = 10336 * y * y + 5 * y
            r = 5814 * n * n + 16 * n
            height_nineteen_multiplier = 342 * r * r + 17 * r + 1
            assert (height_nineteen_multiplier - 1) % 20 == 0
            table[t_base, higher_coordinate] = (
                (height_nineteen_multiplier - 1) // 20
            ) % modulus
    return table


def _count_map(values: np.ndarray[Any, np.dtype[np.int64]]) -> dict[int, int]:
    unique, counts = np.unique(values, return_counts=True)
    return {
        int(key): int(value)
        for key, value in zip(unique, counts, strict=True)
    }


def _merge_counts(target: dict[int, int], values: np.ndarray[Any, np.dtype[np.int64]]) -> None:
    for residue, count in _count_map(values).items():
        target[residue] = target.get(residue, 0) + count


def _source_cylinder() -> tuple[
    list[int],
    np.ndarray[Any, np.dtype[np.int64]],
    np.ndarray[Any, np.dtype[np.int64]],
]:
    height_eighteen = json.loads(
        (REPO_ROOT / HEIGHT_EIGHTEEN_RECEIPT_REF).read_text(encoding="utf-8")
    )
    base_classes = _base_classes_mod_3527160(height_eighteen)
    _, q10 = source_quotient_polynomials()
    parameters = (
        base_classes[:, None]
        + HEIGHT_EIGHTEEN_MODULUS * np.arange(10, dtype=np.int64)[None, :]
    ).reshape(-1)
    t_base_all = _t_values(q10, parameters, 1)
    keep = np.isin(t_base_all, list(PAYMENT_ONE_T_CLASSES))
    source_classes = parameters[keep]
    t_base = t_base_all[keep]
    assert source_classes.size == 506_880
    return q10, source_classes, t_base


def _affine_coordinates(
    q10: list[int],
    source_classes: np.ndarray[Any, np.dtype[np.int64]],
    t_base: np.ndarray[Any, np.dtype[np.int64]],
    modulus: int,
) -> tuple[
    np.ndarray[Any, np.dtype[np.int64]],
    np.ndarray[Any, np.dtype[np.int64]],
]:
    stacked = np.concatenate(
        [source_classes, source_classes + HEIGHT_NINETEEN_MODULUS]
    )
    lifted_t = _t_values(q10, stacked, modulus)
    count = source_classes.size
    at_zero = ((lifted_t[:count] - t_base) // 10) % modulus
    at_one = ((lifted_t[count:] - t_base) // 10) % modulus
    return affine_lift_coordinates_mod(at_zero, at_one, modulus=modulus)


def complete_height_twenty_one_split() -> dict[str, Any]:
    q10, source_classes, t_base = _source_cylinder()
    u21, slope21 = _affine_coordinates(q10, source_classes, t_base, 21)
    u22, slope22 = _affine_coordinates(q10, source_classes, t_base, 22)
    u9, slope9 = _affine_coordinates(q10, source_classes, t_base, 9)
    p21_table = _p_table(21)
    p22_table = _p_table(22)
    p9_table = _p_table(9)
    inverse_21_mod_22 = pow(21, -1, 22)
    inverse_7_mod_9 = pow(7, -1, 9)

    payment_counts = {1: 0, 11: 0}
    r_mod_22_counts: dict[int, int] = {}
    multiplier_mod_22_counts: dict[int, int] = {}
    payment_eleven_refined_count = 0
    height_two_full_payment_three = 0
    height_two_payment_one = 0
    height_three_full_payment_four = 0
    r_mod_66_counts: dict[int, int] = {}
    w_mod_3_counts: dict[int, int] = {}
    height_two_multiplier_mod_3_counts: dict[int, int] = {}
    height_twenty_survivors = 0

    for lift21 in range(21):
        coordinate21 = (u21 + slope21 * lift21) % 21
        p21 = p21_table[t_base, coordinate21]
        survives_height_twenty = p21 != 18
        height_twenty_survivors += int(np.sum(survives_height_twenty))
        p7 = p21 % 7

        for lift22 in range(22):
            total_lift = lift21 + 21 * lift22
            coordinate22 = (u22 + slope22 * total_lift) % 22
            p22 = p22_table[t_base, coordinate22]
            p462 = p21 + 21 * (
                ((p22 - p21) * inverse_21_mod_22) % 22
            )
            k = 380 * p462 * p462 + 18 * p462 + 1
            assert bool(np.all((k[survives_height_twenty] - 1) % 21 == 0))
            r22 = ((k - 1) // 21) % 22
            multiplier22 = (420 * r22 * r22 + 19 * r22 + 1) % 22
            payments = np.gcd(multiplier22 * multiplier22, 22)
            live_r22 = r22[survives_height_twenty]
            live_multiplier22 = multiplier22[survives_height_twenty]
            _merge_counts(r_mod_22_counts, live_r22)
            _merge_counts(multiplier_mod_22_counts, live_multiplier22)
            for payment in payment_counts:
                payment_counts[payment] += int(
                    np.sum(survives_height_twenty & (payments == payment))
                )

            payment_eleven_mask = survives_height_twenty & (payments == 11)
            payment_eleven_count = int(np.sum(payment_eleven_mask))
            if payment_eleven_count == 0:
                continue
            t_base_live = t_base[payment_eleven_mask]
            p7_live = p7[payment_eleven_mask]
            u9_live = u9[payment_eleven_mask]
            slope9_live = slope9[payment_eleven_mask]
            r22_live = r22[payment_eleven_mask]
            for lift3 in range(3):
                total_refined_lift = total_lift + 21 * 22 * lift3
                coordinate9 = (u9_live + slope9_live * total_refined_lift) % 9
                p9 = p9_table[t_base_live, coordinate9]
                p63 = p7_live + 7 * (
                    ((p9 - p7_live) * inverse_7_mod_9) % 9
                )
                k63 = 380 * p63 * p63 + 18 * p63 + 1
                assert bool(np.all((k63 - 1) % 21 == 0))
                r3 = ((k63 - 1) // 21) % 3
                r66 = r22_live + 22 * ((r3 - r22_live) % 3)
                multiplier66 = 420 * r66 * r66 + 19 * r66 + 1
                assert bool(np.all(multiplier66 % 11 == 0))
                w = multiplier66 // 11
                height_two_multiplier = (w * (231 * w - 22) + 1) // 2
                height_two_payment = np.gcd(
                    height_two_multiplier * height_two_multiplier, 3
                )
                payment_eleven_refined_count += payment_eleven_count
                height_two_full_payment_three += int(
                    np.sum(height_two_payment == 3)
                )
                height_two_payment_one_mask = height_two_payment == 1
                height_two_payment_one += int(np.sum(height_two_payment_one_mask))
                payment_one_multiplier = height_two_multiplier[
                    height_two_payment_one_mask
                ]
                assert bool(
                    np.all(payment_one_multiplier % 3 == 1)
                )
                c = (payment_one_multiplier - 1) // 3
                height_three_multiplier = 6 * c * c + c
                # Squaring this representative can exceed int64, but modulo
                # four its square has gcd four exactly when the multiplier is
                # even.  Classify by parity before any square is materialised.
                height_three_payment = np.where(
                    height_three_multiplier % 2 == 0, 4, 1
                )
                height_three_full_payment_four += int(
                    np.sum(height_three_payment == 4)
                )
                _merge_counts(r_mod_66_counts, r66)
                _merge_counts(w_mod_3_counts, w % 3)
                _merge_counts(
                    height_two_multiplier_mod_3_counts,
                    height_two_multiplier % 3,
                )

    assert height_twenty_survivors == EXPECTED_HEIGHT_TWENTY_SURVIVORS
    assert payment_counts == EXPECTED_HEIGHT_TWENTY_ONE_COUNTS
    assert r_mod_22_counts == {0: 120_931_560, 6: 59_720_472}
    assert multiplier_mod_22_counts == {1: 120_931_560, 11: 59_720_472}
    assert payment_eleven_refined_count == payment_counts[11] * 3
    assert payment_eleven_refined_count == EXPECTED_PAYMENT_ELEVEN_REFINED_COUNT
    assert height_two_full_payment_three == 0
    assert height_two_payment_one == EXPECTED_PAYMENT_ELEVEN_REFINED_COUNT
    assert height_three_full_payment_four == EXPECTED_PAYMENT_ELEVEN_REFINED_COUNT
    assert r_mod_66_counts == {6: EXPECTED_PAYMENT_ELEVEN_REFINED_COUNT}
    assert w_mod_3_counts == {2: EXPECTED_PAYMENT_ELEVEN_REFINED_COUNT}
    assert height_two_multiplier_mod_3_counts == {
        1: EXPECTED_PAYMENT_ELEVEN_REFINED_COUNT
    }
    assert (
        height_two_full_payment_three + height_two_payment_one
        == payment_eleven_refined_count
    )
    return {
        "input_height_twenty_class_count_mod_740703600": height_twenty_survivors,
        "height_twenty_one_modulus": HEIGHT_TWENTY_ONE_MODULUS,
        "complete_height_twenty_one_class_count": height_twenty_survivors * 22,
        "affine_slope_counts_mod_21": {
            str(key): value for key, value in sorted(_count_map(slope21).items())
        },
        "affine_slope_counts_mod_22": {
            str(key): value for key, value in sorted(_count_map(slope22).items())
        },
        "affine_slope_counts_mod_9": {
            str(key): value for key, value in sorted(_count_map(slope9).items())
        },
        "height_twenty_one_parameter_counts_mod_22": {
            str(key): value for key, value in sorted(r_mod_22_counts.items())
        },
        "height_twenty_one_multiplier_counts_mod_22": {
            str(key): value
            for key, value in sorted(multiplier_mod_22_counts.items())
        },
        "height_twenty_one_payment_counts": {
            str(key): value for key, value in sorted(payment_counts.items())
        },
        "payment_eleven_three_lift_refinement": {
            "refined_class_count": payment_eleven_refined_count,
            "r_counts_mod_66": {
                str(key): value for key, value in sorted(r_mod_66_counts.items())
            },
            "quotient_w_counts_mod_3": {
                str(key): value for key, value in sorted(w_mod_3_counts.items())
            },
            "height_two_multiplier_counts_mod_3": {
                str(key): value
                for key, value in sorted(height_two_multiplier_mod_3_counts.items())
            },
            "full_payment_three_cofinal_return": height_two_full_payment_three,
            "payment_one_to_height_three": height_two_payment_one,
            "height_three_full_payment_four_cofinal_return": (
                height_three_full_payment_four
            ),
        },
        "affine_compression": {
            "classified_height_twenty_one_classes": height_twenty_survivors * 22,
            "classified_payment_eleven_refined_classes": payment_eleven_refined_count,
            "degree_1024_evaluations_per_source_class": 7,
            "shared_primitive": (
                "system.lib.formal_math_residue_cylinder."
                "affine_lift_coordinates_mod"
            ),
            "exactness": (
                "bounded numpy.int64 modular arithmetic; height-three payment "
                "uses the equivalent parity test before an unsafe square"
            ),
        },
    }


def symbolic_payment_eleven_transition() -> dict[str, Any]:
    for lift in range(60):
        a = 3 * lift
        r = 22 * a + 6
        multiplier = 420 * r * r + 19 * r + 1
        assert math.gcd(multiplier * multiplier, 22) == 11
        w = multiplier // 11
        b = 9240 * a * a + 5059 * a + 692
        assert w == 2 * b + 1
        reduced = w * (231 * w - 22)
        height_two_multiplier = 462 * b * b + 440 * b + 105
        assert reduced == 2 * height_two_multiplier - 1
        payment = math.gcd(height_two_multiplier * height_two_multiplier, 3)
        assert payment == 1 and height_two_multiplier % 6 == 1
        c = (height_two_multiplier - 1) // 3
        assert c % 2 == 0
        height_three_value = height_two_multiplier * (
            2 * height_two_multiplier - 3
        )
        assert height_three_value == 3 * (6 * c * c + c) - 1
        height_three_multiplier = 6 * c * c + c
        assert height_three_multiplier % 2 == 0
        assert math.gcd(height_three_multiplier * height_three_multiplier, 4) == 4
    return {
        "input": "height-21 parameter r=22*a+6 and payment eleven",
        "universal_transition": "(21,-1) --11--> (2,-1)",
        "actual_source_digit_mod_3": 0,
        "actual_cascade": "(21,-1) --11--> (2,-1) --1--> (3,-1) --4--> (1,0 forever)",
        "complete_symbolic_lifts": 60,
        "lean_declarations": [
            "ErdosProblems.Erdos243.heightTwentyOne_paymentOne",
            "ErdosProblems.Erdos243.heightTwentyOnePaymentEleven_heightTwoIdentity",
            "ErdosProblems.Erdos243.heightTwentyOnePaymentEleven_heightThreeIdentity",
            "ErdosProblems.Erdos243.heightTwentyOnePaymentEleven_heightThreeMultiplierEven",
            "ErdosProblems.Erdos243.heightTwentyOnePaymentEleven_fullPaymentFour",
            "ErdosProblems.Erdos243.heightTwentyOnePaymentEleven_finalCollapse",
        ],
    }


def build_receipt() -> dict[str, Any]:
    height_twenty = json.loads(
        (REPO_ROOT / HEIGHT_TWENTY_RECEIPT_REF).read_text(encoding="utf-8")
    )
    assert height_twenty["status"] == "verified_exact_payment_seven_mode_elimination"
    split = complete_height_twenty_one_split()
    transition = symbolic_payment_eleven_transition()
    refinement = split["payment_eleven_three_lift_refinement"]
    assert refinement["full_payment_three_cofinal_return"] == 0
    new_zero = refinement["height_three_full_payment_four_cofinal_return"]
    surviving_height_three = 0
    surviving_height_twenty_two = (
        split["height_twenty_one_payment_counts"]["1"] * 3
    )
    zero = 583_408_395 * 66 + new_zero
    positive = 149_083_749 * 66
    negative = surviving_height_three + surviving_height_twenty_two
    assert zero + positive + negative == COMMON_MODULUS

    contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Under a_(n+1)/a_n^2 -> 1 and rational reciprocal sum, force "
            "eventual Sylvester recurrence."
        ),
        claim_ceiling=(
            "Exact height-21 payment image {1,11} and cofinal return of all "
            "179161416 three-lift refinements of the payment-eleven classes through "
            "the forced 21->2->3->1 cascade; the height-22 branch and unrestricted "
            "#243 remain open."
        ),
        hypothesis_id="height_twenty_one_payment_eleven_can_force_full_payment_three",
        hypothesis_statement=(
            "Some actual height-21 payment-eleven cylinder can pay the full factor "
            "three after landing at height two and return cofinally."
        ),
        probe_id="affine_mod22_then_mod3_payment_eleven_split",
        probe_question=(
            "What payment mechanisms occur at height 21, and what does payment "
            "eleven force after its exact height-two landing?"
        ),
        computation=(
            "Recover the height-21 parameter by affine lift evaluations modulo 21 "
            "and 22, then refine the payment-eleven classes through a modulo-nine "
            "coordinate that determines the divided height-two multiplier modulo 3."
        ),
        falsifier=(
            "A complete exact split showing that no payment-eleven class has a "
            "height-two multiplier divisible by three and that every resulting "
            "height-three multiplier is even."
        ),
        stop_condition=(
            "Stop after every payment-eleven three-lift class is certified through "
            "full payment four and cofinal return; do not horizon-audit the "
            "height-twenty-two survivors."
        ),
        survival_consequence=(
            "A nonzero full-payment-three class would close part of the branch by "
            "cofinal return and leave its complement for separate refinement."
        ),
        falsification_consequence=(
            "The full-payment-three mechanism is absent, but the singleton source "
            "residue forces an even height-three multiplier and full payment four; "
            "all 179161416 refined classes return cofinally."
        ),
        consumer_ref=LEAN_REF,
        consumer_declarations=transition["lean_declarations"],
        analysis_refs=[NOTE_REF, PACKET_REF, HEIGHT_TWENTY_RECEIPT_REF],
        source_refs=[
            SCRIPT_REF,
            HEIGHT_TWENTY_REF,
            HEIGHT_TWENTY_RECEIPT_REF,
            RESIDUE_CYLINDER_REF,
            LEAN_REF,
        ],
        result_status="exact_one_way_result",
        result_summary=(
            "The height-21 parameter image is {0,6} modulo 22, so the payment "
            "image is {1,11}. Payment eleven always lands at height two, but its "
            "exact three-lift refinement has the singleton r-image {6} modulo 66: "
            "full payment three never occurs, but every class reaches height three "
            "with an even multiplier and then pays the full factor four."
        ),
        progress_class="one_way_theorem",
        decision_basis=(
            "Affine two-lift certificates classify the complete cylinders, and "
            "symbolic integer identities replace finite orbit-horizon inference."
        ),
        next_analytic_target=(
            "Discard every payment-eleven class and restrict the next probe to the "
            "362794680 refined height-22 payment-one classes."
        ),
        resource_bounds={
            "source_polynomial_degree": 1024,
            "input_base_classes": 506_880,
            "classified_height_twenty_one_classes": split[
                "complete_height_twenty_one_class_count"
            ],
            "classified_payment_eleven_refined_classes": refinement[
                "refined_class_count"
            ],
            "degree_1024_evaluations_per_source_class": 7,
            "symbolic_residue_checks": 60,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos243-height21-payment-split-receipt/1",
        "status": "verified_exact_height_twenty_one_payment_split",
        "complete_affine_height_twenty_one_split": split,
        "symbolic_payment_eleven_transition": transition,
        "cumulative_source_class_partition": {
            "common_modulus": COMMON_MODULUS,
            "new_cofinal_return_count": new_zero,
            "height_three_negative_candidate_count": surviving_height_three,
            "height_twenty_two_negative_candidate_count": surviving_height_twenty_two,
            "zero_centered_class_count": zero,
            "positive_centered_class_count": positive,
            "continuing_negative_candidate_class_count": negative,
            "exact_partition": f"{zero} zero + {positive} positive + {negative} negative = {COMMON_MODULUS}",
        },
        "experiment_contract": contract,
        "consequence_reconciliation": {
            "height_twenty_one_payment_eleven_mode": {
                "decision": "update_now",
                "reason": "complete split forces the universal 21->2->3->1 cofinal cascade",
                "authority_surface": PACKET_REF,
            },
            "height_three_and_height_twenty_two_survivors": {
                "decision": "update_now",
                "reason": "height three is closed; height twenty two is the only remaining negative branch",
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
                HEIGHT_TWENTY_REF,
                HEIGHT_TWENTY_RECEIPT_REF,
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
