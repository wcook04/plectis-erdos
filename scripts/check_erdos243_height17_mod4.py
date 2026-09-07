#!/usr/bin/env python3
"""Certify the #243 height-17 rigidity and height-18 modulus-19 split.

The height-16 certificate leaves 2160 multiplier-one source classes modulo
46410.  Refinement modulo four proves that every lift has the next quotient
parameter ``d = 0 mod 4``.  Consequently the height-17 multiplier is
``1 mod 18``: all 8640 refined cylinders pay one and retain centered error
-1 at height 18.

Writing ``d=4*e`` makes the next quotient parameter ``y`` an exact integer
polynomial of degree eight in ``e``.  Since the current modulus is coprime to
19, every surviving source cylinder sees every residue modulo 19 exactly
once.  Evaluation of the original degree-1024 source polynomial and the
degree-eight quotient identity over F_19 gives only height-18 multiplier
classes 0 and 1: eleven lifts collapse by full payment 19 and eight continue
with centered error -1.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path
from typing import Any


sys.set_int_max_str_digits(1_000_000)

REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)
from system.lib.formal_math_residue_cylinder import (  # noqa: E402
    evaluate_polynomial_mod,
    exact_quotient_value_mod,
)

from check_erdos243_forced_excursion_split import (  # noqa: E402
    source_quotient_polynomials,
)


SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_height17_mod4.py"
)
HEIGHT_SIXTEEN_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_height16_mod17.py"
)
HEIGHT_SIXTEEN_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos243_height16_mod17_receipt.json"
)
LIBRARY_REF = "system/lib/formal_math_residue_cylinder.py"
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
    "erdos243_height17_mod4_receipt.json"
)

HEIGHT_SIXTEEN_MODULUS = 13 * 14 * 15 * 17
HEIGHT_SEVENTEEN_MODULUS = HEIGHT_SIXTEEN_MODULUS * 4
COMMON_MODULUS = HEIGHT_SEVENTEEN_MODULUS * 19
Y_POLYNOMIAL_EXACT = [
    0,
    91,
    3_641_570,
    96_380_575_200,
    1_979_756_570_484_000,
    30_696_953_409_158_400_000,
    358_998_746_431_506_854_400_000,
    2_661_345_515_642_393_309_184_000_000,
    10_292_753_781_746_956_123_269_120_000_000,
]
EXPECTED_FULL_K_CLASSES_MOD_19 = [1, 3, 4, 7, 8, 10, 11, 13, 14, 17, 18]
EXPECTED_NEGATIVE_K_CLASSES_MOD_19 = [0, 2, 5, 6, 9, 12, 15, 16]


def _height_twelve_raw_denominator(q10: int, modulus: int) -> int:
    return ((q10 + 1) * (12 * q10 - 1)) % modulus


def _q11_value(
    q10_coefficients: list[int], parameter: int, quotient_modulus: int
) -> int:
    composite_modulus = 13 * quotient_modulus
    q10 = evaluate_polynomial_mod(
        q10_coefficients, parameter, composite_modulus
    )
    numerator = (
        _height_twelve_raw_denominator(q10, composite_modulus) + 1
    ) % composite_modulus
    return exact_quotient_value_mod(
        numerator, divisor=13, quotient_modulus=quotient_modulus
    )


def _evaluate_integer_polynomial(coefficients: list[int], value: int) -> int:
    total = 0
    for coefficient in reversed(coefficients):
        total = total * value + coefficient
    return total


def _y_from_exact_transition(e: int) -> int:
    c = 68 * e
    m = 2730 * c * c + 12 * c
    d_multiplier = 210 * m * m + 13 * m + 1
    e_numerator = 15 * d_multiplier * d_multiplier - 16 * d_multiplier + 17
    assert e_numerator % 16 == 0
    height_sixteen_multiplier = e_numerator // 16
    assert (height_sixteen_multiplier - 1) % 17 == 0
    z = (height_sixteen_multiplier - 1) // 17
    assert z % 6 == 0
    return z // 6


def height_seventeen_rigidity_certificate(
    q10: list[int], base_classes: list[int]
) -> dict[str, Any]:
    q10_modulus = [coefficient % HEIGHT_SEVENTEEN_MODULUS for coefficient in q10]
    d_counts: dict[int, int] = {}
    survivor_classes: list[int] = []
    for base_class in base_classes:
        for lift in range(4):
            parameter = base_class + HEIGHT_SIXTEEN_MODULUS * lift
            q11 = _q11_value(
                q10_modulus, parameter, quotient_modulus=14 * 15 * 17 * 4
            )
            w = exact_quotient_value_mod(
                q11, divisor=14, quotient_modulus=15 * 17 * 4
            )
            c = exact_quotient_value_mod(
                w, divisor=15, quotient_modulus=17 * 4
            )
            d_mod_4 = exact_quotient_value_mod(
                c, divisor=17, quotient_modulus=4
            )
            d_counts[d_mod_4] = d_counts.get(d_mod_4, 0) + 1
            survivor_classes.append(parameter % HEIGHT_SEVENTEEN_MODULUS)

    survivor_classes.sort()
    assert d_counts == {0: 8640}
    assert len(survivor_classes) == len(set(survivor_classes)) == 8640
    return {
        "input_class_count_mod_46410": len(base_classes),
        "refinement_modulus": HEIGHT_SEVENTEEN_MODULUS,
        "refined_class_count": len(survivor_classes),
        "actual_d_image_mod_4": [0],
        "d_image_class_counts": {"0": 8640},
        "height_seventeen_multiplier_class": "1 mod 18",
        "height_seventeen_payment": 1,
        "height_eighteen_centered_error": -1,
        "height_eighteen_survivor_k_classes_mod_185640": survivor_classes,
        "conclusion": (
            "full payment 18 and partial payments 9 or 2 are impossible; every "
            "height-17 lift pays one and retains negative-unit error at height 18"
        ),
    }


def height_eighteen_mod19_certificate(q10: list[int]) -> dict[str, Any]:
    # Nine point checks certify the displayed degree-eight integer-polynomial
    # identity.  Both sides have degree at most eight.
    for e in range(9):
        assert _evaluate_integer_polynomial(Y_POLYNOMIAL_EXACT, e) == (
            _y_from_exact_transition(e)
        )

    q10_mod_19 = [coefficient % 19 for coefficient in q10]
    y_polynomial_mod_19 = [coefficient % 19 for coefficient in Y_POLYNOMIAL_EXACT]
    rows: list[dict[str, int | None | str]] = []
    full_classes: list[int] = []
    negative_classes: list[int] = []
    e_image: set[int] = set()
    y_image: set[int] = set()
    multiplier_image: set[int] = set()

    for parameter_residue in range(19):
        q10_value = evaluate_polynomial_mod(
            q10_mod_19, parameter_residue, 19
        )
        raw_v = _height_twelve_raw_denominator(q10_value, 19)
        q11 = (raw_v + 1) * pow(13, -1, 19) % 19
        w = q11 * pow(14, -1, 19) % 19
        c = w * pow(15, -1, 19) % 19
        d = c * pow(17, -1, 19) % 19
        e = d * pow(4, -1, 19) % 19
        y = evaluate_polynomial_mod(y_polynomial_mod_19, e, 19)
        m = (12 * y * y + 5 * y) % 19
        multiplier = (2 * m * m + 16 * m + 1) % 19
        error: int | None
        if multiplier == 0:
            error = None
            branch = "full_payment_cofinal_return"
            full_classes.append(parameter_residue)
        else:
            residue = (-(multiplier * multiplier)) % 19
            error = residue if residue <= 9 else residue - 19
            assert error < 0
            branch = "continuing_negative"
            negative_classes.append(parameter_residue)
        e_image.add(e)
        y_image.add(y)
        multiplier_image.add(multiplier)
        rows.append(
            {
                "parameter_class_mod_19": parameter_residue,
                "e_mod_19": e,
                "y_mod_19": y,
                "height_eighteen_multiplier_mod_19": multiplier,
                "next_centered_error": error,
                "branch": branch,
            }
        )

    assert full_classes == EXPECTED_FULL_K_CLASSES_MOD_19
    assert negative_classes == EXPECTED_NEGATIVE_K_CLASSES_MOD_19
    assert e_image == {0, 2, 15}
    assert y_image == {0, 9, 15}
    assert multiplier_image == {0, 1}
    return {
        "parameter_refinement_prime": 19,
        "stride_mod_19": HEIGHT_SEVENTEEN_MODULUS % 19,
        "stride_is_unit_mod_19": math.gcd(HEIGHT_SEVENTEEN_MODULUS, 19) == 1,
        "degree_eight_y_polynomial_coefficients_low_to_high": Y_POLYNOMIAL_EXACT,
        "degree_eight_y_polynomial_coefficients_mod_19_low_to_high": y_polynomial_mod_19,
        "actual_e_image_mod_19": sorted(e_image),
        "actual_y_image_mod_19": sorted(y_image),
        "height_eighteen_multiplier_image_mod_19": sorted(multiplier_image),
        "full_payment_nineteen_k_classes_mod_19": full_classes,
        "continuing_negative_k_classes_mod_19": negative_classes,
        "full_payment_lifts_per_base_class": len(full_classes),
        "continuing_negative_lifts_per_base_class": len(negative_classes),
        "positive_switch_lifts_per_base_class": 0,
        "rows": rows,
        "conclusion": (
            "every height-18 source cylinder has multiplier 0 or 1 modulo 19; "
            "eleven of nineteen lifts collapse and eight retain centered error -1"
        ),
    }


def build_receipt() -> dict[str, Any]:
    height_sixteen_receipt = json.loads(
        (REPO_ROOT / HEIGHT_SIXTEEN_RECEIPT_REF).read_text(encoding="utf-8")
    )
    assert height_sixteen_receipt["status"] == (
        "verified_exact_cofinal_return_and_sign_split"
    )
    base_classes = height_sixteen_receipt["height_sixteen_split_certificate"][
        "continuing_negative_k_classes_mod_46410"
    ]
    assert len(base_classes) == 2160

    _, q10 = source_quotient_polynomials()
    height_seventeen = height_seventeen_rigidity_certificate(q10, base_classes)
    height_eighteen = height_eighteen_mod19_certificate(q10)

    branch_classes = height_seventeen["refined_class_count"]
    new_zero = branch_classes * height_eighteen["full_payment_lifts_per_base_class"]
    negative = branch_classes * height_eighteen["continuing_negative_lifts_per_base_class"]
    zero = 34920 * 4 * 19 + new_zero
    positive = 9330 * 4 * 19
    assert (new_zero, zero, positive, negative) == (95040, 2748960, 709080, 69120)
    assert zero + positive + negative == COMMON_MODULUS

    contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Under a_(n+1)/a_n^2 -> 1 and rational reciprocal sum, force "
            "eventual Sylvester recurrence."
        ),
        claim_ceiling=(
            "Exact elimination of every nontrivial height-17 payment and exact "
            "cofinal return on eleven of nineteen height-18 lifts; 69120 refined "
            "negative-unit classes and unrestricted #243 remain open."
        ),
        hypothesis_id="height_seventeen_or_eighteen_supports_unbroken_negative_expansion",
        hypothesis_statement=(
            "The multiplier-one height-17 cylinders can pass both heights 17 and "
            "18 without an exact payment or sign partition."
        ),
        probe_id="height_seventeen_mod4_then_height_eighteen_mod19",
        probe_question=(
            "Does the actual quotient image force a nontrivial height-17 payment, "
            "or a full payment 19 on the next negative-unit height?"
        ),
        computation=(
            "Refine all 2160 height-17 source classes modulo four by exact "
            "value-level quotient division; derive the degree-eight integer "
            "polynomial for the remaining lift parameter, then evaluate the exact "
            "source and multiplier maps on the complete field F_19."
        ),
        falsifier=(
            "An exact full-payment class at height 18 or a finite image theorem "
            "that eliminates a distinct height-17 payment mechanism."
        ),
        stop_condition=(
            "Stop when the complete mod-4 and mod-19 cylinders have an exact "
            "terminal/survivor partition; do not audit the mod-19 survivors later."
        ),
        survival_consequence=(
            "If every modulus-19 multiplier were one, the entire height-18 branch "
            "would remain available for negative-unit expansion."
        ),
        falsification_consequence=(
            "All height-17 lifts pay one, but eleven of nineteen height-18 lifts "
            "pay the full factor 19 and collapse. Only eight lifts per source "
            "class continue, leaving 69120 negative candidates modulo 3527160."
        ),
        consumer_ref=LEAN_REF,
        consumer_declarations=[
            "ErdosProblems.Erdos243.paymentOneHeightSeventeen_paymentOne",
            "ErdosProblems.Erdos243.paymentOneHeightEighteen_fullPayment",
            "ErdosProblems.Erdos243.paymentOneHeightEighteen_fullCollapse",
            "ErdosProblems.Erdos243.paymentOneHeightEighteen_negativeSurvivorIdentity",
        ],
        analysis_refs=[NOTE_REF, PACKET_REF, HEIGHT_SIXTEEN_REF, HEIGHT_SIXTEEN_RECEIPT_REF],
        source_refs=[SCRIPT_REF, HEIGHT_SIXTEEN_REF, HEIGHT_SIXTEEN_RECEIPT_REF, LIBRARY_REF, LEAN_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "Every mod-4 lift has d=0, hence payment one at height 17 and error -1 "
            "at height 18. Modulo 19 the next multiplier image is {0,1}: eleven "
            "lifts collapse by full payment 19 and eight continue with error -1."
        ),
        progress_class="one_way_theorem",
        decision_basis=(
            "Exact composite-modulus evaluation covers all mod-4 lifts; the "
            "coprime stride makes the F_19 table universal for every surviving "
            "base cylinder, and the degree-eight identity is certified exactly."
        ),
        next_analytic_target=(
            "Discard the eleven cofinal-return classes.  Restrict the next exact "
            "probe to the eight multiplier-one height-19 residue classes per "
            "surviving height-18 cylinder."
        ),
        resource_bounds={
            "source_polynomial_degree": 1024,
            "height_seventeen_base_classes": len(base_classes),
            "mod4_refined_classes": branch_classes,
            "mod19_residues_per_base_class": 19,
            "degree_eight_identity_check_points": 9,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos243-height17-mod4-height18-mod19-receipt/1",
        "status": "verified_exact_height17_rigidity_and_height18_cofinal_split",
        "height_seventeen_rigidity_certificate": height_seventeen,
        "height_eighteen_mod19_certificate": height_eighteen,
        "cumulative_source_class_partition": {
            "common_modulus": COMMON_MODULUS,
            "new_full_payment_nineteen_class_count": new_zero,
            "zero_centered_class_count": zero,
            "positive_centered_class_count": positive,
            "continuing_negative_candidate_class_count": negative,
            "exact_partition": (
                "2748960 zero + 709080 positive + 69120 negative = 3527160"
            ),
        },
        "experiment_contract": contract,
        "consequence_reconciliation": {
            "height_seventeen_nontrivial_payment_modes": {
                "decision": "update_now",
                "reason": "all exact source lifts avoid payments 18, 9, and 2",
                "authority_surface": PACKET_REF,
            },
            "height_eighteen_full_payment_mode": {
                "decision": "update_now",
                "reason": "eleven of nineteen lifts per source class have cofinal return",
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
            for ref in [SCRIPT_REF, HEIGHT_SIXTEEN_REF, HEIGHT_SIXTEEN_RECEIPT_REF, LIBRARY_REF, LEAN_REF, NOTE_REF, PACKET_REF]
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
