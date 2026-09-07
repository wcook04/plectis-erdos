#!/usr/bin/env python3
"""Certify the exact modulus-17 split of the #243 height-16 survivors.

The height-14 certificate leaves 360 source cylinders modulo 2730.  They all
reach height 16 with centered error -1.  This checker refines those cylinders
by the final factor 17 and evaluates the exact degree-1024 source polynomial
on the complete modulus-46410 residue cylinder.

Value-level exact division avoids expanding another large affine-substituted
polynomial.  The resulting quotient image is exceptionally small: the
intermediate parameter ``c`` is only 0, 10, or 12 modulo 17.  These images
respectively continue with error -1, switch to error +8, or pay the full
factor 17 and collapse to primitive height one.
"""

from __future__ import annotations

import argparse
import json
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
from check_erdos243_payment_one_height14 import (  # noqa: E402
    PAYMENT_ONE_T_CLASSES,
)


SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_height16_mod17.py"
)
HEIGHT_FOURTEEN_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_payment_one_height14.py"
)
LIBRARY_REF = "system/lib/formal_math_residue_cylinder.py"
TEST_REF = "system/server/tests/test_formal_math_residue_cylinder.py"
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
    "erdos243_height16_mod17_receipt.json"
)

BASE_MODULUS = 13 * 14 * 15
COMMON_MODULUS = BASE_MODULUS * 17
EXPECTED_C_IMAGE = {0, 10, 12}
EXPECTED_MULTIPLIER_IMAGE = {0, 1, 3}


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


def _height_sixteen_multiplier_mod_17(c: int) -> int:
    # m=2730*c^2+12*c and D=210*m^2+13*m+1.  Modulo 17 these reduce as below.
    m = (10 * c * c + 12 * c) % 17
    d = (6 * m * m + 13 * m + 1) % 17
    # E=(15*D^2-16*D+17)/16 = 2*D^2-D modulo 17.
    return (2 * d * d - d) % 17


def _next_centered_error(multiplier: int) -> int | None:
    if multiplier % 17 == 0:
        return None
    residue = (-(multiplier * multiplier)) % 17
    return residue if residue <= 8 else residue - 17


def height_sixteen_split_certificate(q10: list[int]) -> dict[str, Any]:
    # Reducing the giant coefficients once is the crucial performance step.
    q10_common = [coefficient % COMMON_MODULUS for coefficient in q10]
    q10_base = [coefficient % BASE_MODULUS for coefficient in q10_common]

    base_survivors: list[tuple[int, int, int]] = []
    for source_residue, t_classes in PAYMENT_ONE_T_CLASSES.items():
        for t_residue in t_classes:
            for s_residue in range(15):
                parameter = source_residue + 13 * (t_residue + 14 * s_residue)
                q11 = _q11_value(q10_base, parameter, 14 * 15)
                w_mod_15 = exact_quotient_value_mod(
                    q11, divisor=14, quotient_modulus=15
                )
                if w_mod_15 == 0:
                    base_survivors.append(
                        (source_residue, t_residue, s_residue)
                    )
    assert len(base_survivors) == 360

    class_lists: dict[str, list[int]] = {
        "full_payment": [],
        "positive_switch": [],
        "continuing_negative": [],
    }
    c_counts: dict[int, int] = {}
    multiplier_counts: dict[int, int] = {}
    error_counts: dict[int, int] = {}

    for source_residue, t_residue, s_residue in base_survivors:
        for lift in range(17):
            parameter = source_residue + 13 * (
                t_residue + 14 * (s_residue + 15 * lift)
            )
            q11 = _q11_value(q10_common, parameter, 14 * 15 * 17)
            w_mod_255 = exact_quotient_value_mod(
                q11, divisor=14, quotient_modulus=15 * 17
            )
            c_mod_17 = exact_quotient_value_mod(
                w_mod_255, divisor=15, quotient_modulus=17
            )
            multiplier = _height_sixteen_multiplier_mod_17(c_mod_17)
            error = _next_centered_error(multiplier)
            parameter_class = parameter % COMMON_MODULUS

            c_counts[c_mod_17] = c_counts.get(c_mod_17, 0) + 1
            multiplier_counts[multiplier] = multiplier_counts.get(multiplier, 0) + 1
            if error is None:
                class_lists["full_payment"].append(parameter_class)
            elif error > 0:
                class_lists["positive_switch"].append(parameter_class)
                error_counts[error] = error_counts.get(error, 0) + 1
            else:
                class_lists["continuing_negative"].append(parameter_class)
                error_counts[error] = error_counts.get(error, 0) + 1

    for classes in class_lists.values():
        classes.sort()
        assert len(classes) == len(set(classes))
    assert not (
        set(class_lists["full_payment"])
        & set(class_lists["positive_switch"])
    )
    assert not (
        set(class_lists["full_payment"])
        & set(class_lists["continuing_negative"])
    )
    assert not (
        set(class_lists["positive_switch"])
        & set(class_lists["continuing_negative"])
    )
    assert set(c_counts) == EXPECTED_C_IMAGE
    assert set(multiplier_counts) == EXPECTED_MULTIPLIER_IMAGE
    assert c_counts == {0: 2160, 10: 2520, 12: 1440}
    assert multiplier_counts == {0: 1440, 1: 2160, 3: 2520}
    assert error_counts == {-1: 2160, 8: 2520}
    assert len(class_lists["full_payment"]) == 1440
    assert len(class_lists["positive_switch"]) == 2520
    assert len(class_lists["continuing_negative"]) == 2160

    return {
        "base_survivor_cylinder_count_mod_2730": len(base_survivors),
        "refinement_modulus": COMMON_MODULUS,
        "refined_cylinder_count": 360 * 17,
        "actual_c_image_mod_17": sorted(c_counts),
        "c_image_class_counts": {str(key): value for key, value in sorted(c_counts.items())},
        "height_sixteen_multiplier_image_mod_17": sorted(multiplier_counts),
        "multiplier_class_counts": {
            str(key): value for key, value in sorted(multiplier_counts.items())
        },
        "next_error_class_counts": {
            str(key): value for key, value in sorted(error_counts.items())
        },
        "full_payment_seventeen_class_count": len(class_lists["full_payment"]),
        "positive_switch_class_count": len(class_lists["positive_switch"]),
        "continuing_negative_class_count": len(class_lists["continuing_negative"]),
        "full_payment_k_classes_mod_46410": class_lists["full_payment"],
        "positive_switch_k_classes_mod_46410": class_lists["positive_switch"],
        "continuing_negative_k_classes_mod_46410": class_lists["continuing_negative"],
        "branch_table": [
            {
                "c_mod_17": 12,
                "multiplier_mod_17": 0,
                "payment": 17,
                "next_height": 1,
                "next_centered_error": 0,
                "class_count": 1440,
            },
            {
                "c_mod_17": 10,
                "multiplier_mod_17": 3,
                "payment": 1,
                "next_height": 17,
                "next_centered_error": 8,
                "class_count": 2520,
            },
            {
                "c_mod_17": 0,
                "multiplier_mod_17": 1,
                "payment": 1,
                "next_height": 17,
                "next_centered_error": -1,
                "class_count": 2160,
            },
        ],
    }


def build_receipt() -> dict[str, Any]:
    _, q10 = source_quotient_polynomials()
    split = height_sixteen_split_certificate(q10)

    zero = 33480 + split["full_payment_seventeen_class_count"]
    positive = 6810 + split["positive_switch_class_count"]
    negative = split["continuing_negative_class_count"]
    assert (zero, positive, negative) == (34920, 9330, 2160)
    assert zero + positive + negative == COMMON_MODULUS

    contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Under a_(n+1)/a_n^2 -> 1 and rational reciprocal sum, force "
            "eventual Sylvester recurrence."
        ),
        claim_ceiling=(
            "Exact cofinal return or positive sign switch for 3960 of the 6120 "
            "height-16 lifts, with exact isolation of 2160 error-minus-one "
            "survivors; the next branch and unrestricted #243 remain open."
        ),
        hypothesis_id="height_sixteen_negative_unit_mode_supports_all_survivors",
        hypothesis_statement=(
            "The 360 height-16 source cylinders can remain one homogeneous "
            "negative-unit expansion mode after modulus-17 refinement."
        ),
        probe_id="complete_height_sixteen_multiplier_cylinder_mod_17",
        probe_question=(
            "Does the exact height-16 multiplier image force full payment or a "
            "centered sign switch on any complete source subcylinders?"
        ),
        computation=(
            "Pre-reduce the exact degree-1024 source polynomial modulo 46410, "
            "enumerate all 6120 lifts of the 360 certified height-16 cylinders, "
            "use value-level exact division by 13,14,15, and classify the "
            "height-16 multiplier and next centered error modulo 17."
        ),
        falsifier=(
            "A nonempty exact class partition into full-payment collapse, "
            "positive sign switch, and a strictly smaller negative survivor set."
        ),
        stop_condition=(
            "Stop at the first complete modulus-17 collapse/sign partition; do "
            "not audit later states of the surviving error-minus-one classes."
        ),
        survival_consequence=(
            "If the image were entirely multiplier 1, every height-16 cylinder "
            "would remain available for negative-unit expansion."
        ),
        falsification_consequence=(
            "The actual c-image is {0,10,12}: 1440 classes collapse by full "
            "payment 17, 2520 switch to error +8, and only 2160 retain error -1. "
            "The cumulative modulus-46410 partition is 34920 zero, 9330 "
            "positive, and 2160 continuing-negative candidates."
        ),
        consumer_ref=LEAN_REF,
        consumer_declarations=[
            "ErdosProblems.Erdos243.paymentOneHeightSixteen_fullPayment",
            "ErdosProblems.Erdos243.paymentOneHeightSixteen_fullCollapse",
            "ErdosProblems.Erdos243.paymentOneHeightSixteen_positiveSwitchIdentity",
            "ErdosProblems.Erdos243.paymentOneHeightSixteen_negativeSurvivorIdentity",
        ],
        analysis_refs=[NOTE_REF, PACKET_REF, HEIGHT_FOURTEEN_REF, LIBRARY_REF],
        source_refs=[SCRIPT_REF, HEIGHT_FOURTEEN_REF, LIBRARY_REF, TEST_REF, LEAN_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "Among 6120 height-16 lifts, the actual quotient image c mod 17 is "
            "only {0,10,12}. Exactly 1440 pay 17 and collapse, 2520 switch to "
            "centered error +8, and 2160 retain centered error -1."
        ),
        progress_class="one_way_theorem",
        decision_basis=(
            "Complete residue enumeration of an exact integer polynomial is "
            "universal over every modulus lift; exact modular division preserves "
            "the quotient values and the Lean identities consume all three images."
        ),
        next_analytic_target=(
            "Discard the collapse and positive classes.  On the exact c=0 mod 17 "
            "survivors, propagate the multiplier-one height-17 transition to the "
            "next prime-height payment and stop at the next structural split."
        ),
        resource_bounds={
            "source_polynomial_degree": 1024,
            "pre_reduced_coefficient_count": len(q10),
            "base_survivor_cylinders": 360,
            "modulus_lifts_per_cylinder": 17,
            "classified_residue_cylinders": 6120,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos243-height16-mod17-receipt/1",
        "status": "verified_exact_cofinal_return_and_sign_split",
        "height_sixteen_split_certificate": split,
        "cumulative_source_class_partition": {
            "common_modulus": COMMON_MODULUS,
            "zero_centered_class_count": zero,
            "positive_centered_class_count": positive,
            "continuing_negative_candidate_class_count": negative,
            "exact_partition": "34920 zero + 9330 positive + 2160 negative = 46410",
        },
        "infrastructure_receipt": {
            "method": "pre_reduced_complete_cylinder_value_evaluation",
            "exact_division_primitive": "exact_quotient_value_mod",
            "library": LIBRARY_REF,
            "test": TEST_REF,
            "avoided_failure_mode": (
                "repeated affine substitution expanded degree-2048 modular "
                "polynomials and obscured the finite cylinder already in scope"
            ),
        },
        "experiment_contract": contract,
        "consequence_reconciliation": {
            "height_sixteen_full_payment_and_positive_modes": {
                "decision": "update_now",
                "reason": "3960 exact cylinders have one-way terminal or sign-switch results",
                "authority_surface": PACKET_REF,
            },
            "height_seventeen_negative_unit_branch": {
                "decision": "update_now",
                "reason": "it is now the sole surviving branch of this family",
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
            for ref in [SCRIPT_REF, HEIGHT_FOURTEEN_REF, LIBRARY_REF, TEST_REF, LEAN_REF, NOTE_REF, PACKET_REF]
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
