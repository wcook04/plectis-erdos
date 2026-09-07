#!/usr/bin/env python3
"""Certify the second exact residue split of the #243 forced excursion.

The first split leaves five source classes modulo 13.  Four retain centered
error -1 at height 13; their payment is always 1 or 7, never the full factor
14.  The fifth class, ``k = 1 + 13*t``, has centered error -4.  Exact modular
quotient propagation proves that four classes of ``t mod 17`` pay the full
factor 17, collapse to primitive height one, and enter the zero-centered tail.

The checker uses the composite-modulus exact-division principle from
``system.lib.formal_math_residue_cylinder``.  It never materialises the
degree-2048 integer quotient polynomial.
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
    affine_substitute_mod,
    exact_quotient_coefficients_mod,
    polynomial_add_constant_mod,
    polynomial_mul_mod,
    residue_table,
)

from check_erdos243_clean_prefix_tiny_reset import reduced_step  # noqa: E402
from check_erdos243_forced_excursion_split import (  # noqa: E402
    COLLAPSE_CLASSES as FIRST_COLLAPSE_CLASSES,
    source_quotient_polynomials,
)
from check_erdos243_infinite_clean_recovery_family import (  # noqa: E402
    BASE_QUOTIENT,
    FAMILY_PERIOD,
)


SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_second_excursion_split.py"
)
FIRST_SPLIT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_forced_excursion_split.py"
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
    "erdos243_second_excursion_split_receipt.json"
)

NEGATIVE_UNIT_SOURCE_CLASSES = [3, 4, 11, 12]
NEGATIVE_UNIT_EXPECTED_VALUES = {
    3: [1, 7, 1, 1, 7, 1, 1, 1, 7, 1, 1, 7, 1, 1],
    4: [1, 1, 7, 1, 1, 7, 1, 1, 1, 7, 1, 1, 7, 1],
    11: [1, 1, 7, 1, 1, 7, 1, 1, 1, 7, 1, 1, 7, 1],
    12: [1, 1, 1, 7, 1, 1, 7, 1, 1, 1, 7, 1, 1, 7],
}
NEGATIVE_FOUR_EXPECTED_VALUES = [
    5,
    13,
    5,
    5,
    13,
    5,
    13,
    5,
    0,
    0,
    13,
    5,
    13,
    0,
    0,
    5,
    13,
]
NEGATIVE_FOUR_COLLAPSE_T_CLASSES = [8, 9, 13, 14]
NEGATIVE_FOUR_COLLAPSE_K_CLASSES_MOD_221 = [105, 118, 170, 183]
NEGATIVE_FOUR_POSITIVE_TWO_T_CLASSES = [0, 2, 3, 5, 7, 11, 15]
NEGATIVE_FOUR_POSITIVE_FOUR_T_CLASSES = [1, 4, 6, 10, 12, 16]


def _scaled_polynomial_mod(
    coefficients: list[int], scalar: int, modulus: int
) -> list[int]:
    return [(scalar * coefficient) % modulus for coefficient in coefficients]


def _height_twelve_raw_denominator_polynomial_mod(
    q10: list[int], modulus: int
) -> list[int]:
    q_plus_one = polynomial_add_constant_mod(q10, 1, modulus)
    twelve_q_minus_one = polynomial_add_constant_mod(
        _scaled_polynomial_mod(q10, 12, modulus), -1, modulus
    )
    return polynomial_mul_mod(q_plus_one, twelve_q_minus_one, modulus)


def negative_unit_height_thirteen_certificate(q10: list[int]) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    all_full_payment_classes: list[list[int]] = []
    for source_residue in NEGATIVE_UNIT_SOURCE_CLASSES:
        quotient_modulus = 14
        composite_modulus = 13 * quotient_modulus
        q10_substituted = affine_substitute_mod(
            q10, source_residue, 13, composite_modulus
        )
        raw_v = _height_twelve_raw_denominator_polynomial_mod(
            q10_substituted, composite_modulus
        )
        negative_unit_numerator = polynomial_add_constant_mod(
            raw_v, 1, composite_modulus
        )
        q11_mod_14 = exact_quotient_coefficients_mod(
            negative_unit_numerator,
            divisor=13,
            quotient_modulus=quotient_modulus,
        )
        multiplier_mod_14 = polynomial_add_constant_mod(
            q11_mod_14, 1, quotient_modulus
        )
        values = residue_table(multiplier_mod_14, range(14), 14)
        assert values == NEGATIVE_UNIT_EXPECTED_VALUES[source_residue]
        payments = [math.gcd(14, value * value) for value in values]
        full_payment = [index for index, payment in enumerate(payments) if payment == 14]
        payment_seven = [index for index, payment in enumerate(payments) if payment == 7]
        payment_one = [index for index, payment in enumerate(payments) if payment == 1]
        assert not full_payment
        assert len(payment_seven) == 4 and len(payment_one) == 10
        all_full_payment_classes.extend(
            [[source_residue, parameter_residue] for parameter_residue in full_payment]
        )
        rows.append(
            {
                "source_class_mod_13": source_residue,
                "parameterization": f"k={source_residue}+13*t",
                "height_thirteen_multiplier_mod_14_by_t_mod_14": values,
                "payment_by_t_mod_14": payments,
                "payment_seven_t_classes": payment_seven,
                "payment_one_t_classes": payment_one,
                "full_payment_fourteen_t_classes": full_payment,
            }
        )
    assert not all_full_payment_classes
    return {
        "branch": "height_13_centered_error_minus_one",
        "source_classes_mod_13": NEGATIVE_UNIT_SOURCE_CLASSES,
        "rows": rows,
        "universal_payment_set": [1, 7],
        "full_payment_fourteen_class_count": 0,
        "conclusion": (
            "the immediate full-payment collapse at height 13 is impossible on "
            "all four negative-unit source classes"
        ),
    }


def negative_four_height_thirteen_certificate(q10: list[int]) -> dict[str, Any]:
    quotient_modulus = 17
    composite_modulus = 13 * quotient_modulus
    q10_substituted = affine_substitute_mod(q10, 1, 13, composite_modulus)
    raw_v = _height_twelve_raw_denominator_polynomial_mod(
        q10_substituted, composite_modulus
    )
    centered_quotient_numerator = polynomial_add_constant_mod(
        raw_v, 4, composite_modulus
    )
    q11_mod_17 = exact_quotient_coefficients_mod(
        centered_quotient_numerator,
        divisor=13,
        quotient_modulus=quotient_modulus,
    )
    multiplier_mod_17 = polynomial_add_constant_mod(q11_mod_17, 1, 17)
    values = residue_table(multiplier_mod_17, range(17), 17)
    assert values == NEGATIVE_FOUR_EXPECTED_VALUES
    payments = [math.gcd(17, value * value) for value in values]
    collapse_t_classes = [
        index for index, payment in enumerate(payments) if payment == 17
    ]
    assert collapse_t_classes == NEGATIVE_FOUR_COLLAPSE_T_CLASSES
    collapse_k_classes = sorted((1 + 13 * value) % 221 for value in collapse_t_classes)
    assert collapse_k_classes == NEGATIVE_FOUR_COLLAPSE_K_CLASSES_MOD_221
    next_centered_errors: list[int | None] = []
    for multiplier_residue, payment in zip(values, payments, strict=True):
        if payment == 17:
            next_centered_errors.append(None)
            continue
        quotient_residue = (multiplier_residue - 1) % 17
        raw_denominator_residue = (
            multiplier_residue * (13 * quotient_residue - 4)
        ) % 17
        centered_error = (
            raw_denominator_residue
            if 2 * raw_denominator_residue < 17
            else raw_denominator_residue - 17
        )
        next_centered_errors.append(centered_error)
    positive_two = [
        index for index, error in enumerate(next_centered_errors) if error == 2
    ]
    positive_four = [
        index for index, error in enumerate(next_centered_errors) if error == 4
    ]
    assert positive_two == NEGATIVE_FOUR_POSITIVE_TWO_T_CLASSES
    assert positive_four == NEGATIVE_FOUR_POSITIVE_FOUR_T_CLASSES
    assert all(error in {None, 2, 4} for error in next_centered_errors)
    return {
        "branch": "height_13_centered_error_minus_four",
        "source_class_mod_13": 1,
        "parameterization": "k=1+13*t",
        "height_thirteen_multiplier_mod_17_by_t_mod_17": values,
        "payment_by_t_mod_17": payments,
        "full_payment_seventeen_t_classes": collapse_t_classes,
        "full_payment_seventeen_k_classes_mod_221": collapse_k_classes,
        "surviving_t_classes_mod_17": [
            value for value in range(17) if value not in collapse_t_classes
        ],
        "next_centered_error_by_t_mod_17": next_centered_errors,
        "positive_error_two_t_classes": positive_two,
        "positive_error_four_t_classes": positive_four,
        "continuing_negative_t_classes": [],
        "conclusion": (
            "four infinite arithmetic subfamilies pay 17 at height 13, "
            "collapse to primitive height one, and enter centered state zero; "
            "all thirteen non-full-payment classes switch to centered error "
            "+2 or +4 at height 17"
        ),
    }


def _post_recovery_rows(parameter: int, step_count: int) -> list[dict[str, int]]:
    q = BASE_QUOTIENT + FAMILY_PERIOD * parameter
    u = 11
    v = u * q - 1
    for _ in range(9):
        step = reduced_step(u, v)
        u, v = step["u_next"], step["v_next"]
    rows: list[dict[str, int]] = []
    for _ in range(step_count):
        step = reduced_step(u, v)
        rows.append(
            {
                "height": u,
                "centered_error": step["e"],
                "payment": step["h"],
                "next_height": step["u_next"],
            }
        )
        u, v = step["u_next"], step["v_next"]
    return rows


def regression_replays() -> dict[str, Any]:
    collapse_rows: list[dict[str, Any]] = []
    for t_residue in NEGATIVE_FOUR_COLLAPSE_T_CLASSES:
        parameter = 1 + 13 * t_residue
        rows = _post_recovery_rows(parameter, 4)
        assert rows == [
            {"height": 11, "centered_error": -1, "payment": 1, "next_height": 12},
            {"height": 12, "centered_error": -1, "payment": 1, "next_height": 13},
            {"height": 13, "centered_error": -4, "payment": 17, "next_height": 1},
            {"height": 1, "centered_error": 0, "payment": 1, "next_height": 1},
        ]
        collapse_rows.append(
            {"t_residue_mod_17": t_residue, "parameter": parameter, "rows": rows}
        )

    positive_rows: list[dict[str, Any]] = []
    expected_positive_errors = {
        **{value: 2 for value in NEGATIVE_FOUR_POSITIVE_TWO_T_CLASSES},
        **{value: 4 for value in NEGATIVE_FOUR_POSITIVE_FOUR_T_CLASSES},
    }
    for t_residue, expected_error in sorted(expected_positive_errors.items()):
        parameter = 1 + 13 * t_residue
        rows = _post_recovery_rows(parameter, 4)
        assert rows[2] == {
            "height": 13,
            "centered_error": -4,
            "payment": 1,
            "next_height": 17,
        }
        assert rows[3]["height"] == 17
        assert rows[3]["centered_error"] == expected_error
        positive_rows.append(
            {
                "t_residue_mod_17": t_residue,
                "parameter": parameter,
                "expected_positive_error": expected_error,
                "rows": rows,
            }
        )

    negative_unit_rows: list[dict[str, Any]] = []
    for source_residue, values in NEGATIVE_UNIT_EXPECTED_VALUES.items():
        for t_residue, value in enumerate(values):
            parameter = source_residue + 13 * t_residue
            rows = _post_recovery_rows(parameter, 3)
            expected_payment = math.gcd(14, value * value)
            assert rows[-1] == {
                "height": 13,
                "centered_error": -1,
                "payment": expected_payment,
                "next_height": 14 // expected_payment,
            }
            negative_unit_rows.append(
                {
                    "source_residue_mod_13": source_residue,
                    "t_residue_mod_14": t_residue,
                    "terminal_row": rows[-1],
                }
            )
    return {
        "negative_four_collapse_representatives": collapse_rows,
        "negative_four_positive_switch_representatives": positive_rows,
        "negative_unit_payment_representatives": negative_unit_rows,
    }


def build_receipt() -> dict[str, Any]:
    _, q10 = source_quotient_polynomials()
    negative_unit = negative_unit_height_thirteen_certificate(q10)
    negative_four = negative_four_height_thirteen_certificate(q10)
    replays = regression_replays()
    first_wave_count_mod_221 = len(FIRST_COLLAPSE_CLASSES) * 17
    total_collapse_count_mod_221 = first_wave_count_mod_221 + len(
        NEGATIVE_FOUR_COLLAPSE_K_CLASSES_MOD_221
    )
    assert total_collapse_count_mod_221 == 140

    contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Under a_(n+1)/a_n^2 -> 1 and rational reciprocal sum, force "
            "eventual Sylvester recurrence."
        ),
        claim_ceiling=(
            "Exact cofinal return for four further classes modulo 221 and exact "
            "elimination of immediate full payment on the four negative-unit "
            "height-13 branches; unrestricted #243 remains open."
        ),
        hypothesis_id="surviving_height_thirteen_classes_avoid_cofinal_return",
        hypothesis_statement=(
            "None of the five source classes surviving the height-12 split can "
            "make a full payment at the next centered height."
        ),
        probe_id="composite_modulus_height_thirteen_payment_split",
        probe_question=(
            "After exact division by 13, which source cylinders make the next "
            "multiplier divisible by the full primitive height?"
        ),
        computation=(
            "Substitute each surviving source class into the exact q10 polynomial "
            "modulo divisor times target modulus, form the centered quotient "
            "numerator, divide its coefficients exactly modulo 14 or 17, and "
            "evaluate the complete residue tables."
        ),
        falsifier=(
            "A source residue cylinder with full height-13 payment, forcing "
            "primitive height one and the absorbing zero-centered tail."
        ),
        stop_condition=(
            "Stop after every one of the five source classes has one complete "
            "next-payment residue table; do not audit later arbitrary steps."
        ),
        survival_consequence=(
            "If all full-payment classes were absent, the immediate payment "
            "route to cofinal return would be closed at height 13."
        ),
        falsification_consequence=(
            "The error-minus-four branch contains four further infinite cofinal-"
            "return subfamilies, while all thirteen complements switch to positive "
            "centered error. Together with the first split, 140 of 221 source "
            "classes modulo 221 are forced into the Sylvester tail and only 68 "
            "remain candidates for continuing negative support."
        ),
        consumer_ref=LEAN_REF,
        consumer_declarations=[
            "ErdosProblems.Erdos243.negativeFourHeightThirteen_fullPayment",
            "ErdosProblems.Erdos243.negativeFourHeightThirteen_collapse",
        ],
        analysis_refs=[NOTE_REF, PACKET_REF, FIRST_SPLIT_REF, LIBRARY_REF],
        source_refs=[SCRIPT_REF, FIRST_SPLIT_REF, LIBRARY_REF, TEST_REF, LEAN_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "For k=1+13*t, the height-13 error is -4 and payment 17 occurs "
            "exactly for t mod 17 in {8,9,13,14}, equivalently k mod 221 in "
            "{105,118,170,183}; every lift collapses to height one and e=0 "
            "forever. Each of the other thirteen t-classes switches to positive "
            "centered error +2 or +4 at height 17. On k mod 13 in {3,4,11,12}, "
            "height-13 payment is always 1 or 7 and never the full factor 14."
        ),
        progress_class="one_way_theorem",
        decision_basis=(
            "Composite-modulus coefficient arithmetic proves the exact quotient "
            "tables for all parameter lifts; exact reduced-pair replays are only "
            "regression checks."
        ),
        next_analytic_target=(
            "Discard the error-minus-four branch as a continuing-negative-support "
            "mechanism. Treat the payment-seven height-two boundary cylinders "
            "separately from the payment-one height-fourteen cylinders in the four "
            "remaining negative-unit source classes."
        ),
        resource_bounds={
            "source_polynomial_degree": 1024,
            "avoided_next_integer_polynomial_degree": 2048,
            "negative_unit_residue_classes": 56,
            "negative_four_residue_classes": 17,
            "representative_replays": 73,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos243-second-excursion-split-receipt/1",
        "status": "verified_exact_second_cofinal_return_split",
        "negative_unit_certificate": negative_unit,
        "negative_four_certificate": negative_four,
        "cumulative_source_class_closure": {
            "common_modulus": 221,
            "first_split_closed_class_count": first_wave_count_mod_221,
            "second_split_additional_closed_classes": (
                NEGATIVE_FOUR_COLLAPSE_K_CLASSES_MOD_221
            ),
            "total_closed_class_count": total_collapse_count_mod_221,
            "remaining_class_count": 221 - total_collapse_count_mod_221,
            "exact_closed_fraction": "140/221",
            "positive_centered_class_count_after_second_split": 13,
            "continuing_negative_support_candidate_class_count": 68,
            "exact_three_way_partition": "140 zero-centered + 13 positive + 68 negative candidates = 221",
        },
        "regression_replays": replays,
        "experiment_contract": contract,
        "infrastructure_receipt": {
            "library": LIBRARY_REF,
            "test": TEST_REF,
            "method": (
                "recover (N/d) mod M from N mod (d*M) after exact "
                "coefficientwise divisibility"
            ),
            "avoided_object": "degree-2048 giant integer quotient polynomial",
        },
        "consequence_reconciliation": {
            "clean_return_family_frontier": {
                "decision": "update_now",
                "reason": "four further cofinal-return subfamilies are exact",
                "authority_surface": PACKET_REF,
            },
            "negative_unit_full_payment_route": {
                "decision": "update_now",
                "reason": "full payment fourteen is exactly absent on all four classes",
                "authority_surface": NOTE_REF,
            },
            "older_type_b_handoffs": {
                "decision": "verified_no_change",
                "reason": "historical research inputs do not own the live claim boundary",
                "authority_surface": PACKET_REF,
            },
            "public_projection": {
                "decision": "defer_with_reason",
                "reason": "private exact source is not automatic publication authority",
                "reentry_condition": "explicit public release wave with owner review",
                "authority_surface": PACKET_REF,
            },
        },
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [
                SCRIPT_REF,
                FIRST_SPLIT_REF,
                LIBRARY_REF,
                TEST_REF,
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
