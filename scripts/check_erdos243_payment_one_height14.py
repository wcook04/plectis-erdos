#!/usr/bin/env python3
"""Certify the exact height-14 split of #243 payment-one cylinders.

The payment-seven branch is already closed.  Every remaining negative-unit
source cylinder reaches height 14 with centered error -1 and a height-13
multiplier ``A = 14*w + 1``.  Generic algebra would permit several payments
at height 14, including a full payment of 15.  Exact quotient propagation on
the actual clean-return family proves the much smaller image

    w mod 15 in {0, 3}.

The ``w = 3`` image pays five and immediately switches to centered error +1
at height three.  The ``w = 0`` image pays one, then pays one again at height
15 and reaches height 16 with centered error -1.  Thus the checker kills 240
of the 600 refined negative cylinders and isolates the only surviving branch
without extending representative orbits past the first decisive split.
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
    source_quotient_polynomials,
)
from check_erdos243_infinite_clean_recovery_family import (  # noqa: E402
    BASE_QUOTIENT,
    FAMILY_PERIOD,
)
from check_erdos243_payment_seven_cascade import (  # noqa: E402
    centered_step_allow_tie,
)
from check_erdos243_second_excursion_split import (  # noqa: E402
    NEGATIVE_UNIT_EXPECTED_VALUES,
    NEGATIVE_UNIT_SOURCE_CLASSES,
)


SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_payment_one_height14.py"
)
SECOND_SPLIT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_second_excursion_split.py"
)
PAYMENT_SEVEN_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_payment_seven_cascade.py"
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
    "erdos243_payment_one_height14_receipt.json"
)

PAYMENT_ONE_T_CLASSES = {
    source_residue: [
        index for index, multiplier in enumerate(values) if multiplier == 1
    ]
    for source_residue, values in NEGATIVE_UNIT_EXPECTED_VALUES.items()
}
EXPECTED_IMAGE_VALUES = {0, 3}
BRANCH_MODULUS = 13 * 14 * 15
COMMON_MODULUS = 13 * 14 * 15 * 17


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


def height_fourteen_split_certificate(q10: list[int]) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    positive_k_classes: list[int] = []
    continuing_k_classes: list[int] = []

    for source_residue in NEGATIVE_UNIT_SOURCE_CLASSES:
        # q11=(v12+1)/13 is needed modulo 14*15.  Recover it from the
        # numerator modulo 13*14*15 without constructing the integer quotient.
        composite_modulus = 13 * 14 * 15
        q10_substituted = affine_substitute_mod(
            q10, source_residue, 13, composite_modulus
        )
        raw_v = _height_twelve_raw_denominator_polynomial_mod(
            q10_substituted, composite_modulus
        )
        q11_mod_210 = exact_quotient_coefficients_mod(
            polynomial_add_constant_mod(raw_v, 1, composite_modulus),
            divisor=13,
            quotient_modulus=14 * 15,
        )

        for t_residue in PAYMENT_ONE_T_CLASSES[source_residue]:
            # The payment-one hypothesis says q11 is coefficientwise divisible
            # by 14 after t=t0+14*s.  Divide exactly to recover w mod 15.
            q11_lifted = affine_substitute_mod(
                q11_mod_210, t_residue, 14, 14 * 15
            )
            w_mod_15 = exact_quotient_coefficients_mod(
                q11_lifted, divisor=14, quotient_modulus=15
            )
            w_values = residue_table(w_mod_15, range(15), 15)
            assert set(w_values) == EXPECTED_IMAGE_VALUES
            assert w_values.count(0) == 9
            assert w_values.count(3) == 6

            multipliers = [
                (182 * w * w + 12 * w + 1) % 15 for w in w_values
            ]
            payments = [math.gcd(multiplier * multiplier, 15) for multiplier in multipliers]
            assert set(payments) == {1, 5}
            assert all(
                payment == (1 if w == 0 else 5)
                for w, payment in zip(w_values, payments, strict=True)
            )

            positive_s_classes = [
                s for s, w in enumerate(w_values) if w == 3
            ]
            continuing_s_classes = [
                s for s, w in enumerate(w_values) if w == 0
            ]
            positive_k_classes.extend(
                (source_residue + 13 * (t_residue + 14 * s)) % BRANCH_MODULUS
                for s in positive_s_classes
            )
            continuing_k_classes.extend(
                (source_residue + 13 * (t_residue + 14 * s)) % BRANCH_MODULUS
                for s in continuing_s_classes
            )
            rows.append(
                {
                    "source_class_mod_13": source_residue,
                    "payment_one_t_class_mod_14": t_residue,
                    "parameterization": (
                        f"k={source_residue}+13*({t_residue}+14*s)"
                    ),
                    "w_mod_15_by_s_mod_15": w_values,
                    "height_fourteen_payment_by_s_mod_15": payments,
                    "positive_switch_s_classes_mod_15": positive_s_classes,
                    "height_sixteen_survivor_s_classes_mod_15": continuing_s_classes,
                }
            )

    positive_k_classes.sort()
    continuing_k_classes.sort()
    assert len(rows) == 40
    assert len(positive_k_classes) == len(set(positive_k_classes)) == 240
    assert len(continuing_k_classes) == len(set(continuing_k_classes)) == 360
    assert not set(positive_k_classes) & set(continuing_k_classes)
    return {
        "source_cylinder_count_mod_182": 40,
        "refinement_modulus": BRANCH_MODULUS,
        "refined_negative_cylinder_count": 600,
        "actual_w_image_mod_15": sorted(EXPECTED_IMAGE_VALUES),
        "full_payment_fifteen_class_count": 0,
        "positive_switch_class_count": len(positive_k_classes),
        "height_sixteen_survivor_class_count": len(continuing_k_classes),
        "positive_switch_k_classes_mod_2730": positive_k_classes,
        "height_sixteen_survivor_k_classes_mod_2730": continuing_k_classes,
        "rows": rows,
    }


def symbolic_transition_certificate() -> dict[str, Any]:
    positive_samples: list[dict[str, int]] = []
    for z in [-5, -1, 0, 1, 7]:
        w = 15 * z + 3
        b = 182 * w * w + 12 * w + 1
        d = 2730 * z * z + 1104 * z + 111
        c = 3 * d + 2
        assert b == 5 * c
        v3 = 5 * c * (14 * c - 3)
        q3 = 210 * d * d + 265 * d + 83
        assert v3 == 3 * q3 + 1
        positive_samples.append({"z": z, "w": w, "payment": 5, "error_at_3": 1})

    survivor_samples: list[dict[str, int]] = []
    for c in [-6, -1, 0, 1, 8]:
        w = 15 * c
        m = 2730 * c * c + 12 * c
        b = 182 * w * w + 12 * w + 1
        d = 210 * m * m + 13 * m + 1
        assert b == 15 * m + 1
        assert d % 2 == 1
        assert math.gcd(d * d, 16) == 1
        assert d * d % 16 == 1
        survivor_samples.append(
            {
                "c": c,
                "w": w,
                "height_fourteen_payment": 1,
                "height_fifteen_payment": 1,
                "error_at_16": -1,
            }
        )

    return {
        "height_fourteen_input": "A=q11+1=14*w+1",
        "height_fourteen_multiplier": "B=q14+1=182*w^2+12*w+1",
        "positive_switch_branch": {
            "condition": "w=15*z+3",
            "payment": 5,
            "transition": (
                "write B=5*C with C=3*d+2; then "
                "v3=5*C*(14*C-3)=3*(210*d^2+265*d+83)+1"
            ),
            "conclusion": "the height-three centered error is +1",
            "lean_declaration": (
                "ErdosProblems.Erdos243."
                "paymentOneHeightFourteen_positiveSwitchIdentity"
            ),
            "regression_samples": positive_samples,
        },
        "survivor_branch": {
            "condition": "w=15*c",
            "height_fourteen_payment": 1,
            "height_fifteen_multiplier": (
                "D=210*m^2+13*m+1 with m=2730*c^2+12*c even"
            ),
            "height_fifteen_payment": 1,
            "height_sixteen_error": (
                "-1 because D^2=1 mod 16; for even c, D=8*x+1, "
                "and for odd c, D=8*x-1"
            ),
            "lean_declarations": [
                "ErdosProblems.Erdos243.paymentOneHeightSixteen_evenLiftSquare",
                "ErdosProblems.Erdos243.paymentOneHeightSixteen_oddLiftSquare",
            ],
            "regression_samples": survivor_samples,
        },
    }


def replay_examples(split: dict[str, Any]) -> list[dict[str, Any]]:
    examples: list[dict[str, Any]] = []
    chosen = [
        (split["positive_switch_k_classes_mod_2730"][0], "positive_switch"),
        (split["height_sixteen_survivor_k_classes_mod_2730"][0], "height_sixteen"),
    ]
    for parameter, expected in chosen:
        quotient = BASE_QUOTIENT + FAMILY_PERIOD * parameter
        u, v = 11, 11 * quotient - 1
        for _ in range(9):
            step = reduced_step(u, v)
            u, v = step["u_next"], step["v_next"]

        rows: list[dict[str, int | bool]] = []
        for _ in range(6):
            step = centered_step_allow_tie(u, v)
            rows.append({key: value for key, value in step.items() if key != "v_next"})
            u, v = int(step["next_height"]), int(step["v_next"])
            if expected == "positive_switch" and rows[-1]["centered_error"] > 0:
                break
            if expected == "height_sixteen" and rows[-1]["height"] == 16:
                break
        assert rows[-1]["centered_error"] == (1 if expected == "positive_switch" else -1)
        assert rows[-1]["height"] == (3 if expected == "positive_switch" else 16)
        examples.append({"parameter": parameter, "expected": expected, "rows": rows})
    return examples


def build_receipt() -> dict[str, Any]:
    _, q10 = source_quotient_polynomials()
    split = height_fourteen_split_certificate(q10)
    symbolic = symbolic_transition_certificate()
    replays = replay_examples(split)

    previous_zero = 2232 * 15
    previous_positive = 182 * 15
    new_positive = split["positive_switch_class_count"] * 17
    survivors = split["height_sixteen_survivor_class_count"] * 17
    total_positive = previous_positive + new_positive
    assert (previous_zero, total_positive, survivors) == (33480, 6810, 6120)
    assert previous_zero + total_positive + survivors == COMMON_MODULUS

    contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Under a_(n+1)/a_n^2 -> 1 and rational reciprocal sum, force "
            "eventual Sylvester recurrence."
        ),
        claim_ceiling=(
            "Exact elimination of the height-14 payment-five submode and exact "
            "isolation of the surviving height-16 negative-unit cylinders; the "
            "height-16 branch and unrestricted #243 remain open."
        ),
        hypothesis_id="payment_one_height_fourteen_supports_uniform_negative_expansion",
        hypothesis_statement=(
            "The remaining payment-one height-14 cylinders can continue as one "
            "undifferentiated expanding negative boundary mode."
        ),
        probe_id="height_fourteen_exact_quotient_image_mod_15",
        probe_question=(
            "What is the actual image of q11/14 modulo 15, and does its payment "
            "split force either a cofinal collapse or a centered sign switch?"
        ),
        computation=(
            "Recover q11 modulo 210 from the degree-1024 source polynomial by "
            "composite-modulus exact division; on each of 40 payment-one source "
            "cylinders divide q11(t0+14*s) by 14 modulo 15, classify all 600 "
            "residue lifts, and prove both resulting transitions symbolically."
        ),
        falsifier=(
            "An exact image restriction and transition identity that removes a "
            "nonempty fraction of the cylinders from negative support."
        ),
        stop_condition=(
            "Stop at the first exact sign-switch/collapse partition and isolate "
            "the next negative branch; do not replace it with a longer-horizon audit."
        ),
        survival_consequence=(
            "If all image classes retained centered error -1, height 14 would "
            "remain a viable homogeneous boundary-expansion mechanism."
        ),
        falsification_consequence=(
            "The actual image is {0,3}: 240 refined cylinders switch to centered "
            "+1 at height 3, while exactly 360 reach height 16 with error -1. "
            "The cumulative modulus-46410 partition is 33480 zero, 6810 positive, "
            "and 6120 continuing-negative candidates."
        ),
        consumer_ref=LEAN_REF,
        consumer_declarations=[
            "ErdosProblems.Erdos243.paymentOneHeightFourteen_positiveSwitchIdentity",
            "ErdosProblems.Erdos243.paymentOneHeightSixteen_evenLiftSquare",
            "ErdosProblems.Erdos243.paymentOneHeightSixteen_oddLiftSquare",
        ],
        analysis_refs=[NOTE_REF, PACKET_REF, SECOND_SPLIT_REF, PAYMENT_SEVEN_REF, LIBRARY_REF],
        source_refs=[SCRIPT_REF, SECOND_SPLIT_REF, PAYMENT_SEVEN_REF, LIBRARY_REF, LEAN_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "The 40 payment-one cylinders refine into 600 classes modulo 2730. "
            "The actual quotient image w mod 15 is only {0,3}; all 240 w=3 "
            "classes pay five and switch positive at height 3, while all 360 "
            "w=0 classes pay one twice and reach height 16 with error -1."
        ),
        progress_class="one_way_theorem",
        decision_basis=(
            "The modular polynomial certificate quantifies over every lift; the "
            "symbolic identities prove the sign switch and surviving error "
            "without representative-horizon inference."
        ),
        next_analytic_target=(
            "Discard the height-14 payment-five classes.  On the exact surviving "
            "classes, classify the height-16 multiplier modulo 17 and stop at a "
            "full payment, sign switch, or new finite mechanism split."
        ),
        resource_bounds={
            "source_polynomial_degree": 1024,
            "payment_one_source_cylinders": 40,
            "residue_lifts_per_cylinder": 15,
            "refined_cylinders": 600,
            "representative_replays": len(replays),
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos243-payment-one-height14-receipt/1",
        "status": "verified_exact_sign_switch_and_survivor_split",
        "height_fourteen_split_certificate": split,
        "symbolic_transition_certificate": symbolic,
        "regression_replays": replays,
        "cumulative_source_class_partition": {
            "common_modulus": COMMON_MODULUS,
            "zero_centered_class_count": previous_zero,
            "positive_centered_class_count": total_positive,
            "continuing_negative_candidate_class_count": survivors,
            "exact_partition": "33480 zero + 6810 positive + 6120 negative = 46410",
        },
        "experiment_contract": contract,
        "consequence_reconciliation": {
            "height_fourteen_payment_five_mode": {
                "decision": "update_now",
                "reason": "all 240 refined cylinders have an exact positive sign switch",
                "authority_surface": PACKET_REF,
            },
            "height_sixteen_negative_unit_branch": {
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
            for ref in [SCRIPT_REF, SECOND_SPLIT_REF, PAYMENT_SEVEN_REF, LIBRARY_REF, LEAN_REF, NOTE_REF, PACKET_REF]
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
