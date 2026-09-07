#!/usr/bin/env python3
"""Certify the #243 height-19 payment-five cofinal-return cascade.

The height-18 split leaves 69120 multiplier-one source classes modulo
3527160.  Refining each class by ten requires 691200 exact polynomial
evaluations.  The checker uses bounded NumPy int64 Horner evaluation after
reducing every coefficient modulo 35271600; explicit bounds prove that every
pre-reduction product stays below 2^63, so this is exact integer arithmetic,
not floating point or a probabilistic acceleration.

The source image has only even next parameters modulo ten.  Classes 2 and 8
pay five at height 19, land at height four with centered error -1, and then
pay the full factor five.  Classes 0, 4, and 6 pay one and reach height 20
with centered error -1.  Full payment 20 and payment four never occur.
"""

from __future__ import annotations

import argparse
import hashlib
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

from check_erdos243_forced_excursion_split import (  # noqa: E402
    source_quotient_polynomials,
)


SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_height19_payment_five_cascade.py"
)
HEIGHT_EIGHTEEN_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_height17_mod4.py"
)
HEIGHT_EIGHTEEN_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos243_height17_mod4_receipt.json"
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
    "erdos243_height19_payment_five_cascade_receipt.json"
)

HEIGHT_SEVENTEEN_MODULUS = 13 * 14 * 15 * 17 * 4
HEIGHT_EIGHTEEN_MODULUS = HEIGHT_SEVENTEEN_MODULUS * 19
COMMON_MODULUS = HEIGHT_EIGHTEEN_MODULUS * 10
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
EXPECTED_T_COUNTS = {0: 322560, 2: 92160, 4: 92160, 6: 92160, 8: 92160}
PAYMENT_FIVE_T_CLASSES = {2, 8}
PAYMENT_ONE_T_CLASSES = {0, 4, 6}


def _exact_quotient_array_mod(
    values: np.ndarray[Any, np.dtype[np.int64]],
    *,
    divisor: int,
    quotient_modulus: int,
) -> np.ndarray[Any, np.dtype[np.int64]]:
    composite_modulus = divisor * quotient_modulus
    residues = values % composite_modulus
    assert bool(np.all(residues % divisor == 0))
    return (residues // divisor) % quotient_modulus


def _evaluate_polynomial_many_int64(
    coefficients: list[int],
    parameters: np.ndarray[Any, np.dtype[np.int64]],
    modulus: int,
) -> np.ndarray[Any, np.dtype[np.int64]]:
    # Horner's pre-modulus product is below modulus^2+modulus.  The caller's
    # nonlinear transition has the larger bound recorded in the receipt.
    assert modulus * modulus + modulus < np.iinfo(np.int64).max
    result = np.zeros(parameters.shape, dtype=np.int64)
    for coefficient in reversed(coefficients):
        result = (result * parameters + (coefficient % modulus)) % modulus
    return result


def _digest_classes(classes: np.ndarray[Any, np.dtype[np.int64]]) -> str:
    digest = hashlib.sha256()
    for value in np.sort(classes):
        digest.update(str(int(value)).encode("ascii"))
        digest.update(b"\n")
    return digest.hexdigest()


def _height_eighteen_base_classes(receipt: dict[str, Any]) -> np.ndarray[Any, np.dtype[np.int64]]:
    base_mod_185640 = np.array(
        receipt["height_seventeen_rigidity_certificate"][
            "height_eighteen_survivor_k_classes_mod_185640"
        ],
        dtype=np.int64,
    )
    negative_mod_19 = receipt["height_eighteen_mod19_certificate"][
        "continuing_negative_k_classes_mod_19"
    ]
    inverse_stride = pow(HEIGHT_SEVENTEEN_MODULUS, -1, 19)
    classes = []
    for residue in negative_mod_19:
        lift = ((residue - base_mod_185640) % 19 * inverse_stride) % 19
        classes.append(base_mod_185640 + HEIGHT_SEVENTEEN_MODULUS * lift)
    result = np.concatenate(classes)
    assert result.size == 69120
    assert np.unique(result).size == result.size
    return result


def complete_height_nineteen_cylinder(
    q10: list[int], base_classes: np.ndarray[Any, np.dtype[np.int64]]
) -> dict[str, Any]:
    lifts = np.arange(10, dtype=np.int64)
    parameters = (
        base_classes[:, None] + HEIGHT_EIGHTEEN_MODULUS * lifts[None, :]
    ).reshape(-1)
    assert parameters.size == 691200
    assert np.unique(parameters).size == parameters.size
    assert int(parameters.min()) >= 0 and int(parameters.max()) < COMMON_MODULUS

    q10_values = _evaluate_polynomial_many_int64(q10, parameters, COMMON_MODULUS)
    nonlinear_bound = 12 * COMMON_MODULUS * COMMON_MODULUS
    assert nonlinear_bound < np.iinfo(np.int64).max
    raw_v = ((q10_values + 1) * (12 * q10_values - 1)) % COMMON_MODULUS
    q11 = _exact_quotient_array_mod(
        (raw_v + 1) % COMMON_MODULUS,
        divisor=13,
        quotient_modulus=14 * 15 * 17 * 4 * 19 * 10,
    )
    w = _exact_quotient_array_mod(
        q11, divisor=14, quotient_modulus=15 * 17 * 4 * 19 * 10
    )
    c = _exact_quotient_array_mod(
        w, divisor=15, quotient_modulus=17 * 4 * 19 * 10
    )
    d = _exact_quotient_array_mod(
        c, divisor=17, quotient_modulus=4 * 19 * 10
    )
    e = _exact_quotient_array_mod(
        d, divisor=4, quotient_modulus=19 * 10
    )
    t = _exact_quotient_array_mod(e, divisor=19, quotient_modulus=10)

    y = _evaluate_polynomial_many_int64(
        Y_POLYNOMIAL_EXACT, e, 19 * 10
    )
    s = _exact_quotient_array_mod(y, divisor=19, quotient_modulus=10)
    assert bool(np.all(s == t))

    n = (10336 * s * s + 5 * s) % 10
    r = (5814 * n * n + 16 * n) % 10
    multiplier = (342 * r * r + 17 * r + 1) % 20
    payment = np.gcd(multiplier * multiplier, 20)

    unique_t, t_counts_array = np.unique(t, return_counts=True)
    t_counts = {
        int(key): int(value)
        for key, value in zip(unique_t, t_counts_array, strict=True)
    }
    assert t_counts == EXPECTED_T_COUNTS
    assert set(np.unique(s).tolist()) == set(EXPECTED_T_COUNTS)
    assert set(np.unique(r).tolist()) == {0, 8}
    assert set(np.unique(multiplier).tolist()) == {1, 5}
    assert set(np.unique(payment).tolist()) == {1, 5}

    payment_five_mask = payment == 5
    payment_one_mask = payment == 1
    assert bool(np.all(np.isin(t[payment_five_mask], list(PAYMENT_FIVE_T_CLASSES))))
    assert bool(np.all(np.isin(t[payment_one_mask], list(PAYMENT_ONE_T_CLASSES))))
    assert int(np.sum(payment_five_mask)) == 184320
    assert int(np.sum(payment_one_mask)) == 506880

    return {
        "input_class_count_mod_3527160": int(base_classes.size),
        "refinement_modulus": COMMON_MODULUS,
        "complete_refined_class_count": int(parameters.size),
        "actual_t_image_mod_10": sorted(t_counts),
        "t_class_counts": {str(key): value for key, value in sorted(t_counts.items())},
        "s_equals_t_mod_10_on_all_classes": True,
        "height_nineteen_multiplier_image_mod_20": [1, 5],
        "payment_image": [1, 5],
        "payment_five_t_classes_mod_10": sorted(PAYMENT_FIVE_T_CLASSES),
        "payment_one_t_classes_mod_10": sorted(PAYMENT_ONE_T_CLASSES),
        "payment_five_class_count": int(np.sum(payment_five_mask)),
        "payment_one_class_count": int(np.sum(payment_one_mask)),
        "payment_five_class_sha256": _digest_classes(parameters[payment_five_mask]),
        "payment_one_class_sha256": _digest_classes(parameters[payment_one_mask]),
        "payment_twenty_class_count": 0,
        "payment_four_class_count": 0,
        "vector_exactness": {
            "dtype": "numpy.int64",
            "modulus": COMMON_MODULUS,
            "horner_intermediate_bound": COMMON_MODULUS * COMMON_MODULUS + COMMON_MODULUS,
            "nonlinear_transition_intermediate_bound": nonlinear_bound,
            "int64_max": int(np.iinfo(np.int64).max),
            "all_bounds_strict": True,
            "floating_point_operations": 0,
        },
    }


def symbolic_payment_five_cascade() -> dict[str, Any]:
    samples: list[dict[str, int]] = []
    for b in [-7, -1, 0, 1, 9]:
        w = 4 * b + 1
        x = 76 * b * b + 34 * b + 4
        v4 = 5 * w * (19 * w - 4)
        height_four_multiplier = 5 * x
        assert v4 == 4 * (height_four_multiplier - 1) - 1
        assert math.gcd(height_four_multiplier * height_four_multiplier, 5) == 5
        samples.append(
            {
                "b": b,
                "height_nineteen_multiplier_divided_by_five": w,
                "height_four_multiplier_divided_by_five": x,
            }
        )
    return {
        "input": "height-19 multiplier H=5*W with W=4*b+1",
        "height_nineteen_payment": 5,
        "height_four_denominator_identity": (
            "5*W*(19*W-4)=4*(5*(76*b^2+34*b+4)-1)-1"
        ),
        "height_four_centered_error": -1,
        "height_four_multiplier": "5*(76*b^2+34*b+4)",
        "height_four_payment": 5,
        "conclusion": "primitive height one and absorbing centered-zero tail",
        "lean_declarations": [
            "ErdosProblems.Erdos243.paymentFiveHeightNineteen_heightFourIdentity",
            "ErdosProblems.Erdos243.paymentFiveHeightNineteen_finalFullPayment",
            "ErdosProblems.Erdos243.paymentFiveHeightNineteen_finalCollapse",
        ],
        "regression_samples": samples,
    }


def build_receipt() -> dict[str, Any]:
    previous = json.loads(
        (REPO_ROOT / HEIGHT_EIGHTEEN_RECEIPT_REF).read_text(encoding="utf-8")
    )
    assert previous["status"] == (
        "verified_exact_height17_rigidity_and_height18_cofinal_split"
    )
    base_classes = _height_eighteen_base_classes(previous)
    _, q10 = source_quotient_polynomials()
    cylinder = complete_height_nineteen_cylinder(q10, base_classes)
    cascade = symbolic_payment_five_cascade()

    zero = 2748960 * 10 + cylinder["payment_five_class_count"]
    positive = 709080 * 10
    negative = cylinder["payment_one_class_count"]
    assert (zero, positive, negative) == (27673920, 7090800, 506880)
    assert zero + positive + negative == COMMON_MODULUS

    contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Under a_(n+1)/a_n^2 -> 1 and rational reciprocal sum, force "
            "eventual Sylvester recurrence."
        ),
        claim_ceiling=(
            "Exact cofinal return for all 184320 height-19 payment-five classes; "
            "506880 height-20 negative-unit classes and unrestricted #243 remain open."
        ),
        hypothesis_id="height_nineteen_payment_five_supports_negative_expansion",
        hypothesis_statement=(
            "A partial payment five at height 19 can pass through the resulting "
            "height-four state and continue negative support."
        ),
        probe_id="complete_mod10_cylinder_and_height_four_cascade",
        probe_question=(
            "Which height-19 payments occur on the exact source cylinder, and "
            "does the payment-five branch force a later full payment?"
        ),
        computation=(
            "Evaluate all 691200 refined source classes modulo 35271600 with "
            "bounded exact int64 Horner arithmetic, propagate exact quotient "
            "divisions to the height-19 multiplier, and derive the payment-five "
            "height-19 to height-4 to height-1 cascade symbolically."
        ),
        falsifier=(
            "A universal algebraic cascade that sends every nonempty payment-five "
            "source class to primitive height one."
        ),
        stop_condition=(
            "Stop after the complete mod-10 payment partition and terminal proof "
            "for every payment-five class; do not audit the payment-one branch."
        ),
        survival_consequence=(
            "Without the forced height-four full payment, partial payment five "
            "would remain a distinct low-height negative expansion mechanism."
        ),
        falsification_consequence=(
            "All 184320 payment-five classes collapse after one height-four step. "
            "Only 506880 payment-one classes reach height 20 with error -1; the "
            "cumulative modulus-35271600 partition has 27673920 zero, 7090800 "
            "positive, and 506880 negative candidates."
        ),
        consumer_ref=LEAN_REF,
        consumer_declarations=[
            "ErdosProblems.Erdos243.paymentFiveHeightNineteen_heightFourIdentity",
            "ErdosProblems.Erdos243.paymentFiveHeightNineteen_finalFullPayment",
            "ErdosProblems.Erdos243.paymentFiveHeightNineteen_finalCollapse",
        ],
        analysis_refs=[NOTE_REF, PACKET_REF, HEIGHT_EIGHTEEN_REF, HEIGHT_EIGHTEEN_RECEIPT_REF],
        source_refs=[SCRIPT_REF, HEIGHT_EIGHTEEN_REF, HEIGHT_EIGHTEEN_RECEIPT_REF, LEAN_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "The complete source image modulo 10 is {0,2,4,6,8}; classes 2 and "
            "8 pay five at height 19 and then the full factor five at height 4, "
            "so all 184320 such classes reach the absorbing height-one tail."
        ),
        progress_class="one_way_theorem",
        decision_basis=(
            "All 691200 residue classes are evaluated exactly under explicit "
            "int64 bounds; branch digests identify the finite cylinders, and the "
            "symbolic cascade removes all dependence on representative horizons."
        ),
        next_analytic_target=(
            "Discard every payment-five class. Restrict the next exact probe to "
            "the payment-one t mod 10 classes {0,4,6} at height 20."
        ),
        resource_bounds={
            "source_polynomial_degree": 1024,
            "input_base_classes": int(base_classes.size),
            "mod10_lifts_per_base_class": 10,
            "classified_residue_cylinders": cylinder["complete_refined_class_count"],
            "symbolic_cascade_samples": len(cascade["regression_samples"]),
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos243-height19-payment-five-cascade-receipt/1",
        "status": "verified_exact_payment_five_cofinal_return",
        "complete_height_nineteen_cylinder": cylinder,
        "symbolic_payment_five_cascade": cascade,
        "cumulative_source_class_partition": {
            "common_modulus": COMMON_MODULUS,
            "new_payment_five_cofinal_return_class_count": cylinder[
                "payment_five_class_count"
            ],
            "zero_centered_class_count": zero,
            "positive_centered_class_count": positive,
            "continuing_negative_candidate_class_count": negative,
            "exact_partition": (
                "27673920 zero + 7090800 positive + 506880 negative = 35271600"
            ),
        },
        "experiment_contract": contract,
        "consequence_reconciliation": {
            "height_nineteen_payment_five_mode": {
                "decision": "update_now",
                "reason": "all 184320 exact cylinders have a forced cofinal return",
                "authority_surface": PACKET_REF,
            },
            "height_twenty_payment_one_branch": {
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
            for ref in [SCRIPT_REF, HEIGHT_EIGHTEEN_REF, HEIGHT_EIGHTEEN_RECEIPT_REF, LEAN_REF, NOTE_REF, PACKET_REF]
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
