#!/usr/bin/env python3
"""Certify the #243 height-20 payment-seven mechanism is terminal.

The height-19 certificate leaves 506880 payment-one source classes modulo
35271600.  The next higher-lift coordinate is affine modulo 21: evaluating
lift zero and lift one determines all 21 lifts of every source class.  A
second affine evaluation modulo five recovers the next digit on precisely the
payment-seven branch by CRT, without evaluating the degree-1024 polynomial on
all ten million refined classes.

The complete height-20 payment image is {1,7}.  Every payment-seven class is
terminal: two factor-five digits collapse at height four, one switches
positive at height five, and the other two follow the exact cascade

    20 --7--> 3 --1--> 4 --1--> 5 --3--> 2 --3--> 1.

Thus only the payment-one classes reach height 21 with centered error -1.
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
from system.lib.formal_math_residue_cylinder import (  # noqa: E402
    affine_lift_coordinates_mod,
)

from check_erdos243_forced_excursion_split import (  # noqa: E402
    source_quotient_polynomials,
)
from check_erdos243_height19_payment_five_cascade import (  # noqa: E402
    HEIGHT_EIGHTEEN_MODULUS,
    HEIGHT_SEVENTEEN_MODULUS,
    Y_POLYNOMIAL_EXACT,
)


SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_height20_payment_seven_cascade.py"
)
HEIGHT_NINETEEN_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_height19_payment_five_cascade.py"
)
HEIGHT_EIGHTEEN_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos243_height17_mod4_receipt.json"
)
HEIGHT_NINETEEN_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos243_height19_payment_five_cascade_receipt.json"
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
RESIDUE_CYLINDER_REF = "system/lib/formal_math_residue_cylinder.py"
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "erdos243_height20_payment_seven_cascade_receipt.json"
)

HEIGHT_NINETEEN_MODULUS = HEIGHT_EIGHTEEN_MODULUS * 10
COMMON_MODULUS = HEIGHT_NINETEEN_MODULUS * 21
PAYMENT_ONE_T_CLASSES = {0, 4, 6}
EXPECTED_SLOPE_COUNTS_MOD_21 = {
    0: 101376,
    3: 101376,
    9: 101376,
    12: 101376,
    18: 101376,
}
EXPECTED_SLOPE_COUNTS_MOD_5 = {0: 230400, 2: 138240, 3: 138240}
EXPECTED_P_COUNTS = {0: 3345408, 12: 4866048, 18: 2433024}
EXPECTED_A_COUNTS = {0: 176960, 1: 176953, 2: 1725225, 3: 176949, 4: 176937}


def _exact_quotient_array_mod(
    values: np.ndarray[Any, np.dtype[np.int64]],
    *,
    divisor: int,
    quotient_modulus: int,
) -> np.ndarray[Any, np.dtype[np.int64]]:
    residues = values % (divisor * quotient_modulus)
    assert bool(np.all(residues % divisor == 0))
    return (residues // divisor) % quotient_modulus


def _evaluate_polynomial_many_int64(
    coefficients: list[int],
    parameters: np.ndarray[Any, np.dtype[np.int64]],
    modulus: int,
) -> np.ndarray[Any, np.dtype[np.int64]]:
    assert 12 * modulus * modulus < np.iinfo(np.int64).max
    result = np.zeros(parameters.shape, dtype=np.int64)
    for coefficient in reversed(coefficients):
        result = (result * parameters + (coefficient % modulus)) % modulus
    return result


def _t_values(
    q10: list[int],
    parameters: np.ndarray[Any, np.dtype[np.int64]],
    extra_modulus: int,
) -> np.ndarray[Any, np.dtype[np.int64]]:
    modulus = HEIGHT_NINETEEN_MODULUS * extra_modulus
    q10_values = _evaluate_polynomial_many_int64(q10, parameters, modulus)
    raw_v = ((q10_values + 1) * (12 * q10_values - 1)) % modulus
    q11 = _exact_quotient_array_mod(
        (raw_v + 1) % modulus,
        divisor=13,
        quotient_modulus=14 * 15 * 17 * 4 * 19 * 10 * extra_modulus,
    )
    w = _exact_quotient_array_mod(
        q11,
        divisor=14,
        quotient_modulus=15 * 17 * 4 * 19 * 10 * extra_modulus,
    )
    c = _exact_quotient_array_mod(
        w,
        divisor=15,
        quotient_modulus=17 * 4 * 19 * 10 * extra_modulus,
    )
    d = _exact_quotient_array_mod(
        c,
        divisor=17,
        quotient_modulus=4 * 19 * 10 * extra_modulus,
    )
    e = _exact_quotient_array_mod(
        d, divisor=4, quotient_modulus=19 * 10 * extra_modulus
    )
    return _exact_quotient_array_mod(
        e, divisor=19, quotient_modulus=10 * extra_modulus
    )


def _integer_polynomial_value(coefficients: list[int], value: int) -> int:
    result = 0
    for coefficient in reversed(coefficients):
        result = result * value + coefficient
    return result


def _p_table_mod_105() -> np.ndarray[Any, np.dtype[np.int64]]:
    table = np.zeros((10, 105), dtype=np.int64)
    for t_base in PAYMENT_ONE_T_CLASSES:
        for u in range(105):
            t = t_base + 10 * u
            e = 19 * t
            y = _integer_polynomial_value(Y_POLYNOMIAL_EXACT, e) // 19
            n = 10336 * y * y + 5 * y
            r = 5814 * n * n + 16 * n
            height_nineteen_multiplier = 342 * r * r + 17 * r + 1
            assert (height_nineteen_multiplier - 1) % 20 == 0
            table[t_base, u] = (
                (height_nineteen_multiplier - 1) // 20
            ) % 105
    return table


def _base_classes_mod_3527160(
    height_eighteen_receipt: dict[str, Any]
) -> np.ndarray[Any, np.dtype[np.int64]]:
    base_mod_185640 = np.array(
        height_eighteen_receipt["height_seventeen_rigidity_certificate"][
            "height_eighteen_survivor_k_classes_mod_185640"
        ],
        dtype=np.int64,
    )
    negative_mod_19 = height_eighteen_receipt["height_eighteen_mod19_certificate"][
        "continuing_negative_k_classes_mod_19"
    ]
    inverse_stride = pow(HEIGHT_SEVENTEEN_MODULUS, -1, 19)
    classes = []
    for residue in negative_mod_19:
        lift = ((residue - base_mod_185640) % 19 * inverse_stride) % 19
        classes.append(base_mod_185640 + HEIGHT_SEVENTEEN_MODULUS * lift)
    result = np.concatenate(classes)
    assert result.size == 69120 and np.unique(result).size == result.size
    return result


def _count_map(values: np.ndarray[Any, np.dtype[np.int64]]) -> dict[int, int]:
    unique, counts = np.unique(values, return_counts=True)
    return {
        int(key): int(value)
        for key, value in zip(unique, counts, strict=True)
    }


def complete_affine_height_twenty_cylinder(
    q10: list[int], base_mod_3527160: np.ndarray[Any, np.dtype[np.int64]]
) -> dict[str, Any]:
    parameters_mod_35271600 = (
        base_mod_3527160[:, None]
        + HEIGHT_EIGHTEEN_MODULUS * np.arange(10, dtype=np.int64)[None, :]
    ).reshape(-1)
    t_base_all = _t_values(q10, parameters_mod_35271600, 1)
    keep = np.isin(t_base_all, list(PAYMENT_ONE_T_CLASSES))
    source_classes = parameters_mod_35271600[keep]
    t_base = t_base_all[keep]
    assert source_classes.size == 506880

    def affine_coordinates(modulus: int) -> tuple[np.ndarray[Any, np.dtype[np.int64]], np.ndarray[Any, np.dtype[np.int64]]]:
        stacked = np.concatenate(
            [source_classes, source_classes + HEIGHT_NINETEEN_MODULUS]
        )
        lifted_t = _t_values(q10, stacked, modulus)
        count = source_classes.size
        u_zero = ((lifted_t[:count] - t_base) // 10) % modulus
        u_one = ((lifted_t[count:] - t_base) // 10) % modulus
        return affine_lift_coordinates_mod(u_zero, u_one, modulus=modulus)

    u21, slope21 = affine_coordinates(21)
    u5, slope5 = affine_coordinates(5)
    assert _count_map(slope21) == EXPECTED_SLOPE_COUNTS_MOD_21
    assert _count_map(slope5) == EXPECTED_SLOPE_COUNTS_MOD_5

    p_table = _p_table_mod_105()
    p_counts = {0: 0, 12: 0, 18: 0}
    a_counts = {key: 0 for key in range(5)}
    payment_one_count = 0
    payment_seven_count = 0
    digests = {
        "payment_one": hashlib.sha256(),
        "payment_seven": hashlib.sha256(),
    }

    for lift in range(21):
        coordinate21 = (u21 + slope21 * lift) % 21
        coordinate5 = (u5 + slope5 * lift) % 5
        coordinate105 = coordinate21 + 21 * ((coordinate5 - coordinate21) % 5)
        p = p_table[t_base, coordinate105]
        p_mod_21 = p % 21
        for residue in p_counts:
            p_counts[residue] += int(np.sum(p_mod_21 == residue))

        parameter_classes = source_classes + HEIGHT_NINETEEN_MODULUS * lift
        payment_seven_mask = p_mod_21 == 18
        payment_one_mask = ~payment_seven_mask
        payment_seven_count += int(np.sum(payment_seven_mask))
        payment_one_count += int(np.sum(payment_one_mask))
        a = ((p[payment_seven_mask] - 18) // 21) % 5
        for residue, count in _count_map(a).items():
            a_counts[residue] += count
        for name, mask in [
            ("payment_one", payment_one_mask),
            ("payment_seven", payment_seven_mask),
        ]:
            for value in parameter_classes[mask]:
                digests[name].update(str(int(value)).encode("ascii"))
                digests[name].update(b"\n")

    assert p_counts == EXPECTED_P_COUNTS
    assert a_counts == EXPECTED_A_COUNTS
    assert payment_one_count == 8211456
    assert payment_seven_count == 2433024
    assert payment_one_count + payment_seven_count == source_classes.size * 21
    return {
        "input_class_count_mod_35271600": int(source_classes.size),
        "refinement_modulus": COMMON_MODULUS,
        "affine_lifts_per_source_class": 21,
        "complete_refined_class_count": int(source_classes.size * 21),
        "affine_slope_counts_mod_21": {
            str(key): value for key, value in sorted(EXPECTED_SLOPE_COUNTS_MOD_21.items())
        },
        "affine_slope_counts_mod_5": {
            str(key): value for key, value in sorted(EXPECTED_SLOPE_COUNTS_MOD_5.items())
        },
        "height_twenty_parameter_counts_mod_21": {
            str(key): value for key, value in sorted(p_counts.items())
        },
        "height_twenty_payment_image": [1, 7],
        "payment_one_class_count": payment_one_count,
        "payment_seven_class_count": payment_seven_count,
        "payment_seven_next_digit_counts_mod_5": {
            str(key): value for key, value in sorted(a_counts.items())
        },
        "payment_one_traversal_sha256": digests["payment_one"].hexdigest(),
        "payment_seven_traversal_sha256": digests["payment_seven"].hexdigest(),
        "affine_compression": {
            "full_classes_classified": int(source_classes.size * 21),
            "degree_1024_evaluations_per_source_class": 5,
            "method": (
                "lift zero and one modulo 21 and 5 determine the affine higher "
                "coordinate; CRT expands all 21 lifts without new polynomial evaluations"
            ),
            "shared_primitive": (
                "system.lib.formal_math_residue_cylinder."
                "affine_lift_coordinates_mod"
            ),
            "exactness": "bounded numpy.int64 modular arithmetic only",
        },
    }


def symbolic_payment_seven_cascade() -> dict[str, Any]:
    outcomes = {
        0: "height_four_full_payment_five",
        1: "height_four_full_payment_five",
        2: "height_five_to_height_two_to_height_one",
        3: "height_five_positive_switch",
        4: "height_five_to_height_two_to_height_one",
    }
    for digit, expected in outcomes.items():
        for lift in range(30):
            a = 5 * lift + digit
            p = 21 * a + 18
            k = 380 * p * p + 18 * p + 1
            assert math.gcd(k * k, 21) == 7
            w = k // 7
            assert w % 6 == 1
            c = (w - 1) // 6
            j = 1680 * c * c + 518 * c + 41
            v3 = 7 * w * (20 * w - 3)
            assert v3 == 3 * (j - 1) - 1
            assert math.gcd(j * j, 4) == 1
            v4 = j * (3 * j - 4)
            q = (v4 + 5) // 4
            assert v4 == 4 * (q - 1) - 1
            payment_four = math.gcd(q * q, 5)
            if digit in {0, 1}:
                assert payment_four == 5
                continue
            assert payment_four == 1
            v5 = q * (4 * q - 5)
            residue5 = v5 % 5
            error5 = residue5 if residue5 <= 2 else residue5 - 5
            if digit == 3:
                assert error5 == 1 and expected == "height_five_positive_switch"
                continue
            assert error5 == -1
            r = (v5 + 6) // 5
            assert r % 6 == 3 and math.gcd(r * r, 6) == 3
            v2 = r * (5 * r - 6) // 3
            assert v2 % 2 == 1
            s = (v2 + 3) // 2
            assert s % 3 == 0 and math.gcd(s * s, 3) == 3
    return {
        "input": "height-20 payment seven with p=21*a+18",
        "universal_prefix": {
            "states": ["(20,-1)", "(3,-1)", "(4,-1)"],
            "payments": [7, 1],
        },
        "next_digit_outcomes_mod_5": {
            "0": outcomes[0],
            "1": outcomes[1],
            "2": outcomes[2],
            "3": outcomes[3],
            "4": outcomes[4],
        },
        "late_collapse_cascade": {
            "digits": [2, 4],
            "states": ["(20,-1)", "(3,-1)", "(4,-1)", "(5,-1)", "(2,-1 tie)", "(1,0 forever)"],
            "payments": [7, 1, 1, 3, 3],
        },
        "complete_residue_check_lifts_per_digit": 30,
        "lean_declarations": [
            "ErdosProblems.Erdos243.heightTwentyPaymentSeven_heightThreeIdentity",
            "ErdosProblems.Erdos243.heightTwentyPaymentSeven_positiveSwitchIdentity",
            "ErdosProblems.Erdos243.heightTwentyPaymentSeven_heightFiveToHeightTwoIdentity",
            "ErdosProblems.Erdos243.heightTwentyPaymentSeven_finalFullPayment",
            "ErdosProblems.Erdos243.heightTwentyPaymentSeven_finalCollapse",
        ],
    }


def build_receipt() -> dict[str, Any]:
    height_eighteen = json.loads(
        (REPO_ROOT / HEIGHT_EIGHTEEN_RECEIPT_REF).read_text(encoding="utf-8")
    )
    height_nineteen = json.loads(
        (REPO_ROOT / HEIGHT_NINETEEN_RECEIPT_REF).read_text(encoding="utf-8")
    )
    assert height_nineteen["status"] == "verified_exact_payment_five_cofinal_return"
    base_classes = _base_classes_mod_3527160(height_eighteen)
    _, q10 = source_quotient_polynomials()
    cylinder = complete_affine_height_twenty_cylinder(q10, base_classes)
    cascade = symbolic_payment_seven_cascade()

    immediate_zero = EXPECTED_A_COUNTS[0] + EXPECTED_A_COUNTS[1]
    late_zero = EXPECTED_A_COUNTS[2] + EXPECTED_A_COUNTS[4]
    new_zero = immediate_zero + late_zero
    new_positive = EXPECTED_A_COUNTS[3]
    assert (immediate_zero, late_zero, new_zero, new_positive) == (
        353913,
        1902162,
        2256075,
        176949,
    )
    zero = 27673920 * 21 + new_zero
    positive = 7090800 * 21 + new_positive
    negative = cylinder["payment_one_class_count"]
    assert (zero, positive, negative) == (583408395, 149083749, 8211456)
    assert zero + positive + negative == COMMON_MODULUS

    contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Under a_(n+1)/a_n^2 -> 1 and rational reciprocal sum, force "
            "eventual Sylvester recurrence."
        ),
        claim_ceiling=(
            "Exact elimination of all 2433024 height-20 payment-seven classes by "
            "cofinal return or positive switch; 8211456 height-21 negative-unit "
            "classes and unrestricted #243 remain open."
        ),
        hypothesis_id="height_twenty_payment_seven_supports_low_height_expansion",
        hypothesis_statement=(
            "A payment-seven height-20 cylinder can survive its induced low-height "
            "cascade and retain negative support."
        ),
        probe_id="affine_mod21_mod5_cylinder_and_low_height_cascade",
        probe_question=(
            "What payments occur at height 20, and does the next factor-five digit "
            "force collapse or a sign switch on every payment-seven class?"
        ),
        computation=(
            "Use lift-zero/lift-one exact evaluations modulo 21 and 5 to determine "
            "the affine higher coordinate for all 10644480 refined classes; combine "
            "by CRT, classify the payment-seven next digit, and verify every low-height "
            "cascade symbolically on complete residue periods."
        ),
        falsifier=(
            "A complete exact partition showing no payment-seven class retains "
            "negative support after the forced low-height cascade."
        ),
        stop_condition=(
            "Stop when every payment-seven next digit has a cofinal-return or "
            "positive-switch certificate; do not audit the payment-one height-21 branch."
        ),
        survival_consequence=(
            "Any surviving factor-five digit would open a distinct recurrent "
            "low-height mechanism requiring further source refinement."
        ),
        falsification_consequence=(
            "All 2433024 payment-seven classes are terminal for negative support: "
            "2256075 return cofinally and 176949 switch positive. Only 8211456 "
            "payment-one classes reach height 21 with error -1."
        ),
        consumer_ref=LEAN_REF,
        consumer_declarations=cascade["lean_declarations"],
        analysis_refs=[NOTE_REF, PACKET_REF, HEIGHT_NINETEEN_REF, HEIGHT_NINETEEN_RECEIPT_REF],
        source_refs=[SCRIPT_REF, RESIDUE_CYLINDER_REF, HEIGHT_NINETEEN_REF, HEIGHT_EIGHTEEN_RECEIPT_REF, HEIGHT_NINETEEN_RECEIPT_REF, LEAN_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "The complete height-20 payment image is {1,7}. Every payment-seven "
            "class either pays five at height four, switches positive at height "
            "five, or follows the forced 20->3->4->5->2->1 cofinal cascade."
        ),
        progress_class="one_way_theorem",
        decision_basis=(
            "Affine two-lift certificates plus CRT cover all 10644480 source "
            "classes, while complete modular cascade checks remove any horizon inference."
        ),
        next_analytic_target=(
            "Discard every payment-seven class. Restrict the next exact probe to "
            "the 8211456 payment-one height-21 cylinders."
        ),
        resource_bounds={
            "source_polynomial_degree": 1024,
            "input_base_classes": cylinder["input_class_count_mod_35271600"],
            "affine_lifts_per_class": 21,
            "classified_residue_cylinders": cylinder["complete_refined_class_count"],
            "degree_1024_evaluations_per_class": 5,
            "cascade_residue_checks": 150,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos243-height20-payment-seven-cascade-receipt/1",
        "status": "verified_exact_payment_seven_mode_elimination",
        "complete_affine_height_twenty_cylinder": cylinder,
        "symbolic_payment_seven_cascade": cascade,
        "payment_seven_outcome_counts": {
            "immediate_height_four_cofinal_return": immediate_zero,
            "late_height_two_cofinal_return": late_zero,
            "total_cofinal_return": new_zero,
            "positive_switch": new_positive,
            "continuing_negative": 0,
        },
        "cumulative_source_class_partition": {
            "common_modulus": COMMON_MODULUS,
            "zero_centered_class_count": zero,
            "positive_centered_class_count": positive,
            "continuing_negative_candidate_class_count": negative,
            "exact_partition": (
                "583408395 zero + 149083749 positive + 8211456 negative = 740703600"
            ),
        },
        "experiment_contract": contract,
        "consequence_reconciliation": {
            "height_twenty_payment_seven_mode": {
                "decision": "update_now",
                "reason": "every exact cylinder has cofinal return or positive switch",
                "authority_surface": PACKET_REF,
            },
            "height_twenty_one_payment_one_branch": {
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
            for ref in [SCRIPT_REF, RESIDUE_CYLINDER_REF, HEIGHT_NINETEEN_REF, HEIGHT_EIGHTEEN_RECEIPT_REF, HEIGHT_NINETEEN_RECEIPT_REF, LEAN_REF, NOTE_REF, PACKET_REF]
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
