#!/usr/bin/env python3
"""Certify the universal cofinal return of #243 payment-seven cylinders.

The second excursion split leaves sixteen source cylinders whose height-13
negative-unit payment is seven.  Exact quotient propagation modulo 42 proves
that their multiplier is always 7 modulo 42, not merely 7 modulo 14.  This
forces the deterministic cascade

    (u,e) = (13,-1) --h=7--> (2,-1 tie)
                         --h=1--> (3,-1) --h=4--> (1,0 forever).

The residue certificate quantifies over every parameter lift.  Replays cover
the three parameter classes needed modulo 42 and are regression evidence only.
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
from check_erdos243_second_excursion_split import (  # noqa: E402
    NEGATIVE_FOUR_COLLAPSE_K_CLASSES_MOD_221,
    NEGATIVE_FOUR_POSITIVE_FOUR_T_CLASSES,
    NEGATIVE_FOUR_POSITIVE_TWO_T_CLASSES,
    NEGATIVE_UNIT_EXPECTED_VALUES,
    NEGATIVE_UNIT_SOURCE_CLASSES,
)


SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_payment_seven_cascade.py"
)
SECOND_SPLIT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_second_excursion_split.py"
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
    "erdos243_payment_seven_cascade_receipt.json"
)

PAYMENT_SEVEN_T_CLASSES = {
    source_residue: [
        index for index, value in enumerate(values) if value == 7
    ]
    for source_residue, values in NEGATIVE_UNIT_EXPECTED_VALUES.items()
}
PAYMENT_SEVEN_K_CLASSES_MOD_182 = sorted(
    (source_residue + 13 * t_residue) % 182
    for source_residue, t_residues in PAYMENT_SEVEN_T_CLASSES.items()
    for t_residue in t_residues
)
EXPECTED_PAYMENT_SEVEN_K_CLASSES_MOD_182 = [
    16,
    30,
    37,
    51,
    55,
    69,
    76,
    90,
    107,
    121,
    128,
    142,
    146,
    160,
    167,
    181,
]


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


def multiplier_mod_42_certificate(q10: list[int]) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for source_residue in NEGATIVE_UNIT_SOURCE_CLASSES:
        composite_modulus = 13 * 42
        q10_substituted = affine_substitute_mod(
            q10, source_residue, 13, composite_modulus
        )
        raw_v = _height_twelve_raw_denominator_polynomial_mod(
            q10_substituted, composite_modulus
        )
        negative_unit_numerator = polynomial_add_constant_mod(
            raw_v, 1, composite_modulus
        )
        q11_mod_42 = exact_quotient_coefficients_mod(
            negative_unit_numerator, divisor=13, quotient_modulus=42
        )
        multiplier_mod_42 = polynomial_add_constant_mod(q11_mod_42, 1, 42)
        values = residue_table(multiplier_mod_42, range(42), 42)
        payment_seven_t_classes = PAYMENT_SEVEN_T_CLASSES[source_residue]
        lifted_classes = sorted(
            t_residue + 14 * lift
            for t_residue in payment_seven_t_classes
            for lift in range(3)
        )
        assert all(values[index] == 7 for index in lifted_classes)
        rows.append(
            {
                "source_class_mod_13": source_residue,
                "parameterization": f"k={source_residue}+13*t",
                "payment_seven_t_classes_mod_14": payment_seven_t_classes,
                "lifted_t_classes_mod_42": lifted_classes,
                "multiplier_residue_on_lifted_classes": 7,
            }
        )
    assert PAYMENT_SEVEN_K_CLASSES_MOD_182 == EXPECTED_PAYMENT_SEVEN_K_CLASSES_MOD_182
    return {
        "source_rows": rows,
        "universal_terminal_multiplier_class": "a13=q13+1=7 mod 42",
        "payment_seven_k_classes_mod_182": PAYMENT_SEVEN_K_CLASSES_MOD_182,
        "payment_seven_class_count_mod_182": len(PAYMENT_SEVEN_K_CLASSES_MOD_182),
    }


def symbolic_cascade_certificate() -> dict[str, Any]:
    sample_rows: list[dict[str, int]] = []
    for z in [-5, -1, 0, 1, 8]:
        w = 6 * z + 1
        q13 = 42 * z + 6
        a13 = q13 + 1
        v2 = 7 * w * (13 * w - 2)
        m = 546 * z * z + 168 * z + 13
        q2 = 3 * m
        a2 = q2 + 1
        v3 = a2 * v2
        q3 = 6 * m * m + m
        a3 = q3 + 1
        assert a13 == 7 * w
        assert v2 == 6 * m - 1
        assert q2 == (v2 + 1) // 2
        assert math.gcd(a2 * a2, 3) == 1
        assert v3 == 3 * q3 - 1
        assert m % 2 == 1
        assert a3 % 2 == 0
        assert math.gcd(a3 * a3, 4) == 4
        sample_rows.append(
            {
                "z": z,
                "w": w,
                "m": m,
                "height_two_multiplier_mod_3": a2 % 3,
                "height_three_multiplier_mod_2": a3 % 2,
            }
        )
    return {
        "input": "a13=42*z+7=7*w with w=6*z+1",
        "height_thirteen_transition": (
            "h13=7; v2=7*w*(13*w-2)=6*m-1 with "
            "m=546*z^2+168*z+13"
        ),
        "height_two_tie_transition": (
            "q2=3*m, e2=-1, a2=3*m+1=1 mod 3, so h2=1 and u3=3"
        ),
        "height_three_transition": (
            "v3=(3*m+1)*(6*m-1)=3*(6*m^2+m)-1; m is odd, "
            "so a3=6*m^2+m+1 is even, h3=4, and u4=1"
        ),
        "absorbing_conclusion": (
            "primitive height one is an integral tail, so centered error is zero "
            "and remains zero"
        ),
        "lean_declarations": [
            "ErdosProblems.Erdos243.paymentSevenCascade_finalFullPayment",
            "ErdosProblems.Erdos243.paymentSevenCascade_finalCollapse",
        ],
        "regression_samples": sample_rows,
    }


def centered_step_allow_tie(u: int, v: int) -> dict[str, int | bool]:
    if not (0 < u <= v) or math.gcd(u, v) != 1:
        raise ValueError("require a positive reduced rational u/v")
    nearest = (2 * v + u) // (2 * u)
    a = nearest + 1
    e = v - nearest * u
    raw_u = a * u - v
    raw_v = a * v
    payment = math.gcd(raw_u, raw_v)
    return {
        "height": u,
        "centered_error": e,
        "strict_centered": 2 * abs(e) < u,
        "payment": payment,
        "next_height": raw_u // payment,
        "v_next": raw_v // payment,
    }


def replay_cylinder(source_residue: int, t_residue: int, lift: int) -> dict[str, Any]:
    parameter = source_residue + 13 * (t_residue + 14 * lift)
    quotient = BASE_QUOTIENT + FAMILY_PERIOD * parameter
    u = 11
    v = u * quotient - 1
    for _ in range(9):
        step = reduced_step(u, v)
        u, v = step["u_next"], step["v_next"]

    rows: list[dict[str, int | bool]] = []
    for _ in range(3):
        step = centered_step_allow_tie(u, v)
        rows.append({key: value for key, value in step.items() if key != "v_next"})
        u, v = int(step["next_height"]), int(step["v_next"])
    assert rows[-1] == {
        "height": 13,
        "centered_error": -1,
        "strict_centered": True,
        "payment": 7,
        "next_height": 2,
    }

    tie = centered_step_allow_tie(u, v)
    rows.append({key: value for key, value in tie.items() if key != "v_next"})
    u, v = int(tie["next_height"]), int(tie["v_next"])
    final = centered_step_allow_tie(u, v)
    rows.append({key: value for key, value in final.items() if key != "v_next"})
    u, v = int(final["next_height"]), int(final["v_next"])
    absorbing = centered_step_allow_tie(u, v)
    rows.append({key: value for key, value in absorbing.items() if key != "v_next"})

    assert rows[-3:] == [
        {
            "height": 2,
            "centered_error": -1,
            "strict_centered": False,
            "payment": 1,
            "next_height": 3,
        },
        {
            "height": 3,
            "centered_error": -1,
            "strict_centered": True,
            "payment": 4,
            "next_height": 1,
        },
        {
            "height": 1,
            "centered_error": 0,
            "strict_centered": True,
            "payment": 1,
            "next_height": 1,
        },
    ]
    return {
        "source_residue_mod_13": source_residue,
        "t_residue_mod_14": t_residue,
        "lift_mod_3": lift,
        "parameter": parameter,
        "rows": rows,
    }


def regression_replays() -> list[dict[str, Any]]:
    return [
        replay_cylinder(source_residue, t_residue, lift)
        for source_residue, t_residues in PAYMENT_SEVEN_T_CLASSES.items()
        for t_residue in t_residues
        for lift in range(3)
    ]


def build_receipt() -> dict[str, Any]:
    _, q10 = source_quotient_polynomials()
    residue_certificate = multiplier_mod_42_certificate(q10)
    cascade = symbolic_cascade_certificate()
    replays = regression_replays()

    common_modulus = 13 * 14 * 17
    first_zero = len(FIRST_COLLAPSE_CLASSES) * 14 * 17
    second_zero = len(NEGATIVE_FOUR_COLLAPSE_K_CLASSES_MOD_221) * 14
    positive = (
        len(NEGATIVE_FOUR_POSITIVE_TWO_T_CLASSES)
        + len(NEGATIVE_FOUR_POSITIVE_FOUR_T_CLASSES)
    ) * 14
    third_zero = len(PAYMENT_SEVEN_K_CLASSES_MOD_182) * 17
    total_zero = first_zero + second_zero + third_zero
    negative_candidates = common_modulus - total_zero - positive
    assert (common_modulus, total_zero, positive, negative_candidates) == (
        3094,
        2232,
        182,
        680,
    )

    contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Under a_(n+1)/a_n^2 -> 1 and rational reciprocal sum, force "
            "eventual Sylvester recurrence."
        ),
        claim_ceiling=(
            "Exact cofinal return for all sixteen payment-seven source cylinders; "
            "the payment-one height-fourteen cylinders and unrestricted #243 "
            "remain open."
        ),
        hypothesis_id="payment_seven_height_two_boundary_supports_expansion",
        hypothesis_statement=(
            "A height-13 payment-seven cylinder can pass through the height-two "
            "centered tie and continue an expanding negative excursion."
        ),
        probe_id="multiplier_mod_42_boundary_cascade",
        probe_question=(
            "Does the stronger multiplier residue on every payment-seven source "
            "cylinder force a full payment after the height-two tie?"
        ),
        computation=(
            "Recover the height-13 multiplier modulo 42 by composite-modulus "
            "exact division, prove it is 7 on all sixteen cylinders, derive the "
            "symbolic 13->2->3->1 cascade, and replay all 48 modulus lifts."
        ),
        falsifier=(
            "A universal congruence and exact algebraic cascade that lands every "
            "payment-seven lift at primitive height one and centered zero."
        ),
        stop_condition=(
            "Stop when the 16 source cylinders and their three lifts modulo 42 "
            "all have an exact absorbing-tail certificate; do not continue the "
            "separate payment-one branches."
        ),
        survival_consequence=(
            "Without a forced final payment four, the height-two tie would remain "
            "a distinct candidate mechanism for continuing negative support."
        ),
        falsification_consequence=(
            "Every payment-seven cylinder is forced into centered zero. On the "
            "common modulus 3094, the family now partitions into 2232 zero, 182 "
            "positive, and only 680 continuing-negative candidate classes."
        ),
        consumer_ref=LEAN_REF,
        consumer_declarations=[
            "ErdosProblems.Erdos243.paymentSevenCascade_finalFullPayment",
            "ErdosProblems.Erdos243.paymentSevenCascade_finalCollapse",
        ],
        analysis_refs=[NOTE_REF, PACKET_REF, SECOND_SPLIT_REF, LIBRARY_REF],
        source_refs=[SCRIPT_REF, SECOND_SPLIT_REF, LIBRARY_REF, LEAN_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "All sixteen payment-seven classes modulo 182 have height-13 "
            "multiplier 7 modulo 42 and follow the forced cascade "
            "(13,-1)->(2,-1 tie)->(3,-1)->(1,0 forever), with payments "
            "7,1,4. The height-two boundary mode is eliminated exactly."
        ),
        progress_class="one_way_theorem",
        decision_basis=(
            "Exact quotient residues quantify over every source lift, while the "
            "symbolic cascade proves the terminal payments independently of "
            "representative orbit length."
        ),
        next_analytic_target=(
            "Discard height-two payment-seven cylinders. Restrict further family "
            "analysis to the payment-one height-fourteen cylinders over source "
            "classes k mod 13 in {3,4,11,12}."
        ),
        resource_bounds={
            "source_polynomial_degree": 1024,
            "source_cylinders": 16,
            "modulus_lifts_per_cylinder": 3,
            "representative_replays": len(replays),
            "post_recovery_steps_per_replay": 6,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos243-payment-seven-cascade-receipt/1",
        "status": "verified_exact_boundary_mode_elimination",
        "residue_certificate": residue_certificate,
        "symbolic_cascade_certificate": cascade,
        "regression_replays": replays,
        "cumulative_source_class_partition": {
            "common_modulus": common_modulus,
            "zero_centered_class_count": total_zero,
            "positive_centered_class_count": positive,
            "continuing_negative_candidate_class_count": negative_candidates,
            "exact_partition": "2232 zero + 182 positive + 680 negative candidates = 3094",
        },
        "experiment_contract": contract,
        "consequence_reconciliation": {
            "height_two_boundary_mode": {
                "decision": "update_now",
                "reason": "all sixteen cylinders now have a universal cofinal return",
                "authority_surface": PACKET_REF,
            },
            "payment_one_height_fourteen_branch": {
                "decision": "defer_with_reason",
                "reason": "structurally disjoint branch not consumed by this cascade",
                "reentry_condition": "exact multiplier/error split at height fourteen",
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
            for ref in [SCRIPT_REF, SECOND_SPLIT_REF, LIBRARY_REF, LEAN_REF, NOTE_REF, PACKET_REF]
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
