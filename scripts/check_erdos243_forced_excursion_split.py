#!/usr/bin/env python3
"""Certify the first exact split of the forced #243 expanding excursion.

The infinite clean-return family reaches height 11 with terminal quotient
``q9 = 41472 (mod 82944)`` and is forced to height 12.  This checker carries
the *actual source parameter* through the exact integer-polynomial quotient
recurrence.  Modulo 13, eight parameter classes pay the full factor 13 at
height 12, collapse the primitive numerator to one, and therefore enter the
zero-centred (Sylvester) tail forever.  Only five classes survive to height 13.

The polynomial/residue certificate, rather than the representative replays,
is the authority for every nonnegative parameter in each congruence class.
"""

from __future__ import annotations

import argparse
import hashlib
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

from check_erdos243_clean_prefix_tiny_reset import reduced_step  # noqa: E402
from check_erdos243_infinite_clean_recovery_family import (  # noqa: E402
    BASE_QUOTIENT,
    FAMILY_PERIOD,
    HEIGHTS,
    PAYMENTS,
    polynomial_add,
    polynomial_mul,
    polynomial_scale,
    polynomial_transition,
)


SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_forced_excursion_split.py"
)
SOURCE_SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_infinite_clean_recovery_family.py"
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
    "erdos243_forced_excursion_split_receipt.json"
)

PRIME = 13
COLLAPSE_CLASSES = [0, 2, 5, 6, 7, 8, 9, 10]
SURVIVOR_CLASSES = [1, 3, 4, 11, 12]
REDUCED_Q10_PLUS_ONE = [0, 0, 1, 4, 2, 3, 9, 12, 8, 7, 7, 7, 7]
FACTOR_ROOT_MULTIPLICITIES = {
    0: 2,
    2: 2,
    5: 1,
    6: 2,
    7: 1,
    8: 1,
    9: 2,
    10: 1,
}


def polynomial_digest(poly: list[int]) -> str:
    digest = hashlib.sha256()
    for coefficient in poly:
        digest.update(str(coefficient).encode("ascii"))
        digest.update(b"\n")
    return digest.hexdigest()


def polynomial_function_mod_prime(poly: list[int], prime: int) -> list[int]:
    """Reduce an integer polynomial as a function on F_p via x^p=x."""

    reduced = [0] * prime
    for exponent, coefficient in enumerate(poly):
        reduced_exponent = (
            0 if exponent == 0 else 1 + (exponent - 1) % (prime - 1)
        )
        reduced[reduced_exponent] = (
            reduced[reduced_exponent] + coefficient
        ) % prime
    return reduced


def polynomial_mul_mod(
    left: list[int], right: list[int], modulus: int
) -> list[int]:
    result = [0] * (len(left) + len(right) - 1)
    for i, left_coefficient in enumerate(left):
        for j, right_coefficient in enumerate(right):
            result[i + j] = (
                result[i + j] + left_coefficient * right_coefficient
            ) % modulus
    return result


def factor_polynomial() -> list[int]:
    # 7 = -6 (mod 13).  The degree-twelve factorisation is exact in F_13[x].
    result = [7]
    for root, multiplicity in FACTOR_ROOT_MULTIPLICITIES.items():
        for _ in range(multiplicity):
            result = polynomial_mul_mod(result, [(-root) % PRIME, 1], PRIME)
    return result


def evaluate_mod(poly: list[int], value: int, modulus: int) -> int:
    total = 0
    for coefficient in reversed(poly):
        total = (total * value + coefficient) % modulus
    return total


def source_quotient_polynomials() -> tuple[list[int], list[int]]:
    q9 = [BASE_QUOTIENT, FAMILY_PERIOD]
    for height, payment in zip(HEIGHTS[:-1], PAYMENTS, strict=True):
        q9 = polynomial_transition(q9, height, payment)
    assert len(q9) - 1 == 512
    assert all(coefficient % 12 == 0 for coefficient in q9)

    # The already-certified terminal transition has height 11 and payment one.
    q10 = polynomial_transition(q9, 11, 1)
    assert len(q10) - 1 == 1024
    return q9, q10


def residue_certificate() -> dict[str, Any]:
    q9, q10 = source_quotient_polynomials()
    q10_plus_one = polynomial_add(q10, [1])
    reduced = polynomial_function_mod_prime(q10_plus_one, PRIME)
    assert reduced == REDUCED_Q10_PLUS_ONE
    assert factor_polynomial() == reduced

    values = [evaluate_mod(reduced, residue, PRIME) for residue in range(PRIME)]
    collapse = [residue for residue, value in enumerate(values) if value == 0]
    survivors = [residue for residue, value in enumerate(values) if value != 0]
    assert collapse == COLLAPSE_CLASSES
    assert survivors == SURVIVOR_CLASSES

    return {
        "source_parameter": "k in nonnegative integers",
        "source_quotient": "q0(k)=33+79833600*k",
        "exact_transition_count_to_q9": 9,
        "q9_polynomial": {
            "degree": len(q9) - 1,
            "sha256_newline_delimited_coefficients": polynomial_digest(q9),
            "all_coefficients_divisible_by_12": True,
        },
        "q10_polynomial": {
            "degree": len(q10) - 1,
            "sha256_newline_delimited_coefficients": polynomial_digest(q10),
        },
        "finite_field": "F_13",
        "reduction_rule": "x^13=x as a polynomial function on F_13",
        "q10_plus_one_reduced_coefficients_low_to_high": reduced,
        "factorization": (
            "7*x^2*(x-2)^2*(x-5)*(x-6)^2*(x-7)*(x-8)*"
            "(x-9)^2*(x-10) in F_13[x]"
        ),
        "values_by_k_mod_13": values,
        "full_payment_collapse_classes": collapse,
        "expanding_survivor_classes": survivors,
        "periodicity_reason": (
            "q10(k) is an exact integer polynomial, so q10(k)+1 modulo 13 "
            "depends only on k modulo 13"
        ),
    }


def replay_parameter(parameter: int, post_steps: int = 3) -> dict[str, Any]:
    q = BASE_QUOTIENT + FAMILY_PERIOD * parameter
    u = 11
    v = u * q - 1
    for _ in range(9):
        step = reduced_step(u, v)
        u, v = step["u_next"], step["v_next"]

    rows: list[dict[str, int]] = []
    for _ in range(post_steps):
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
    return {"parameter": parameter, "parameter_mod_13": parameter % 13, "rows": rows}


def regression_replays() -> dict[str, Any]:
    collapses = [replay_parameter(residue) for residue in COLLAPSE_CLASSES]
    survivors = [replay_parameter(residue, post_steps=2) for residue in SURVIVOR_CLASSES]
    for replay in collapses:
        assert replay["rows"] == [
            {"height": 11, "centered_error": -1, "payment": 1, "next_height": 12},
            {"height": 12, "centered_error": -1, "payment": 13, "next_height": 1},
            {"height": 1, "centered_error": 0, "payment": 1, "next_height": 1},
        ]
    for replay in survivors:
        assert replay["rows"][:2] == [
            {"height": 11, "centered_error": -1, "payment": 1, "next_height": 12},
            {"height": 12, "centered_error": -1, "payment": 1, "next_height": 13},
        ]
    return {"collapse_representatives": collapses, "survivor_representatives": survivors}


def build_receipt() -> dict[str, Any]:
    certificate = residue_certificate()
    replays = regression_replays()
    contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Under a_(n+1)/a_n^2 -> 1 and rational reciprocal sum, force "
            "eventual Sylvester recurrence."
        ),
        claim_ceiling=(
            "Exact cofinal return for eight of thirteen congruence subfamilies "
            "inside the known infinite clean-return family; the five surviving "
            "classes and unrestricted #243 remain open."
        ),
        hypothesis_id="all_clean_return_parameters_survive_forced_expansion",
        hypothesis_statement=(
            "After the forced 11->12 ascent, every member of the infinite "
            "clean-return family can continue an expanding negative excursion."
        ),
        probe_id="height_twelve_payment_residue_split",
        probe_question=(
            "For which source parameters does the exact height-12 quotient make "
            "gcd(13,(q10+1)^2)=13 rather than one?"
        ),
        computation=(
            "Propagate q0(k)=33+79833600*k through ten exact integer-polynomial "
            "negative-unit transitions, reduce q10(k)+1 as a function on F_13, "
            "and factor the resulting degree-twelve polynomial."
        ),
        falsifier=(
            "A nonempty parameter residue class for which q10+1 vanishes modulo "
            "13, forcing full payment 13, primitive height one, and zero centred "
            "state forever."
        ),
        stop_condition=(
            "Stop after the exact F_13 factorisation classifies all thirteen "
            "source classes; do not extend representatives to a longer horizon."
        ),
        survival_consequence=(
            "If no class collapsed, every source parameter would remain eligible "
            "for the expanding-boundary mechanism at height 13."
        ),
        falsification_consequence=(
            "Eight infinite arithmetic subfamilies are forced into the absorbing "
            "zero-centred tail. Any infinite negative-support construction inside "
            "this family must lie in k mod 13 in {1,3,4,11,12}."
        ),
        consumer_ref=LEAN_REF,
        consumer_declarations=[
            "ErdosProblems.Erdos243.negativeUnitRecovery_heightTwelve_fullPayment",
            "ErdosProblems.Erdos243.negativeUnitRecovery_heightTwelve_collapse",
        ],
        analysis_refs=[NOTE_REF, PACKET_REF, LEAN_REF, SOURCE_SCRIPT_REF],
        source_refs=[SCRIPT_REF, SOURCE_SCRIPT_REF, LEAN_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "The exact reduced polynomial for q10(k)+1 over F_13 vanishes "
            "precisely for k mod 13 in {0,2,5,6,7,8,9,10}. Those eight classes "
            "pay 13 at height 12, collapse to height one, and have e=0 forever; "
            "only {1,3,4,11,12} survive to height 13."
        ),
        progress_class="one_way_theorem",
        decision_basis=(
            "The quotient is an exact degree-1024 integer polynomial in the "
            "source parameter, and its complete F_13 function factorisation "
            "classifies every lift, not only sampled representatives."
        ),
        next_analytic_target=(
            "Restrict every further expanding-excursion analysis to the five "
            "surviving source classes, and seek the next exact residue split "
            "rather than auditing longer arbitrary trajectories."
        ),
        resource_bounds={
            "exact_polynomial_degree": 1024,
            "finite_field_classes": 13,
            "representative_replays": 13,
            "post_recovery_steps_per_replay_at_most": 3,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos243-forced-excursion-split-receipt/1",
        "status": "verified_exact_cofinal_return_split",
        "residue_certificate": certificate,
        "absorbing_tail_certificate": {
            "full_payment_condition": "13 divides q10+1",
            "payment": "gcd(13,(q10+1)^2)=13",
            "next_primitive_height": "13/13=1",
            "zero_state_reason": (
                "a primitive rational state with numerator one has integral tail, "
                "hence centered error zero; the exact cocycle keeps height one "
                "and centered error zero thereafter"
            ),
        },
        "regression_replays": replays,
        "experiment_contract": contract,
        "consequence_reconciliation": {
            "expanding_boundary_family": {
                "decision": "update_now",
                "reason": "eight of thirteen parameter classes are now exactly closed",
                "authority_surface": PACKET_REF,
            },
            "generic_height_twelve_payment": {
                "decision": "update_now",
                "reason": "the small divisibility consumer is suitable for kernel checking",
                "authority_surface": LEAN_REF,
            },
            "five_survivor_classes": {
                "decision": "defer_with_reason",
                "reason": (
                    "their next transition branches further; this receipt stops at "
                    "the first complete residue partition"
                ),
                "reentry_condition": (
                    "run an exact residue cylinder restricted to k mod 13 in "
                    "{1,3,4,11,12}"
                ),
                "authority_surface": PACKET_REF,
            },
        },
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [SCRIPT_REF, SOURCE_SCRIPT_REF, LEAN_REF, NOTE_REF, PACKET_REF]
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
