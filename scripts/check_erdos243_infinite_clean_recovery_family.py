#!/usr/bin/env python3
"""Certify an infinite congruence family of exact #243 clean recoveries.

For every ``k >= 0`` the primitive state

    (u, v) = (11, 11 * (33 + 79_833_600*k) - 1)

follows the same nine negative-unit heights and payments as the previously
known finite witness.  The unbounded family is proved by a descending chain
of quotient congruences; sample replay is only a regression check, not the
quantifier authority.  The generic propagation identity is independently
kernel-checked in ``CleanRecoveryLengthCounterexample.lean``.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)

from check_erdos243_clean_prefix_tiny_reset import reduced_step  # noqa: E402


SCRIPT_REF = (
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
    "erdos243_infinite_clean_recovery_family_receipt.json"
)

HEIGHTS = [11, 3, 4, 5, 6, 7, 8, 9, 10, 11]
PAYMENTS = [4, 1, 1, 1, 1, 1, 1, 1, 1]
BASE_QUOTIENT = 33
FAMILY_PERIOD = 79_833_600
SAMPLE_PARAMETERS = [0, 1, 2, 10, 100]


def polynomial_add(left: list[int], right: list[int]) -> list[int]:
    width = max(len(left), len(right))
    return [
        (left[index] if index < len(left) else 0)
        + (right[index] if index < len(right) else 0)
        for index in range(width)
    ]


def polynomial_mul(left: list[int], right: list[int]) -> list[int]:
    result = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] += a * b
    return result


def polynomial_scale(poly: list[int], scalar: int) -> list[int]:
    return [scalar * coefficient for coefficient in poly]


def polynomial_exact_div(poly: list[int], divisor: int) -> list[int]:
    if any(coefficient % divisor for coefficient in poly):
        raise AssertionError(("nonintegral polynomial division", divisor))
    return [coefficient // divisor for coefficient in poly]


def polynomial_transition(poly: list[int], u: int, h: int) -> list[int]:
    q_plus_one = polynomial_add(poly, [1])
    u_q_minus_one = polynomial_add(polynomial_scale(poly, u), [-1])
    numerator = polynomial_add(polynomial_mul(q_plus_one, u_q_minus_one), [h])
    return polynomial_exact_div(numerator, u + 1)


def transition_numerator(u: int, h: int, q: int) -> int:
    return (q + 1) * (u * q - 1) + h


def descending_moduli() -> list[int]:
    moduli = [1] * len(HEIGHTS)
    for index in range(len(PAYMENTS) - 1, -1, -1):
        moduli[index] = (HEIGHTS[index] + 1) * moduli[index + 1]
    return moduli


def prove_residue_chain() -> dict[str, Any]:
    """Check the finite congruence certificate that proves every family member."""

    moduli = descending_moduli()
    assert moduli[0] == FAMILY_PERIOD
    residues = [BASE_QUOTIENT]
    rows: list[dict[str, int]] = []

    for index, (u, h) in enumerate(zip(HEIGHTS[:-1], PAYMENTS, strict=True)):
        modulus = moduli[index]
        next_modulus = moduli[index + 1]
        n = u + 1
        r = residues[-1]
        assert modulus == n * next_modulus
        assert math.gcd(n, (r + 1) ** 2) == h
        numerator = transition_numerator(u, h, r)
        assert numerator % n == 0
        quotient = numerator // n
        next_residue = quotient % next_modulus
        residues.append(next_residue)
        rows.append(
            {
                "index": index,
                "height": u,
                "payment": h,
                "height_plus_one": n,
                "quotient_modulus": modulus,
                "quotient_residue": r,
                "base_next_quotient": quotient,
                "next_quotient_modulus": next_modulus,
                "next_quotient_residue": next_residue,
            }
        )

    assert residues == [33, 1026, 790020, 141372, 11088, 4752, 0, 0, 0, 0]
    return {"moduli": moduli, "residues": residues, "rows": rows}


def replay_member(k: int) -> dict[str, Any]:
    q = BASE_QUOTIENT + FAMILY_PERIOD * k
    u = HEIGHTS[0]
    v = u * q - 1
    initial_v = v
    seen_heights = [u]
    seen_payments: list[int] = []
    seen_errors: list[int] = []

    for expected_u, expected_h in zip(HEIGHTS[:-1], PAYMENTS, strict=True):
        assert u == expected_u
        assert math.gcd(u, v) == 1
        step = reduced_step(u, v)
        assert step["e"] == -1
        assert step["h"] == expected_h
        seen_errors.append(step["e"])
        seen_payments.append(step["h"])
        u, v = step["u_next"], step["v_next"]
        seen_heights.append(u)

    endpoint = reduced_step(u, v)
    assert seen_heights == HEIGHTS
    assert seen_payments == PAYMENTS
    assert seen_errors == [-1] * 9
    assert endpoint["e"] == -1
    assert all(value < HEIGHTS[0] for value in seen_heights[1:-1])
    return {
        "parameter": k,
        "initial_q": q,
        "initial_v_decimal_digits": len(str(initial_v)),
        "heights": seen_heights,
        "payments": seen_payments,
        "centered_errors": seen_errors,
        "normalized_endpoint_return": [[1, seen_heights[0]], [1, seen_heights[-1]]],
    }


def terminal_residue_certificate() -> dict[str, Any]:
    """Prove the terminal quotient is 41472 modulo 82944 for every lift."""

    q6_polynomial = [BASE_QUOTIENT, FAMILY_PERIOD]
    for u, h in zip(HEIGHTS[:6], PAYMENTS[:6], strict=True):
        q6_polynomial = polynomial_transition(q6_polynomial, u, h)
    t_polynomial = polynomial_exact_div(q6_polynomial, 990)
    shifted_t = polynomial_add(t_polynomial, [36])
    c_polynomial = polynomial_exact_div(shifted_t, 1152)
    assert len(t_polynomial) == 65
    assert math.gcd(*map(abs, t_polynomial)) == 36

    # Substitute t = -36 + 1152*c into the three exact terminal factors.
    symbolic_t = [-36, 1152]
    a_polynomial = polynomial_mul(
        symbolic_t,
        polynomial_add(polynomial_scale(symbolic_t, 7920), [7]),
    )
    b_polynomial = polynomial_mul(
        a_polynomial,
        polynomial_add(polynomial_scale(a_polynomial, 990), [8]),
    )
    q9_polynomial = polynomial_mul(
        b_polynomial,
        polynomial_add(polynomial_scale(b_polynomial, 110), [9]),
    )
    nonconstant_period = math.gcd(*map(abs, q9_polynomial[1:]))
    assert nonconstant_period == 82_944
    assert q9_polynomial[0] % nonconstant_period == 41_472

    sample_rows: list[dict[str, int]] = []
    for k in SAMPLE_PARAMETERS:
        q = BASE_QUOTIENT + FAMILY_PERIOD * k
        for u, h in zip(HEIGHTS[:6], PAYMENTS[:6], strict=True):
            q = transition_numerator(u, h, q) // (u + 1)
        q6 = q
        assert q6 % 990 == 0
        t = q6 // 990
        a = t * (7920 * t + 7)
        b = a * (990 * a + 8)
        q7 = transition_numerator(8, 1, q6) // 9
        q8 = transition_numerator(9, 1, q7) // 10
        q9 = transition_numerator(10, 1, q8) // 11
        assert q7 == 110 * a
        assert q8 == 11 * b
        assert b == 2 * a * (495 * a + 4)
        assert q9 == b * (110 * b + 9)
        assert t == -36 + 1152 * c_polynomial_value(c_polynomial, k)
        assert q9 % 82_944 == 41_472
        assert q9 % 2 == 0
        assert math.gcd(12, (q9 + 1) ** 2) == 1
        assert q9 % FAMILY_PERIOD != BASE_QUOTIENT
        sample_rows.append(
            {
                "parameter": k,
                "q6_div_990_bit_length": t.bit_length(),
                "q6_div_990_decimal_digits": len(str(t)),
                "q6_div_990_mod_1152": t % 1152,
                "terminal_quotient_mod_82944": q9 % 82_944,
                "terminal_quotient_mod_2": q9 % 2,
                "forced_next_payment": math.gcd(12, (q9 + 1) ** 2),
                "forced_next_height": 12 // math.gcd(12, (q9 + 1) ** 2),
                "required_reentry_residue_mod_2": BASE_QUOTIENT % 2,
            }
        )

    return {
        "universal_input_from_residue_chain": "q6=990*t with t=-36+1152*c(k)",
        "source_parameter_polynomial": {
            "q6_degree": len(q6_polynomial) - 1,
            "t_polynomial_degree": len(t_polynomial) - 1,
            "t_polynomial_coefficient_gcd": math.gcd(*map(abs, t_polynomial)),
            "t_plus_36_coefficient_divisor": 1152,
            "c_polynomial_degree": len(c_polynomial) - 1,
        },
        "exact_factorization": [
            "A=t*(7920*t+7)",
            "q7=110*A",
            "B=A*(990*A+8)=2*A*(495*A+4)",
            "q8=11*B",
            "q9=B*(110*B+9)",
        ],
        "terminal_residue": {
            "modulus": 82_944,
            "residue": 41_472,
            "equivalent_factorization": "q9=41472*(2*z+1)",
        },
        "forced_next_ascent": {
            "return_height": 11,
            "payment_formula": "gcd(12,(q9+1)^2)",
            "payment": 1,
            "next_height": 12,
            "reason": "q9 is divisible by 41472 and hence by 12",
            "consequence": (
                "the terminal class cannot directly begin another height-11 "
                "clean recovery with all intermediate heights below 11"
            ),
        },
        "conclusion": (
            "q9 is always 41472 modulo 82944, while every reentry quotient "
            "33+79833600*k is odd; direct self-concatenation is impossible and "
            "every switching cylinder receives one fixed terminal 2-adic/3-adic class"
        ),
        "lean_declarations": [
            "ErdosProblems.Erdos243.negativeUnitRecovery_terminalQuotient_even",
            "ErdosProblems.Erdos243.negativeUnitRecovery_terminalQuotient_oddMultiple_41472",
            "ErdosProblems.Erdos243.negativeUnitRecovery_terminal_nextPayment_one",
            "ErdosProblems.Erdos243.negativeUnitRecovery_terminal_nextHeight_twelve",
        ],
        "lean_validation_state": "lean_checked",
        "regression_samples": sample_rows,
    }


def c_polynomial_value(poly: list[int], value: int) -> int:
    total = 0
    for coefficient in reversed(poly):
        total = total * value + coefficient
    return total


def rejected_inexact_floor_switch() -> dict[str, Any]:
    """Reject a quotient-only floor transition that manufactures a return."""

    q = 41_472 + 82_944 * 6
    u = 11
    v = u * q - 1
    heights = [u]
    payments: list[int] = []
    errors: list[int] = []
    for _ in range(8):
        step = reduced_step(u, v)
        errors.append(step["e"])
        if step["e"] != -1:
            break
        payments.append(step["h"])
        u, v = step["u_next"], step["v_next"]
        heights.append(u)
    assert heights == [11, 12, 13, 14, 3]
    assert payments == [1, 1, 1, 5]
    assert errors[-1] != -1
    return {
        "terminal_class_parameter_z": 6,
        "initial_quotient": q,
        "exact_negative_unit_heights": heights,
        "exact_negative_unit_payments": payments,
        "first_non_negative_unit_error": errors[-1],
        "rejected_shortcut": (
            "floor-dividing a nonintegral quotient transition and continuing "
            "the height/payment recurrence"
        ),
        "authority_rule": (
            "carry the full reduced pair through reduced_step, or assert exact "
            "divisibility before every quotient transition"
        ),
    }


def build_receipt() -> dict[str, Any]:
    certificate = prove_residue_chain()
    samples = [replay_member(k) for k in SAMPLE_PARAMETERS]
    parity_certificate = terminal_residue_certificate()
    rejected_switch = rejected_inexact_floor_switch()
    contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Under a_(n+1)/a_n^2 -> 1 and rational reciprocal sum, force "
            "eventual Sylvester recurrence."
        ),
        claim_ceiling=(
            "An exact infinite arithmetic family of finite nine-step complete "
            "clean recoveries with identical normalized endpoint mass; not an "
            "infinite trajectory and not a solution of Erdős #243."
        ),
        hypothesis_id="large_scale_breaks_complete_recovery_normalized_returns",
        hypothesis_statement=(
            "The known normalized-state return is an isolated small-scale fixture, "
            "or sufficiently large initial quotient/denominator forces strict slack."
        ),
        probe_id="descending_quotient_congruence_family",
        probe_question=(
            "Does the exact recovery pattern persist for an unbounded arithmetic "
            "progression of primitive initial states?"
        ),
        computation=(
            "Propagate quotient residues through the modulus chain "
            "79,833,600 -> 6,652,800 -> ... -> 1, checking each exact payment "
            "and negative-unit transition; replay five spaced family members."
        ),
        falsifier=(
            "A certified nonzero period such that every nonnegative lift of the "
            "base quotient follows the same complete normalized return."
        ),
        stop_condition=(
            "Stop after the nine exact congruence implications close at modulus "
            "one; sample replays cannot replace any failed implication."
        ),
        survival_consequence=(
            "Large initial scale could still exclude the finite normalized-return "
            "fixture and rescue a scale-sensitive strict recovery descent."
        ),
        falsification_consequence=(
            "Neither isolation nor large quotient/denominator scale can rescue "
            "strict normalized-mass descent at complete recoveries. A viable "
            "potential must retain changing prefix arithmetic across recoveries."
        ),
        consumer_ref=LEAN_REF,
        consumer_declarations=[
            "ErdosProblems.Erdos243.negativeUnitTransitionNumerator_periodic",
            "ErdosProblems.Erdos243.negativeUnitTransitionQuotient_periodic",
            "ErdosProblems.Erdos243.cleanRecoveryWitness_normalizedNegativeMass_return",
        ],
        analysis_refs=[NOTE_REF, PACKET_REF, LEAN_REF],
        source_refs=[SCRIPT_REF, LEAN_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "For every k>=0, q=33+79,833,600*k and (u,v)=(11,11*q-1) "
            "produce the same nine-step clean recovery, returning normalized "
            "negative mass exactly from 1/11 to 1/11."
        ),
        progress_class="mechanism_eliminated",
        decision_basis=(
            "The Lean-checked periodic transition identity and the exact descending "
            "residue certificate quantify over every lift; the family is unbounded."
        ),
        next_analytic_target=(
            "Seek a cross-recovery invariant using changing complete-prefix residues "
            "or prime support; discard all scale-only repairs of normalized descent."
        ),
        resource_bounds={
            "congruence_implications": 9,
            "sample_replays": len(SAMPLE_PARAMETERS),
            "steps_per_sample": 9,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    parity_contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Under a_(n+1)/a_n^2 -> 1 and rational reciprocal sum, force "
            "eventual Sylvester recurrence."
        ),
        claim_ceiling=(
            "Exact obstruction to directly concatenating this particular "
            "infinite family or switching immediately into any same-height clean "
            "recovery; not an exclusion of expanding continuations and not a "
            "solution of Erdős #243."
        ),
        hypothesis_id="clean_recovery_family_direct_self_renewal",
        hypothesis_statement=(
            "Some member of the arithmetic clean-recovery family ends in the "
            "same quotient congruence class and can therefore start another "
            "copy of the identical nine-step recovery."
        ),
        probe_id="terminal_quotient_residue_factorization",
        probe_question=(
            "Which exact residue class receives every terminal quotient, and can "
            "it re-enter the odd class 33 modulo 79,833,600?"
        ),
        computation=(
            "Propagate the source parameter as an exact degree-64 integer "
            "polynomial, prove t=q6/990=-36 mod 1152 coefficientwise, then "
            "factor the last three transitions to obtain q9=41472*(2*z+1)."
        ),
        falsifier=(
            "A universal factorization putting every q9 in the single class "
            "41472 modulo 82944 while every allowed re-entry quotient is odd."
        ),
        stop_condition=(
            "Stop once exact coefficient divisibility and the Lean algebraic "
            "consumer separate terminal and initial classes; no longer orbit audit."
        ),
        survival_consequence=(
            "The family could be iterated verbatim to produce an infinite "
            "negative-unit recovery orbit."
        ),
        falsification_consequence=(
            "The family cannot self-concatenate or enter another height-11 clean "
            "cylinder directly: payment one forces height 12. Any infinite "
            "construction must first control an expanding boundary excursion."
        ),
        consumer_ref=LEAN_REF,
        consumer_declarations=[
            "ErdosProblems.Erdos243.negativeUnitRecovery_terminalQuotient_even",
            "ErdosProblems.Erdos243.negativeUnitRecovery_terminalQuotient_oddMultiple_41472",
            "ErdosProblems.Erdos243.negativeUnitRecovery_terminal_nextPayment_one",
            "ErdosProblems.Erdos243.negativeUnitRecovery_terminal_nextHeight_twelve",
        ],
        analysis_refs=[NOTE_REF, PACKET_REF, LEAN_REF],
        source_refs=[SCRIPT_REF, LEAN_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "Every family member has q9=41472 mod 82944, equivalently q9 is "
            "41472 times an odd integer. Its next payment at height 11 is exactly "
            "one, forcing height 12; direct self-renewal and every immediate "
            "same-height clean-cylinder switch are impossible."
        ),
        progress_class="mechanism_eliminated",
        decision_basis=(
            "Exact polynomial arithmetic gives t=q6/990=-36 mod 1152, and the "
            "Lean-checked terminal factorization gives q9=41472*(2*z+1)."
        ),
        next_analytic_target=(
            "Control the forced expanding excursion beginning 11->12, rather than "
            "searching for another immediately clean height-11 return cylinder."
        ),
        resource_bounds={
            "symbolic_transition_count": 9,
            "source_parameter_polynomial_degree": 64,
            "regression_samples": len(SAMPLE_PARAMETERS),
        },
    )
    validate_experiment_contract(parity_contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos243-infinite-clean-recovery-family-receipt/2",
        "status": "verified_exact_infinite_family",
        "family": {
            "parameter_domain": "k in nonnegative integers",
            "initial_state": "(11, 11*(33+79833600*k)-1)",
            "initial_quotient": "33+79833600*k",
            "period": FAMILY_PERIOD,
            "height_pattern": HEIGHTS,
            "payment_pattern": PAYMENTS,
            "centered_error_pattern": [-1] * 9,
            "normalized_mass_return": [[1, 11], [1, 11]],
        },
        "congruence_certificate": certificate,
        "self_renewal_parity_certificate": parity_certificate,
        "rejected_inexact_floor_switch": rejected_switch,
        "regression_samples": samples,
        "experiment_contract": contract,
        "self_renewal_experiment_contract": parity_contract,
        "consequence_reconciliation": {
            "self_renewal_terminal_residue": {
                "decision": "update_now",
                "reason": (
                    "direct same-cylinder concatenation is newly excluded by "
                    "a universal terminal residue factorization"
                ),
                "authority_surface": LEAN_REF,
            },
            "research_packet_or_crosswalk": {
                "decision": "update_now",
                "reason": "the scale-only repair is newly eliminated by an unbounded family",
                "authority_surface": PACKET_REF,
            },
            "computational_lab": {
                "decision": "update_now",
                "reason": "the computation-to-proof bridge and its analytic consequence are new",
                "authority_surface": NOTE_REF,
            },
            "prior_finite_checker": {
                "decision": "verified_no_change",
                "reason": "its finite witness and narrower claim remain exact",
                "authority_surface": (
                    "formal_math/erdos257_period_noncollapse/scripts/"
                    "check_erdos243_clean_recovery_length.py"
                ),
            },
            "project_readme": {
                "decision": "verified_no_change",
                "reason": "it carries build/navigation guidance, not this claim boundary",
                "authority_surface": "formal_math/erdos257_period_noncollapse/README.md",
            },
            "assimilation_manifest": {
                "decision": "verified_no_change",
                "reason": (
                    "the owning Lean module is already present; the manifest does not "
                    "enumerate individual theorem-strength refinements"
                ),
                "authority_surface": (
                    "formal_math/erdos257_period_noncollapse/ErdosProblems/"
                    "assimilation_manifest.json"
                ),
            },
            "lean_microcosm_projection": {
                "decision": "defer_with_reason",
                "reason": (
                    "the generated projection is navigation-only and its broad owner "
                    "builder is not required to validate or land this exact source result"
                ),
                "authority_surface": (
                    "tools/meta/factory/build_lean_mathematics_microcosm_projection.py"
                ),
                "reentry_condition": "next uncontended scheduled projection refresh",
            },
            "unrelated_namespace_validators": {
                "decision": "outside_scope",
                "reason": (
                    "the foreign-residue, adelic-height, and build-wrapper candidates "
                    "are lexical namespace edges and do not consume this recovery mechanism"
                ),
                "authority_surface": "mathematical_consequence_map_v1 candidate map",
            },
        },
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [SCRIPT_REF, LEAN_REF, NOTE_REF, PACKET_REF]
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
