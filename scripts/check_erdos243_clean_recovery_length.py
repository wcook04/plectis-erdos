#!/usr/bin/env python3
"""Certify a short-payment complete clean recovery for Erdős #243.

The exact primitive rational cocycle has a clean first-return interval of
length nine whose only nontrivial reduction factor is four.  This refutes any
universal lower bound charging the length of a complete clean recovery to its
payment alone.  Replaying the endpoint step also shows that normalized
negative mass returns exactly from ``1/11`` to ``1/11``, refuting every strict
complete-recovery descent law in that coordinate alone.  Neither conclusion
addresses lower bounds using complete-prefix residues or several globally
coherent recoveries, and neither settles #243.
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

from check_erdos243_clean_prefix_tiny_reset import (  # noqa: E402
    _integer_record,
    reduced_step,
)


SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_clean_recovery_length.py"
)
PRIMITIVE_STEP_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_clean_prefix_tiny_reset.py"
)
NOTE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/"
    "CleanRecoveryLengthComputationalLab.md"
)
LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/"
    "CleanRecoveryLengthCounterexample.lean"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/"
    "SparseResetRecovery.lean"
)
PACKET_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/"
    "research_packet.json"
)
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "erdos243_clean_recovery_length_receipt.json"
)

INITIAL_U = 11
INITIAL_V = 362
RECOVERY_LENGTH = 9
EXPECTED_PAYMENT = 4


def check_witness() -> dict[str, Any]:
    u, v = INITIAL_U, INITIAL_V
    rows: list[dict[str, Any]] = []
    exact_u_values = [u]

    for index in range(RECOVERY_LENGTH):
        if math.gcd(u, v) != 1:
            raise AssertionError("the input state is not primitive")
        step = reduced_step(u, v)
        rows.append(
            {
                "index": index,
                "u": _integer_record(u),
                "v": _integer_record(v),
                "a": _integer_record(step["a"]),
                "centered_error": step["e"],
                "payment": step["h"],
                "u_next": _integer_record(step["u_next"]),
                "v_next": _integer_record(step["v_next"]),
            }
        )
        u, v = step["u_next"], step["v_next"]
        exact_u_values.append(u)

    payments = [row["payment"] for row in rows]
    centered_errors = [row["centered_error"] for row in rows]
    payment_product = math.prod(payments)
    if math.gcd(u, v) != 1:
        raise AssertionError("the recovery endpoint is not primitive")
    endpoint_step = reduced_step(u, v)
    endpoint_negative_magnitude = -endpoint_step["e"]
    initial_negative_magnitude = -centered_errors[0]

    assert exact_u_values == [11, 3, 4, 5, 6, 7, 8, 9, 10, 11]
    assert centered_errors == [-1] * RECOVERY_LENGTH
    assert payments == [EXPECTED_PAYMENT] + [1] * (RECOVERY_LENGTH - 1)
    assert all(value < INITIAL_U for value in exact_u_values[1:-1])
    assert exact_u_values[-1] >= INITIAL_U
    assert payment_product == EXPECTED_PAYMENT
    assert payment_product < RECOVERY_LENGTH
    assert payment_product < 2**RECOVERY_LENGTH
    assert endpoint_step["e"] == -1
    assert (
        initial_negative_magnitude * exact_u_values[-1]
        == endpoint_negative_magnitude * exact_u_values[0]
    )

    return {
        "initial_primitive_pair": [INITIAL_U, INITIAL_V],
        "recovery_length": RECOVERY_LENGTH,
        "exact_u_values": exact_u_values,
        "centered_errors": centered_errors,
        "payments": payments,
        "payment_product": payment_product,
        "two_to_recovery_length": 2**RECOVERY_LENGTH,
        "normalized_negative_mass_return": {
            "initial_fraction": [initial_negative_magnitude, exact_u_values[0]],
            "terminal_fraction": [endpoint_negative_magnitude, exact_u_values[-1]],
            "exactly_equal": True,
        },
        "first_recovery_checks": {
            "endpoint_returns_to_initial_height": exact_u_values[-1] >= INITIAL_U,
            "all_interior_heights_are_strictly_lower": all(
                value < INITIAL_U for value in exact_u_values[1:-1]
            ),
            "initial_step_is_a_reset": payments[0] > 1,
            "all_interior_payments_are_one": payments[1:] == [1] * 8,
        },
        "trace": rows,
        "verified_invariants": [
            "every input and output is a positive primitive rational pair",
            "the exact centered nearest-remainder rule is used at every step",
            "h=gcd(a^2,u-e) at every step",
            "u=[11,3,4,5,6,7,8,9,10,11] makes this a first recovery",
            "h=[4,1,1,1,1,1,1,1,1] makes the recovery clean",
            "the complete payment is 4<9<2^9",
            "the normalized negative mass returns exactly from 1/11 to 1/11",
        ],
    }


def build_receipt() -> dict[str, Any]:
    witness = check_witness()
    result_summary = (
        "The exact primitive orbit from (u,v)=(11,362) has a clean first "
        "recovery of length 9 with heights [11,3,4,5,6,7,8,9,10,11] and "
        "payments [4,1,1,1,1,1,1,1,1]. Hence its complete payment is "
        "4<9<2^9."
    )
    contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Under a_(n+1)/a_n^2 -> 1 and rational reciprocal sum, force "
            "eventual Sylvester recurrence."
        ),
        claim_ceiling=(
            "Exact finite counterexample to length-only lower bounds on complete "
            "clean-recovery payment; not an infinite orbit, not a prefix-CRT "
            "counterexample, and not a solution of Erdős #243."
        ),
        hypothesis_id="clean_recovery_length_forces_payment_growth",
        hypothesis_statement=(
            "For every complete clean recovery of length L, its initial reset "
            "payment is at least L (or, more strongly, at least 2^L)."
        ),
        probe_id="exact_primitive_clean_first_return_trace",
        probe_question=(
            "Can an actual primitive orbit complete a long clean first recovery "
            "while paying less than both its length and 2^length?"
        ),
        computation=(
            "Start from the reduced pair (11,362), iterate the exact centered "
            "primitive cocycle for nine transitions, and verify the first-return "
            "and clean-payment predicates directly."
        ),
        falsifier=(
            "A clean first recovery of length L whose full payment product is "
            "strictly below L."
        ),
        stop_condition=(
            "Stop after the declared nine-step first return; any failed exact "
            "state, primitivity, centering, or recovery check invalidates the result."
        ),
        survival_consequence=(
            "Complete-recovery alignment alone could still provide the lower "
            "payment mass missing from the global subexponential budget argument."
        ),
        falsification_consequence=(
            "Complete-recovery alignment alone cannot provide even a linear "
            "length charge. Any surviving lower bound must use unbounded prefix "
            "arithmetic, cross-recovery coherence, or source-specific residue data."
        ),
        consumer_ref=CONSUMER_REF,
        consumer_declarations=[
            "ErdosProblems.Erdos243.CleanRecoveryAt",
            "ErdosProblems.Erdos243.cleanRecovery_payment_eq",
        ],
        analysis_refs=[NOTE_REF, LEAN_REF, CONSUMER_REF],
        source_refs=[SCRIPT_REF, PRIMITIVE_STEP_REF],
        result_status="exact_one_way_result",
        result_summary=result_summary,
        progress_class="mechanism_eliminated",
        decision_basis=(
            "The exact first-return and payment lists prove 4<9<2^9; no longer "
            "horizon can restore either universal length-only inequality."
        ),
        next_analytic_target=(
            "Use complete-prefix gcd/CRT information or relations between several "
            "globally coherent recoveries; do not charge recovery length alone."
        ),
        resource_bounds={"exact_transition_count": RECOVERY_LENGTH},
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    normalized_return_contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Under a_(n+1)/a_n^2 -> 1 and rational reciprocal sum, force "
            "eventual Sylvester recurrence."
        ),
        claim_ceiling=(
            "Exact finite counterexample to every strict complete-recovery "
            "descent law depending only on normalized negative mass; not an "
            "infinite orbit or a solution of Erdős #243."
        ),
        hypothesis_id="complete_recovery_normalized_mass_strict_descent",
        hypothesis_statement=(
            "Every nontrivial complete clean recovery strictly decreases the "
            "normalized negative magnitude m/u between its endpoints."
        ),
        probe_id="exact_normalized_state_first_return",
        probe_question=(
            "Can a true primitive complete clean recovery return to exactly the "
            "same normalized negative mass?"
        ),
        computation=(
            "Replay the exact nine-step first recovery from (11,362), evaluate "
            "the centered remainder at both endpoints, and compare the two "
            "fractions by integer cross multiplication."
        ),
        falsifier=(
            "A nontrivial complete clean recovery with identical endpoint values "
            "of m/u."
        ),
        stop_condition=(
            "Stop at the first exact normalized-state return; do not extend the "
            "orbit as evidence for an infinite trajectory."
        ),
        survival_consequence=(
            "A strict recovery-level Lyapunov function of normalized negative mass "
            "would remain available after one-step descent failed."
        ),
        falsification_consequence=(
            "Normalized negative mass alone cannot orient complete recoveries; any "
            "global descent must retain residue, payment, prime, or prefix state."
        ),
        consumer_ref=LEAN_REF,
        consumer_declarations=[
            "ErdosProblems.Erdos243.cleanRecoveryWitness_normalizedNegativeMass_return"
        ],
        analysis_refs=[NOTE_REF, LEAN_REF, PACKET_REF],
        source_refs=[SCRIPT_REF, PRIMITIVE_STEP_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "The exact recovery has endpoint normalized masses 1/11 and 1/11, "
            "so strict complete-recovery descent in that coordinate is false."
        ),
        progress_class="mechanism_eliminated",
        decision_basis=(
            "Both endpoint errors are exactly -1 and both endpoint heights are "
            "exactly 11; the equality is replayed by integer arithmetic and "
            "kernel-checked independently."
        ),
        next_analytic_target=(
            "Use state retaining changing residues, cancellation payments, prime "
            "support, or complete-prefix coherence; normalized mass alone is cyclic."
        ),
        resource_bounds={"exact_transition_count": RECOVERY_LENGTH},
    )
    validate_experiment_contract(normalized_return_contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos243-clean-recovery-length-receipt/2",
        "status": "verified_exact_counterexample",
        "result_summary": result_summary,
        "experiment_contract": contract,
        "normalized_return_experiment_contract": normalized_return_contract,
        "witness": witness,
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [SCRIPT_REF, PRIMITIVE_STEP_REF, NOTE_REF, LEAN_REF]
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
