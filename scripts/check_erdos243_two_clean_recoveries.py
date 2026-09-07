#!/usr/bin/env python3
"""Certify two consecutive short-payment clean recoveries for Erdős #243.

The primitive orbit from ``(u,v)=(19,14684)`` has two consecutive complete
clean recoveries.  Each has length three and payment two, so their cumulative
payment is ``4 < 6``.  This refutes a linear length charge even after passing
from one recovery to a pair of aligned recoveries.  It is a finite mechanism
elimination, not an infinite orbit or a solution of Erdős #243.
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
    "check_erdos243_two_clean_recoveries.py"
)
STEP_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_clean_prefix_tiny_reset.py"
)
NOTE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/"
    "TwoCleanRecoveriesComputationalLab.md"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/"
    "SparseResetRecovery.lean"
)
PACKET_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/"
    "research_packet.json"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos243_two_clean_recoveries_receipt.json"
)

INITIAL_U = 19
INITIAL_V = 14684
TRANSITION_COUNT = 6


def check_witness() -> dict[str, Any]:
    u, v = INITIAL_U, INITIAL_V
    rows: list[dict[str, Any]] = []
    exact_u_values = [u]

    for index in range(TRANSITION_COUNT):
        if math.gcd(u, v) != 1:
            raise AssertionError("input pair is not primitive")
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

    centered_errors = [row["centered_error"] for row in rows]
    payments = [row["payment"] for row in rows]
    recovery_lengths = [3, 3]
    recovery_payments = [payments[0], payments[3]]
    payment_product = math.prod(recovery_payments)
    total_length = sum(recovery_lengths)

    assert exact_u_values == [19, 11, 13, 19, 13, 17, 19]
    assert centered_errors == [-3, -2, -6, -7, -4, -2]
    assert payments == [2, 1, 1, 2, 1, 1]
    for start in (0, 3):
        assert exact_u_values[start + 1] < exact_u_values[start]
        assert exact_u_values[start + 2] < exact_u_values[start]
        assert exact_u_values[start + 3] == exact_u_values[start]
        assert payments[start] > 1
        assert payments[start + 1 : start + 3] == [1, 1]
    assert payment_product == 4 < total_length == 6
    assert payment_product < 2**total_length

    return {
        "initial_primitive_pair": [INITIAL_U, INITIAL_V],
        "exact_u_values": exact_u_values,
        "centered_errors": centered_errors,
        "payments": payments,
        "recovery_lengths": recovery_lengths,
        "recovery_payments": recovery_payments,
        "cumulative_payment": payment_product,
        "total_recovery_length": total_length,
        "two_to_total_recovery_length": 2**total_length,
        "trace": rows,
        "verified_invariants": [
            "every state is a positive primitive rational pair",
            "both intervals return to height 19 for the first time after three steps",
            "each interval starts with payment 2 and has two payment-one interior steps",
            "the cumulative payment is 4<6<2^6",
        ],
    }


def build_receipt() -> dict[str, Any]:
    witness = check_witness()
    summary = (
        "The exact primitive orbit from (19,14684) has consecutive clean "
        "recoveries with heights [19,11,13,19] and [19,13,17,19], payments "
        "[2,1,1] and [2,1,1], and cumulative payment 4<6<2^6."
    )
    contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Under a_(n+1)/a_n^2 -> 1 and rational reciprocal sum, force "
            "eventual Sylvester recurrence."
        ),
        claim_ceiling=(
            "Exact finite counterexample to length-only cumulative payment bounds "
            "across two clean recoveries; not an infinite orbit, not a general "
            "prefix-coherence counterexample, and not a solution of Erdős #243."
        ),
        hypothesis_id="two_clean_recovery_lengths_force_cumulative_payment",
        hypothesis_statement=(
            "For two consecutive complete clean recoveries of lengths L1,L2, "
            "the product of their reset payments is at least L1+L2."
        ),
        probe_id="exact_two_consecutive_clean_recovery_trace",
        probe_question=(
            "Can two consecutive aligned clean recoveries still pay less in total "
            "than their combined length?"
        ),
        computation=(
            "Iterate the exact centered primitive cocycle from (19,14684) for six "
            "steps and verify both first-return and clean-payment predicates."
        ),
        falsifier=(
            "Two consecutive clean recoveries with product(h_j)<sum(L_j)."
        ),
        stop_condition=(
            "Stop after the second exact first return; any failed primitivity, "
            "centering, cleanliness, or return check invalidates the result."
        ),
        survival_consequence=(
            "A two-recovery length charge would remain available as the first "
            "cross-recovery input to the global payment budget."
        ),
        falsification_consequence=(
            "Even two aligned recoveries cannot be charged by their lengths alone; "
            "a viable lower bound must use unbounded prefix arithmetic or richer "
            "cross-recovery residue/prime data."
        ),
        consumer_ref=CONSUMER_REF,
        analysis_refs=[NOTE_REF, CONSUMER_REF, PACKET_REF],
        source_refs=[SCRIPT_REF, STEP_REF],
        result_status="exact_one_way_result",
        result_summary=summary,
        progress_class="mechanism_eliminated",
        decision_basis=(
            "The exact lists prove two consecutive clean first returns and "
            "4<6; extending the horizon cannot restore the universal inequality."
        ),
        next_analytic_target=(
            "Use unbounded complete-prefix CRT coherence or arithmetic relations "
            "between recoveries beyond their lengths and reset payments."
        ),
        resource_bounds={"exact_transition_count": TRANSITION_COUNT},
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos243-two-clean-recoveries-receipt/1",
        "status": "verified_exact_two_recovery_mechanism_elimination",
        "result_summary": summary,
        "experiment_contract": contract,
        "witness": witness,
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [SCRIPT_REF, STEP_REF, NOTE_REF, CONSUMER_REF, PACKET_REF]
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
