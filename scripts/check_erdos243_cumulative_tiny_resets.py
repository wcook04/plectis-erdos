#!/usr/bin/env python3
"""Check an exact two-reset Erdős #243 cumulative-payment falsifier.

The search hypothesis charges the total lengths of successive negative,
cancellation-free runs directly to the product of the following raw reset
payments.  This checker regenerates a compact exact witness showing that even
the two-reset cumulative version fails.  It does not address payments attached
to globally aligned complete recoveries and does not settle Erdős #243.
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
    canonical_seed,
    reduced_step,
)


SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_cumulative_tiny_resets.py"
)
PRIOR_SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_clean_prefix_tiny_reset.py"
)
NOTE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/"
    "CumulativeTinyResetsComputationalLab.md"
)
PACKET_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/"
    "research_packet.json"
)
LEAN_REFS = [
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/"
    "DynamicCancellation.lean",
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/"
    "SparseResetRecovery.lean",
]

TAIL_START = 26
GUARANTEED_HEIGHT = 4
SCALE = 1
TARGET_RESET_COUNT = 2
MAX_STEPS = 12
MAX_STATE_BITS = 50_000


def check_witness() -> dict[str, Any]:
    u, v, seed = canonical_seed(
        tail_start=TAIL_START,
        guaranteed_height=GUARANTEED_HEIGHT,
        scale=SCALE,
    )
    rows: list[dict[str, Any]] = []
    resets: list[dict[str, Any]] = []
    clean_run_length = 0
    max_observed_state_bits = 0

    for index in range(MAX_STEPS):
        state_bits = max(u.bit_length(), v.bit_length())
        if state_bits > MAX_STATE_BITS:
            raise AssertionError(
                f"state bit budget exhausted before witness: {state_bits}>{MAX_STATE_BITS}"
            )
        max_observed_state_bits = max(max_observed_state_bits, state_bits)
        step = reduced_step(u, v)
        is_clean_negative = step["e"] < 0 and step["h"] == 1
        if is_clean_negative:
            clean_run_length += 1

        row = {
            "index": index,
            "u": _integer_record(u),
            "v": _integer_record(v),
            "a": _integer_record(step["a"]),
            "centered_error": step["e"],
            "payment": step["h"],
            "u_next": _integer_record(step["u_next"]),
            "state_bits": state_bits,
        }
        rows.append(row)

        if step["h"] > 1:
            resets.append(
                {
                    "index": index,
                    "preceding_clean_negative_length": clean_run_length,
                    "centered_error": step["e"],
                    "payment": step["h"],
                }
            )
            clean_run_length = 0
            if len(resets) == TARGET_RESET_COUNT:
                break
        elif not is_clean_negative:
            clean_run_length = 0

        u, v = step["u_next"], step["v_next"]

    if len(resets) != TARGET_RESET_COUNT:
        raise AssertionError("two resets were not reached within the exact resource bounds")

    run_lengths = [reset["preceding_clean_negative_length"] for reset in resets]
    payments = [reset["payment"] for reset in resets]
    total_clean_length = sum(run_lengths)
    payment_product = math.prod(payments)
    exponential_charge = 2**total_clean_length

    assert run_lengths == [7, 1]
    assert payments == [2, 2]
    assert payment_product == 4
    assert total_clean_length == 8
    assert payment_product < total_clean_length
    assert payment_product < exponential_charge

    return {
        "seed": seed,
        "trace": rows,
        "resets": resets,
        "cumulative_test": {
            "run_lengths": run_lengths,
            "total_clean_negative_length": total_clean_length,
            "payments": payments,
            "payment_product": payment_product,
            "two_to_total_clean_length": exponential_charge,
            "strict_linear_falsification": payment_product < total_clean_length,
            "strict_exponential_falsification": payment_product < exponential_charge,
        },
        "resource_usage": {
            "steps_used": len(rows),
            "max_observed_state_bits": max_observed_state_bits,
            "max_steps": MAX_STEPS,
            "max_state_bits": MAX_STATE_BITS,
        },
        "verified_invariants": [
            "every stored state is a positive primitive rational pair",
            "2*abs(e)<u at every step",
            "h=gcd(a^2,u-e) at every step",
            "the two preceding clean negative run lengths are exactly 7 and 1",
            "the first two reset payments have product 4<8<2^8",
        ],
    }


def build_receipt() -> dict[str, Any]:
    witness = check_witness()
    contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Under a_(n+1)/a_n^2 -> 1 and rational reciprocal sum, force "
            "eventual Sylvester recurrence."
        ),
        claim_ceiling=(
            "Finite exact counterexample to cumulative raw-reset length charging; "
            "not an infinite orbit, not a statement about complete aligned recoveries, "
            "and not a solution of Erdős #243."
        ),
        hypothesis_id="successive_clean_lengths_force_cumulative_raw_reset_payment",
        hypothesis_statement=(
            "For successive raw resets preceded by negative h=1 runs of lengths L_j, "
            "the payment product is at least 2^(sum_j L_j)."
        ),
        probe_id="two_reset_exact_cumulative_payment_trace",
        probe_question=(
            "Can two successive exact resets still have tiny cumulative payment after "
            "two nonempty negative cancellation-free runs?"
        ),
        computation=(
            "Construct the canonical seed (tail_start,height,scale)=(26,4,1), iterate "
            "the primitive rational cocycle exactly, and stop at the second reset."
        ),
        falsifier=(
            "Two successive reset payments whose product is below 2 raised to the sum "
            "of their immediately preceding clean negative run lengths."
        ),
        stop_condition=(
            "Stop at the second reset, after 12 transitions, or before any state "
            "exceeds 50000 bits."
        ),
        survival_consequence=(
            "A cumulative clean-length charge across raw resets would remain available "
            "for comparison with the checked subexponential payment budget."
        ),
        falsification_consequence=(
            "Raw reset lengths cannot supply the global lower bound even after taking "
            "payment products; the surviving producer must consume complete-recovery "
            "alignment, prefix residues, or another global arithmetic coherence."
        ),
        consumer_ref=PACKET_REF,
        analysis_refs=[NOTE_REF, *LEAN_REFS],
        source_refs=[SCRIPT_REF, PRIOR_SCRIPT_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "The first two resets have preceding clean negative lengths 7 and 1 and "
            "payments 2 and 2, so their cumulative payment is 4<8<2^8."
        ),
        resource_bounds={
            "max_state_bits": MAX_STATE_BITS,
            "max_steps": MAX_STEPS,
            "target_reset_count": TARGET_RESET_COUNT,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos243-cumulative-tiny-resets-receipt/1",
        "status": "verified_exact_counterexample",
        "experiment_contract": contract,
        "witness": witness,
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [SCRIPT_REF, PRIOR_SCRIPT_REF, NOTE_REF]
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = json.dumps(build_receipt(), indent=2, sort_keys=True) + "\n"
    if args.output is None:
        print(payload, end="")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
