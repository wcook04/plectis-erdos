#!/usr/bin/env python3
"""Explain Erdős 68 private-owner transitions by exact factorial recurrences.

The expensive private-projection scan selects small prime private quotients.
For such an owner prime ``q`` first seen at ``n``, this checker finds every
``m < q`` with ``m! == 1 (mod q)``.  Its first later hit is exactly when the
growing block collision core can absorb ``q``.  This is a transition-structure
probe, not evidence that suitable owners exist cofinally.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[3]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
)

SCRIPT_REF = str(Path(__file__).resolve().relative_to(REPO_ROOT))
PROJECTION_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos68_private_projection_receipt.json"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/"
    "PrivateProjectionComputationalLab.md"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/"
    "EndpointWeightedPrivateSupport.lean"
)
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse"
    / "erdos68_private_owner_recurrence_receipt.json"
)


def is_prime(value: int) -> bool:
    if value < 2:
        return False
    if value % 2 == 0:
        return value == 2
    divisor = 3
    while divisor * divisor <= value:
        if value % divisor == 0:
            return False
        divisor += 2
    return True


def next_prime_at_least(value: int) -> int:
    candidate = max(2, value)
    while not is_prime(candidate):
        candidate += 1
    return candidate


def factorial_one_hits(prime: int) -> list[int]:
    if not is_prime(prime):
        raise ValueError(f"owner quotient {prime} is not prime")
    residue = 1
    hits: list[int] = []
    for index in range(1, prime):
        residue = residue * index % prime
        if index >= 2 and residue == 1:
            hits.append(index)
    return hits


def owner_rows(pair_runs: list[dict[str, Any]]) -> list[dict[str, Any]]:
    first_owner_index: dict[int, int] = {}
    for run in pair_runs:
        for index, quotient in zip(
            run["selected_indices"], run["selected_private_quotients"], strict=True
        ):
            first_owner_index.setdefault(quotient, index)

    rows: list[dict[str, Any]] = []
    for quotient, index in first_owner_index.items():
        hits = factorial_one_hits(quotient)
        if index not in hits:
            raise AssertionError(
                f"selected owner q={quotient} does not hit at index {index}"
            )
        later_hits = [hit for hit in hits if hit > index]
        if not later_hits:
            raise AssertionError(f"selected owner q={quotient} has no later hit")
        first_repeat = later_hits[0]
        block_threshold = (first_repeat + 2) // 2
        rows.append(
            {
                "owner_index": index,
                "owner_prime": quotient,
                "factorial_one_hits_below_prime": hits,
                "first_repeat_index": first_repeat,
                "first_block_parameter_containing_repeat": block_threshold,
                "first_prime_checkpoint_containing_repeat": next_prime_at_least(
                    block_threshold
                ),
                "transition_mechanism": (
                    "the repeated hit puts the owner prime into the pairwise "
                    "collision core"
                ),
            }
        )
    return rows


def build_receipt() -> dict[str, Any]:
    projection_path = REPO_ROOT / PROJECTION_RECEIPT_REF
    projection = json.loads(projection_path.read_text(encoding="utf-8"))
    pair_runs = projection["pair_runs"]
    owners = owner_rows(pair_runs)
    by_prime = {row["owner_prime"]: row for row in owners}

    transitions: list[dict[str, Any]] = []
    for previous, current in zip(pair_runs, pair_runs[1:], strict=False):
        previous_primes = set(previous["selected_private_quotients"])
        current_primes = set(current["selected_private_quotients"])
        exited = sorted(previous_primes - current_primes)
        entered = sorted(current_primes - previous_primes)
        if len(exited) != 1:
            raise AssertionError(
                "expected exactly one exited prime at each observed transition"
            )
        exited_prime = exited[0]
        predicted = by_prime[exited_prime][
            "first_prime_checkpoint_containing_repeat"
        ]
        observed = current["prime_from"]
        transitions.append(
            {
                "previous_run_through": previous["prime_through"],
                "observed_transition_prime": observed,
                "exited_owner_prime": exited_prime,
                "entered_owner_primes": entered,
                "first_repeat_index": by_prime[exited_prime]["first_repeat_index"],
                "predicted_transition_prime": predicted,
                "prediction_matches_observation": predicted == observed,
            }
        )

    if not transitions or not all(
        row["prediction_matches_observation"] for row in transitions
    ):
        raise AssertionError("factorial recurrence does not explain every transition")

    active_primes = set(pair_runs[-1]["selected_private_quotients"])
    active_predictions = [
        {
            "owner_prime": prime,
            "first_repeat_index": by_prime[prime]["first_repeat_index"],
            "first_prime_checkpoint_containing_repeat": by_prime[prime][
                "first_prime_checkpoint_containing_repeat"
            ],
        }
        for prime in sorted(active_primes)
    ]
    result_summary = (
        f"All {len(transitions)} observed owner transitions occur at exactly the "
        "first prime checkpoint whose block contains the exited owner's second "
        "factorial-one hit."
    )
    return {
        "schema": "erdos68_private_owner_recurrence_receipt_v1",
        "problem_id": "erdos_68",
        "authority_boundary": (
            "Exact modular arithmetic explains the displayed finite transitions; "
            "it does not prove a cofinal supply of renewable owners."
        ),
        "source_projection_range": projection["range"],
        "owner_recurrences": owners,
        "observed_transition_explanations": transitions,
        "active_owner_expiry_predictions": active_predictions,
        "all_observed_transitions_explained": True,
        "result_summary": result_summary,
        "experiment_contract": build_experiment_contract(
            problem_id="erdos_68",
            target_statement="Prove that S=sum_{n>=2} 1/(n!-1) is irrational.",
            claim_ceiling=(
                "Exact transition timing does not prove that renewable private "
                "owners or projection disagreements exist cofinally."
            ),
            hypothesis_id="private_owner_expiry_by_first_repeated_factorial_hit",
            hypothesis_statement=(
                "A selected prime private owner leaves the deterministic pair when "
                "its first later factorial-one hit enters the displayed block."
            ),
            probe_id="exact_selected_owner_factorial_recurrence_scan",
            probe_question=(
                "Do the first repeated factorial-one hits exactly predict every "
                "observed owner transition?"
            ),
            computation=(
                "For each selected prime quotient q, iterate n! modulo q for n<q, "
                "find the first hit after its owner index, and compare the first "
                "prime block containing that hit with the next recorded pair run."
            ),
            falsifier=(
                "An observed transition whose exited prime has no matching first "
                "repeat checkpoint."
            ),
            stop_condition=(
                "If any transition mismatches, retire the recurrence explanation; "
                "otherwise stop giant-LCM horizon extension as a transition probe."
            ),
            survival_consequence=(
                "Replace vague owner genealogy with a cofinal supply target for at "
                "least two prime owners whose next factorial-one hits lie beyond "
                "the active block."
            ),
            falsification_consequence=(
                "Search for valuation changes or projection coalescence as the true "
                "transition trigger."
            ),
            consumer_ref=CONSUMER_REF,
            consumer_declarations=[
                "ErdosProblems.Erdos68.factorialBlockPrime_dvd_privateQuotient_of_unique_upper_prime",
                "ErdosProblems.Erdos68.irrational_factorialGapSeries_of_cofinal_complementary_disagreement_collisionCap",
            ],
            analysis_refs=[ANALYSIS_REF],
            source_refs=[SCRIPT_REF],
            input_receipt_refs=[PROJECTION_RECEIPT_REF],
            resource_bounds={
                "owner_count": len(owners),
                "maximum_owner_prime": max(by_prime),
            },
            result_status="exact_one_way_result",
            result_summary=result_summary,
            progress_class="mechanism_opened",
            decision_basis=(
                "Every displayed pair transition agrees exactly with the exited "
                "owner prime's first repeated factorial-one checkpoint."
            ),
            next_analytic_target=(
                "Prove a cofinal two-owner renewal theorem with both first-repeat "
                "indices beyond the block endpoint, then feed those owners to the "
                "checked collision-cap projection consumer."
            ),
        ),
        "sources": [
            source_record(REPO_ROOT, SCRIPT_REF),
            source_record(REPO_ROOT, PROJECTION_RECEIPT_REF),
        ],
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    payload = build_receipt()
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
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
