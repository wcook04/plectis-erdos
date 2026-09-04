#!/usr/bin/env python3
"""Replay the exact backward cone from an Erdős #249 prime-successor lock.

The source endpoint-cocycle receipt contains the record trajectory at
``c=490794``.  At its prime ``p=490829`` the successor is still endpoint
trapped, so the Lean-checked bottom-lock inequality bounds the pre-prime
error.  This checker takes every integer error allowed by that bound, pulls it
back through the *actual* intervening totient letters, and retains only paths
inside every moving endpoint window.

A nonempty cone is an exact counterexample to the proposed local implication
"one prime-successor bottom lock, propagated through its preceding composite
block, forces a lower-boundary crossing".  It does not construct an infinite
trap or settle Erdős #249.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/scripts/"
    "check_prime_successor_precursor_cone.py"
)
INPUT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos249_pure_dyadic_endpoint_cocycle_receipt.json"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/"
    "PureDyadicEndpointCocycleComputationalLab.md"
)
LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/"
    "PeriodMultipleEscape.lean"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos249_prime_successor_precursor_cone_receipt.json"
)


def load_final_champion(input_path: Path) -> dict[str, Any]:
    payload = json.loads(input_path.read_text(encoding="utf-8"))
    champion = payload["scan"]["final_champion"]
    assert champion["c"] == 490794
    assert champion["geometry_clear_height"] == 20
    assert champion["first_central_height"] == 39
    assert champion["fixed_trap_quotient"] == 327611
    return champion


def build_cone(champion: dict[str, Any]) -> dict[str, Any]:
    c = champion["c"]
    k = champion["fixed_trap_quotient"]
    geometry_height = champion["geometry_clear_height"]
    rows = {row["height"]: row for row in champion["trajectory"]}

    eligible: list[tuple[int, dict[str, Any], dict[str, Any], dict[str, Any]]] = []
    for height in sorted(rows):
        if height - 1 not in rows or height + 1 not in rows:
            continue
        prime_row = rows[height]
        successor = rows[height + 1]
        if prime_row["prime_argument"] and not successor["central"]:
            eligible.append((height - 1, rows[height - 1], prime_row, successor))
    assert len(eligible) == 1
    terminal_height, terminal_row, prime_row, successor = eligible[0]

    terminal_upper = (
        4 + 3 * k - prime_row["argument"] - successor["totient_letter"]
    ) // 4
    terminal_lower = -terminal_row["radius"]
    terminal_upper = min(terminal_upper, terminal_row["radius"])
    assert terminal_lower <= terminal_upper

    errors = set(range(terminal_lower, terminal_upper + 1))
    layers: list[dict[str, Any]] = [
        {
            "height": terminal_height,
            "allowed_error_count": len(errors),
            "minimum_error": min(errors),
            "maximum_error": max(errors),
        }
    ]
    for height in range(terminal_height, geometry_height, -1):
        letter = rows[height]["totient_letter"]
        predecessor_radius = rows[height - 1]["radius"]
        predecessors = {
            (error - letter + k) // 2
            for error in errors
            if (error - letter + k) % 2 == 0
            and abs((error - letter + k) // 2) <= predecessor_radius
        }
        assert predecessors
        errors = predecessors
        layers.append(
            {
                "height": height - 1,
                "totient_letter_consumed": letter,
                "allowed_error_count": len(errors),
                "minimum_error": min(errors),
                "maximum_error": max(errors),
            }
        )

    seeds = sorted(errors)
    actual_seed = rows[geometry_height]["signed_endpoint_error"]
    assert actual_seed in errors

    replays: list[dict[str, int]] = []
    for seed in seeds:
        error = seed
        minimum_margin = rows[geometry_height]["radius"] - abs(error)
        for height in range(geometry_height + 1, terminal_height + 1):
            error = 2 * error + rows[height]["totient_letter"] - k
            minimum_margin = min(minimum_margin, rows[height]["radius"] - abs(error))
            assert abs(error) <= rows[height]["radius"]
        assert error <= terminal_upper
        replays.append(
            {
                "geometry_seed_error": seed,
                "terminal_error": error,
                "minimum_endpoint_margin": minimum_margin,
            }
        )

    return {
        "basepoint_c": c,
        "fixed_quotient_k": k,
        "geometry_clear_height": geometry_height,
        "terminal_preprime_height": terminal_height,
        "prime_argument": prime_row["argument"],
        "successor_totient_letter": successor["totient_letter"],
        "terminal_bottom_lock_interval": [terminal_lower, terminal_upper],
        "backward_layer_summaries": layers,
        "geometry_seed_count": len(seeds),
        "exact_geometry_seed_errors": seeds,
        "actual_geometry_seed_error": actual_seed,
        "actual_seed_is_admissible": True,
        "exact_forward_replays": replays,
        "all_replays_endpoint_trapped": True,
        "single_block_forced_crossing": False,
    }


def build_receipt(input_path: Path) -> dict[str, Any]:
    cone = build_cone(load_final_champion(input_path))
    contract = build_experiment_contract(
        problem_id="erdos_249",
        target_statement="Prove irrationality of sum_(n>=1) phi(n)/2^n.",
        claim_ceiling=(
            "Exact finite mechanism elimination at the c=490794 record word; "
            "no infinite endpoint trap, universal escape, or irrationality proof."
        ),
        hypothesis_id="single_prime_successor_lock_forces_backward_crossing",
        hypothesis_statement=(
            "The Lean-checked prime-successor bottom lock, propagated backward "
            "through the exact preceding totient letters while enforcing every "
            "endpoint bound, forces a lower-boundary crossing."
        ),
        probe_id="exact_integer_backward_precursor_cone",
        probe_question=(
            "Is the full integer preimage cone of the c=490794 bottom lock empty "
            "at the geometry-clear boundary?"
        ),
        computation=(
            "Enumerate the terminal integer interval allowed by the exact bottom-"
            "lock inequality, invert E_(h+1)=2E_h+phi(c+h+1)-k with parity checks, "
            "intersect every layer with its moving endpoint window, and replay all "
            "surviving seeds forward."
        ),
        falsifier=(
            "Any surviving geometry-boundary seed whose exact forward replay "
            "remains endpoint-trapped and reaches the terminal bottom-lock interval."
        ),
        stop_condition=(
            "Stop once the complete finite preimage cone is enumerated and every "
            "surviving seed is independently replayed."
        ),
        survival_consequence=(
            "An empty cone would open a local one-block route from cofinal prime "
            "bottom locks to endpoint escape."
        ),
        falsification_consequence=(
            "A nonempty cone eliminates the one-block route; any successful proof "
            "must couple multiple locks or add a cross-gap arithmetic invariant."
        ),
        consumer_ref=LEAN_REF,
        analysis_refs=[ANALYSIS_REF, LEAN_REF],
        source_refs=[SOURCE_REF, INPUT_REF],
        result_status="exact_one_way_result",
        result_summary=(
            f"The exact 14-letter preimage cone has {cone['geometry_seed_count']} "
            "geometry-boundary seeds.  Every seed replays inside every endpoint "
            "window to the prime-successor bottom lock, and the actual seed "
            f"{cone['actual_geometry_seed_error']} is among them.  Thus one local "
            "bottom lock plus the exact intervening letters does not force escape."
        ),
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos249-prime-successor-precursor-cone/1",
        "status": "verified_exact_single_block_mechanism_elimination",
        "experiment_contract": contract,
        "precursor_cone_certificate": cone,
        "consequence_decisions": [
            {
                "mechanism": "single_bottom_lock_exact_one_block_backward_propagation",
                "decision": "eliminated",
                "reason": "complete exact preimage cone is nonempty",
            },
            {
                "mechanism": "multiple_lock_or_cross_gap_arithmetic_coupling",
                "decision": "opened_as_required_stronger_input",
                "reason": "the single-block consumer cannot force a crossing",
            },
            {
                "mechanism": "universal_escape_or_irrationality",
                "decision": "not_claimed",
                "reason": "certificate is finite and local",
            },
        ],
        "source_records": [
            source_record(REPO_ROOT, SOURCE_REF),
            source_record(REPO_ROOT, INPUT_REF),
            source_record(REPO_ROOT, ANALYSIS_REF),
            source_record(REPO_ROOT, LEAN_REF),
        ],
    }


def emit(payload: dict[str, Any], output: Path, check: bool) -> int:
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if check:
        if not output.exists() or output.read_text(encoding="utf-8") != rendered:
            print(f"stale receipt: {output}", file=sys.stderr)
            return 1
        print(json.dumps({"status": "current", "output": str(output)}))
        return 0
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(rendered, encoding="utf-8")
    print(json.dumps({"status": "written", "output": str(output)}))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=REPO_ROOT / INPUT_REF)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    return emit(build_receipt(args.input), args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
