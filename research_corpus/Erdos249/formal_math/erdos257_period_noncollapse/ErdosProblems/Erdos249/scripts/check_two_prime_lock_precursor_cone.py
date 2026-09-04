#!/usr/bin/env python3
"""Test two exact prime-successor locks on an Erdős #249 record word.

The c=349 endpoint-cocycle champion contains trapped successors after the
distinct prime arguments 359 and 367.  This checker enumerates every integer
error allowed at the geometry-clear height, replays the actual totient word,
and intersects the moving endpoint window first through the successor of 359
and then through the successor of 367.

The second lock determines the actual initial error uniquely but still does
not force endpoint escape.  This is an exact finite counterexample to the
mechanism "two prime-successor locks force a crossing"; it is not an infinite
trap or an irrationality proof.
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
    "check_two_prime_lock_precursor_cone.py"
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
    "erdos249_two_prime_lock_precursor_cone_receipt.json"
)


def load_champion(input_path: Path) -> dict[str, Any]:
    payload = json.loads(input_path.read_text(encoding="utf-8"))
    champion = next(row for row in payload["scan"]["record_champions"] if row["c"] == 349)
    assert champion["geometry_clear_height"] == 10
    assert champion["first_central_height"] == 22
    assert champion["fixed_trap_quotient"] == 167
    return champion


def replay_seeds(
    rows: dict[int, dict[str, Any]],
    *,
    start_height: int,
    stop_height: int,
    quotient: int,
) -> list[dict[str, int]]:
    survivors: list[dict[str, int]] = []
    start_radius = rows[start_height]["radius"]
    for seed in range(-start_radius, start_radius + 1):
        error = seed
        minimum_margin = start_radius - abs(error)
        trapped = True
        for height in range(start_height + 1, stop_height + 1):
            error = 2 * error + rows[height]["totient_letter"] - quotient
            margin = rows[height]["radius"] - abs(error)
            minimum_margin = min(minimum_margin, margin)
            if margin < 0:
                trapped = False
                break
        if trapped:
            survivors.append(
                {
                    "geometry_seed_error": seed,
                    "terminal_error": error,
                    "minimum_endpoint_margin": minimum_margin,
                }
            )
    return survivors


def build_certificate(champion: dict[str, Any]) -> dict[str, Any]:
    c = champion["c"]
    quotient = champion["fixed_trap_quotient"]
    start_height = champion["geometry_clear_height"]
    rows = {row["height"]: row for row in champion["trajectory"]}

    lock_rows = []
    for height in sorted(rows):
        if height + 1 not in rows:
            continue
        row = rows[height]
        successor = rows[height + 1]
        if row["prime_argument"] and not successor["central"]:
            lock_rows.append(
                {
                    "prime_height": height,
                    "prime_argument": row["argument"],
                    "successor_height": height + 1,
                }
            )
    assert lock_rows == [
        {"prime_height": 10, "prime_argument": 359, "successor_height": 11},
        {"prime_height": 18, "prime_argument": 367, "successor_height": 19},
    ]

    first = replay_seeds(
        rows,
        start_height=start_height,
        stop_height=lock_rows[0]["successor_height"],
        quotient=quotient,
    )
    second = replay_seeds(
        rows,
        start_height=start_height,
        stop_height=lock_rows[1]["successor_height"],
        quotient=quotient,
    )
    actual_seed = rows[start_height]["signed_endpoint_error"]

    assert len(first) == 362
    assert [first[0]["geometry_seed_error"], first[-1]["geometry_seed_error"]] == [-145, 216]
    assert second == [
        {
            "geometry_seed_error": -15,
            "terminal_error": -109,
            "minimum_endpoint_margin": 238,
        }
    ]
    assert actual_seed == -15
    assert not rows[lock_rows[1]["successor_height"]]["central"]

    return {
        "basepoint_c": c,
        "fixed_quotient_k": quotient,
        "geometry_clear_height": start_height,
        "complete_geometry_seed_interval": [-rows[start_height]["radius"], rows[start_height]["radius"]],
        "complete_geometry_seed_count": 2 * rows[start_height]["radius"] + 1,
        "prime_successor_locks": lock_rows,
        "after_first_lock_successor": {
            "height": lock_rows[0]["successor_height"],
            "surviving_seed_count": len(first),
            "surviving_seed_range": [first[0]["geometry_seed_error"], first[-1]["geometry_seed_error"]],
        },
        "after_second_lock_successor": {
            "height": lock_rows[1]["successor_height"],
            "surviving_seed_count": len(second),
            "exact_survivors": second,
        },
        "actual_geometry_seed_error": actual_seed,
        "unique_survivor_is_actual_seed": True,
        "unique_survivor_remains_endpoint_trapped": True,
        "two_lock_forced_crossing": False,
    }


def build_receipt(input_path: Path) -> dict[str, Any]:
    certificate = build_certificate(load_champion(input_path))
    contract = build_experiment_contract(
        problem_id="erdos_249",
        target_statement="Prove irrationality of sum_(n>=1) phi(n)/2^n.",
        claim_ceiling=(
            "Exact finite mechanism elimination on the c=349 record word; no "
            "infinite endpoint trap, universal escape, or irrationality proof."
        ),
        hypothesis_id="two_prime_successor_locks_force_endpoint_escape",
        hypothesis_statement=(
            "Two distinct trapped prime successors, together with every exact "
            "intervening totient letter and endpoint bound, force a crossing."
        ),
        probe_id="complete_two_lock_integer_precursor_intersection",
        probe_question=(
            "Does the complete geometry-boundary seed interval become empty by "
            "the successor of the second prime lock?"
        ),
        computation=(
            "Enumerate all 721 integer errors at H=10, replay the exact fixed-k "
            "cocycle through each moving endpoint window, and intersect at the "
            "successors of the distinct primes 359 and 367."
        ),
        falsifier=(
            "A seed that remains endpoint-trapped through both prime successors; "
            "uniqueness is recorded separately and does not count as escape."
        ),
        stop_condition=(
            "Stop at the successor of the second distinct prime lock after the "
            "complete finite seed interval has been intersected; do not extend "
            "the trajectory merely to accumulate horizon."
        ),
        survival_consequence=(
            "An empty intersection would open a two-lock route from cofinal "
            "bottom locks to endpoint escape."
        ),
        falsification_consequence=(
            "A trapped survivor eliminates two-lock forced crossing.  Even a "
            "unique precursor is insufficient, so the next route needs a third "
            "lock or a genuinely global cross-gap invariant."
        ),
        consumer_ref=LEAN_REF,
        analysis_refs=[ANALYSIS_REF, LEAN_REF],
        source_refs=[SOURCE_REF, INPUT_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "The complete seed set contracts 721 -> 362 -> 1 at the two prime "
            "successors.  The unique seed is the actual E_10=-15, and it remains "
            "strictly endpoint-trapped through H=19 with E_19=-109 and minimum "
            "margin 238.  Thus two locks can determine the orbit without forcing "
            "escape."
        ),
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos249-two-prime-lock-precursor-cone/1",
        "status": "verified_exact_two_lock_mechanism_elimination",
        "experiment_contract": contract,
        "two_lock_certificate": certificate,
        "consequence_decisions": [
            {
                "mechanism": "two_prime_successor_locks_force_endpoint_crossing",
                "decision": "eliminated",
                "reason": "the complete intersection has a strictly trapped survivor",
            },
            {
                "mechanism": "precursor_uniqueness_implies_endpoint_escape",
                "decision": "eliminated",
                "reason": "the unique precursor is the actual trapped orbit",
            },
            {
                "mechanism": "third_lock_or_global_cross_gap_invariant",
                "decision": "opened_as_required_stronger_input",
                "reason": "one and two local locks are now both insufficient",
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
