#!/usr/bin/env python3
"""Deterministic large-denominator falsifier for record recovery.

The exhaustive companion controls all reduced denominators through 500.  This
probe samples a predeclared, reproducible set far beyond that cutoff and looks
specifically for a record whose recovery distance exceeds the finite-census
bound four.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import random
from pathlib import Path

from cantor_staircase_run_length_lab import Engine
from interprime_carry_repair_falsifier import REPO_ROOT, canonical_bytes, sha256
from prime_record_recovery_census import exact_carry, recovery_audit

SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_DIR = SCRIPT_PATH.parent
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "prime_record_recovery_random_receipt.json"
)


def sample_targets(args: argparse.Namespace) -> list[tuple[int, int]]:
    rng = random.Random(args.seed)
    targets: set[tuple[int, int]] = set()
    while len(targets) < args.samples:
        q = rng.randint(args.min_denominator, args.max_denominator)
        p = rng.randint(1, q - 1)
        g = math.gcd(p, q)
        p //= g
        q //= g
        if q >= args.min_denominator:
            targets.add((p, q))
    return sorted(targets, key=lambda row: (row[1], row[0]))


def build_receipt(args: argparse.Namespace) -> dict[str, object]:
    targets = sample_targets(args)
    engine = Engine(args.depth)
    alive_count = 0
    dead_count = 0
    precision_count = 0
    record_event_count = 0
    direct_violations = 0
    block_violations = 0
    first_over_four = None
    worst_recovery = None

    for p, q in targets:
        result = engine.run(p, q)
        if result["status"] == "dead":
            dead_count += 1
            continue
        if result["status"] != "alive":
            precision_count += 1
            continue
        alive_count += 1
        loads, carries, digits, violations = exact_carry(
            result["word"], p, q, args.depth
        )
        direct_violations += violations
        events, block_bad, worst, _ = recovery_audit(
            f"{p}/{q}", loads, carries, digits, args.start_rank
        )
        record_event_count += events
        block_violations += block_bad
        if worst is None:
            continue
        if worst_recovery is None:
            worst_recovery = worst
        elif worst["recovery_distance"] is None or (
            worst_recovery["recovery_distance"] is not None
            and worst["recovery_distance"] > worst_recovery["recovery_distance"]
        ):
            worst_recovery = worst
        if (
            first_over_four is None
            and (
                worst["recovery_distance"] is None
                or worst["recovery_distance"] > 4
            )
        ):
            first_over_four = worst

    census_path = SCRIPT_DIR / "prime_record_recovery_census.py"
    engine_path = SCRIPT_DIR / "cantor_staircase_run_length_lab.py"
    observed_bound = None if worst_recovery is None else worst_recovery["recovery_distance"]
    payload: dict[str, object] = {
        "schema": "erdos257_prime_record_recovery_random_v1",
        "programme_target": (
            "Challenge the finite H=4 record-recovery bound on a deterministic "
            "large-denominator rational cohort."
        ),
        "claim_boundary": (
            "The sample and replay are exact and reproducible, but not exhaustive beyond "
            "the declared sample. A surviving bound is finite evidence only."
        ),
        "parameters": {
            "seed": args.seed,
            "samples": args.samples,
            "min_denominator": args.min_denominator,
            "max_denominator": args.max_denominator,
            "depth": args.depth,
            "start_rank": args.start_rank,
        },
        "source": {
            "script": str(SCRIPT_PATH.relative_to(REPO_ROOT)),
            "script_sha256": sha256(SCRIPT_PATH),
            "census_library": str(census_path.relative_to(REPO_ROOT)),
            "census_library_sha256": sha256(census_path),
            "engine": str(engine_path.relative_to(REPO_ROOT)),
            "engine_sha256": sha256(engine_path),
        },
        "cohort": {
            "sampled_reduced_target_count": len(targets),
            "alive_target_count": alive_count,
            "dead_target_count": dead_count,
            "precision_target_count": precision_count,
            "record_event_count": record_event_count,
            "observed_uniform_recovery_bound": observed_bound,
        },
        "validation": {
            "direct_floor_prefix_crosscheck_violation_count_through_rank_256": direct_violations,
            "record_recovery_block_identity_violation_count": block_violations,
        },
        "falsifiers": {
            "first_recovery_distance_over_four": first_over_four,
            "worst_recovery": worst_recovery,
        },
        "mechanism_decision": {
            "status": (
                "finite_H4_record_recovery_falsified"
                if first_over_four is not None
                else "finite_H4_record_recovery_survives_large_denominator_sample"
            ),
            "next_action": (
                "replace H=4 by the exact observed witness or rotate if distances keep growing"
                if first_over_four is not None
                else "do not infer a theorem; seek structural proof or a different mechanism"
            ),
        },
    }
    payload["payload_sha256"] = hashlib.sha256(canonical_bytes(payload)).hexdigest()
    return payload


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=257)
    parser.add_argument("--samples", type=int, default=10000)
    parser.add_argument("--min-denominator", type=int, default=501)
    parser.add_argument("--max-denominator", type=int, default=1000000)
    parser.add_argument("--depth", type=int, default=5000)
    parser.add_argument("--start-rank", type=int, default=64)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    receipt = build_receipt(args)
    rendered = json.dumps(receipt, sort_keys=True, indent=2) + "\n"
    print(json.dumps({key: receipt[key] for key in (
        "parameters", "cohort", "validation", "falsifiers", "mechanism_decision", "payload_sha256"
    )}, indent=2))
    if args.check:
        if not args.check.is_file():
            print(f"missing receipt: {args.check}")
            return 2
        if args.check.read_text() != rendered:
            print(f"receipt drift: {args.check}")
            return 1
        print(f"CHECKED {args.check}")
        return 0
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(rendered)
    print(f"WROTE {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
