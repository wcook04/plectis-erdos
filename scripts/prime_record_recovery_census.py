#!/usr/bin/env python3
"""Exhaustively challenge bounded record recovery over reduced rationals.

This is the breadth adversary for ``prime_record_compensation.py``.  It scans
every reduced p/q in (0,1) up to a denominator cutoff, keeps exactly the greedy
words certified alive to the requested depth, and measures how many ranks a new
carry record needs to fall back below the preceding record.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path

from cantor_staircase_run_length_lab import Engine
from interprime_carry_repair_falsifier import REPO_ROOT, canonical_bytes, sha256

SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_DIR = SCRIPT_PATH.parent
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "prime_record_recovery_census_receipt.json"
)


def exact_carry(word: list[int], p: int, q: int, depth: int):
    loads = [0] * (depth + 1)
    for divisor, selected in enumerate(word, start=1):
        if selected:
            for multiple in range(divisor, depth + 1, divisor):
                loads[multiple] += 1
    carries = [0] * (depth + 1)
    digits = [0] * (depth + 1)
    remainder = p % q
    coefficient_prefix = 0
    power = 1
    direct_violations = 0
    for rank in range(1, depth + 1):
        remainder *= 2
        digits[rank] = remainder // q
        remainder %= q
        carries[rank] = 2 * carries[rank - 1] + digits[rank] - loads[rank]
        if carries[rank] < 0:
            raise RuntimeError(f"negative carry for certified survivor {p}/{q} at {rank}")
        if rank <= min(depth, 256):
            coefficient_prefix = 2 * coefficient_prefix + loads[rank]
            power <<= 1
            if carries[rank] != (power * p) // q - coefficient_prefix:
                direct_violations += 1
    return loads, carries, digits, direct_violations


def weighted(values: list[int], left: int, right: int) -> int:
    total = 0
    for rank in range(left + 1, right + 1):
        total = 2 * total + values[rank]
    return total


def recovery_audit(
    target: str,
    loads: list[int],
    carries: list[int],
    digits: list[int],
    start_rank: int,
):
    running_max = max(carries[:start_rank])
    event_count = 0
    block_violations = 0
    worst = None
    first_non_immediate = None
    for rank in range(start_rank, len(carries)):
        carry = carries[rank]
        if carry <= running_max:
            continue
        event_count += 1
        old_max = running_max
        recovery_rank = None
        for later in range(rank + 1, len(carries)):
            if carries[later] <= old_max:
                recovery_rank = later
                break
        distance = None if recovery_rank is None else recovery_rank - rank
        row = {
            "target": target,
            "record_rank": rank,
            "previous_record_height": old_max,
            "record_height": carry,
            "recovery_rank": recovery_rank,
            "recovery_distance": distance,
            "recovered_within_horizon": recovery_rank is not None,
        }
        if recovery_rank is not None:
            digit_weight = weighted(digits, rank, recovery_rank)
            load_weight = weighted(loads, rank, recovery_rank)
            homogeneous = (1 << distance) * carry
            predicted = homogeneous + digit_weight - load_weight
            verified = predicted == carries[recovery_rank]
            block_violations += not verified
            row.update(
                {
                    "carry_at_recovery": carries[recovery_rank],
                    "weighted_digit_supply": digit_weight,
                    "weighted_divisor_compensation": load_weight,
                    "homogeneous_mass": homogeneous,
                    "block_identity_verified": verified,
                }
            )
        if distance != 1 and first_non_immediate is None:
            first_non_immediate = row
        if worst is None:
            worst = row
        elif distance is None or (
            worst["recovery_distance"] is not None and distance > worst["recovery_distance"]
        ):
            worst = row
        running_max = carry
    return event_count, block_violations, worst, first_non_immediate


def build_receipt(args: argparse.Namespace) -> dict[str, object]:
    engine = Engine(args.depth)
    reduced_target_count = 0
    alive_count = 0
    dead_count = 0
    precision_count = 0
    record_event_count = 0
    direct_violations = 0
    block_violations = 0
    first_non_immediate = None
    worst_recovery = None
    first_recovery_over_two = None

    for q in range(2, args.max_denominator + 1):
        for p in range(1, q):
            if math.gcd(p, q) != 1:
                continue
            reduced_target_count += 1
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
            events, block_bad, worst, non_immediate = recovery_audit(
                f"{p}/{q}", loads, carries, digits, args.start_rank
            )
            record_event_count += events
            block_violations += block_bad
            if first_non_immediate is None and non_immediate is not None:
                first_non_immediate = non_immediate
            if worst is not None:
                if worst_recovery is None:
                    worst_recovery = worst
                elif worst["recovery_distance"] is None or (
                    worst_recovery["recovery_distance"] is not None
                    and worst["recovery_distance"] > worst_recovery["recovery_distance"]
                ):
                    worst_recovery = worst
                if (
                    first_recovery_over_two is None
                    and (
                        worst["recovery_distance"] is None
                        or worst["recovery_distance"] > 2
                    )
                ):
                    first_recovery_over_two = worst

    engine_path = SCRIPT_DIR / "cantor_staircase_run_length_lab.py"
    record_path = SCRIPT_DIR / "prime_record_compensation.py"
    observed_recovery_bound = (
        None if worst_recovery is None else worst_recovery["recovery_distance"]
    )
    payload: dict[str, object] = {
        "schema": "erdos257_prime_record_recovery_census_v1",
        "programme_target": (
            "Exhaustively seek a finite rational-target counterexample to the "
            "two-rank record-recovery mechanism for Erdős 257."
        ),
        "claim_boundary": (
            "This is exhaustive only for the declared denominator cutoff and finite "
            "depth. It can falsify a proposed finite law but cannot prove the all-depth "
            "record-recovery theorem, rational membership, or Erdős 257."
        ),
        "parameters": {
            "max_denominator": args.max_denominator,
            "depth": args.depth,
            "start_rank": args.start_rank,
        },
        "source": {
            "script": str(SCRIPT_PATH.relative_to(REPO_ROOT)),
            "script_sha256": sha256(SCRIPT_PATH),
            "engine": str(engine_path.relative_to(REPO_ROOT)),
            "engine_sha256": sha256(engine_path),
            "record_probe": str(record_path.relative_to(REPO_ROOT)),
            "record_probe_sha256": sha256(record_path),
        },
        "census": {
            "reduced_target_count": reduced_target_count,
            "alive_target_count": alive_count,
            "dead_target_count": dead_count,
            "precision_target_count": precision_count,
            "record_event_count": record_event_count,
            "observed_uniform_recovery_bound": observed_recovery_bound,
        },
        "validation": {
            "direct_floor_prefix_crosscheck_violation_count_through_rank_256": direct_violations,
            "record_recovery_block_identity_violation_count": block_violations,
        },
        "falsifiers": {
            "first_one_step_recovery_failure": first_non_immediate,
            "first_two_step_recovery_failure": first_recovery_over_two,
            "worst_recovery": worst_recovery,
        },
        "mechanism_decision": {
            "status": (
                "bounds_below_observed_falsified_observed_bound_survives_finite_census"
                if worst_recovery is not None
                else "no_record_events_in_declared_census"
            ),
            "next_action": (
                f"retain H={observed_recovery_bound} as the current proof target; "
                "seek a structural reason or an exact longer-recovery falsifier"
                if observed_recovery_bound is not None
                else "expand the declared census until record events occur"
            ),
            "claim_ceiling": (
                "The finite census falsifies every smaller observed recovery bound and "
                "retains only the displayed finite bound. It proves no uniform all-depth bound."
            ),
        },
    }
    payload["payload_sha256"] = hashlib.sha256(canonical_bytes(payload)).hexdigest()
    return payload


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-denominator", type=int, default=300)
    parser.add_argument("--depth", type=int, default=2000)
    parser.add_argument("--start-rank", type=int, default=64)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    receipt = build_receipt(args)
    rendered = json.dumps(receipt, sort_keys=True, indent=2) + "\n"
    print(json.dumps({key: receipt[key] for key in (
        "parameters", "census", "validation", "falsifiers", "mechanism_decision", "payload_sha256"
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
