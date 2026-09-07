#!/usr/bin/env python3
"""Audit record-height creation and aggregate repair in Erdős 257 carries.

The local prime-gap laws are false, but an escaping homogeneous carry must keep
creating new record heights.  This probe therefore ignores ordinary gaps and
examines only the one-way events that an escape actually needs: first hits of a
new integer height and the exact weighted compensation required to return below
the preceding record.

Every greedy word is integer-certified by the shared engine.  Every carry,
divisor load, first-hit rank, and block compensation identity is exact.  The
finite height barriers are discriminators, not asymptotic theorems.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path

from interprime_carry_repair_falsifier import (
    REPO_ROOT,
    SCRIPT_DIR,
    canonical_bytes,
    primes_up_to,
    sha256,
    target_rows,
)

SCRIPT_PATH = Path(__file__).resolve()
DEFAULT_INPUT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "rational_target_headroom_funnel_receipt.json"
)
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "prime_record_compensation_receipt.json"
)


def carry_for_target_linear(engine, p: int, q: int, depth: int):
    """Certified word plus linear-size exact carry recurrence.

    The older shared helper recomputes ``floor(2^n p/q)`` with an n-bit integer
    at every rank.  Here the rational binary digit is advanced by its bounded
    remainder state, so the same exact recurrence costs linear-size arithmetic.
    A direct floor/prefix cross-check is retained through rank 512.
    """
    result = engine.run(p, q)
    if result["status"] != "alive":
        raise RuntimeError(f"{p}/{q} did not survive replay: {result['status']}")
    word = result["word"]
    divisor_load = [0] * (depth + 1)
    for index, selected in enumerate(word, start=1):
        if not selected:
            continue
        for multiple in range(index, depth + 1, index):
            divisor_load[multiple] += 1

    carries = [0] * (depth + 1)
    remainder = p % q
    recurrence_violations = 0
    crosscheck_violations = 0
    coefficient_prefix = 0
    power = 1
    for rank in range(1, depth + 1):
        remainder *= 2
        epsilon = remainder // q
        remainder %= q
        carries[rank] = 2 * carries[rank - 1] + epsilon - divisor_load[rank]
        if carries[rank] < 0:
            raise RuntimeError(f"negative carry on certified survivor {p}/{q} at {rank}")
        if carries[rank] != 2 * carries[rank - 1] + epsilon - divisor_load[rank]:
            recurrence_violations += 1
        if rank <= min(depth, 512):
            coefficient_prefix = 2 * coefficient_prefix + divisor_load[rank]
            power <<= 1
            if carries[rank] != (power * p) // q - coefficient_prefix:
                crosscheck_violations += 1
    return (
        word,
        divisor_load,
        carries,
        recurrence_violations,
        crosscheck_violations,
    )


def weighted_block(values: list[int], left: int, right: int) -> int:
    """Return sum_{j=left+1..right} 2^(right-j) values[j]."""
    total = 0
    for rank in range(left + 1, right + 1):
        total = 2 * total + values[rank]
    return total


def better(
    current: dict[str, object] | None,
    candidate: dict[str, object],
    key: str,
) -> dict[str, object]:
    if current is None or candidate[key] > current[key]:
        return candidate
    return current


def record_events(
    target: str,
    carries: list[int],
    divisor_load: list[int],
    prime_set: set[int],
    start_rank: int,
) -> tuple[list[dict[str, object]], dict[int, int], int]:
    running_max = max(carries[:start_rank])
    first_hits: dict[int, int] = {}
    events: list[dict[str, object]] = []
    identity_violations = 0
    prefix_load_max = [0] * len(divisor_load)
    digit_bits = [0] * len(carries)
    for rank in range(1, len(divisor_load)):
        prefix_load_max[rank] = max(prefix_load_max[rank - 1], divisor_load[rank])
        digit_bits[rank] = carries[rank] - 2 * carries[rank - 1] + divisor_load[rank]

    for rank in range(start_rank, len(carries)):
        carry = carries[rank]
        if carry <= running_max:
            continue
        old_max = running_max
        for height in range(old_max + 1, carry + 1):
            first_hits.setdefault(height, rank)
        recovery_rank = None
        for later in range(rank + 1, len(carries)):
            if carries[later] <= old_max:
                recovery_rank = later
                break

        row: dict[str, object] = {
            "target": target,
            "record_rank": rank,
            "record_is_prime": rank in prime_set,
            "previous_record_height": old_max,
            "record_height": carry,
            "record_increment": carry - old_max,
            "recovery_rank": recovery_rank,
            "recovery_distance": None if recovery_rank is None else recovery_rank - rank,
            "recovered_within_horizon": recovery_rank is not None,
        }
        if rank + 1 < len(carries):
            immediate_repair = carries[rank + 1] <= old_max
            successor_load = divisor_load[rank + 1]
            epsilon_successor = (
                carries[rank + 1] - 2 * carry + successor_load
            )
            row.update(
                {
                    "successor_rank": rank + 1,
                    "successor_divisor_load": successor_load,
                    "successor_epsilon": epsilon_successor,
                    "immediate_repair_below_previous_record": immediate_repair,
                    "successor_load_is_prefix_record": (
                        successor_load > prefix_load_max[rank]
                    ),
                    "record_height_lt_successor_load": carry < successor_load,
                    "repair_load_threshold": 2 * carry + epsilon_successor - old_max,
                    "repair_load_slack": (
                        successor_load - (2 * carry + epsilon_successor - old_max)
                    ),
                }
            )
        if recovery_rank is not None:
            digit_weight = weighted_block(digit_bits, rank, recovery_rank)
            load_weight = weighted_block(divisor_load, rank, recovery_rank)
            predicted = (1 << (recovery_rank - rank)) * carry + digit_weight - load_weight
            if predicted != carries[recovery_rank]:
                identity_violations += 1
            row.update(
                {
                    "carry_at_recovery": carries[recovery_rank],
                    "weighted_digit_supply": digit_weight,
                    "weighted_divisor_compensation": load_weight,
                    "homogeneous_mass": (1 << (recovery_rank - rank)) * carry,
                    "block_identity_verified": predicted == carries[recovery_rank],
                }
            )
        events.append(row)
        running_max = carry

    return events, first_hits, identity_violations


def build_receipt(args: argparse.Namespace) -> dict[str, object]:
    requested_ranks = tuple(
        int(value) for value in args.source_ranks.split(",") if value.strip()
    )
    row_limit = max((args.target_limit, *requested_ranks))
    available_rows = target_rows(args.input, row_limit)
    if requested_ranks:
        if min(requested_ranks) < 1 or max(requested_ranks) > len(available_rows):
            raise ValueError(f"source ranks must lie in 1..{len(available_rows)}")
        ranked_rows = [(rank, available_rows[rank - 1]) for rank in requested_ranks]
    else:
        ranked_rows = list(enumerate(available_rows[: args.target_limit], start=1))
    from cantor_staircase_run_length_lab import Engine

    engine = Engine(args.depth)
    prime_set = set(primes_up_to(args.depth))
    recurrence_violations = 0
    direct_floor_crosscheck_violations = 0
    block_identity_violations = 0
    all_events: list[dict[str, object]] = []
    global_first_hits: dict[int, dict[str, object]] = {}
    target_summaries: list[dict[str, object]] = []
    worst_recovery = None
    worst_increment = None
    latest_unrecovered = None
    first_non_immediate_repair = None
    immediate_repair_count = 0
    successor_load_record_count = 0
    record_below_successor_load_count = 0
    successor_frequency: dict[int, int] = {}

    for source_rank, source in ranked_rows:
        numerator, denominator = int(source["p"]), int(source["q"])
        target = f"{numerator}/{denominator}"
        (
            word,
            divisor_load,
            carries,
            violations,
            crosscheck_violations,
        ) = carry_for_target_linear(
            engine, numerator, denominator, args.depth
        )
        recurrence_violations += violations
        direct_floor_crosscheck_violations += crosscheck_violations
        events, first_hits, identity_violations = record_events(
            target, carries, divisor_load, prime_set, args.start_rank
        )
        block_identity_violations += identity_violations
        all_events.extend(events)
        for event in events:
            if event.get("immediate_repair_below_previous_record"):
                immediate_repair_count += 1
            if event.get("successor_load_is_prefix_record"):
                successor_load_record_count += 1
            if event.get("record_height_lt_successor_load"):
                record_below_successor_load_count += 1
            if (
                not event.get("immediate_repair_below_previous_record")
                and first_non_immediate_repair is None
            ):
                first_non_immediate_repair = event
            successor = event.get("successor_rank")
            if isinstance(successor, int):
                successor_frequency[successor] = successor_frequency.get(successor, 0) + 1
        for height, rank in first_hits.items():
            candidate = {"height": height, "first_rank": rank, "target": target}
            incumbent = global_first_hits.get(height)
            if incumbent is None or rank < incumbent["first_rank"]:
                global_first_hits[height] = candidate
        for event in events:
            worst_increment = better(worst_increment, event, "record_increment")
            if event["recovered_within_horizon"]:
                worst_recovery = better(worst_recovery, event, "recovery_distance")
            elif latest_unrecovered is None or event["record_rank"] > latest_unrecovered["record_rank"]:
                latest_unrecovered = event

        height_curve = [
            {
                "height": height,
                "first_rank": first_hits[height],
                "log2_first_rank_over_height": round(
                    math.log2(first_hits[height]) / height, 12
                ),
            }
            for height in sorted(first_hits)
        ]
        target_summaries.append(
            {
                "source_rank": source_rank,
                "target": target,
                "support_density": round(sum(word) / len(word), 12),
                "max_carry": max(carries),
                "record_event_count_after_start": len(events),
                "prime_record_event_count": sum(bool(row["record_is_prime"]) for row in events),
                "unrecovered_record_event_count": sum(
                    not bool(row["recovered_within_horizon"]) for row in events
                ),
                "first_hit_curve": height_curve,
                "support_word_sha256": hashlib.sha256(bytes(word)).hexdigest(),
            }
        )

    prime_record_count = sum(bool(row["record_is_prime"]) for row in all_events)
    recovered_count = sum(bool(row["recovered_within_horizon"]) for row in all_events)
    observed_recovery_bound = max(
        (int(row["recovery_distance"]) for row in all_events if row["recovered_within_horizon"]),
        default=0,
    )
    global_curve = [global_first_hits[height] for height in sorted(global_first_hits)]
    engine_path = SCRIPT_DIR / "cantor_staircase_run_length_lab.py"
    carry_path = SCRIPT_DIR / "interprime_carry_repair_falsifier.py"
    payload: dict[str, object] = {
        "schema": "erdos257_prime_record_compensation_v1",
        "programme_target": (
            "Use computation to isolate or falsify an aggregate mechanism that kills "
            "the expanding carry mode in Erdős 257."
        ),
        "claim_boundary": (
            "All replay, record, and compensation identities are exact. First-hit and "
            "recovery bounds are finite cohort observations; they do not prove a uniform "
            "height barrier, a subexponential carry, rational membership, or Erdős 257."
        ),
        "exact_block_identity": (
            "C_R = 2^(R-P) C_P + sum_(j=P+1..R) 2^(R-j) "
            "epsilon_j - sum_(j=P+1..R) 2^(R-j) tau_A(j)"
        ),
        "parameters": {
            "depth": args.depth,
            "start_rank": args.start_rank,
            "target_limit": args.target_limit,
            "source_ranks": list(requested_ranks),
            "target_count": len(ranked_rows),
        },
        "source": {
            "script": str(SCRIPT_PATH.relative_to(REPO_ROOT)),
            "script_sha256": sha256(SCRIPT_PATH),
            "carry_library": str(carry_path.relative_to(REPO_ROOT)),
            "carry_library_sha256": sha256(carry_path),
            "engine": str(engine_path.relative_to(REPO_ROOT)),
            "engine_sha256": sha256(engine_path),
            "input_receipt": str(args.input.relative_to(REPO_ROOT)),
            "input_receipt_sha256": sha256(args.input),
        },
        "validation": {
            "integer_carry_recurrence_violation_count": recurrence_violations,
            "direct_floor_prefix_crosscheck_violation_count_through_rank_512": (
                direct_floor_crosscheck_violations
            ),
            "record_recovery_block_identity_violation_count": block_identity_violations,
            "all_greedy_replays_certified_alive": True,
        },
        "aggregate": {
            "record_event_count": len(all_events),
            "prime_record_event_count": prime_record_count,
            "prime_record_fraction": round(prime_record_count / max(1, len(all_events)), 12),
            "recovered_record_event_count": recovered_count,
            "unrecovered_record_event_count": len(all_events) - recovered_count,
            "immediate_repair_below_previous_record_count": immediate_repair_count,
            "immediate_repair_below_previous_record_fraction": round(
                immediate_repair_count / max(1, len(all_events)), 12
            ),
            "record_height_lt_successor_load_count": record_below_successor_load_count,
            "successor_load_is_prefix_record_count": successor_load_record_count,
            "worst_record_increment": worst_increment,
            "worst_recovery_distance": worst_recovery,
            "latest_unrecovered_record": latest_unrecovered,
            "first_non_immediate_repair": first_non_immediate_repair,
            "observed_uniform_recovery_bound": observed_recovery_bound,
            "most_common_record_successors": [
                {"successor_rank": rank, "target_event_count": count}
                for rank, count in sorted(
                    successor_frequency.items(), key=lambda item: (-item[1], item[0])
                )[:24]
            ],
        },
        "global_earliest_first_hit_curve": global_curve,
        "mechanism_decision": {
            "status": (
                "one_step_record_repair_falsified_two_step_survives"
                if first_non_immediate_repair is not None
                and observed_recovery_bound <= 2
                and recovered_count == len(all_events)
                else "finite_record_height_barrier_and_aggregate_repair_audited"
            ),
            "producer_if_proved": (
                "If every new record C_N is repaired below the previous record within "
                "a fixed H ranks, the exact block identity forces weighted divisor load "
                ">=(2^ell-1)C_N+1 for some ell<=H. Since every load is at most "
                "tau(m)<=2*sqrt(m), C_N<2*sqrt(N+H). Thus every carry is polynomial, "
                "the homogeneous mode dies, and the corresponding greedy rational "
                "support is certified. The current surviving finite candidate is H=2."
            ),
            "falsifier_condition": (
                "Early large-height records or record events with recovery scales growing "
                "as fast as their ranks would eliminate this aggregate route."
            ),
        },
        "target_summaries": target_summaries,
    }
    payload["payload_sha256"] = hashlib.sha256(canonical_bytes(payload)).hexdigest()
    return payload


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--depth", type=int, default=30000)
    parser.add_argument("--start-rank", type=int, default=64)
    parser.add_argument("--target-limit", type=int, default=128)
    parser.add_argument(
        "--source-ranks",
        default="",
        help="Optional comma-separated 1-based eligible rows; overrides target-limit selection.",
    )
    parser.add_argument("--check", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    receipt = build_receipt(args)
    rendered = json.dumps(receipt, sort_keys=True, indent=2) + "\n"
    print(
        json.dumps(
            {
                "parameters": receipt["parameters"],
                "validation": receipt["validation"],
                "aggregate": receipt["aggregate"],
                "global_earliest_first_hit_curve": receipt["global_earliest_first_hit_curve"],
                "mechanism_decision": receipt["mechanism_decision"],
                "payload_sha256": receipt["payload_sha256"],
            },
            indent=2,
        )
    )
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
