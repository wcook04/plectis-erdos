#!/usr/bin/env python3
"""Falsify one-gap prime/composite repair laws for the Erdős 257 carry.

At a prime p, tau_A(p)=1_A(p), so the forward carry has a forced spike.  A
natural proposed producer is that composite divisor supply before the next prime
q repairs that spike.  This program tests exact prime-to-prime inequalities on a
quotient-distinct rational-target cohort and emits the first and worst witnesses.

The greedy words are integer-certified.  Carries and divisor multiplicities are
integers.  The receipt is canonical and source-linked.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from pathlib import Path

SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_DIR = SCRIPT_PATH.parent
REPO_ROOT = SCRIPT_DIR.parents[2]
DEFAULT_INPUT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "rational_target_headroom_funnel_receipt.json"
)
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "interprime_carry_repair_falsifier_receipt.json"
)
sys.path.insert(0, str(SCRIPT_DIR))

from cantor_staircase_run_length_lab import Engine  # noqa: E402


def canonical_bytes(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def primes_up_to(limit: int) -> list[int]:
    sieve = bytearray([1]) * (limit + 1)
    sieve[0] = sieve[1] = 0
    for value in range(2, int(limit**0.5) + 1):
        if sieve[value]:
            sieve[value * value :: value] = bytearray(len(sieve[value * value :: value]))
    return [value for value in range(2, limit + 1) if sieve[value]]


def target_rows(path: Path, limit: int) -> list[dict[str, object]]:
    receipt = json.loads(path.read_text())
    rows = [
        row
        for row in receipt["deep_replay"]["records"]
        if row.get("eligible") and row.get("status") == "alive"
    ]
    return rows[:limit]


def carry_for_target(engine: Engine, p: int, q: int, depth: int):
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
    coefficient_prefix = 0
    power = 1
    remainder = p % q
    recurrence_violations = 0
    for rank in range(1, depth + 1):
        coefficient_prefix = 2 * coefficient_prefix + divisor_load[rank]
        power <<= 1
        carries[rank] = (power * p) // q - coefficient_prefix
        remainder *= 2
        epsilon = remainder // q
        remainder %= q
        if carries[rank] != 2 * carries[rank - 1] + epsilon - divisor_load[rank]:
            recurrence_violations += 1
    if min(carries) < 0:
        raise RuntimeError(f"negative carry on certified survivor {p}/{q}")
    return word, divisor_load, carries, recurrence_violations


def interval_witness(
    target: str,
    previous_prime: int,
    next_prime: int,
    carries: list[int],
    divisor_load: list[int],
) -> dict[str, object]:
    return {
        "target": target,
        "previous_prime": previous_prime,
        "next_prime": next_prime,
        "prime_gap": next_prime - previous_prime,
        "carry_at_previous_prime": carries[previous_prime],
        "carry_before_next_prime": carries[next_prime - 1],
        "carry_at_next_prime": carries[next_prime],
        "interior_divisor_load": divisor_load[previous_prime + 1 : next_prime],
    }


def build_receipt(args: argparse.Namespace) -> dict[str, object]:
    rows = target_rows(args.input, args.target_limit)
    engine = Engine(args.depth)
    primes = primes_up_to(args.depth)
    pairs = [
        (left, right)
        for left, right in zip(primes, primes[1:])
        if left >= args.start_rank
    ]
    first_pre_failure = None
    first_peak_failure = None
    first_log4_failure = None
    worst_jump = (-10**9, None)
    worst_prime_slope = (-1.0, None)
    worst_interior_excess_slope = (-1.0, None)
    first_prime_slope_failures: dict[int, dict[str, object] | None] = {
        constant: None for constant in range(1, 9)
    }
    first_interior_slope_failures: dict[int, dict[str, object] | None] = {
        constant: None for constant in range(1, 9)
    }
    worst_pre_ratio = (-1.0, None)
    worst_log_envelope = (-10**9, None)
    longest_failure_run = (0, None)
    reset_count = 0
    interval_count = 0
    recurrence_violations = 0
    target_summaries = []

    for source in rows:
        p, q = int(source["p"]), int(source["q"])
        target = f"{p}/{q}"
        word, divisor_load, carries, violations = carry_for_target(engine, p, q, args.depth)
        recurrence_violations += violations
        current_run = 0
        run_start = None
        target_reset_count = 0
        for previous_prime, next_prime in pairs:
            interval_count += 1
            repaired = carries[next_prime - 1] <= carries[previous_prime]
            if repaired:
                reset_count += 1
                target_reset_count += 1
                current_run = 0
                run_start = None
            else:
                if current_run == 0:
                    run_start = previous_prime
                current_run += 1
                if current_run > longest_failure_run[0]:
                    longest_failure_run = (
                        current_run,
                        {
                            "target": target,
                            "start_prime": run_start,
                            "end_prime": next_prime,
                            "ending_carry": carries[next_prime - 1],
                        },
                    )
                if first_pre_failure is None:
                    first_pre_failure = interval_witness(
                        target, previous_prime, next_prime, carries, divisor_load
                    )
            if carries[next_prime] > carries[previous_prime] + 1 and first_peak_failure is None:
                first_peak_failure = interval_witness(
                    target, previous_prime, next_prime, carries, divisor_load
                )
            log4_bound = max(carries[previous_prime], math.ceil(math.log2(next_prime)) + 4)
            if carries[next_prime] > log4_bound and first_log4_failure is None:
                first_log4_failure = {
                    **interval_witness(target, previous_prime, next_prime, carries, divisor_load),
                    "candidate_bound": log4_bound,
                }
            jump = carries[next_prime] - carries[previous_prime]
            if jump > worst_jump[0]:
                worst_jump = (
                    jump,
                    interval_witness(target, previous_prime, next_prime, carries, divisor_load),
                )
            prime_slope = max(0, jump) / (next_prime - previous_prime)
            if prime_slope > worst_prime_slope[0]:
                worst_prime_slope = (
                    prime_slope,
                    interval_witness(target, previous_prime, next_prime, carries, divisor_load),
                )
            for constant in first_prime_slope_failures:
                if (
                    jump > constant * (next_prime - previous_prime)
                    and first_prime_slope_failures[constant] is None
                ):
                    first_prime_slope_failures[constant] = interval_witness(
                        target, previous_prime, next_prime, carries, divisor_load
                    )
            endpoint_peak = max(carries[previous_prime], carries[next_prime])
            interior_peak = max(carries[previous_prime : next_prime + 1])
            interior_excess = max(0, interior_peak - endpoint_peak)
            interior_slope = interior_excess / (next_prime - previous_prime)
            if interior_slope > worst_interior_excess_slope[0]:
                worst_interior_excess_slope = (
                    interior_slope,
                    {
                        **interval_witness(
                            target, previous_prime, next_prime, carries, divisor_load
                        ),
                        "interior_peak": interior_peak,
                        "endpoint_peak": endpoint_peak,
                    },
                )
            for constant in first_interior_slope_failures:
                if (
                    interior_excess > constant * (next_prime - previous_prime)
                    and first_interior_slope_failures[constant] is None
                ):
                    first_interior_slope_failures[constant] = {
                        **interval_witness(
                            target, previous_prime, next_prime, carries, divisor_load
                        ),
                        "interior_peak": interior_peak,
                        "endpoint_peak": endpoint_peak,
                    }
            ratio = carries[next_prime - 1] / max(1, carries[previous_prime])
            if ratio > worst_pre_ratio[0]:
                worst_pre_ratio = (
                    ratio,
                    interval_witness(target, previous_prime, next_prime, carries, divisor_load),
                )
        for rank in range(args.start_rank, args.depth + 1):
            excess = carries[rank] - math.ceil(math.log2(rank))
            if excess > worst_log_envelope[0]:
                worst_log_envelope = (
                    excess,
                    {
                        "target": target,
                        "rank": rank,
                        "carry": carries[rank],
                        "ceil_log2_rank": math.ceil(math.log2(rank)),
                    },
                )
        target_summaries.append(
            {
                "target": target,
                "support_density": round(sum(word) / len(word), 12),
                "max_carry": max(carries),
                "repaired_interval_count": target_reset_count,
                "prime_interval_count": len(pairs),
                "support_word_sha256": hashlib.sha256(bytes(word)).hexdigest(),
            }
        )

    engine_path = SCRIPT_DIR / "cantor_staircase_run_length_lab.py"
    observed_linear_constant = math.ceil(
        max(worst_prime_slope[0], worst_interior_excess_slope[0])
    )
    payload: dict[str, object] = {
        "schema": "erdos257_interprime_carry_repair_falsifier_v1",
        "programme_target": "Solve Erdős 257; this tests a disposable prime-gap producer.",
        "claim_boundary": (
            "The witnesses disprove one-gap monotone repair and the tested log-plus-four "
            "envelope. They do not disprove multi-gap, average-drift, or full-ancestry bounds."
        ),
        "candidate_laws": {
            "pre_next_le_previous_peak": "C_(q-1) <= C_p for consecutive primes p<q",
            "next_peak_le_previous_plus_one": "C_q <= C_p + 1",
            "next_peak_log4_envelope": "C_q <= max(C_p, ceil(log2 q)+4)",
            "prime_skeleton_lipschitz": "C_q-C_p <= K(q-p)",
            "intra_gap_lipschitz": (
                "max_(p<=m<=q) C_m-max(C_p,C_q) <= K(q-p)"
            ),
        },
        "parameters": {
            "depth": args.depth,
            "start_rank": args.start_rank,
            "target_limit": args.target_limit,
            "target_count": len(rows),
            "prime_interval_count_per_target": len(pairs),
        },
        "source": {
            "script": str(SCRIPT_PATH.relative_to(REPO_ROOT)),
            "script_sha256": sha256(SCRIPT_PATH),
            "engine": str(engine_path.relative_to(REPO_ROOT)),
            "engine_sha256": sha256(engine_path),
            "input_receipt": str(args.input.relative_to(REPO_ROOT)),
            "input_receipt_sha256": sha256(args.input),
        },
        "validation": {
            "integer_carry_recurrence_violation_count": recurrence_violations,
            "all_greedy_replays_certified_alive": True,
        },
        "aggregate": {
            "tested_prime_intervals": interval_count,
            "repaired_interval_count": reset_count,
            "repaired_interval_fraction": round(reset_count / interval_count, 12),
            "longest_consecutive_no_repair_run": {
                "length": longest_failure_run[0],
                **(longest_failure_run[1] or {}),
            },
        },
        "falsifiers": {
            "first_pre_next_le_previous_peak_failure": first_pre_failure,
            "first_next_peak_le_previous_plus_one_failure": first_peak_failure,
            "first_next_peak_log4_envelope_failure": first_log4_failure,
            "worst_prime_peak_jump": {"jump": worst_jump[0], **(worst_jump[1] or {})},
            "first_prime_slope_failures": {
                str(constant): witness
                for constant, witness in first_prime_slope_failures.items()
            },
            "first_interior_slope_failures": {
                str(constant): witness
                for constant, witness in first_interior_slope_failures.items()
            },
            "worst_prime_peak_slope": {
                "slope": round(worst_prime_slope[0], 12),
                **(worst_prime_slope[1] or {}),
            },
            "worst_interior_excess_slope": {
                "slope": round(worst_interior_excess_slope[0], 12),
                **(worst_interior_excess_slope[1] or {}),
            },
            "worst_pre_next_to_previous_peak_ratio": {
                "ratio": round(worst_pre_ratio[0], 12),
                **(worst_pre_ratio[1] or {}),
            },
            "worst_observed_log_envelope_excess": {
                "excess": worst_log_envelope[0],
                **(worst_log_envelope[1] or {}),
            },
        },
        "mechanism_decision": {
            "status": "single_prime_gap_repair_falsified",
            "surviving_scope": "prime-skeleton Lipschitz, aggregate-drift, or complete-ancestry repair only",
            "observed_linear_envelope_candidate": {
                "constant": observed_linear_constant,
                "statement": (
                    "For consecutive primes p<q, both C_q-C_p and the interior "
                    "excess above max(C_p,C_q) are at most constant*(q-p)."
                ),
                "producer_if_proved": (
                    "Telescoping prime gaps would give C_n=O(n), hence a tempered "
                    "carry and exclusion of the expanding homogeneous mode."
                ),
                "status": "finite_evidence_theorem_target_not_proved",
            },
        },
        "target_summaries": target_summaries,
    }
    payload["payload_sha256"] = hashlib.sha256(canonical_bytes(payload)).hexdigest()
    return payload


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--target-limit", type=int, default=128)
    parser.add_argument("--depth", type=int, default=10000)
    parser.add_argument("--start-rank", type=int, default=64)
    parser.add_argument("--check", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    receipt = build_receipt(args)
    rendered = json.dumps(receipt, sort_keys=True, indent=2) + "\n"
    print(json.dumps({
        "mechanism_decision": receipt["mechanism_decision"],
        "aggregate": receipt["aggregate"],
        "falsifiers": receipt["falsifiers"],
        "payload_sha256": receipt["payload_sha256"],
    }, indent=2))
    if args.check:
        if not args.check.is_file():
            print(f"missing receipt: {args.check}", file=sys.stderr)
            return 2
        if args.check.read_text() != rendered:
            print(f"receipt drift: {args.check}", file=sys.stderr)
            return 1
        print(f"CHECKED {args.check}")
        return 0
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(rendered)
    print(f"WROTE {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
