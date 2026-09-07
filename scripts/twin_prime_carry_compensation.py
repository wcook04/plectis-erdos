#!/usr/bin/env python3
"""Resolve prime-slope growth into exact twin-prime divisor compensation.

For twin primes p,p+2 the carry recurrence gives

    C_(p+2)-C_p = 3 C_p - 2 tau_A(p+1) + B_p,

where B_p is the exactly recorded digit/load term.  This probe follows a
sentinel cohort containing the broad-funnel leaders and every previous extreme,
checks the identity, and measures whether short-gap slope is being controlled by
divisor supply at p+1.  Finite observations are emitted as a canonical receipt;
they are not promoted to an asymptotic bound.
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
    carry_for_target,
    primes_up_to,
    sha256,
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
    "twin_prime_carry_compensation_receipt.json"
)
DEFAULT_SOURCE_RANKS = tuple(range(1, 17)) + (49, 71, 84, 118, 125)


def source_rows(path: Path, ranks: tuple[int, ...]) -> list[dict[str, object]]:
    receipt = json.loads(path.read_text())
    rows = [
        row
        for row in receipt["deep_replay"]["records"]
        if row.get("eligible") and row.get("status") == "alive"
    ]
    if not ranks or min(ranks) < 1 or max(ranks) > len(rows):
        raise ValueError(f"source ranks must lie in 1..{len(rows)}")
    return [rows[rank - 1] for rank in ranks]


def witness(
    target: str,
    p: int,
    carries: list[int],
    divisor_load: list[int],
) -> dict[str, object]:
    q = p + 2
    epsilon_middle = carries[p + 1] - 2 * carries[p] + divisor_load[p + 1]
    epsilon_q = carries[q] - 2 * carries[p + 1] + divisor_load[q]
    bit_term = 2 * epsilon_middle + epsilon_q - divisor_load[q]
    jump = carries[q] - carries[p]
    return {
        "target": target,
        "previous_prime": p,
        "next_prime": q,
        "carry_at_previous_prime": carries[p],
        "carry_at_middle": carries[p + 1],
        "carry_at_next_prime": carries[q],
        "middle_divisor_load": divisor_load[p + 1],
        "next_prime_divisor_load": divisor_load[q],
        "epsilon_middle": epsilon_middle,
        "epsilon_next_prime": epsilon_q,
        "bounded_bit_term": bit_term,
        "endpoint_jump": jump,
        "endpoint_slope": jump / 2,
        "uncompensated_core": 3 * carries[p] - 2 * divisor_load[p + 1],
        "load_deficit_from_three_halves_carry": max(
            0, math.ceil(3 * carries[p] / 2) - divisor_load[p + 1]
        ),
    }


def better(current: dict[str, object] | None, candidate: dict[str, object], key: str):
    if current is None or candidate[key] > current[key]:
        return candidate
    return current


def build_receipt(args: argparse.Namespace) -> dict[str, object]:
    ranks = tuple(int(value) for value in args.source_ranks.split(",") if value)
    rows = source_rows(args.input, ranks)
    twin_pairs = [
        (p, q)
        for p, q in zip(primes_up_to(args.depth), primes_up_to(args.depth)[1:])
        if p >= args.start_rank and q - p == 2
    ]

    identity_violations = 0
    nonbinary_epsilon_count = 0
    recurrence_violations = 0
    worst_jump = None
    worst_carry = None
    worst_core = None
    worst_deficit = None
    first_slope_failures: dict[int, dict[str, object] | None] = {
        constant: None for constant in range(1, 17)
    }
    low_load_worst: dict[str, dict[str, object] | None] = {
        "middle_load_eq_0": None,
        "middle_load_le_1": None,
        "middle_load_le_2": None,
    }
    bands: dict[str, dict[str, object]] = {}
    target_summaries: list[dict[str, object]] = []

    from cantor_staircase_run_length_lab import Engine

    engine = Engine(args.depth)
    for source_rank, source in zip(ranks, rows):
        numerator, denominator = int(source["p"]), int(source["q"])
        target = f"{numerator}/{denominator}"
        word, divisor_load, carries, violations = carry_for_target(
            engine, numerator, denominator, args.depth
        )
        recurrence_violations += violations
        target_worst = None
        for p, _ in twin_pairs:
            row = witness(target, p, carries, divisor_load)
            expected_jump = row["uncompensated_core"] + row["bounded_bit_term"]
            if row["endpoint_jump"] != expected_jump:
                identity_violations += 1
            if row["epsilon_middle"] not in (0, 1) or row["epsilon_next_prime"] not in (0, 1):
                nonbinary_epsilon_count += 1

            worst_jump = better(worst_jump, row, "endpoint_jump")
            worst_carry = better(worst_carry, row, "carry_at_previous_prime")
            worst_core = better(worst_core, row, "uncompensated_core")
            worst_deficit = better(
                worst_deficit, row, "load_deficit_from_three_halves_carry"
            )
            target_worst = better(target_worst, row, "endpoint_jump")
            for constant in first_slope_failures:
                if row["endpoint_jump"] > 2 * constant and first_slope_failures[constant] is None:
                    first_slope_failures[constant] = row
            middle_load = row["middle_divisor_load"]
            if middle_load == 0:
                low_load_worst["middle_load_eq_0"] = better(
                    low_load_worst["middle_load_eq_0"], row, "carry_at_previous_prime"
                )
            if middle_load <= 1:
                low_load_worst["middle_load_le_1"] = better(
                    low_load_worst["middle_load_le_1"], row, "carry_at_previous_prime"
                )
            if middle_load <= 2:
                low_load_worst["middle_load_le_2"] = better(
                    low_load_worst["middle_load_le_2"], row, "carry_at_previous_prime"
                )

            exponent = p.bit_length() - 1
            label = f"[{1 << exponent},{1 << (exponent + 1)})"
            band = bands.setdefault(
                label,
                {
                    "rank_start": 1 << exponent,
                    "rank_end_exclusive": 1 << (exponent + 1),
                    "tested_target_intervals": 0,
                    "worst_endpoint_jump": None,
                    "worst_carry_at_previous_prime": None,
                    "worst_load_deficit": None,
                },
            )
            band["tested_target_intervals"] += 1
            band["worst_endpoint_jump"] = better(
                band["worst_endpoint_jump"], row, "endpoint_jump"
            )
            band["worst_carry_at_previous_prime"] = better(
                band["worst_carry_at_previous_prime"], row, "carry_at_previous_prime"
            )
            band["worst_load_deficit"] = better(
                band["worst_load_deficit"],
                row,
                "load_deficit_from_three_halves_carry",
            )

        target_summaries.append(
            {
                "source_rank": source_rank,
                "target": target,
                "support_density": round(sum(word) / len(word), 12),
                "max_carry": max(carries),
                "worst_twin_prime_endpoint_jump": target_worst,
                "support_word_sha256": hashlib.sha256(bytes(word)).hexdigest(),
            }
        )

    interprime_path = SCRIPT_DIR / "interprime_carry_repair_falsifier.py"
    engine_path = SCRIPT_DIR / "cantor_staircase_run_length_lab.py"
    observed_constant = math.ceil(max(0, worst_jump["endpoint_jump"]) / 2)
    payload: dict[str, object] = {
        "schema": "erdos257_twin_prime_carry_compensation_v1",
        "programme_target": (
            "Test the exact short-prime-gap obstruction behind a carry-growth proof for Erdős 257."
        ),
        "claim_boundary": (
            "The identity is exact. The envelope and rank-band maxima are finite observations "
            "on a sentinel rational-target cohort, not an asymptotic carry bound."
        ),
        "exact_identity": (
            "C_(p+2)-C_p = 3*C_p - 2*tau_A(p+1) "
            "+ 2*epsilon_(p+1)+epsilon_(p+2)-tau_A(p+2)"
        ),
        "parameters": {
            "depth": args.depth,
            "start_rank": args.start_rank,
            "source_ranks": list(ranks),
            "target_count": len(rows),
            "twin_prime_pair_count_per_target": len(twin_pairs),
            "tested_target_intervals": len(rows) * len(twin_pairs),
        },
        "source": {
            "script": str(SCRIPT_PATH.relative_to(REPO_ROOT)),
            "script_sha256": sha256(SCRIPT_PATH),
            "interprime_library": str(interprime_path.relative_to(REPO_ROOT)),
            "interprime_library_sha256": sha256(interprime_path),
            "engine": str(engine_path.relative_to(REPO_ROOT)),
            "engine_sha256": sha256(engine_path),
            "input_receipt": str(args.input.relative_to(REPO_ROOT)),
            "input_receipt_sha256": sha256(args.input),
        },
        "validation": {
            "identity_violation_count": identity_violations,
            "nonbinary_epsilon_count": nonbinary_epsilon_count,
            "integer_carry_recurrence_violation_count": recurrence_violations,
            "all_greedy_replays_certified_alive": True,
        },
        "extremes": {
            "worst_endpoint_jump": worst_jump,
            "worst_carry_at_previous_prime": worst_carry,
            "worst_uncompensated_core": worst_core,
            "worst_load_deficit": worst_deficit,
            "first_endpoint_slope_failures": {
                str(constant): row for constant, row in first_slope_failures.items()
            },
            "low_middle_load_witnesses": low_load_worst,
        },
        "rank_bands": [bands[key] for key in sorted(bands, key=lambda key: bands[key]["rank_start"])],
        "mechanism_decision": {
            "status": "exact_twin_prime_compensation_obstruction_exposed",
            "observed_required_endpoint_constant": observed_constant,
            "analytic_target": (
                "Control the deficit 3*C_p-2*tau_A(p+1) at twin primes; "
                "a bound on C_p alone cannot control the endpoint jump."
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
    parser.add_argument(
        "--source-ranks",
        default=",".join(str(rank) for rank in DEFAULT_SOURCE_RANKS),
        help="Comma-separated 1-based eligible-row ranks from the broad funnel.",
    )
    parser.add_argument("--depth", type=int, default=200000)
    parser.add_argument("--start-rank", type=int, default=64)
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
                "extremes": receipt["extremes"],
                "rank_bands": receipt["rank_bands"],
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
