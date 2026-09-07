#!/usr/bin/env python3
"""Expose the finite-horizon cylinder behind periodic carry MILPs.

For a periodic binary word ``epsilon`` enumerate every prefix satisfying

    C_n = 2 C_(n-1) + epsilon_n - sum_(d|n) b_d,
    b_n in {0,1},  C_0 = 0,  0 <= C_n <= floor(sqrt(n)) + 1.

The computation keeps the complete Boolean prefix as a Python bitset.  It
therefore detects rather than assumes uniqueness at a fixed terminal carry.
It also computes the ordinary superincreasing greedy word by directed dyadic
intervals and compares it with the common part of the carry tree.

This is a finite classifier.  A nonempty tree at a finite depth is not an
infinite support and does not settle Erdos 257.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path


SCRIPT_PATH = Path(__file__).resolve()
REPO_ROOT = SCRIPT_PATH.parents[3]
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "periodic_carry_tree_collapse_receipt.json"
)
CANDIDATE = {
    "name": "period_22_milp_target",
    "numerator": 152261,
    "denominator": (1 << 22) - 1,
    "word": "0000100101001011000101",
}
CONTROL = {
    "name": "one_over_twenty_one_control",
    "numerator": 1,
    "denominator": 21,
    "word": "000011",
}


def canonical_bytes(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def proper_divisors(rank: int) -> list[int]:
    result: list[int] = []
    for divisor in range(1, math.isqrt(rank) + 1):
        if rank % divisor:
            continue
        quotient = rank // divisor
        if divisor < rank:
            result.append(divisor)
        if quotient != divisor and quotient < rank:
            result.append(quotient)
    return result


def directed_greedy_bits(numerator: int, denominator: int, depth: int) -> int:
    """Return certified greedy decisions packed with rank one in bit zero."""
    precision = 2 * depth + 512
    scale = 1 << precision
    lower = scale * numerator // denominator
    upper = (scale * numerator + denominator - 1) // denominator
    bits = 0
    for rank in range(1, depth + 1):
        weight_floor = scale // ((1 << rank) - 1)
        if lower >= weight_floor + 1:
            lower -= weight_floor + 1
            upper -= weight_floor
            bits |= 1 << (rank - 1)
        elif upper <= weight_floor:
            continue
        else:
            raise AssertionError(f"directed interval undecided at rank {rank}")
    return bits


def common_prefix_length(bitsets: list[int], depth: int) -> int:
    if not bitsets:
        return 0
    varying = 0
    first = bitsets[0]
    for bits in bitsets[1:]:
        varying |= first ^ bits
    if not varying:
        return depth
    return (varying & -varying).bit_length() - 1


def packed_prefix_sha256(bits: int, depth: int) -> str:
    width = (depth + 7) // 8
    return hashlib.sha256(bits.to_bytes(width, "little")).hexdigest()


def enumerate_tree(spec: dict[str, object], depth: int) -> dict[str, object]:
    word = str(spec["word"])
    # terminal carry -> (Boolean prefix bitset, selected count)
    states: dict[int, tuple[int, int]] = {0: (0, 0)}
    first_full_interval_rank: int | None = None
    full_interval_persisted = True
    geometry: list[tuple[int, int, int, bool]] = []
    checkpoints: list[dict[str, object]] = []
    next_checkpoint = 8
    for rank in range(1, depth + 1):
        digit = int(word[(rank - 1) % len(word)])
        bound = math.isqrt(rank) + 1
        divisors = proper_divisors(rank)
        next_states: dict[int, tuple[int, int]] = {}
        collision_count = 0
        surviving_loads: set[int] = set()
        for carry, (bits, selected) in states.items():
            divisor_load = sum((bits >> (divisor - 1)) & 1 for divisor in divisors)
            raw_carry = 2 * carry + digit - divisor_load
            for support_bit in (0, 1):
                next_carry = raw_carry - support_bit
                if not 0 <= next_carry <= bound:
                    continue
                surviving_loads.add(divisor_load)
                if next_carry in next_states:
                    collision_count += 1
                    continue
                next_states[next_carry] = (
                    bits | (support_bit << (rank - 1)),
                    selected + support_bit,
                )
        if collision_count:
            raise AssertionError(
                f"{spec['name']}: {collision_count} terminal-carry collisions at {rank}"
            )
        states = next_states
        if not states:
            raise AssertionError(f"{spec['name']}: tree empty at rank {rank}")
        carries = sorted(states)
        full_interval = carries == list(range(bound + 1))
        if first_full_interval_rank is None and full_interval:
            first_full_interval_rank = rank
        if first_full_interval_rank is not None and not full_interval:
            full_interval_persisted = False
        geometry.append((rank, len(states), max(carries), full_interval))
        if rank == next_checkpoint or rank == depth:
            bitsets = [value[0] for value in states.values()]
            common = common_prefix_length(bitsets, rank)
            counts = [value[1] for value in states.values()]
            checkpoints.append(
                {
                    "rank": rank,
                    "carry_bound": bound,
                    "state_count": len(states),
                    "terminal_carry_range": [min(carries), max(carries)],
                    "full_terminal_carry_interval": full_interval,
                    "common_prefix_length": common,
                    "varying_suffix_width": rank - common,
                    "selected_count_range": [min(counts), max(counts)],
                    "surviving_proper_divisor_load_count": len(surviving_loads),
                }
            )
            next_checkpoint *= 2

    bitsets = [value[0] for value in states.values()]
    common = common_prefix_length(bitsets, depth)
    common_mask = (1 << common) - 1
    common_bits = bitsets[0] & common_mask
    greedy_bits = directed_greedy_bits(
        int(spec["numerator"]), int(spec["denominator"]), common
    )
    counts = [value[1] for value in states.values()]
    state_digest_payload = [
        {
            "terminal_carry": carry,
            "selected_count": selected,
            "support_sha256": packed_prefix_sha256(bits, depth),
        }
        for carry, (bits, selected) in sorted(states.items())
    ]
    return {
        "target": {
            "name": spec["name"],
            "numerator": spec["numerator"],
            "denominator": spec["denominator"],
            "periodic_word": word,
        },
        "depth": depth,
        "nonempty_at_every_rank": True,
        "first_full_terminal_carry_interval_rank": first_full_interval_rank,
        "full_interval_persisted_after_first_occurrence": full_interval_persisted,
        "terminal_state_count": len(states),
        "terminal_carry_range": [min(states), max(states)],
        "terminal_carry_bound": math.isqrt(depth) + 1,
        "terminal_common_prefix_length": common,
        "terminal_varying_suffix_width": depth - common,
        "terminal_selected_count_range": [min(counts), max(counts)],
        "common_prefix_matches_exact_greedy": common_bits == greedy_bits,
        "common_prefix_support_sha256": packed_prefix_sha256(common_bits, common),
        "terminal_state_digest": hashlib.sha256(
            canonical_bytes(state_digest_payload)
        ).hexdigest(),
        "checkpoints": checkpoints,
        "geometry_digest": hashlib.sha256(canonical_bytes(geometry)).hexdigest(),
    }


def build_receipt(candidate_depth: int, control_depth: int) -> dict[str, object]:
    candidate = enumerate_tree(CANDIDATE, candidate_depth)
    control = enumerate_tree(CONTROL, control_depth)
    shared_depth = min(candidate_depth, control_depth)
    candidate_rows = {
        row["rank"]: row for row in candidate["checkpoints"] if row["rank"] <= shared_depth
    }
    control_rows = {
        row["rank"]: row for row in control["checkpoints"] if row["rank"] <= shared_depth
    }
    shared_ranks = sorted(set(candidate_rows) & set(control_rows))
    geometry_fields = (
        "carry_bound",
        "state_count",
        "terminal_carry_range",
        "full_terminal_carry_interval",
    )
    shared_geometry_equal = all(
        all(candidate_rows[rank][field] == control_rows[rank][field] for field in geometry_fields)
        for rank in shared_ranks
    )
    receipt: dict[str, object] = {
        "schema": "periodic_carry_tree_collapse_receipt_v0",
        "parameters": {
            "candidate_depth": candidate_depth,
            "control_depth": control_depth,
            "carry_bound": "floor(sqrt(n))+1",
            "support_constraint": "b_n in {0,1}",
        },
        "candidate": candidate,
        "control": control,
        "comparison": {
            "shared_checkpoint_ranks": shared_ranks,
            "terminal_interval_geometry_equal_at_shared_checkpoints": shared_geometry_equal,
            "both_match_their_exact_greedy_common_prefix": bool(
                candidate["common_prefix_matches_exact_greedy"]
                and control["common_prefix_matches_exact_greedy"]
            ),
            "mechanism_decision": (
                "the period-22 MILP target has the same finite terminal-carry "
                "cylinder geometry as the 1/21 control; its long feasible "
                "prefix is a greedy-prefix survival certificate, not a "
                "structurally distinct offline rounding construction"
            ),
        },
        "validation": {
            "script_sha256": sha256(SCRIPT_PATH),
            "ok": bool(
                shared_geometry_equal
                and candidate["common_prefix_matches_exact_greedy"]
                and control["common_prefix_matches_exact_greedy"]
                and candidate["full_interval_persisted_after_first_occurrence"]
                and control["full_interval_persisted_after_first_occurrence"]
            ),
        },
        "claim_status": (
            "exact finite enumeration and directed-interval comparison; "
            "no all-depth branch or Erdos 257 conclusion is claimed"
        ),
    }
    receipt["canonical_digest"] = hashlib.sha256(canonical_bytes(receipt)).hexdigest()
    return receipt


def check_receipt(path: Path) -> None:
    receipt = json.loads(path.read_text())
    digest = receipt.pop("canonical_digest")
    if hashlib.sha256(canonical_bytes(receipt)).hexdigest() != digest:
        raise AssertionError("canonical receipt digest mismatch")
    if receipt["validation"]["script_sha256"] != sha256(SCRIPT_PATH):
        raise AssertionError("receipt source hash does not match current script")
    if not receipt["validation"]["ok"]:
        raise AssertionError("stored receipt is not valid")
    print(json.dumps({"receipt": str(path), "ok": True}, indent=2))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--candidate-depth", type=int, default=32768)
    parser.add_argument("--control-depth", type=int, default=8192)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check-receipt", type=Path)
    args = parser.parse_args()
    if args.check_receipt:
        check_receipt(args.check_receipt)
        return
    if args.candidate_depth < 64 or args.control_depth < 64:
        raise SystemExit("both depths must be at least 64")
    receipt = build_receipt(args.candidate_depth, args.control_depth)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(canonical_bytes(receipt))
    print(
        json.dumps(
            {
                "output": str(args.output),
                "candidate_depth": args.candidate_depth,
                "control_depth": args.control_depth,
                "validation": receipt["validation"],
                "comparison": receipt["comparison"],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
