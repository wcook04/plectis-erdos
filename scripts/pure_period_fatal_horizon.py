#!/usr/bin/env python3
"""Exhaust pure binary periods for late Mersenne-greedy fatality.

For every

    x = m / (2^P - 1),  1 <= m < 2^P - 1,

the binary source is purely periodic with a period dividing ``P``.  This
program enumerates the complete numerator lattice for each requested ``P``.
Greedy decisions and comparisons with the infinite remaining Mersenne tail
are made with directed dyadic intervals; uncertain comparisons are reported,
never guessed.  Exact ``Fraction`` arithmetic verifies the sparse boundary
cases where the target hits a Mersenne weight exactly.

The experiment is finite.  Absence of a fatal rank through ``depth_factor*P``
does not prove absence at all later ranks.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path


SCRIPT_PATH = Path(__file__).resolve()
REPO_ROOT = SCRIPT_PATH.parents[3]
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "pure_period_fatal_horizon_receipt.json"
)


def canonical_bytes(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def divisor_count(value: int) -> int:
    count = 0
    root = math.isqrt(value)
    for divisor in range(1, root + 1):
        if value % divisor == 0:
            count += 2
    if root * root == value:
        count -= 1
    return count


def exact_boundary_support(
    numerator: int, denominator: int, boundary_rank: int
) -> list[int]:
    """Verify that a directed ambiguity is an exact finite greedy tie."""
    residual = Fraction(numerator, denominator)
    support: list[int] = []
    for rank in range(1, boundary_rank + 1):
        weight = Fraction(1, (1 << rank) - 1)
        if residual >= weight:
            residual -= weight
            support.append(rank)
    if residual:
        raise AssertionError(
            f"directed ambiguity at {boundary_rank} was not an exact finite tie"
        )
    return support


def dyadic_tables(precision: int) -> tuple[int, list[int], list[int], int]:
    scale = 1 << precision
    # At top=precision+1 the scaled floor of the weight is zero.  The omitted
    # infinite tail beyond top is less than one further scaled unit.
    top = precision + 1
    weights = [0] * (top + 2)
    for rank in range(1, top + 1):
        weights[rank] = scale // ((1 << rank) - 1)
    tails = [0] * (top + 2)
    for rank in range(top, 0, -1):
        tails[rank - 1] = tails[rank] + weights[rank]
    return scale, weights, tails, top


def classify_target(
    numerator: int,
    denominator: int,
    depth: int,
    scale: int,
    weights: list[int],
    tails: list[int],
    top: int,
) -> dict[str, object]:
    lower = scale * numerator // denominator
    upper = (scale * numerator + denominator - 1) // denominator
    selected = 0
    for rank in range(1, depth + 1):
        weight_floor = weights[rank]
        if lower >= weight_floor + 1:
            # residual - weight remains inside this directed interval because
            # floor(S*w) < S*w < floor(S*w)+1.
            lower -= weight_floor + 1
            upper -= weight_floor
            selected += 1
        elif upper <= weight_floor:
            pass
        else:
            support = exact_boundary_support(numerator, denominator, rank)
            return {
                "status": "finite_boundary",
                "rank": rank,
                "support": support,
            }

        tail_lower = tails[rank]
        # Each scaled floor loses less than one unit.  There are top-rank
        # remaining displayed terms, and the geometric tail past top costs
        # less than one unit; +2 keeps the strict comparison comfortably open.
        tail_upper = tails[rank] + (top - rank) + 2
        if lower > tail_upper:
            return {
                "status": "fatal",
                "rank": rank,
                "selected_before_fatal": selected,
                "certified_scaled_margin": lower - tail_upper,
            }
        if upper <= tail_lower:
            continue
        return {
            "status": "tail_ambiguous",
            "rank": rank,
            "residual_interval": [lower, upper],
            "tail_interval": [tail_lower, tail_upper],
        }
    return {
        "status": "safe_through_depth",
        "rank": depth,
        "selected": selected,
    }


def run(max_period: int, depth_factor: int, precision: int) -> dict[str, object]:
    maximum_depth = max_period * depth_factor
    if precision < 2 * maximum_depth + 256:
        raise ValueError("precision must be at least 2*maximum_depth+256")
    scale, weights, tails, top = dyadic_tables(precision)
    rows: list[dict[str, object]] = []
    global_counts = {
        "targets": 0,
        "certified_fatal": 0,
        "finite_boundary": 0,
        "safe_through_depth": 0,
        "tail_ambiguous": 0,
        "fatal_at_or_after_own_period": 0,
    }
    for period in range(2, max_period + 1):
        denominator = (1 << period) - 1
        depth = depth_factor * period
        fatal_histogram: dict[int, int] = {}
        finite_rows: list[dict[str, object]] = []
        safe_numerators: list[int] = []
        counts = {
            "targets": denominator - 1,
            "certified_fatal": 0,
            "finite_boundary": 0,
            "safe_through_depth": 0,
            "tail_ambiguous": 0,
            "fatal_at_or_after_own_period": 0,
        }
        for numerator in range(1, denominator):
            result = classify_target(
                numerator,
                denominator,
                depth,
                scale,
                weights,
                tails,
                top,
            )
            status = str(result["status"])
            if status == "fatal":
                rank = int(result["rank"])
                counts["certified_fatal"] += 1
                fatal_histogram[rank] = fatal_histogram.get(rank, 0) + 1
                if rank >= period:
                    counts["fatal_at_or_after_own_period"] += 1
            elif status == "finite_boundary":
                counts["finite_boundary"] += 1
                if len(finite_rows) < 16:
                    finite_rows.append(
                        {
                            "numerator": numerator,
                            "rank": result["rank"],
                            "support": result["support"],
                        }
                    )
            elif status == "safe_through_depth":
                counts["safe_through_depth"] += 1
                if len(safe_numerators) < 16:
                    safe_numerators.append(numerator)
            else:
                counts["tail_ambiguous"] += 1

        tau_period = divisor_count(period)
        expected = {
            "certified_fatal": (1 << (period - 1)) - 1,
            "finite_boundary": (1 << (tau_period - 1)) - 1,
            "safe_through_depth": (
                (1 << (period - 1)) - (1 << (tau_period - 1))
            ),
        }
        exact_partition_formula = all(counts[key] == value for key, value in expected.items())
        maximum_fatal_rank = max(fatal_histogram, default=None)
        row = {
            "period": period,
            "denominator": denominator,
            "depth": depth,
            "divisor_count_of_period": tau_period,
            "counts": counts,
            "expected_partition_counts": expected,
            "exact_partition_formula_verified": exact_partition_formula,
            "maximum_certified_fatal_rank": maximum_fatal_rank,
            "maximum_fatal_rank_equals_period_minus_one": (
                maximum_fatal_rank == period - 1
            ),
            "fatal_histogram": {
                str(rank): count for rank, count in sorted(fatal_histogram.items())
            },
            "sample_finite_boundaries": finite_rows,
            "sample_safe_numerators": safe_numerators,
        }
        rows.append(row)
        for key in global_counts:
            global_counts[key] += counts[key]

    validation_ok = bool(
        all(row["exact_partition_formula_verified"] for row in rows)
        and all(row["maximum_fatal_rank_equals_period_minus_one"] for row in rows)
        and global_counts["tail_ambiguous"] == 0
        and global_counts["fatal_at_or_after_own_period"] == 0
    )
    receipt: dict[str, object] = {
        "schema": "pure_period_fatal_horizon_receipt_v0",
        "parameters": {
            "minimum_period": 2,
            "maximum_period": max_period,
            "depth_factor": depth_factor,
            "dyadic_precision_bits": precision,
            "target_family": "m/(2^P-1), 1<=m<2^P-1",
        },
        "global_counts": global_counts,
        "period_rows": rows,
        "mechanism_decision": {
            "candidate": (
                "pure-period fatal-horizon conjecture: if a rational target "
                "with binary period P ever enters a greedy fatal gap, its "
                "first fatal rank is strictly below P"
            ),
            "one_way_consequence_if_proved": (
                "any non-finite pure-period target surviving its first P "
                "ranks has an infinite Mersenne support with rational sum"
            ),
            "finite_result": (
                f"the complete numerator lattices for P=2..{max_period} have "
                f"no certified fatality at or after P through depth {depth_factor}P"
            ),
        },
        "validation": {
            "script_sha256": sha256(SCRIPT_PATH),
            "ok": validation_ok,
        },
        "claim_status": (
            "exact finite directed-interval census with rigorous infinite-tail "
            "bounds; no all-depth fatal-horizon theorem or Erdos 257 conclusion"
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
    parser.add_argument("--max-period", type=int, default=20)
    parser.add_argument("--depth-factor", type=int, default=8)
    parser.add_argument("--precision", type=int, default=2048)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check-receipt", type=Path)
    args = parser.parse_args()
    if args.check_receipt:
        check_receipt(args.check_receipt)
        return
    if args.max_period < 2 or args.depth_factor < 1:
        raise SystemExit("require max_period>=2 and depth_factor>=1")
    receipt = run(args.max_period, args.depth_factor, args.precision)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(canonical_bytes(receipt))
    print(
        json.dumps(
            {
                "output": str(args.output),
                "parameters": receipt["parameters"],
                "global_counts": receipt["global_counts"],
                "mechanism_decision": receipt["mechanism_decision"],
                "validation": receipt["validation"],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
