#!/usr/bin/env python3
"""Exact denominator-grid probe for the canonical Erdős 249 residue normal form.

For a prospective rational denominator 2^c v with v odd, the latest Lean
reduction asks for an Euler-multiple height H such that, with

    M = (2^H - 1) / v,
    r = (-totientBlock(H,c)) mod M,

the residue r lies strictly between B=c+H+1 and M-B.  This checker searches
successive multiples H=t*phi(v), records the first central multiplier, and
falsifies proposed uniform bounds on t with exact witnesses.

Finite success does not prove the universal denominator statement.  A delay
violation, however, exactly eliminates the tested bounded-multiplier producer.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
import sys


REPO_ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
)


SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/"
    "scripts/check_canonical_mersenne_residue.py"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/"
    "CanonicalMersenneResidueComputationalLab.md"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/"
    "CyclotomicAnchoredKill.lean"
)


def totients_through(limit: int) -> list[int]:
    values = list(range(limit + 1))
    if limit >= 1:
        values[1] = 1
    for prime in range(2, limit + 1):
        if values[prime] == prime:
            for n in range(prime, limit + 1, prime):
                values[n] -= values[n] // prime
    return values


def attempt_record(c: int, v: int, multiplier: int, phi_v: int, block: int) -> dict[str, object]:
    height = multiplier * phi_v
    mersenne = (1 << height) - 1
    if mersenne % v != 0:
        raise AssertionError((c, v, height, "Euler divisibility failed"))
    modulus = mersenne // v
    radius = c + height + 1
    residue = (-block) % modulus
    interval_nonempty = 2 * radius < modulus
    central = interval_nonempty and radius < residue < modulus - radius
    return {
        "multiplier": multiplier,
        "height": height,
        "modulus": modulus,
        "radius": radius,
        "residue": residue,
        "distance_to_nearest_endpoint": min(residue, modulus - residue),
        "central_interval_nonempty": interval_nonempty,
        "central_gap": central,
    }


def scan(
    max_odd_denominator: int,
    max_dyadic_exponent: int,
    max_euler_multiplier: int,
    residue_delay_threshold: int,
) -> dict[str, object]:
    phi_den = totients_through(max_odd_denominator)
    max_height = max_euler_multiplier * max(phi_den[1:])
    phi_letters = totients_through(max_dyadic_exponent + max_height + 1)

    multiplier_histogram: dict[int, int] = {}
    delay_histogram: dict[int, int] = {}
    unresolved: list[dict[str, object]] = []
    violations: list[dict[str, object]] = []
    max_first_multiplier = 0
    max_residue_delay = 0
    max_cases: list[dict[str, object]] = []
    tested_pairs = 0

    for v in range(1, max_odd_denominator + 1, 2):
        phi_v = phi_den[v]
        for c in range(max_dyadic_exponent + 1):
            tested_pairs += 1
            block = 0
            trajectory: list[dict[str, object]] = []
            first: dict[str, object] | None = None
            first_geometry_clear: dict[str, object] | None = None
            next_target = phi_v
            multiplier = 1
            for height in range(1, max_euler_multiplier * phi_v + 1):
                block = 2 * block + phi_letters[c + height]
                if height != next_target:
                    continue
                record = attempt_record(c, v, multiplier, phi_v, block)
                trajectory.append(record)
                if first_geometry_clear is None and record["central_interval_nonempty"]:
                    first_geometry_clear = record
                if record["central_gap"]:
                    first = record
                    break
                multiplier += 1
                next_target += phi_v

            if first is None:
                unresolved.append(
                    {
                        "c": c,
                        "v": v,
                        "phi_v": phi_v,
                        "first_geometry_clear_multiplier": (
                            first_geometry_clear["multiplier"]
                            if first_geometry_clear is not None
                            else None
                        ),
                        "trajectory": trajectory,
                    }
                )
                continue

            first_multiplier = int(first["multiplier"])
            if first_geometry_clear is None:
                raise AssertionError("central residue without a nonempty interval")
            clear_multiplier = int(first_geometry_clear["multiplier"])
            residue_delay = first_multiplier - clear_multiplier
            multiplier_histogram[first_multiplier] = (
                multiplier_histogram.get(first_multiplier, 0) + 1
            )
            delay_histogram[residue_delay] = delay_histogram.get(residue_delay, 0) + 1
            case = {
                "c": c,
                "v": v,
                "phi_v": phi_v,
                "first_central_multiplier": first_multiplier,
                "first_central_height": first["height"],
                "first_geometry_clear_multiplier": clear_multiplier,
                "post_geometry_clear_residue_delay": residue_delay,
                "trajectory": trajectory,
            }
            if residue_delay > residue_delay_threshold:
                violations.append(case)
            if first_multiplier > max_first_multiplier:
                max_first_multiplier = first_multiplier
                max_cases = [case]
            elif first_multiplier == max_first_multiplier:
                max_cases.append(case)
            max_residue_delay = max(max_residue_delay, residue_delay)

    return {
        "tested_pairs": tested_pairs,
        "resolved_pair_count": tested_pairs - len(unresolved),
        "unresolved_pair_count": len(unresolved),
        "first_unresolved_pairs": unresolved[:20],
        "first_multiplier_histogram": {
            str(key): value for key, value in sorted(multiplier_histogram.items())
        },
        "post_geometry_clear_residue_delay_histogram": {
            str(key): value for key, value in sorted(delay_histogram.items())
        },
        "residue_delay_threshold": residue_delay_threshold,
        "threshold_violation_count": len(violations),
        "first_threshold_violations": violations[:20],
        "largest_first_central_multiplier": max_first_multiplier,
        "largest_first_central_multiplier_case_count": len(max_cases),
        "largest_first_central_multiplier_cases": max_cases[:50],
        "largest_post_geometry_clear_residue_delay": max_residue_delay,
    }


def emit(result: dict[str, object], output: Path | None, check: bool) -> int:
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if output is None:
        print(rendered, end="")
        return 0
    resolved = output.resolve()
    if check:
        if not resolved.exists() or resolved.read_text(encoding="utf-8") != rendered:
            print(f"stale receipt: {resolved}", file=sys.stderr)
            return 1
        print(json.dumps({"status": "current", "output": str(resolved)}))
        return 0
    resolved.parent.mkdir(parents=True, exist_ok=True)
    resolved.write_text(rendered, encoding="utf-8")
    print(json.dumps({"status": "written", "output": str(resolved)}))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-odd-denominator", type=int, default=75)
    parser.add_argument("--max-dyadic-exponent", type=int, default=20)
    parser.add_argument("--max-euler-multiplier", type=int, default=8)
    parser.add_argument("--residue-delay-threshold", type=int, default=4)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.max_odd_denominator < 1:
        parser.error("--max-odd-denominator must be positive")
    if args.max_dyadic_exponent < 0:
        parser.error("--max-dyadic-exponent must be nonnegative")
    if args.max_euler_multiplier < 1:
        parser.error("--max-euler-multiplier must be positive")
    if not 0 <= args.residue_delay_threshold <= args.max_euler_multiplier:
        parser.error("threshold must lie between zero and max multiplier")
    if args.check and args.output is None:
        parser.error("--check requires --output")

    result_scan = scan(
        args.max_odd_denominator,
        args.max_dyadic_exponent,
        args.max_euler_multiplier,
        args.residue_delay_threshold,
    )
    if result_scan["threshold_violation_count"]:
        status = "finite_counterexample"
        summary = (
            f"The exact grid contains {result_scan['threshold_violation_count']} "
            f"denominators whose residue stays trapped for more than "
            f"{args.residue_delay_threshold} Euler multiples after the central "
            "interval first becomes nonempty."
        )
    elif result_scan["unresolved_pair_count"]:
        status = "mixed"
        summary = (
            f"The exact grid leaves {result_scan['unresolved_pair_count']} pairs "
            f"unresolved through multiplier {args.max_euler_multiplier}."
        )
    else:
        status = "finite_support"
        summary = (
            f"Every one of {result_scan['tested_pairs']} exact denominator pairs "
            f"has a canonical central residue by multiplier "
            f"{result_scan['largest_first_central_multiplier']}."
        )

    result = {
        "schema": "erdos249-canonical-mersenne-residue-grid/1",
        "claim_ceiling": (
            "Finite denominator grid only; success does not prove the universal "
            "canonical-basepoint residue-gap supply or irrationality."
        ),
        "parameters": {
            "max_odd_denominator": args.max_odd_denominator,
            "max_dyadic_exponent": args.max_dyadic_exponent,
            "max_euler_multiplier": args.max_euler_multiplier,
            "residue_delay_threshold": args.residue_delay_threshold,
        },
        "scan": result_scan,
        "experiment_contract": build_experiment_contract(
            problem_id="erdos_249",
            target_statement=(
                "Prove irrationality of sum_{n>=1} phi(n)/2^n."
            ),
            claim_ceiling=(
                "Finite denominator/multiplier scans do not prove the universal "
                "canonical-basepoint residue-gap supply."
            ),
            hypothesis_id="uniform_post_geometry_residue_escape_delay",
            hypothesis_statement=(
                f"Once the central interval is nonempty, every denominator in "
                f"the probe grid reaches a central residue within "
                f"{args.residue_delay_threshold} additional Euler multiples."
            ),
            probe_id="canonical_mersenne_residue_denominator_grid",
            probe_question=(
                "After deterministic modulus growth makes the central interval "
                "possible, do exact denominators create long residue traps?"
            ),
            computation=(
                "For every 2^c v in the grid, build the exact totient block and "
                "test (-block) mod ((2^H-1)/v) at successive Euler multiples."
            ),
            falsifier=(
                f"Any exact (c,v) whose post-geometry-clear residue delay exceeds "
                f"{args.residue_delay_threshold}."
            ),
            stop_condition=(
                "At a delay violation, retire the proposed uniform multiplier "
                "and inspect its endpoint-residue trajectory; if no violation "
                "appears, formulate a structural centrality lemma rather than "
                "treating a larger grid as proof."
            ),
            survival_consequence=(
                "A universal short-multiplier theorem would instantiate the "
                "Lean canonical-basepoint gap supply and prove irrationality."
            ),
            falsification_consequence=(
                "The tested residue-delay constant is impossible even after "
                "separating deterministic interval growth; the producer must "
                "explain the exact endpoint trap."
            ),
            consumer_ref=CONSUMER_REF,
            analysis_refs=[ANALYSIS_REF],
            source_refs=[SOURCE_REF, CONSUMER_REF],
            result_status=status,
            result_summary=summary,
        ),
        "sources": [
            source_record(REPO_ROOT, SOURCE_REF),
            source_record(REPO_ROOT, CONSUMER_REF),
        ],
    }
    return emit(result, args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
