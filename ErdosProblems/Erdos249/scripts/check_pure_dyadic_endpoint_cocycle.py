#!/usr/bin/env python3
"""Exact pure-dyadic endpoint-cocycle scan for Erdős #249.

For ``v=1`` write ``Q_H=totientBlock(H,c)``, ``M_H=2^H-1``, and let ``k`` be
the nearest integer quotient of ``Q_H/M_H``.  The signed endpoint error

    E_H = Q_H - k M_H

obeys ``E_(H+1)=2E_H+phi(c+H+1)-k`` while ``k`` stays fixed.  The canonical
residue is endpoint-trapped exactly when ``|E_H| <= c+H+1`` once the central
interval is nonempty.  This checker uses a totient sieve, records every new
delay champion, and verifies the affine recurrence on each champion word.

Finite records do not prove unbounded delay or settle Erdős #249.
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
    "check_pure_dyadic_endpoint_cocycle.py"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/"
    "PureDyadicEndpointCocycleComputationalLab.md"
)
LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/"
    "PeriodMultipleEscape.lean"
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
            for multiple in range(prime, limit + 1, prime):
                values[multiple] -= values[multiple] // prime
    return values


def nearest_quotient(block: int, modulus: int) -> int:
    if modulus <= 0:
        raise ValueError("modulus must be positive")
    return (2 * block + modulus) // (2 * modulus)


def scan(max_c: int, max_height: int, delay_threshold: int) -> dict[str, Any]:
    phi = totients_through(max_c + max_height + 1)
    champions: list[dict[str, Any]] = []
    best_delay = -1
    resolved_count = 0
    unresolved_count = 0

    for c in range(max_c + 1):
        block = 0
        modulus = 0
        geometry_height: int | None = None
        trajectory: list[dict[str, Any]] = []
        escaped = False

        for height in range(1, max_height + 1):
            letter = phi[c + height]
            block = 2 * block + letter
            modulus = 2 * modulus + 1
            radius = c + height + 1
            if geometry_height is None and 2 * radius < modulus:
                geometry_height = height
            if geometry_height is None:
                continue

            quotient = nearest_quotient(block, modulus)
            error = block - quotient * modulus
            assert 2 * abs(error) <= modulus
            central = abs(error) > radius
            argument = c + height
            is_prime_argument = argument >= 2 and phi[argument] == argument - 1
            row = {
                "height": height,
                "argument": argument,
                "totient_letter": letter,
                "prime_argument": is_prime_argument,
                "nearest_quotient": quotient,
                "signed_endpoint_error": error,
                "radius": radius,
                "central": central,
            }
            if trajectory:
                previous = trajectory[-1]
                if quotient == previous["nearest_quotient"]:
                    predicted = (
                        2 * previous["signed_endpoint_error"]
                        + letter
                        - quotient
                    )
                    assert error == predicted
                    row["affine_recurrence_verified"] = True
                else:
                    row["affine_recurrence_verified"] = False
                if is_prime_argument and quotient == previous["nearest_quotient"]:
                    prime_lower_bound = argument - 1 - quotient
                    adjacent_error_budget = (
                        abs(error) + 2 * abs(previous["signed_endpoint_error"])
                    )
                    assert prime_lower_bound <= adjacent_error_budget
                    row["prime_excursion_certificate"] = {
                        "prime_minus_one_minus_quotient": prime_lower_bound,
                        "adjacent_error_budget": adjacent_error_budget,
                        "inequality_verified": True,
                    }
            trajectory.append(row)

            if central:
                escaped = True
                delay = height - geometry_height
                resolved_count += 1
                if delay > best_delay:
                    trap_rows = trajectory[:-1]
                    if trap_rows:
                        trap_quotients = {
                            item["nearest_quotient"] for item in trap_rows
                        }
                        assert len(trap_quotients) == 1
                        assert all(
                            item["affine_recurrence_verified"]
                            for item in trap_rows[1:]
                        )
                    best_delay = delay
                    champions.append(
                        {
                            "c": c,
                            "geometry_clear_height": geometry_height,
                            "first_central_height": height,
                            "post_geometry_clear_delay": delay,
                            "fixed_trap_quotient": (
                                trap_rows[0]["nearest_quotient"] if trap_rows else None
                            ),
                            "trajectory": trajectory,
                        }
                    )
                break

        if not escaped:
            unresolved_count += 1

    violations = [
        champion
        for champion in champions
        if champion["post_geometry_clear_delay"] > delay_threshold
    ]
    prime_excursion_rows = [
        {
            "c": champion["c"],
            "height": row["height"],
            "argument": row["argument"],
            "radius": row["radius"],
            **row["prime_excursion_certificate"],
        }
        for champion in champions
        for row in champion["trajectory"]
        if "prime_excursion_certificate" in row
    ]
    prime_successor_bottom_lock_rows: list[dict[str, Any]] = []
    for champion in champions:
        trajectory = champion["trajectory"]
        for index in range(1, len(trajectory) - 1):
            previous = trajectory[index - 1]
            prime_row = trajectory[index]
            successor = trajectory[index + 1]
            if not prime_row["prime_argument"] or successor["central"]:
                continue
            quotient = prime_row["nearest_quotient"]
            if not (
                previous["nearest_quotient"] == quotient
                and successor["nearest_quotient"] == quotient
            ):
                continue
            lhs = (
                4 * previous["signed_endpoint_error"]
                + prime_row["argument"]
                + successor["totient_letter"]
            )
            rhs = 4 + 3 * quotient
            assert lhs <= rhs
            prime_successor_bottom_lock_rows.append(
                {
                    "c": champion["c"],
                    "preprime_height": previous["height"],
                    "prime_argument": prime_row["argument"],
                    "quotient": quotient,
                    "preprime_error": previous["signed_endpoint_error"],
                    "prime_error": prime_row["signed_endpoint_error"],
                    "successor_error": successor["signed_endpoint_error"],
                    "successor_totient_letter": successor["totient_letter"],
                    "bottom_lock_lhs": lhs,
                    "bottom_lock_rhs": rhs,
                    "bottom_lock_slack": rhs - lhs,
                    "preprime_negative": previous["signed_endpoint_error"] < 0,
                    "inequality_verified": True,
                }
            )
    return {
        "tested_c_count": max_c + 1,
        "resolved_count": resolved_count,
        "unresolved_count": unresolved_count,
        "max_height": max_height,
        "delay_threshold": delay_threshold,
        "largest_delay": best_delay,
        "record_champions": champions,
        "record_champions_above_threshold": violations,
        "final_champion": champions[-1],
        "record_champion_prime_excursions": prime_excursion_rows,
        "record_champion_prime_successor_bottom_locks": (
            prime_successor_bottom_lock_rows
        ),
    }


def build_receipt(max_c: int, max_height: int, delay_threshold: int) -> dict[str, Any]:
    result_scan = scan(max_c, max_height, delay_threshold)
    final = result_scan["final_champion"]
    canonical = next(
        champion
        for champion in result_scan["record_champions"]
        if champion["c"] == 50490
    )
    assert canonical["post_geometry_clear_delay"] == 17
    assert canonical["fixed_trap_quotient"] == 35363
    assert canonical["geometry_clear_height"] == 17
    assert canonical["first_central_height"] == 34

    contract = build_experiment_contract(
        problem_id="erdos_249",
        target_statement="Prove irrationality of sum_(n>=1) phi(n)/2^n.",
        claim_ceiling=(
            "Finite pure-dyadic scan, an exact affine recurrence, and exact "
            "prime-successor bottom-lock certificates; no proof of unbounded "
            "delay, universal residue escape, or irrationality."
        ),
        hypothesis_id="pure_dyadic_post_geometry_delay_at_most_tested_threshold",
        hypothesis_statement=(
            "Every pure-dyadic canonical residue escapes the endpoint window within "
            f"{delay_threshold} heights after the central interval first becomes "
            "nonempty."
        ),
        probe_id="signed_endpoint_error_totient_word_scan",
        probe_question=(
            f"Do exact totient words produce a delay beyond {delay_threshold}, and "
            "is their trap governed by a fixed-quotient affine error cocycle?"
        ),
        computation=(
            f"Sieve phi through c={max_c}, update Q_H and M_H exactly through "
            f"H={max_height}, and verify E_(H+1)=2E_H+phi(c+H+1)-k on each "
            "record endpoint word."
        ),
        falsifier=(
            f"An exact c with post-geometry-clear delay above {delay_threshold}; a quotient "
            "change inside its trapped word would falsify the fixed-k model."
        ),
        stop_condition=(
            "Stop after the first scan range containing a new delay record above "
            f"{delay_threshold} and bind its complete signed endpoint word."
        ),
        survival_consequence=(
            "A genuine universal delay cap would directly feed the canonical "
            "Mersenne residue-gap supply."
        ),
        falsification_consequence=(
            f"Delay {delay_threshold} is impossible; the exact fixed-k cocycle "
            "redirects the frontier to anti-shadowing for totient-letter words in "
            "a moving window."
        ),
        consumer_ref=CONSUMER_REF,
        analysis_refs=[ANALYSIS_REF, LEAN_REF],
        source_refs=[SOURCE_REF, LEAN_REF],
        result_status="exact_one_way_result",
        result_summary=(
            f"At c={final['c']} geometry clears at H={final['geometry_clear_height']}, "
            f"the fixed quotient k={final['fixed_trap_quotient']} keeps the signed "
            f"error endpoint-trapped through H={final['first_central_height'] - 1}, "
            f"and escape first occurs at H={final['first_central_height']}: exact "
            f"delay {final['post_geometry_clear_delay']}, eliminating "
            f"delay<={delay_threshold}.  Every prime argument inside every record "
            "word also satisfies the exact adjacent-error excursion inequality "
            "p-1-k <= |E_H|+2|E_(H-1)|.  Whenever its successor is still "
            "trapped, the directional certificate "
            "4E_(H-1)+p+phi(p+1) <= 4+3k is also verified."
        ),
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos249-pure-dyadic-endpoint-cocycle/1",
        "status": (
            "verified_exact_record_cocycle_prime_excursions_and_successor_bottom_locks"
        ),
        "parameters": {
            "max_c": max_c,
            "max_height": max_height,
            "delay_threshold": delay_threshold,
        },
        "experiment_contract": contract,
        "scan": result_scan,
        "canonical_regression_witness": canonical,
        "source_records": [
            source_record(REPO_ROOT, SOURCE_REF),
            source_record(REPO_ROOT, LEAN_REF),
            source_record(REPO_ROOT, ANALYSIS_REF),
        ],
    }


def emit(payload: dict[str, Any], output: Path | None, check: bool) -> int:
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if output is None:
        print(rendered, end="")
        return 0
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
    parser.add_argument("--max-c", type=int, default=1000000)
    parser.add_argument("--max-height", type=int, default=100)
    parser.add_argument("--delay-threshold", type=int, default=17)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.max_c < 50490:
        parser.error("--max-c must include the canonical c=50490 witness")
    if args.max_height < 34:
        parser.error("--max-height must include the canonical H=34 escape")
    if args.delay_threshold < 0:
        parser.error("--delay-threshold must be nonnegative")
    if args.check and args.output is None:
        parser.error("--check requires --output")
    return emit(
        build_receipt(args.max_c, args.max_height, args.delay_threshold),
        args.output,
        args.check,
    )


if __name__ == "__main__":
    raise SystemExit(main())
