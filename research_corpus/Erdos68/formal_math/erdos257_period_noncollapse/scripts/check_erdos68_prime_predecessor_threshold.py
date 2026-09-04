#!/usr/bin/env python3
"""Exact prime-index falsifier for the Erdős #68 predecessor-gap threshold.

The Lean consumer proves that the cleared inequality

    ((m+2)m! - 2) v_m <= m^2 (m!-1) u_m

is a sufficient tail-free certificate, where ``Delta_m=u_m/v_m`` is the
reduced strict-successor predecessor gap.  This checker evaluates the exact
Fraction recurrence and finds the first prime at which that sufficient
threshold fails.  One such prime eliminates the proposed mechanism that prime
indices supply the threshold automatically; it does not settle Erdős #68.
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from math import factorial
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos68_prime_predecessor_threshold.py"
)
LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/"
    "PrimeZeroBranch.lean"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/"
    "PrimePredecessorGapComputationalLab.md"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos68_prime_predecessor_threshold_receipt.json"
)


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    divisor = 2
    while divisor * divisor <= n:
        if n % divisor == 0:
            return False
        divisor += 1
    return True


def ceil_fraction(value: Fraction) -> int:
    return -((-value.numerator) // value.denominator)


def probe(stop: int) -> dict[str, Any]:
    if stop < 3:
        raise ValueError("stop must be at least 3")
    delta = Fraction(1)
    fac = 2
    prime_rows: list[dict[str, Any]] = []
    first_failure: dict[str, Any] | None = None

    for m in range(3, stop + 1):
        fac *= m
        # At loop entry delta is Delta_m.  Test the m-indexed threshold before
        # applying the recurrence that advances it to Delta_(m+1).
        if is_prime(m):
            u_m = delta.numerator
            v_m = delta.denominator
            cleared_left = ((m + 2) * fac - 2) * v_m
            cleared_right = m * m * (fac - 1) * u_m
            holds = cleared_left <= cleared_right
            row = {
                "prime_m": m,
                "u_m": u_m,
                "v_m": v_m,
                "cleared_left": cleared_left,
                "cleared_right": cleared_right,
                "signed_cleared_margin": cleared_right - cleared_left,
                "threshold_holds": holds,
            }
            prime_rows.append(row)
            if not holds and first_failure is None:
                first_failure = row
                break

        y = m * delta - Fraction(1, fac - 1)
        carry = ceil_fraction(y) - 1
        delta = y - carry
        assert 0 < delta <= 1

    if first_failure is None:
        raise AssertionError(f"no prime threshold failure through {stop}")
    assert first_failure["prime_m"] == 5
    assert all(row["threshold_holds"] for row in prime_rows[:-1])
    return {
        "searched_through": stop,
        "delta_indexing": (
            "the threshold at m uses Delta_m before the recurrence advances "
            "to Delta_(m+1)"
        ),
        "prime_rows_checked": len(prime_rows),
        "primes_before_failure": [row["prime_m"] for row in prime_rows[:-1]],
        "first_prime_failure": first_failure,
    }


def build_receipt(stop: int) -> dict[str, Any]:
    result = probe(stop)
    failure = result["first_prime_failure"]
    contract = build_experiment_contract(
        problem_id="erdos_68",
        target_statement="Prove irrationality of sum_(n>=2) 1/(n!-1).",
        claim_ceiling=(
            "One exact prime-index counterexample to a sufficient threshold; "
            "no cofinal carry theorem or irrationality proof."
        ),
        hypothesis_id="prime_indices_automatically_meet_predecessor_gap_threshold",
        hypothesis_statement=(
            "Every prime m satisfies ((m+2)m!-2)v_m <= "
            "m^2(m!-1)u_m for the exact reduced predecessor gap u_m/v_m."
        ),
        probe_id="exact_fraction_prime_predecessor_threshold",
        probe_question="Does the cleared threshold hold at every prime?",
        computation=(
            "Iterate the exact Fraction recurrence for Delta_m, reduce it to "
            "u_m/v_m, and compare the two cleared integers at prime indices."
        ),
        falsifier="One prime with cleared_left > cleared_right.",
        stop_condition="Stop at the first exact prime-index failure.",
        survival_consequence=(
            "Universal prime supply would reduce the cofinal threshold producer "
            "to Euclid's theorem."
        ),
        falsification_consequence=(
            "The universal every-prime threshold assertion is false. An "
            "eventual-prime theorem allowing finite exceptions remains possible; "
            "alternatively the prime route can use the sharper lower-cylinder "
            "escape or extra denominator/residue structure."
        ),
        consumer_ref=LEAN_REF,
        analysis_refs=[ANALYSIS_REF, LEAN_REF],
        source_refs=[SOURCE_REF, LEAN_REF],
        result_status="finite_counterexample",
        result_summary=(
            f"The threshold first fails at the prime m={failure['prime_m']}: "
            "the exact cleared right-minus-left margin is negative. Primehood "
            "alone therefore does not force this sufficient certificate."
        ),
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos68-prime-predecessor-threshold/1",
        "status": "verified_exact_prime_supply_mechanism_elimination",
        "experiment_contract": contract,
        "probe": result,
        "consequence_decisions": [
            {
                "mechanism": "automatic_predecessor_threshold_at_prime_indices",
                "decision": "eliminated",
                "witness": 5,
            },
            {
                "mechanism": "prime_lower_endpoint_cylinder_escape",
                "decision": "remains_open_and_strictly_sharper",
            },
            {
                "mechanism": "irrationality_of_erdos_68",
                "decision": "not_claimed",
            },
        ],
        "source_records": [
            source_record(REPO_ROOT, SOURCE_REF),
            source_record(REPO_ROOT, LEAN_REF),
            source_record(REPO_ROOT, ANALYSIS_REF),
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
    parser.add_argument("--stop", type=int, default=100)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    return emit(build_receipt(args.stop), args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
