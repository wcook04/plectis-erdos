#!/usr/bin/env python3
"""Audit the odd/prime structure of Erdős #68 threshold failures.

The certified scalar-spectrum receipt records every index ``m <= 300000``
with rounding digit ``D_m = -1``.  Such a digit always fails the tail-free
predecessor-gap threshold.  Conversely, ``D_m >= 1`` always passes, while the
boundary case ``D_m = 0`` additionally requires ``A_m >= 2/m``.  The certified
digit-law receipt checks that boundary at every unit carry through the same
horizon.  This probe independently recomputes a short exact ``Fraction``
prefix, then asks the target-producing question whether any odd index after 23
fails either branch of the full threshold.

The answer is finite evidence only.  The cofinal theorem

    Odd m and 25 <= m  ->  D_m + A_m >= 2/m

would imply the Erdős #68 irrationality endpoint.  The observed exclusion of
``D_m=-1`` is one obligation; the thin ``D_m=0`` boundary is the other.
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


SOURCE_REF = "formal_math/probes/erdos68_prime_threshold_parity.py"
UPSTREAM_REF = "state/formal_math/probes/erdos68_gap_scalar_spectrum_receipt.json"
DIGIT_LAW_REF = "state/formal_math/probes/erdos68_digit_law_receipt.json"
LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/"
    "PrimeZeroBranch.lean"
)
LAB_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/"
    "PrimeThresholdParityLab.md"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/probes/erdos68_prime_threshold_parity_receipt.json"
)


def ceil_fraction(value: Fraction) -> int:
    return -((-value.numerator) // value.denominator)


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    divisor = 2
    while divisor * divisor <= n:
        if n % divisor == 0:
            return False
        divisor += 1
    return True


def exact_threshold_failures(stop: int) -> list[int]:
    """Return all failures through ``stop`` with correctly indexed Delta_m."""
    if stop < 3:
        raise ValueError("direct horizon must be at least 3")
    delta = Fraction(1)  # Delta_3
    fac = 2
    failures: list[int] = []
    for m in range(3, stop + 1):
        fac *= m
        u_m = delta.numerator
        v_m = delta.denominator
        left = ((m + 2) * fac - 2) * v_m
        right = m * m * (fac - 1) * u_m
        if left > right:
            failures.append(m)
        y = m * delta - Fraction(1, fac - 1)
        carry = ceil_fraction(y) - 1
        delta = y - carry
        if not 0 < delta <= 1:
            raise AssertionError(f"Delta_(m+1) left (0,1] after m={m}")
    return failures


def run(direct_horizon: int) -> dict[str, Any]:
    upstream_path = REPO_ROOT / UPSTREAM_REF
    upstream = json.loads(upstream_path.read_text(encoding="utf-8"))
    digit_law_path = REPO_ROOT / DIGIT_LAW_REF
    digit_law = json.loads(digit_law_path.read_text(encoding="utf-8"))
    certified = upstream["result"]["threshold_failures_D_eq_minus_one"]
    certified_horizon = upstream["result"]["max_m"]
    unit_carries = upstream["result"]["unit_carries_D_eq_zero"]
    margin_rows = digit_law["result"]["canonical_digits"][
        "unit_carry_threshold_margins"
    ]
    margin_indices = [row["m"] for row in margin_rows]
    failed_unit_margins = [row["m"] for row in margin_rows if not row["fires"]]
    failed_next_carry_rule = [
        row["m"] for row in margin_rows if row["next_digit"] + 1 < 3
    ]

    direct = exact_threshold_failures(direct_horizon)
    certified_prefix = [m for m in certified if m <= direct_horizon]
    if direct != certified_prefix:
        raise AssertionError(
            f"direct recurrence {direct} != certified prefix {certified_prefix}"
        )

    odd_failures = [m for m in certified if m % 2 == 1]
    prime_failures = [m for m in certified if is_prime(m)]
    late_odd_failures = [m for m in odd_failures if m >= 25]
    late_prime_failures = [m for m in prime_failures if m >= 29]
    odd_unit_carries = [m for m in unit_carries if m % 2 == 1]
    late_odd_unit_margin_failures = [
        m for m in failed_unit_margins if m >= 25 and m % 2 == 1
    ]
    expected_certified = [
        5, 9, 23, 60, 470, 3026, 19222, 27472, 30324, 35366, 65768
    ]
    falsifiers = {
        "upstream exact failure list has expected payload": certified == expected_certified,
        "direct exact recurrence reproduces certified prefix": direct == certified_prefix,
        "only odd failures are 5, 9, 23": odd_failures == [5, 9, 23],
        "only prime failures are 5 and 23": prime_failures == [5, 23],
        "no odd failure from 25 through certified horizon": not late_odd_failures,
        "no prime failure from 29 through certified horizon": not late_prime_failures,
        "digit-law margin rows cover every certified unit carry": (
            margin_indices == unit_carries
        ),
        "every certified unit carry clears the threshold sliver": (
            not failed_unit_margins
        ),
        "every certified unit carry has next carry at least three": (
            not failed_next_carry_rule
        ),
        "no odd unit-carry sliver failure from 25 through certified horizon": (
            not late_odd_unit_margin_failures
        ),
    }
    return {
        "certified_horizon": certified_horizon,
        "certified_threshold_failures": certified,
        "direct_exact_horizon": direct_horizon,
        "direct_exact_failures": direct,
        "odd_failures": odd_failures,
        "prime_failures": prime_failures,
        "late_odd_failures": late_odd_failures,
        "late_prime_failures": late_prime_failures,
        "unit_carries": unit_carries,
        "odd_unit_carries": odd_unit_carries,
        "failed_unit_carry_margins": failed_unit_margins,
        "failed_next_carry_rule": failed_next_carry_rule,
        "unit_carry_next_digits": {
            str(row["m"]): row["next_digit"] for row in margin_rows
        },
        "late_odd_unit_margin_failures": late_odd_unit_margin_failures,
        "falsifiers": falsifiers,
        "all_falsifiers_pass": all(falsifiers.values()),
        "candidate_theorem": (
            "For every odd m >= 25, D_m + A_m >= 2/m; equivalently, the "
            "tail-free predecessor threshold holds. It splits into excluding "
            "D_m=-1 and controlling the D_m=0 boundary A_m>=2/m. A stronger "
            "purely discrete sufficient target is: carry_m>=1, and carry_m=1 "
            "implies carry_(m+1)>=3."
        ),
        "target_composition": (
            "The full candidate theorem would make every prime p >= 29 a threshold "
            "certificate; Euclid plus the Lean cofinal-threshold consumer would "
            "prove irrationality of sum_(n>=2) 1/(n!-1)."
        ),
        "claim_boundary": (
            "Exact derived audit through m=300000, with an independently recomputed "
            "Fraction prefix and a source-bound audit of every unit-carry margin. "
            "It discovers a two-branch odd-index conjecture but proves no cofinal "
            "odd-index theorem and no irrationality result."
        ),
    }


def build_receipt(direct_horizon: int) -> dict[str, Any]:
    result = run(direct_horizon)
    contract = build_experiment_contract(
        problem_id="erdos_68",
        target_statement="Prove irrationality of sum_(n>=2) 1/(n!-1).",
        claim_ceiling=(
            "Finite exact parity pattern through m=300000; no cofinal odd-index theorem."
        ),
        hypothesis_id="eventual_odd_index_tailfree_threshold",
        hypothesis_statement=(
            "Every odd m>=25 satisfies D_m+A_m>=2/m, the tail-free "
            "predecessor-gap threshold."
        ),
        probe_id="certified_threshold_failure_parity_audit",
        probe_question=(
            "Does any odd or prime index after 23 either have D_m=-1 or fail "
            "the A_m>=2/m boundary when D_m=0?"
        ),
        computation=(
            "Independently recompute the exact Fraction prefix, verify it against the "
            "certified GMP-derived scalar-spectrum receipt, and filter the complete "
            "D_m=-1 list through 300000 by parity and primality, then bind it "
            "to the digit-law receipt's complete D_m=0 threshold margins."
        ),
        falsifier=(
            "One odd m>=25 with D_m=-1, or one odd D_m=0 index with A_m<2/m."
        ),
        stop_condition="Stop at the certified horizon m=300000.",
        survival_consequence=(
            "Prove both the parity exclusion and the unit-carry boundary clause, "
            "prove the adjacent-carry sufficient rule, or prove the combined "
            "odd-index threshold theorem directly."
        ),
        falsification_consequence=(
            "Discard parity as the explanation and classify the first late odd failure."
        ),
        consumer_ref=LEAN_REF,
        analysis_refs=[LAB_REF, LEAN_REF],
        source_refs=[SOURCE_REF, UPSTREAM_REF, DIGIT_LAW_REF, LEAN_REF],
        result_status="finite_support",
        result_summary=(
            "Through m=300000, D_m=-1 occurs at odd indices only at 5,9,23, "
            "and every certified D_m=0 index clears its separate threshold margin. "
            "Thus the full threshold has no odd failure after 23 in this horizon."
        ),
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos68-prime-threshold-parity/1",
        "status": "verified_exact_finite_parity_pattern",
        "experiment_contract": contract,
        "result": result,
        "source_records": [
            source_record(REPO_ROOT, SOURCE_REF),
            source_record(REPO_ROOT, UPSTREAM_REF),
            source_record(REPO_ROOT, DIGIT_LAW_REF),
            source_record(REPO_ROOT, LEAN_REF),
            source_record(REPO_ROOT, LAB_REF),
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
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--direct-horizon", type=int, default=100)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    return emit(build_receipt(args.direct_horizon), args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
