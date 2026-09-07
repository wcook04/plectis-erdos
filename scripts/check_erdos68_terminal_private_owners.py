#!/usr/bin/env python3
"""Exact terminal private-owner probe for Erdős #68.

For every prime ``q`` the Wilson endpoint ``q-2`` satisfies
``(q-2)! == 1 (mod q)``.  This checker reuses the independently cross-checked
factorial recurrence engine and selects the primes for which that endpoint is
the *first* factorial-one hit.  The Lean theorem
``prime_terminal_factorialGap_hit_iff`` then shows that the endpoint is the
only hit globally: ``q-1`` is excluded by Wilson and all later factorials are
zero modulo ``q``.

The finite scan tests whether such globally unique owners occur in comparable
pairs that fit one factorial block.  It is mechanism evidence, not an
infinitude, density theorem, collision-cap estimate, or irrationality proof.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT))

from formal_math.erdos257_period_noncollapse.scripts.check_erdos68_arbitrary_valuation_records import (  # noqa: E402
    fast_scan_rows,
)
from formal_math.erdos257_period_noncollapse.scripts.check_erdos68_private_projections import (  # noqa: E402
    complementary_projection,
    lcm,
)
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos68_terminal_private_owners.py"
)
ENGINE_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos68_arbitrary_valuation_records.py"
)
FAST_ENGINE_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos68_arbitrary_valuation_records_fast.cpp"
)
PRIVATE_ENGINE_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos68_private_projections.py"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/"
    "PrivateProjectionComputationalLab.md"
)
TERMINAL_THEOREM_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/"
    "PrimeZeroBranch.lean"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/"
    "EndpointWeightedPrivateSupport.lean"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos68_terminal_private_owner_receipt.json"
)


def canonical_digest(value: Any) -> str:
    encoded = json.dumps(value, separators=(",", ":"), sort_keys=True).encode()
    return hashlib.sha256(encoded).hexdigest()


def integer_fingerprint(value: int) -> dict[str, Any]:
    payload = value.to_bytes(max(1, (value.bit_length() + 7) // 8), "big")
    return {"bit_length": value.bit_length(), "sha256": hashlib.sha256(payload).hexdigest()}


def factor_pair_endpoint_certificate(p: int, left: int, right: int) -> dict[str, Any]:
    upper = 2 * p - 1
    factorials = [1] * (upper + 1)
    for n in range(1, upper + 1):
        factorials[n] = factorials[n - 1] * n
    denominators = [0] * (upper + 1)
    for n in range(2, upper + 1):
        denominators[n] = factorials[n] - 1

    denominator_lcm = 1
    collision_lcm = 1
    tail_numerator = 0
    for n in range(2, upper + 1):
        old_lcm = denominator_lcm
        collision_lcm = lcm(collision_lcm, math.gcd(denominators[n], old_lcm))
        denominator_lcm = lcm(old_lcm, denominators[n])
        tail_numerator = (
            tail_numerator * (denominator_lcm // old_lcm)
            + denominator_lcm // denominators[n]
        )

    base = factorials[p - 1]
    endpoint_lcm = lcm(base, denominator_lcm)
    endpoint_scale = endpoint_lcm // denominator_lcm
    collision_core = lcm(base, collision_lcm)
    private_modulus = endpoint_lcm // collision_core
    endpoint_tail_numerator = tail_numerator * endpoint_scale
    if private_modulus % left or private_modulus % right or math.gcd(left, right) != 1:
        raise AssertionError("terminal factors are not a coprime private-modulus pair")

    left_modulus = private_modulus // left
    right_modulus = private_modulus // right
    left_projection = complementary_projection(endpoint_tail_numerator, left_modulus)
    right_projection = complementary_projection(endpoint_tail_numerator, right_modulus)
    pair_floor = (
        left_projection
        if left_projection == right_projection
        else min(left_modulus, right_modulus)
    )
    budget_times_lcm = (2 * p + 1) * endpoint_lcm
    scale = 2 * p * p * factorials[upper]
    global_residue = complementary_projection(endpoint_tail_numerator, private_modulus)
    checks = {
        "left_factor_divides_private_modulus": private_modulus % left == 0,
        "right_factor_divides_private_modulus": private_modulus % right == 0,
        "factors_are_coprime": math.gcd(left, right) == 1,
        "private_modulus_nontrivial": private_modulus > 1,
        "complementary_factor_projections_disagree": left_projection != right_projection,
        "factor_pair_scale_inequality_closes": budget_times_lcm < scale * pair_floor,
        "global_complementary_residue_inequality_closes": budget_times_lcm < scale * global_residue,
    }
    if not all(checks.values()):
        raise AssertionError([name for name, passed in checks.items() if not passed])
    return {
        "block_parameter": p,
        "block_index_interval": [2, upper],
        "left_factor": left,
        "right_factor": right,
        "checks": checks,
        "private_modulus": integer_fingerprint(private_modulus),
        "left_projection": integer_fingerprint(left_projection),
        "right_projection": integer_fingerprint(right_projection),
        "pair_floor": integer_fingerprint(pair_floor),
        "factor_pair_closing_margin": integer_fingerprint(scale * pair_floor - budget_times_lcm),
        "global_closing_margin": integer_fingerprint(scale * global_residue - budget_times_lcm),
    }


def build_scan(max_prime: int) -> dict[str, Any]:
    rows, engine = fast_scan_rows(max_prime)
    terminal = [
        int(row["q"])
        for row in rows
        if int(row["q"]) >= 5
        and row["first_support_index"] is not None
        and int(row["first_support_index"]) == int(row["q"]) - 2
    ]
    comparable_pairs: list[tuple[int, int]] = []
    for left, right in zip(terminal, terminal[1:], strict=False):
        # Owner indices are left-2 and right-2.  Some block [p,2p-1]
        # contains both iff right-2 <= 2*(left-2)-1.
        if right - 2 <= 2 * (left - 2) - 1:
            comparable_pairs.append((left, right))

    if (37, 41) not in comparable_pairs:
        raise AssertionError("canonical terminal-owner pair (37,41) disappeared")
    factor_pair = factor_pair_endpoint_certificate(20, 37, 41)
    return {
        "parameters": {"max_prime": max_prime},
        "prime_count": len(rows),
        "terminal_first_hit_prime_count": len(terminal),
        "terminal_first_hit_prime_digest": canonical_digest(terminal),
        "terminal_first_hit_primes_first_20": terminal[:20],
        "terminal_first_hit_primes_last_20": terminal[-20:],
        "largest_terminal_first_hit_prime": terminal[-1],
        "consecutive_comparable_pair_count": len(comparable_pairs),
        "comparable_pair_digest": canonical_digest(comparable_pairs),
        "first_20_comparable_pairs": comparable_pairs[:20],
        "last_20_comparable_pairs": comparable_pairs[-20:],
        "canonical_mechanism_witness": {
            "left_prime": 37,
            "left_unique_owner_index": 35,
            "right_prime": 41,
            "right_unique_owner_index": 39,
            "block_parameter": 20,
            "block_index_interval": [2, 39],
            "both_owner_indices_in_block": True,
            "both_primes_divide_exactly_one_factorial_gap_globally": True,
        },
        "canonical_factor_pair_endpoint_certificate": factor_pair,
        "engine": engine,
    }


def build_receipt(max_prime: int) -> dict[str, Any]:
    result = build_scan(max_prime)
    contract = build_experiment_contract(
        problem_id="erdos_68",
        target_statement="Prove that S=sum_{n>=2} 1/(n!-1) is irrational.",
        claim_ceiling=(
            "One exact globally unique two-owner endpoint contradiction certificate "
            "and a finite terminal-owner census; no infinitude, density, cofinal "
            "certificate supply, cofinal miss, or irrationality theorem."
        ),
        hypothesis_id="terminal_wilson_first_hits_are_too_sparse_for_two_owner_blocks",
        hypothesis_statement=(
            "Primes whose first factorial-one hit is q-2 do not occur in "
            "comparable pairs capable of supplying two private owners in one block."
        ),
        probe_id="exact_terminal_first_hit_pair_scan",
        probe_question=(
            "Can Wilson endpoints supply two globally unique private owners without "
            "any collision-renewal obligation?"
        ),
        computation=(
            "Reuse the exact q^2 recurrence engine, select primes with first support "
            "index q-2, and test consecutive owner indices for joint membership in "
            "a block [2,2p-1]."
        ),
        falsifier=(
            "One pair of terminal-first-hit primes whose two unique owner indices "
            "lie in a common factorial block."
        ),
        stop_condition=(
            "Stop at the first exact pair opening the mechanism, then retain the "
            "configured census only as structural mapping rather than extending it "
            "as purported infinitary evidence."
        ),
        survival_consequence=(
            "Retire terminal Wilson owners as too isolated and return to ordinary "
            "first-repeat renewal."
        ),
        falsification_consequence=(
            "Open globally unique terminal-owner pairs as a separate cofinal supply "
            "target; the canonical pair already fires the complete finite factor-pair "
            "consumer, leaving only cofinal supply for this mechanism."
        ),
        consumer_ref=CONSUMER_REF,
        consumer_declarations=[
            "ErdosProblems.Erdos68.factorialBlock_endpointWindow_false_of_complementaryFactorPairFloor",
            "ErdosProblems.Erdos68.irrational_factorialGapSeries_of_cofinal_complementaryFactorPairFloor_nat",
        ],
        analysis_refs=[ANALYSIS_REF],
        source_refs=[
            SOURCE_REF,
            ENGINE_REF,
            FAST_ENGINE_REF,
            PRIVATE_ENGINE_REF,
            TERMINAL_THEOREM_REF,
        ],
        resource_bounds={"max_prime": max_prime},
        result_status="exact_one_way_result",
        result_summary=(
            "The exact pair q=37,41 owns indices 35,39 in block p=20; both "
            "factors divide the private modulus, their projections disagree, and "
            "the complete factor-pair endpoint inequality closes."
        ),
        progress_class="mechanism_opened",
        decision_basis=(
            "A source-faithful pair bypasses repeated-hit renewal and fires the "
            "existing endpoint contradiction through two globally unique channels."
        ),
        next_analytic_target=(
            "Prove cofinally many comparable terminal-first-hit prime pairs, or a "
            "weaker supply sufficient for the checked two-projection collision cap."
        ),
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos68-terminal-private-owner/1",
        "status": "verified_exact_terminal_two_owner_mechanism_opening",
        "experiment_contract": contract,
        "result": result,
        "consequence_decisions": [
            {
                "mechanism": "ordinary_private_owner_collision_renewal_only",
                "decision": "strictly_incomplete",
            },
            {
                "mechanism": "globally_unique_terminal_owner_pairs",
                "decision": "opened_by_exact_pair_37_41",
            },
            {
                "mechanism": "cofinal_pair_supply_or_irrationality",
                "decision": "not_claimed",
            },
        ],
        "source_records": [
            source_record(REPO_ROOT, SOURCE_REF),
            source_record(REPO_ROOT, ENGINE_REF),
            source_record(REPO_ROOT, FAST_ENGINE_REF),
            source_record(REPO_ROOT, PRIVATE_ENGINE_REF),
            source_record(REPO_ROOT, ANALYSIS_REF),
            source_record(REPO_ROOT, TERMINAL_THEOREM_REF),
            source_record(REPO_ROOT, CONSUMER_REF),
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
    parser.add_argument("--max-prime", type=int, default=50_000)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.max_prime < 41:
        parser.error("max-prime must include the canonical pair 37,41")
    return emit(build_receipt(args.max_prime), args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
