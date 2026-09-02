#!/usr/bin/env python3
"""Certify divisor centrality and its strict converse failure for Erdős #249.

For ``N = 2^H - 1`` and ``M = N / v``, centrality of ``(-Q) mod M``
implies centrality of ``(-Q) mod N``.  This is the useful direction for the
full denominator residual.  The reverse direction would reduce all odd
denominators to the pure-dyadic axis; this checker finds its first exact
totient-block counterexample and stops immediately.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)
from system.lib.formal_math_modular_arcs import (  # noqa: E402
    certify_central_arc_projection,
)

from check_canonical_mersenne_residue import totients_through  # noqa: E402


SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/scripts/"
    "check_mersenne_divisor_centrality.py"
)
INFRA_REF = "system/lib/formal_math_modular_arcs.py"
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/"
    "CanonicalMersenneResidueComputationalLab.md"
)
LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/"
    "CyclotomicAnchoredKill.lean"
)
PACKET_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/"
    "research_packet.json"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos249_mersenne_divisor_centrality_receipt.json"
)


def first_converse_failure(
    *, max_odd_denominator: int, max_c: int, max_multiplier: int
) -> dict[str, Any] | None:
    phi_den = totients_through(max_odd_denominator)
    max_height = max_multiplier * max(phi_den[1:])
    phi_letters = totients_through(max_c + max_height + 1)

    for v in range(3, max_odd_denominator + 1, 2):
        phi_v = phi_den[v]
        for c in range(max_c + 1):
            block = 0
            for height in range(1, max_multiplier * phi_v + 1):
                block = 2 * block + phi_letters[c + height]
                if height % phi_v:
                    continue
                multiplier = height // phi_v
                full_modulus = (1 << height) - 1
                quotient_modulus = full_modulus // v
                radius = c + height + 1
                certificate = certify_central_arc_projection(
                    -block,
                    small_modulus=quotient_modulus,
                    large_modulus=full_modulus,
                    radius=radius,
                )
                if certificate.large_central and not certificate.small_central:
                    return {
                        "c": c,
                        "v": v,
                        "phi_v": phi_v,
                        "euler_multiplier": multiplier,
                        "height": height,
                        "totient_block": block,
                        "projection": certificate.to_dict(),
                    }
    return None


def build_payload(
    *, max_odd_denominator: int, max_c: int, max_multiplier: int
) -> dict[str, Any]:
    witness = first_converse_failure(
        max_odd_denominator=max_odd_denominator,
        max_c=max_c,
        max_multiplier=max_multiplier,
    )
    if witness is None:
        return {
            "schema": "erdos249-mersenne-divisor-centrality/1",
            "status": "bounded_null_result_not_mathematical_progress",
            "claim_ceiling": "No converse failure found in the declared finite box.",
            "witness": None,
        }

    if max_odd_denominator >= 3 and max_c >= 0 and max_multiplier >= 3:
        assert witness["c"] == 0
        assert witness["v"] == 3
        assert witness["height"] == 6
        assert witness["totient_block"] == 82
        projection = witness["projection"]
        assert projection["large_modulus"] == 63
        assert projection["large_residue"] == 44
        assert projection["small_modulus"] == 21
        assert projection["small_residue"] == 2
        assert projection["radius"] == 7

    contract = build_experiment_contract(
        problem_id="erdos_249",
        target_statement="Prove irrationality of sum_(n>=1) phi(n)/2^n.",
        claim_ceiling=(
            "General exact central-arc projection theorem plus one actual finite "
            "counterexample to its converse; no universal residue supply or "
            "irrationality proof."
        ),
        hypothesis_id="pure_dyadic_escape_descends_to_every_odd_denominator",
        hypothesis_statement=(
            "At an Euler-compatible height, centrality modulo 2^H-1 remains "
            "central after quotienting by the candidate odd denominator v."
        ),
        probe_id="exact_mersenne_divisor_arc_projection",
        probe_question=(
            "What is the valid direction of central-arc inheritance under "
            "M=(2^H-1)/v dividing N=2^H-1, and does the converse fail on the "
            "actual totient block?"
        ),
        computation=(
            "Record the exact residue layer r_N=jM+r_M, certify that M-central "
            "implies N-central, and lexicographically stop at the first actual "
            "totient block with N-central but M-endpoint residue."
        ),
        falsifier=(
            "An actual Euler-compatible (c,v,H) whose full-Mersenne residue is "
            "central while its quotient-modulus residue is not."
        ),
        stop_condition=(
            "Stop at the first lexicographic converse failure; do not extend the "
            "denominator or height horizon after the implication is decided."
        ),
        survival_consequence=(
            "If the converse held, a pure-dyadic residue theorem could feed all "
            "odd denominator quotients at the same heights."
        ),
        falsification_consequence=(
            "Pure-dyadic escape alone cannot be quotient-projected to the full "
            "odd-denominator residual; v-specific arithmetic remains necessary."
        ),
        consumer_ref=LEAN_REF,
        analysis_refs=[ANALYSIS_REF, LEAN_REF, PACKET_REF],
        source_refs=[SOURCE_REF, INFRA_REF, PACKET_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "Centrality modulo a divisor implies centrality modulo its multiple. "
            "The converse fails for the actual block Q(6,0)=82: residue 44 is "
            "central modulo 63 at radius 7, but residue 2 is trapped modulo 21."
        ),
        resource_bounds={
            "max_odd_denominator": max_odd_denominator,
            "max_c": max_c,
            "max_multiplier": max_multiplier,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos249-mersenne-divisor-centrality/1",
        "status": "verified_projection_theorem_and_exact_converse_failure",
        "experiment_contract": contract,
        "general_theorem": {
            "statement": (
                "For positive M|N and B>=0, if B < z mod M < M-B, "
                "then B < z mod N < N-B."
            ),
            "proof_coordinate": (
                "Write z mod N = jM + (z mod M), with "
                "0 <= j < N/M, and apply the two strict endpoint bounds."
            ),
        },
        "first_actual_converse_failure": witness,
        "consequence_decisions": [
            {
                "mechanism": "quotient_centrality_implies_full_centrality",
                "decision": "opened_and_certified",
            },
            {
                "mechanism": "pure_dyadic_escape_descends_to_odd_denominators",
                "decision": "eliminated",
                "reason": "actual c=0, v=3, H=6 converse failure",
            },
            {
                "mechanism": "full_odd_denominator_residue_supply",
                "decision": "still_open_requires_v_specific_input",
            },
        ],
        "source_records": [
            source_record(REPO_ROOT, SOURCE_REF),
            source_record(REPO_ROOT, INFRA_REF),
            source_record(REPO_ROOT, ANALYSIS_REF),
            source_record(REPO_ROOT, LEAN_REF),
            source_record(REPO_ROOT, PACKET_REF),
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
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-odd-denominator", type=int, default=15)
    parser.add_argument("--max-c", type=int, default=12)
    parser.add_argument("--max-multiplier", type=int, default=8)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.max_odd_denominator < 3:
        parser.error("max odd denominator must be at least 3")
    if args.max_c < 0 or args.max_multiplier < 1:
        parser.error("max-c must be nonnegative and max-multiplier positive")
    payload = build_payload(
        max_odd_denominator=args.max_odd_denominator,
        max_c=args.max_c,
        max_multiplier=args.max_multiplier,
    )
    return emit(payload, args.output.resolve(), args.check)


if __name__ == "__main__":
    raise SystemExit(main())
