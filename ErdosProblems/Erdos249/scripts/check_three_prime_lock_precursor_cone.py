#!/usr/bin/env python3
"""Search for an exact three-lock precursor-cone falsifier for Erdős #249.

For a pure-dyadic basepoint ``c``, the signed endpoint error obeys

    E_(H+1) = 2 E_H + phi(c+H+1) - k

while the nearest Mersenne quotient ``k`` is fixed inside an endpoint trap.
The existing one- and two-lock certificates show that trapped successors of
one or two distinct prime arguments do not force a crossing.  This checker
stops at the first actual word containing three such trapped successors and
intersects the *complete* integer precursor cone by exact affine inequalities.

One surviving seed is a finite exact counterexample to the universal claim
that three local locks force crossing.  Absence inside a bounded scan is kept
as a null result and is never promoted to an infinitary claim.
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
from system.lib.formal_math_affine_cylinder import (  # noqa: E402
    IntegerAffineConstraint,
    certify_integer_seed_in_affine_preimages,
    intersect_integer_affine_preimages,
)

from check_pure_dyadic_endpoint_cocycle import (  # noqa: E402
    nearest_quotient,
    totients_through,
)


SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/scripts/"
    "check_three_prime_lock_precursor_cone.py"
)
AFFINE_REF = "system/lib/formal_math_affine_cylinder.py"
COCYCLE_REF = (
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
PACKET_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/"
    "research_packet.json"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos249_three_prime_lock_precursor_cone_receipt.json"
)


def intersect_precursor_cone(
    rows: list[dict[str, Any]], lock_successor_heights: list[int]
) -> dict[str, Any]:
    start = rows[0]
    quotient = start["nearest_quotient"]
    affine_constant = 0
    power = 1
    lock_set = set(lock_successor_heights)
    intersections: list[dict[str, Any]] = []
    constraints: list[IntegerAffineConstraint] = []

    for index, row in enumerate(rows):
        if index:
            power *= 2
            affine_constant = (
                2 * affine_constant + row["totient_letter"] - quotient
            )
        constraints.append(
            IntegerAffineConstraint(
                scale=power,
                offset=affine_constant,
                lower=-row["radius"],
                upper=row["radius"],
                label=f"height_{row['height']}",
            )
        )
        interval = intersect_integer_affine_preimages(constraints)
        assert interval.nonempty
        if row["height"] in lock_set:
            intersections.append(
                {
                    "successor_height": row["height"],
                    "surviving_seed_interval": [interval.lower, interval.upper],
                    "surviving_seed_count": interval.count,
                }
            )

    actual_seed = start["signed_endpoint_error"]
    membership = certify_integer_seed_in_affine_preimages(constraints, actual_seed)
    assert membership.equivalence_verified
    assert membership.proves_nonempty
    terminal = rows[-1]
    return {
        "complete_geometry_seed_interval": [
            -start["radius"],
            start["radius"],
        ],
        "complete_geometry_seed_count": 2 * start["radius"] + 1,
        "lock_intersections": intersections,
        "terminal_surviving_seed_interval": [interval.lower, interval.upper],
        "terminal_surviving_seed_count": interval.count,
        "actual_geometry_seed_error": actual_seed,
        "actual_terminal_error": terminal["signed_endpoint_error"],
        "actual_terminal_margin": (
            terminal["radius"] - abs(terminal["signed_endpoint_error"])
        ),
        "actual_seed_survives_three_locks": True,
        "finite_prefix_membership_certificate": {
            "seed": membership.seed,
            "constraint_count": membership.constraint_count,
            "satisfies_every_band": membership.satisfies_every_band,
            "interval_contains_seed": membership.interval_contains_seed,
            "equivalence_verified": membership.equivalence_verified,
            "proves_nonempty": membership.proves_nonempty,
            "first_failed_constraint_index": (
                membership.first_failed_constraint_index
            ),
            "first_failed_constraint_label": (
                membership.first_failed_constraint_label
            ),
        },
        "finite_prefix_proof_boundary": (
            "For any finite affine-band prefix, a seed lies in the complete "
            "pulled-back cone iff its trajectory value satisfies every original "
            "band. Hence an already observed trapped finite trajectory supplies "
            "an explicit survivor of its own complete prefix cone."
        ),
    }


def first_three_lock_witness(
    *, min_c: int, max_c: int, max_height: int
) -> dict[str, Any] | None:
    phi = totients_through(max_c + max_height + 1)
    for c in range(min_c, max_c + 1):
        block = 0
        modulus = 0
        geometry_height: int | None = None
        rows: list[dict[str, Any]] = []
        locks: list[dict[str, int]] = []

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
            central = abs(error) > radius
            argument = c + height
            row = {
                "height": height,
                "argument": argument,
                "totient_letter": letter,
                "prime_argument": argument >= 2 and phi[argument] == argument - 1,
                "nearest_quotient": quotient,
                "signed_endpoint_error": error,
                "radius": radius,
                "central": central,
            }
            if rows and not central:
                assert quotient == rows[0]["nearest_quotient"]
                assert error == (
                    2 * rows[-1]["signed_endpoint_error"] + letter - quotient
                )
            rows.append(row)

            if central:
                break
            if len(rows) >= 2 and rows[-2]["prime_argument"]:
                locks.append(
                    {
                        "prime_height": rows[-2]["height"],
                        "prime_argument": rows[-2]["argument"],
                        "successor_height": height,
                    }
                )
                if len(locks) == 3:
                    lock_heights = [lock["successor_height"] for lock in locks]
                    cone = intersect_precursor_cone(rows, lock_heights)
                    return {
                        "basepoint_c": c,
                        "geometry_clear_height": geometry_height,
                        "fixed_quotient_k": rows[0]["nearest_quotient"],
                        "prime_successor_locks": locks,
                        "trajectory_through_third_lock": rows,
                        "precursor_cone": cone,
                    }
    return None


def build_payload(min_c: int, max_c: int, max_height: int) -> dict[str, Any]:
    witness = first_three_lock_witness(
        min_c=min_c, max_c=max_c, max_height=max_height
    )
    bounds = {"min_c": min_c, "max_c": max_c, "max_height": max_height}
    contract_bounds = {
        "tested_c_count": max_c - min_c + 1,
        "max_c_plus_one": max_c + 1,
        "max_height": max_height,
    }
    if witness is None:
        return {
            "schema": "erdos249-three-prime-lock-precursor-cone/1",
            "status": "bounded_null_result_not_mathematical_progress",
            "resource_bounds": bounds,
            "witness": None,
            "claim_ceiling": (
                "No three-lock witness in the configured finite scan; this does not "
                "support a universal crossing theorem and must not be promoted."
            ),
        }

    if min_c == 0 and max_c >= 1858 and max_height >= 20:
        cone = witness["precursor_cone"]
        assert witness["basepoint_c"] == 1858
        assert witness["geometry_clear_height"] == 12
        assert witness["fixed_quotient_k"] == 1251
        assert [row["prime_argument"] for row in witness["prime_successor_locks"]] == [
            1871,
            1873,
            1877,
        ]
        assert [row["surviving_seed_count"] for row in cone["lock_intersections"]] == [
            937,
            234,
            15,
        ]
        assert cone["terminal_surviving_seed_interval"] == [-193, -179]
        assert cone["actual_geometry_seed_error"] == -189
        assert cone["actual_terminal_error"] == -741
        assert cone["actual_terminal_margin"] == 1138

    contract = build_experiment_contract(
        problem_id="erdos_249",
        target_statement="Prove irrationality of sum_(n>=1) phi(n)/2^n.",
        claim_ceiling=(
            "Exact elimination of three-local-lock forced crossing, together with "
            "the general proof boundary that an observed trapped finite prefix "
            "cannot empty its own complete affine precursor cone; no infinite "
            "endpoint trap, universal escape, or irrationality proof."
        ),
        hypothesis_id="three_prime_successor_locks_force_endpoint_escape",
        hypothesis_statement=(
            "Three distinct trapped prime successors, together with every exact "
            "intervening totient letter and moving endpoint bound, force crossing."
        ),
        probe_id="complete_three_lock_affine_precursor_intersection",
        probe_question=(
            "Does the complete geometry-boundary seed cone become empty by the "
            "successor of the third distinct prime lock?"
        ),
        computation=(
            "Sieve the actual totient word, stop at the first three-lock trap, and "
            "intersect every exact affine seed inequality through the third successor."
        ),
        falsifier=(
            "A geometry-boundary seed that satisfies every moving endpoint bound "
            "through all three trapped prime successors."
        ),
        stop_condition=(
            "Stop at the first exact three-lock witness; if none occurs inside the "
            "declared bounds, retain only a typed null result and make no claim."
        ),
        survival_consequence=(
            "An empty complete cone would leave a three-lock local crossing route open."
        ),
        falsification_consequence=(
            "Three local locks are insufficient; any local proof must use a stronger "
            "cross-gap relation or genuinely global cofinal coherence."
        ),
        consumer_ref=LEAN_REF,
        analysis_refs=[ANALYSIS_REF, LEAN_REF, PACKET_REF],
        source_refs=[SOURCE_REF, AFFINE_REF, COCYCLE_REF, PACKET_REF],
        result_status="exact_one_way_result",
        result_summary=(
            f"At c={witness['basepoint_c']}, the actual fixed-quotient word remains "
            "endpoint-trapped through three distinct prime successors, and the exact "
            "complete precursor cone remains nonempty. Exact seed-membership "
            "equivalence certifies that every already observed trapped finite prefix "
            "contains its actual seed."
        ),
        resource_bounds=contract_bounds,
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos249-three-prime-lock-precursor-cone/1",
        "status": "verified_exact_three_lock_mechanism_elimination",
        "resource_bounds": bounds,
        "experiment_contract": contract,
        "witness": witness,
        "consequence_decisions": [
            {
                "mechanism": "three_prime_successor_locks_force_endpoint_crossing",
                "decision": "eliminated",
                "reason": "the complete three-lock precursor cone is nonempty",
            },
            {
                "mechanism": "post_hoc_finite_trapped_prefix_cone_emptying",
                "decision": "eliminated",
                "reason": (
                    "exact preimage membership is equivalent to satisfying every "
                    "original band, so the observed trapped seed is a survivor"
                ),
            },
            {
                "mechanism": "global_cross_gap_or_cofinal_coherence",
                "decision": "required_stronger_input",
                "reason": "one, two, and now three finite local locks are insufficient",
            },
            {
                "mechanism": "universal_escape_or_irrationality",
                "decision": "not_claimed",
                "reason": "the certificate is finite and local",
            },
        ],
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [
                SOURCE_REF,
                AFFINE_REF,
                COCYCLE_REF,
                ANALYSIS_REF,
                LEAN_REF,
                PACKET_REF,
            ]
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
    print(json.dumps({"status": payload["status"], "output": str(output)}))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--min-c", type=int, default=0)
    parser.add_argument("--max-c", type=int, default=1858)
    parser.add_argument("--max-height", type=int, default=20)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if not (0 <= args.min_c <= args.max_c):
        parser.error("require 0 <= min-c <= max-c")
    if args.max_height < 3:
        parser.error("max-height must be at least 3")
    return emit(
        build_payload(args.min_c, args.max_c, args.max_height),
        args.output,
        args.check,
    )


if __name__ == "__main__":
    raise SystemExit(main())
