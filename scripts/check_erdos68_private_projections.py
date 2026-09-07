#!/usr/bin/env python3
"""Generate an exact finite receipt for the Erdős #68 private projections.

The computation mirrors the definitions in
`ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean`.  It uses only
Python integers.  The result is finite research evidence, not proof of the
cofinal producer required for irrationality.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from pathlib import Path
from typing import Any

sys.set_int_max_str_digits(0)

REPO_ROOT = Path(__file__).resolve().parents[3]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
)

SCRIPT_PATH = Path(__file__).resolve()
SOURCE_REF = str(SCRIPT_PATH.relative_to(REPO_ROOT))
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/"
    "PrivateProjectionComputationalLab.md"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/"
    "EndpointWeightedPrivateSupport.lean"
)
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse"
    / "erdos68_private_projection_receipt.json"
)


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    divisor = 3
    while divisor * divisor <= n:
        if n % divisor == 0:
            return False
        divisor += 2
    return True


def lcm(a: int, b: int) -> int:
    return a // math.gcd(a, b) * b


def int_bytes(value: int) -> bytes:
    if value < 0:
        raise ValueError("receipt integers must be nonnegative")
    if value == 0:
        return b"\x00"
    return value.to_bytes((value.bit_length() + 7) // 8, "big")


def update_exact_digest(digest: Any, tag: str, value: int) -> None:
    payload = int_bytes(value)
    tag_bytes = tag.encode("utf-8")
    digest.update(len(tag_bytes).to_bytes(4, "big"))
    digest.update(tag_bytes)
    digest.update(len(payload).to_bytes(8, "big"))
    digest.update(payload)


def fingerprint(value: int) -> dict[str, Any]:
    payload = int_bytes(value)
    return {
        "encoding": "minimal_unsigned_big_endian",
        "bit_length": value.bit_length(),
        "sha256": hashlib.sha256(payload).hexdigest(),
    }


def complementary_projection(tail: int, modulus: int) -> int:
    if modulus <= 0:
        raise ValueError("projection modulus must be positive")
    return (modulus - tail % modulus) % modulus


def select_projection_pair(
    *,
    indices: range,
    private_quotients: dict[int, int],
    private_modulus: int,
    tail_numerator: int,
) -> tuple[dict[str, int], dict[str, int]]:
    # Since every modulus is R/q for the same private modulus R, descending
    # modulus order is exactly ascending private-quotient order.  Sorting the
    # much smaller quotients lets us postpone enormous R/q divisions and
    # modular reductions until a candidate is actually inspected.
    ordered = sorted(
        (quotient, index)
        for index in indices
        if (quotient := private_quotients[index]) > 1
    )
    if len(ordered) < 2:
        raise AssertionError("fewer than two nontrivial private quotients")
    first_quotient, first_index = ordered[0]
    first_modulus = private_modulus // first_quotient
    first = {
        "index": first_index,
        "private_quotient": first_quotient,
        "modulus": first_modulus,
        "projection": complementary_projection(tail_numerator, first_modulus),
    }
    for quotient, index in ordered[1:]:
        modulus = private_modulus // quotient
        candidate = {
            "index": index,
            "private_quotient": quotient,
            "modulus": modulus,
            "projection": complementary_projection(tail_numerator, modulus),
        }
        if candidate["projection"] != first["projection"]:
            return first, candidate
    raise AssertionError("all nontrivial complementary projections agree")


def compress_pair_runs(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    runs: list[dict[str, Any]] = []
    for row in rows:
        signature = (
            tuple(row["selected_indices"]),
            tuple(row["selected_private_quotients"]),
        )
        if runs and runs[-1]["signature"] == signature:
            runs[-1]["prime_through"] = row["p"]
            runs[-1]["prime_count"] += 1
            continue
        runs.append(
            {
                "signature": signature,
                "prime_from": row["p"],
                "prime_through": row["p"],
                "prime_count": 1,
                "selected_indices": row["selected_indices"],
                "selected_private_quotients":
                    row["selected_private_quotients"],
            }
        )
    for run in runs:
        del run["signature"]
    return runs


def build_receipt(max_prime: int) -> dict[str, Any]:
    if max_prime < 11:
        raise ValueError("max-prime must be at least 11")
    max_index = 2 * max_prime - 1
    factorials = [1] * (max_index + 1)
    for n in range(1, max_index + 1):
        factorials[n] = factorials[n - 1] * n
    denominators = [0] * (max_index + 1)
    for n in range(2, max_index + 1):
        denominators[n] = factorials[n] - 1

    target_primes = {
        p for p in range(11, max_prime + 1) if is_prime(p)
    }
    denominator_lcm = 1
    denominator_lcm_tail_numerator = 0
    pairwise_collision_lcm = 1
    exact_digest = hashlib.sha256()
    rows: list[dict[str, Any]] = []

    for upper_index in range(2, max_index + 1):
        denominator = denominators[upper_index]
        # Primewise valuations give the exact incremental identity
        #
        #   lcm_i gcd(denominator, d_i)
        #     = gcd(denominator, lcm_i d_i).
        #
        # This replaces the quadratic rescan of every prior denominator
        # while preserving the literal pairwise-collision core.
        previous_denominator_lcm = denominator_lcm
        pairwise_collision_lcm = lcm(
            pairwise_collision_lcm,
            math.gcd(denominator, previous_denominator_lcm),
        )
        denominator_lcm = lcm(previous_denominator_lcm, denominator)
        lcm_growth = denominator_lcm // previous_denominator_lcm
        # If L' = lcm(L,d), then the old prefix numerator scales by L'/L
        # and the new summand is L'/d.  This replaces every prime checkpoint's
        # O(p) list of huge exact divisions by one multiplication and division.
        denominator_lcm_tail_numerator = (
            denominator_lcm_tail_numerator * lcm_growth
            + denominator_lcm // denominator
        )
        if upper_index % 2 == 0:
            continue
        p = (upper_index + 1) // 2
        if p not in target_primes:
            continue

        indices = range(2, upper_index + 1)
        base = factorials[p - 1]
        endpoint_lcm = lcm(base, denominator_lcm)
        endpoint_scale = endpoint_lcm // denominator_lcm
        collision_core = lcm(base, pairwise_collision_lcm)
        private_quotients = {
            n: denominators[n] // math.gcd(denominators[n], collision_core)
            for n in indices
        }
        # The private quotients are pairwise coprime after the collision core
        # is removed, so their product is the already-checked L_p/C_p ratio.
        # Avoid rebuilding that enormous product at every prime checkpoint.
        private_modulus = endpoint_lcm // collision_core
        tail_numerator = denominator_lcm_tail_numerator * endpoint_scale
        first, second = select_projection_pair(
            indices=indices,
            private_quotients=private_quotients,
            private_modulus=private_modulus,
            tail_numerator=tail_numerator,
        )
        global_complementary_residue = complementary_projection(
            tail_numerator,
            private_modulus,
        )
        smaller_modulus = min(first["modulus"], second["modulus"])
        larger_private_quotient = max(
            first["private_quotient"],
            second["private_quotient"],
        )
        budget_times_lcm = (2 * p + 1) * endpoint_lcm
        scale = 2 * p * p * factorials[upper_index]
        scale_times_modulus = scale * smaller_modulus
        scale_times_global_residue = (
            scale * global_complementary_residue
        )
        collision_cap_left = (
            (2 * p + 1)
            * collision_core
            * larger_private_quotient
        )
        collision_cap_margin = scale - collision_cap_left
        checks = {
            "private_modulus_nontrivial": private_modulus > 1,
            "collision_times_private_equals_lcm":
                collision_core * private_modulus == endpoint_lcm,
            "selected_quotients_divide_private_modulus":
                private_modulus % first["private_quotient"] == 0
                and private_modulus % second["private_quotient"] == 0,
            "selected_moduli_positive":
                first["modulus"] > 0 and second["modulus"] > 0,
            "complement_formula_exact":
                first["projection"] == (-tail_numerator) % first["modulus"]
                and second["projection"]
                == (-tail_numerator) % second["modulus"],
            "global_complement_formula_exact":
                global_complementary_residue
                == (-tail_numerator) % private_modulus,
            "complementary_projections_disagree":
                first["projection"] != second["projection"],
            "min_modulus_times_max_quotient_equals_private_modulus":
                smaller_modulus * larger_private_quotient
                == private_modulus,
            "collision_cap_closing_inequality":
                collision_cap_left < scale,
            "scaled_closing_inequality":
                budget_times_lcm < scale_times_modulus,
            "collision_cap_margin_factorization":
                scale_times_modulus - budget_times_lcm
                == collision_cap_margin * smaller_modulus,
            "global_scaled_closing_inequality":
                budget_times_lcm < scale_times_global_residue,
        }
        if not all(checks.values()):
            failed = [name for name, passed in checks.items() if not passed]
            raise AssertionError(f"p={p}: failed checks: {failed}")

        exact_values = {
            "endpoint_lcm": endpoint_lcm,
            "collision_core": collision_core,
            "private_modulus": private_modulus,
            "tail_numerator": tail_numerator,
            "first_modulus": first["modulus"],
            "second_modulus": second["modulus"],
            "first_projection": first["projection"],
            "second_projection": second["projection"],
            "closing_margin": scale_times_modulus - budget_times_lcm,
            "collision_cap_left": collision_cap_left,
            "collision_cap_margin": collision_cap_margin,
            "global_complementary_residue":
                global_complementary_residue,
            "global_closing_margin":
                scale_times_global_residue - budget_times_lcm,
        }
        for name, value in exact_values.items():
            update_exact_digest(exact_digest, f"p={p}:{name}", value)
        rows.append(
            {
                "p": p,
                "selected_indices": [first["index"], second["index"]],
                "selected_private_quotients": [
                    first["private_quotient"],
                    second["private_quotient"],
                ],
                "nontrivial_private_quotient_count": sum(
                    quotient > 1 for quotient in private_quotients.values()
                ),
                "checks": checks,
                "exact_value_fingerprints": {
                    name: fingerprint(value)
                    for name, value in exact_values.items()
                },
            }
        )

    all_check_names = sorted(rows[0]["checks"])
    aggregate_checks = {
        name: all(row["checks"][name] for row in rows)
        for name in all_check_names
    }
    experiment_contract = build_experiment_contract(
        problem_id="erdos_68",
        target_statement=(
            "Prove that S=sum_{n>=2} 1/(n!-1) is irrational."
        ),
        claim_ceiling=(
            "Finite prime-block certificates do not prove the cofinal "
            "collision-cap producer required for irrationality."
        ),
        hypothesis_id="cofinal_moving_private_projection_pair",
        hypothesis_statement=(
            "Cofinal prime blocks admit a moving pair of private quotients "
            "whose complementary projections disagree and whose collision "
            "cap closes the Lean-checked endpoint window."
        ),
        probe_id="deterministic_prime_block_projection_scan",
        probe_question=(
            "Does the max-min leave-one-out pair survive on every displayed "
            "prime block, and does its owner genealogy expose a tractable "
            "moving-pair supply law?"
        ),
        computation=(
            "Reconstruct L_p, C_p, all private quotients, R_p, T_p, the "
            "global complementary residue, and the deterministic first "
            "projection-disagreeing max-min pair with Python integers."
        ),
        falsifier=(
            "A displayed prime block with fewer than two nontrivial private "
            "quotients, no projection disagreement, or a failed collision-cap "
            "or global-residue closing inequality."
        ),
        stop_condition=(
            "Stop extending this mechanism at the first exact failed check; "
            "otherwise use pair-run transitions to formulate a cofinal owner "
            "supply lemma rather than counting the longer horizon as proof."
        ),
        survival_consequence=(
            "Finite survival retains the moving-pair producer and promotes "
            "its owner-transition law as the next analytic target."
        ),
        falsification_consequence=(
            "The first failed exact block eliminates this deterministic "
            "moving-pair selection mechanism and redirects effort to the "
            "global complementary-residue or prime-cylinder routes."
        ),
        consumer_ref=CONSUMER_REF,
        analysis_refs=[ANALYSIS_REF],
        source_refs=[SOURCE_REF],
        result_status="finite_support",
        result_summary=(
            f"All {len(rows)} prime blocks from 11 through {max_prime} pass "
            "the exact disagreement, collision-cap, and global-residue checks; "
            "this is finite mechanism support only."
        ),
        consumer_declarations=[
            "ErdosProblems.Erdos68.irrational_factorialGapSeries_of_cofinal_complementary_disagreement_collisionCap"
        ],
        resource_bounds={
            "maximum_prime": max_prime,
            "maximum_factorial_index": max_index,
        },
        progress_class="finite_horizon_only",
        decision_basis=(
            "No displayed block falsifies the deterministic selector, but a "
            "bounded prime range supplies no cofinal quantifier."
        ),
        next_analytic_target=(
            "Use the separate exact owner-recurrence receipt to formulate a "
            "cofinal two-owner renewal theorem rather than extending this horizon."
        ),
    )
    return {
        "schema": "erdos68_private_projection_receipt_v1",
        "proof_authority":
            "exact_finite_integer_computation_not_cofinal_lean_proof",
        "definitions": {
            "index_block": "2 <= n <= 2p-1",
            "denominator": "d_n = n! - 1",
            "endpoint_lcm": "L_p = lcm((p-1)!, d_2, ..., d_(2p-1))",
            "collision_core":
                "C_p = lcm((p-1)!, gcd(d_i,d_j) for i<j)",
            "collision_core_increment":
                "lcm_i gcd(d_n,d_i) = gcd(d_n,lcm_i d_i)",
            "tail_numerator_increment":
                "if L'=lcm(L,d), then T'=T*(L'/L)+L'/d",
            "private_quotient": "r_n = d_n / gcd(d_n,C_p)",
            "private_modulus": "R_p = product_n r_n",
            "tail_numerator": "T_p = sum_n L_p/d_n",
            "leave_one_out_modulus": "Q_n = R_p/r_n",
            "projection_scale": "A_p = 2p^2(2p-1)!",
            "collision_cap":
                "(2p+1) C_p max(r_i,r_j) < A_p",
            "complementary_projection": "(Q_n-(T_p mod Q_n)) mod Q_n",
            "global_complementary_residue":
                "rho_p = (R_p-(T_p mod R_p)) mod R_p",
        },
        "selection_policy": (
            "among r_n>1, maximize the smaller leave-one-out modulus; "
            "choose the least-index deterministic pair at the first "
            "complementary-projection disagreement"
        ),
        "range": {
            "minimum_prime": 11,
            "maximum_prime": max_prime,
            "prime_count": len(rows),
        },
        "all_checks": aggregate_checks,
        "pair_runs": compress_pair_runs(rows),
        "rows": rows,
        "experiment_contract": experiment_contract,
        "canonical_exact_payload_sha256": exact_digest.hexdigest(),
        "source": source_record(REPO_ROOT, SOURCE_REF),
        "lean_reentry_target": (
            "ErdosProblems.Erdos68."
            "irrational_factorialGapSeries_of_cofinal_"
            "complementary_disagreement_collisionCap"
        ),
        "claim_ceiling": (
            "The receipt verifies finitely many prime blocks only. "
            "It does not prove that disagreeing projections satisfying "
            "the collision-cap inequality exist cofinally, or that the "
            "global complementary residue clears its threshold cofinally."
        ),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-prime", type=int, default=503)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument(
        "--check",
        action="store_true",
        help="compare the deterministic receipt with --output",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    receipt = build_receipt(args.max_prime)
    rendered = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    output = args.output.resolve()
    if args.check:
        if not output.exists():
            print(f"missing receipt: {output}", file=sys.stderr)
            return 1
        if output.read_text(encoding="utf-8") != rendered:
            print(f"stale receipt: {output}", file=sys.stderr)
            return 1
        print(
            json.dumps(
                {
                    "status": "current",
                    "output": str(output),
                    "prime_count": receipt["range"]["prime_count"],
                    "maximum_prime": receipt["range"]["maximum_prime"],
                    "canonical_exact_payload_sha256":
                        receipt["canonical_exact_payload_sha256"],
                },
                sort_keys=True,
            )
        )
        return 0
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(rendered, encoding="utf-8")
    print(
        json.dumps(
            {
                "status": "written",
                "output": str(output),
                "prime_count": receipt["range"]["prime_count"],
                "maximum_prime": receipt["range"]["maximum_prime"],
                "canonical_exact_payload_sha256":
                    receipt["canonical_exact_payload_sha256"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
