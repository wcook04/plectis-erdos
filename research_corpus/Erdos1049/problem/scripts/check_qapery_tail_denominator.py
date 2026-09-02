#!/usr/bin/env python3
"""Exact finite tail-denominator arithmetic for the primitive q-Apéry rows.

The source recurrence is imported from the existing exact selector checker.
For every tail start in the declared range, this checker computes

* the coordinate gcds on the finite tail,
* the gcd of all anchor Plücker minors,
* the certified moving-tail modulus, and
* the quotient of the Plücker gcd by that modulus.

The observed identity between that quotient and the denominator-coordinate
tail gcd is exact in the checked finite range.  The receipt deliberately does
not promote it to an all-index theorem.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import sys
from pathlib import Path

import sympy as sp


if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


REPO_ROOT = Path(__file__).resolve().parents[5]
SCRIPT_DIR = Path(__file__).resolve().parent
ROW_SOURCE_PATH = SCRIPT_DIR / "check_qapery_selector_remainder_escape.py"
ROW_SOURCE_SPEC = importlib.util.spec_from_file_location(
    "qapery_selector_rows", ROW_SOURCE_PATH
)
if ROW_SOURCE_SPEC is None or ROW_SOURCE_SPEC.loader is None:
    raise RuntimeError("cannot load the exact q-Apéry row generator")
row_source = importlib.util.module_from_spec(ROW_SOURCE_SPEC)
ROW_SOURCE_SPEC.loader.exec_module(row_source)

sys.path.insert(0, str(REPO_ROOT))
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


ROW_COUNT = 256
TAIL_STARTS = tuple(range(16))
LOSS_WITNESSES = (
    # (prime, multiplicative order of 3/2, first index where divisibility fails)
    (5, 2, 8),
    (19, 3, 54),
    (13, 4, 48),
    (7, 6, 36),
    (29, 7, 91),
    (97, 8, 88),
    (23, 11, 242),
)
SOURCE_REF = str(Path(__file__).resolve().relative_to(REPO_ROOT))
ROW_SOURCE_REF = str(ROW_SOURCE_PATH.relative_to(REPO_ROOT))
LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "QAperyTailDenominator.lean"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "QAperyTailDenominatorLab.md"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1049_qapery_tail_denominator_receipt.json"
)


def gcd_many(values: list[int]) -> int:
    result = 0
    for value in values:
        result = math.gcd(result, abs(value))
    return result


def factorization(value: int) -> dict[str, int]:
    return {str(prime): int(power) for prime, power in sp.factorint(value).items()}


def moving_tail_modulus(start: int) -> int:
    return 2 ** (3 * start * start + 3 * start + 1) * 3 ** (start + 1)


def first_squarefree_determinant_witness(
    rows: list[tuple[int, int]], start: int, prime: int
) -> dict[str, str | int] | None:
    """Find a tail pair whose determinant has exactly one factor `prime`."""

    for left in range(start, len(rows)):
        A_left, B_left = rows[left]
        for right in range(left + 1, len(rows)):
            A_right, B_right = rows[right]
            determinant = A_left * B_right - A_right * B_left
            if determinant % prime == 0 and determinant % (prime * prime) != 0:
                return {
                    "left_index": left,
                    "right_index": right,
                    "determinant": str(determinant),
                    "determinant_mod_prime_squared": determinant % (prime * prime),
                }
    return None


def build_result() -> dict[str, object]:
    rows = row_source.primitive_rows(ROW_COUNT)
    records: list[dict[str, object]] = []
    previous_denominator_gcd = 1

    for start in TAIL_STARTS:
        tail = rows[start:]
        anchor_A, anchor_B = rows[start]
        gcd_A = gcd_many([A for A, _ in tail])
        gcd_B = gcd_many([B for _, B in tail])
        gcd_all = gcd_many([coordinate for row in tail for coordinate in row])
        determinants = [
            anchor_A * B - A * anchor_B for A, B in rows[start + 1 :]
        ]
        determinant_gcd = gcd_many(determinants)
        modulus = moving_tail_modulus(start)
        if determinant_gcd % modulus != 0:
            raise AssertionError(f"moving-tail modulus fails at start {start}")
        normalized_plucker_gcd = determinant_gcd // modulus
        if normalized_plucker_gcd != gcd_B:
            raise AssertionError(
                f"tail denominator/Plucker identity fails at start {start}"
            )
        if gcd_all != 1:
            raise AssertionError(f"primitive tail lattice collapsed at start {start}")

        increment = gcd_B // math.gcd(gcd_B, previous_denominator_gcd)
        source_difference = 3**start - 2**start if start else 0
        increment_is_source_supported = (
            increment == 1 or source_difference % increment == 0
        )
        if not increment_is_source_supported:
            raise AssertionError(f"new divisor is not source-supported at {start}")

        odd_prime_consumers = []
        for prime_text, power in factorization(gcd_B).items():
            prime = int(prime_text)
            if prime in (2, 3):
                continue
            numerator_witness = next(
                index for index, (A, _) in enumerate(rows[start:], start) if A % prime
            )
            determinant_witness = (
                first_squarefree_determinant_witness(rows, start, prime)
                if power == 1
                else None
            )
            if power == 1 and determinant_witness is None:
                raise AssertionError(
                    f"gcd valuation one has no determinant witness for {prime}"
                )
            odd_prime_consumers.append(
                {
                    "prime": prime,
                    "tail_gcd_exponent": power,
                    "first_numerator_unit_index": numerator_witness,
                    "squarefree_determinant_witness": determinant_witness,
                }
            )

        records.append(
            {
                "tail_start": start,
                "finite_tail_end": ROW_COUNT - 1,
                "gcd_numerator_coordinates": str(gcd_A),
                "gcd_denominator_coordinates": str(gcd_B),
                "gcd_all_coordinates": str(gcd_all),
                "moving_tail_modulus": str(modulus),
                "anchor_plucker_gcd": str(determinant_gcd),
                "normalized_plucker_gcd": str(normalized_plucker_gcd),
                "normalized_plucker_equals_denominator_gcd": True,
                "denominator_gcd_factorization": factorization(gcd_B),
                "new_denominator_factor": str(increment),
                "new_factor_factorization": factorization(increment),
                "source_difference": str(source_difference),
                "new_factor_divides_three_pow_start_sub_two_pow_start": (
                    increment_is_source_supported
                ),
                "prime_support_consumers": odd_prime_consumers,
            }
        )
        previous_denominator_gcd = gcd_B

    loss_records = []
    for prime, order, first_loss in LOSS_WITNESSES:
        if any(B % prime != 0 for _, B in rows[order:first_loss]):
            raise AssertionError(
                f"prime {prime} does not persist up to its asserted first loss"
            )
        if rows[first_loss][1] % prime == 0:
            raise AssertionError(f"prime {prime} does not fail at {first_loss}")
        loss_block_end = min(first_loss + order, ROW_COUNT)
        if any(B % prime == 0 for _, B in rows[first_loss:loss_block_end]):
            raise AssertionError(f"prime {prime} loss is not block-aligned")
        returns_after_block = (
            first_loss + order < ROW_COUNT
            and rows[first_loss + order][1] % prime == 0
        )
        if first_loss + order < ROW_COUNT and not returns_after_block:
            raise AssertionError(f"prime {prime} does not return after its loss block")
        loss_records.append(
            {
                "prime": prime,
                "order_of_three_over_two_mod_prime": order,
                "divides_every_denominator_from_order_through": first_loss - 1,
                "first_loss_index": first_loss,
                "verified_loss_block_end": loss_block_end - 1,
                "returns_immediately_after_full_loss_block": returns_after_block,
            }
        )

    nontrivial = [
        record for record in records if int(record["gcd_denominator_coordinates"]) > 1
    ]
    result = {
        "schema": "erdos1049-qapery-tail-denominator/1",
        "parameters": {
            "row_count": ROW_COUNT,
            "tail_starts": list(TAIL_STARTS),
            "arithmetic": "exact Python integers generated from the exact Fraction recurrence",
        },
        "tail_records": records,
        "fixed_prime_loss_witnesses": loss_records,
        "first_nontrivial_tail": nontrivial[0],
        "last_checked_tail": records[-1],
        "finite_conclusions": {
            "all_tail_lattices_primitive": True,
            "gcd_numerator_coordinates_constant": str(
                gcd_many([int(record["gcd_numerator_coordinates"]) for record in records])
            ),
            "normalized_plucker_equals_denominator_gcd_at_every_start": True,
            "every_new_denominator_factor_is_source_supported": True,
            "first_long_run_odd_prime": 211,
            "first_long_run_odd_prime_start": 5,
            "fixed_prime_infinite_persistence_falsified_for_displayed_primes": True,
        },
        "claim_ceiling": (
            "The identities and long finite divisor runs are exact only for primitive "
            "rows 0 through 255 and tail starts 0 through 15. Explicit later loss "
            "blocks refute promotion of several fixed primes to infinite-tail "
            "divisors. The checker supplies neither a cofinal moving-window law nor "
            "asymptotic real-form decay or irrationality at 3/2."
        ),
        "experiment_contract": build_experiment_contract(
            problem_id="erdos_1049",
            target_statement="Prove irrationality of the Lambert value at q=3/2.",
            claim_ceiling=(
                "Exact finite tail-denominator/Plucker identities through row 255 "
                "plus explicit fixed-prime loss blocks; no cofinal window or "
                "irrationality theorem."
            ),
            hypothesis_id="primitive_qapery_tail_denominator_support",
            hypothesis_statement=(
                "Primitive q-Apéry moving tails carry odd denominator-coordinate "
                "divisors that also account for the extra Plücker lattice index."
            ),
            probe_id="exact_tail_coordinate_and_anchor_minor_gcd",
            probe_question=(
                "Does the primitive moving-tail lattice acquire persistent odd "
                "denominator support, and does it equal the Plücker index beyond "
                "the certified 2-adic/3-adic modulus?"
            ),
            computation=(
                "Generate 256 primitive recurrence rows; for starts 0 through 15 "
                "compute exact coordinate gcds, anchor-minor gcds, source moduli, "
                "prime factorizations, determinant witnesses, and first-loss blocks."
            ),
            falsifier=(
                "A checked start where the source modulus does not divide every "
                "anchor minor, the normalized minor gcd differs from the tail-B gcd, "
                "or a new factor is absent from 3^s-2^s."
            ),
            stop_condition=(
                "Stop finite extension once fixed-prime infinite persistence is "
                "falsified and the required replacement is a precise moving-window law."
            ),
            survival_consequence=(
                "Long finite-window arithmetic supplies an automatic rational "
                "nonvanishing and one-coordinate selector certificate."
            ),
            falsification_consequence=(
                "Without persistent odd tail support, this source-specific route "
                "does not improve generic determinant nonvanishing."
            ),
            consumer_ref=LEAN_REF,
            analysis_refs=[ANALYSIS_REF],
            source_refs=[SOURCE_REF, ROW_SOURCE_REF],
            input_receipt_refs=[],
            result_status="exact_one_way_result",
            result_summary=(
                "All checked primitive tail lattices remain primitive, while from "
                "start five the denominator-coordinate tail gcd is nontrivial. At "
                "every checked start it equals the anchor Plücker gcd divided by "
                "the certified moving-tail modulus; each newly appearing factor "
                "divides 3^s-2^s."
            ),
            progress_class="mechanism_opened",
            decision_basis=(
                "The exact first long-run divisor is 211 from start five, while "
                "5, 7, 13, 19, 23, 29 and 97 have explicit later loss blocks."
            ),
            next_analytic_target=(
                "Prove or falsify a cofinal moving-prime law on the exact selector "
                "window of width 3s^2+5s+3, analyze the block dynamics modulo each "
                "prime, then compare the finite-window gain with source-derived "
                "decay for two analytic-aware recombined forms."
            ),
        ),
        "sources": [
            source_record(REPO_ROOT, ref)
            for ref in [SOURCE_REF, ROW_SOURCE_REF, LEAN_REF, ANALYSIS_REF]
        ],
    }
    validate_experiment_contract(result["experiment_contract"])
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = build_result()
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.check:
        if not args.output.exists() or args.output.read_text() != encoded:
            raise SystemExit("q-Apéry tail-denominator receipt is stale")
        print("q-Apéry tail-denominator receipt is current")
        return
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(encoded)
    print(args.output)


if __name__ == "__main__":
    main()
