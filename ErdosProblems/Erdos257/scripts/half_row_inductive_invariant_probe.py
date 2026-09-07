#!/usr/bin/env python3
"""Exact structural probe for the target-zero half-row producer.

This is deliberately not a longer survival audit.  It tests candidate
induction mechanisms for excluding the even-row bank hole singled out by the
existing target-zero analysis.  Every
reported failure is an exact integer counterexample to the proposed lemma.

The modulo-``2^d`` row is additionally checked against its exact partition
identity and strict bank boundary.  On that boundary, modular silence is the
midpoint hole itself, so the audit reports it as a route obstruction rather
than as an independent finite invariant.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from typing import Any


def valuation_two(value: int) -> int:
    if value <= 0:
        raise ValueError("valuation_two expects a positive integer")
    return (value & -value).bit_length() - 1


def analyze(max_d: int) -> dict[str, Any]:
    if max_d < 8:
        raise ValueError("--max-d must be at least 8")

    parity_failure: dict[str, int] | None = None
    one_carry_failure: dict[str, int] | None = None
    modular_silence: dict[str, int] | None = None
    modular_identity_failure: dict[str, int] | None = None
    strict_bank_bound_failure: dict[str, int] | None = None
    modular_hole_equivalence_failure: dict[str, int] | None = None
    first_hole: dict[str, int] | None = None
    max_pre_valuation = (-1, -1, -1)
    valuation_records: list[dict[str, int]] = []
    suffix_fixture: dict[str, Any] | None = None
    digest = hashlib.sha256()

    for d in range(2, max_d + 1):
        n = 2 * d
        residual = 1 << (n - 1)
        selected: list[int] = []
        low_load = 0

        # Stop immediately before the new midpoint coin.  The exact midpoint
        # coin is 2^d+1.  Greedy row closure can fail at this step only when
        # this pre-residual is exactly 2^d.
        for a in range(2, d):
            coin = (1 << n) // ((1 << a) - 1)
            if coin <= residual:
                residual -= coin
                selected.append(a)
                low_load += coin & ((1 << d) - 1)

        divisor_pulse = sum(n % a == 0 for a in selected)
        low_residue = low_load & ((1 << d) - 1)
        digest.update(
            f"{d}:{residual}:{divisor_pulse}:{low_load}:{low_residue};".encode()
        )

        if d >= 8 and parity_failure is None and divisor_pulse % 2 == 0:
            parity_failure = {
                "rank": d,
                "pre_residual": residual,
                "divisor_pulse": divisor_pulse,
            }

        if d >= 8 and one_carry_failure is None and low_load >= (1 << d):
            one_carry_failure = {
                "rank": d,
                "pre_residual": residual,
                "low_load": low_load,
                "modulus": 1 << d,
            }

        if d >= 8 and modular_identity_failure is None and (
            low_residue + residual
        ) % (1 << d) != 0:
            modular_identity_failure = {
                "rank": d,
                "pre_residual": residual,
                "low_residue": low_residue,
                "modulus": 1 << d,
            }

        strict_bank = 0 < residual < (1 << (d + 1))
        if d >= 8 and strict_bank_bound_failure is None and not strict_bank:
            strict_bank_bound_failure = {
                "rank": d,
                "pre_residual": residual,
                "strict_upper_bound": 1 << (d + 1),
            }

        if (
            d >= 8
            and strict_bank
            and modular_hole_equivalence_failure is None
            and ((low_residue == 0) != (residual == (1 << d)))
        ):
            modular_hole_equivalence_failure = {
                "rank": d,
                "pre_residual": residual,
                "low_residue": low_residue,
                "hole_value": 1 << d,
            }

        if d >= 8 and modular_silence is None and low_residue == 0:
            modular_silence = {
                "rank": d,
                "pre_residual": residual,
                "hole_value": 1 << d,
                "low_load": low_load,
                "modulus": 1 << d,
            }

        if residual == (1 << d) and first_hole is None:
            first_hole = {
                "rank": d,
                "pre_residual": residual,
                "divisor_pulse": divisor_pulse,
            }

        if residual > 0:
            candidate = (valuation_two(residual), d, residual)
            if candidate[0] > max_pre_valuation[0]:
                max_pre_valuation = candidate
                valuation_records.append(
                    {
                        "valuation": candidate[0],
                        "rank": d,
                        "pre_residual": residual,
                    }
                )

        if d == 26:
            midpoint_coin = (1 << d) + 1
            midpoint_take = residual >= midpoint_coin
            suffix_fixture = {
                "rank": d,
                "pre_residual": residual,
                "midpoint_take": midpoint_take,
                "post_residual": residual - midpoint_coin if midpoint_take else residual,
                "support_through_midpoint": selected + ([d] if midpoint_take else []),
            }

    mechanisms = {
        "odd_divisor_pulse": {
            "claim": "the selected proper-divisor pulse is always odd",
            "status": "falsified" if parity_failure else "not_falsified",
            "first_counterexample": parity_failure,
        },
        "single_low_half_carry": {
            "claim": "the selected low-half quotient load is below 2^d",
            "status": "falsified" if one_carry_failure else "not_falsified",
            "first_counterexample": one_carry_failure,
        },
        "fixed_fourteen_bit_nonzero_window": {
            "claim": "the even-row pre-residual is never divisible by 2^15",
            "status": (
                "falsified" if max_pre_valuation[0] >= 15 else "not_falsified"
            ),
            "first_counterexample": next(
                (row for row in valuation_records if row["valuation"] >= 15),
                None,
            ),
        },
        "pure_mod_2d_hole_exclusion": {
            "claim": "the low-half quotient residue alone is nonzero",
            "status": (
                "boundary_not_certified"
                if modular_identity_failure
                or strict_bank_bound_failure
                or modular_hole_equivalence_failure
                else (
                    "falsified"
                    if modular_silence
                    else "not_falsified_but_exactly_the_midpoint_hole"
                )
            ),
            "first_counterexample": modular_silence,
            "exact_relation": (
                "(low_residue + pre_residual) mod 2^d = 0"
            ),
            "strict_bank_boundary": "0 < pre_residual < 2^(d+1)",
            "route_obstruction": (
                "on the strict bank interval, low_residue = 0 iff "
                "pre_residual = 2^d; modular nonvanishing is the midpoint "
                "hole exclusion itself, not an independent invariant"
            ),
            "first_modular_identity_failure": modular_identity_failure,
            "first_strict_bank_bound_failure": strict_bank_bound_failure,
            "first_equivalence_failure": modular_hole_equivalence_failure,
        },
    }
    return {
        "schema": "erdos257_half_row_inductive_invariant_probe_v1",
        "range": {"min_rank": 2, "max_rank": max_d},
        "exact_arithmetic": "integer quotient greedy",
        "tested_hole": "pre_residual_at_even_row_2d_equals_2^d",
        "mechanisms": mechanisms,
        "first_actual_hole": first_hole,
        "maximum_two_adic_valuation_of_pre_residual": {
            "valuation": max_pre_valuation[0],
            "rank": max_pre_valuation[1],
            "pre_residual": max_pre_valuation[2],
        },
        "two_adic_valuation_records": valuation_records,
        "suffix_cylinder_fixture": suffix_fixture,
        "trace_sha256": digest.hexdigest(),
        "claim_ceiling": (
            "exact counterexamples eliminate only the named induction lemmas; "
            "the modular row is an exact route retirement only under its "
            "stated strict bank boundary; absence of an actual hole on the "
            "finite range is not a proof"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-d", type=int, default=2500)
    parser.add_argument("--check-receipt")
    args = parser.parse_args()
    result = analyze(args.max_d)
    if args.check_receipt:
        with open(args.check_receipt, encoding="utf-8") as handle:
            expected = json.load(handle)
        if result != expected:
            raise SystemExit("receipt mismatch")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
