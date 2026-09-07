#!/usr/bin/env python3
"""Discriminate record-phase laws at the Erdős-257 fatal boundary.

The exact analytic observation behind this lab is that a final greedy skip
leaves a positive residual gap.  On the subsequent all-take tail the Lambert
defect has a positive homogeneous dyadic component.  Since the divisor load
at rank ``n`` is at most ``n``, every sufficiently late rank is then a new
strict defect record.

The computation does not prove survival of the canonical ``1/21`` orbit.  It
checks the two sides of the theorem selector: the canonical prefix has a very
sparse record set, while exact rational fatal-gap splices acquire a terminal
suffix in which every rank is a record and the observed mod-four lock fails.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
import json
from pathlib import Path
from typing import Any

from euler_midpoint_service_lab import reconstruct_orbit, target_digits
from newton_nested_height_lab import (
    load_canonical_bits,
    tail_upper_bound,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/"
    "RecordCofinitenessBoundary.md"
)


def canonical_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def longest_consecutive_run(values: list[int]) -> int:
    best = current = 0
    previous: int | None = None
    for value in values:
        current = current + 1 if previous is not None and value == previous + 1 else 1
        best = max(best, current)
        previous = value
    return best


def positive_divisors(n: int) -> list[int]:
    """Return all positive divisors in increasing order."""

    low: list[int] = []
    high: list[int] = []
    divisor = 1
    while divisor * divisor <= n:
        if n % divisor == 0:
            low.append(divisor)
            if divisor * divisor != n:
                high.append(n // divisor)
        divisor += 1
    return low + list(reversed(high))


def prime_factorization(n: int) -> list[list[int]]:
    """Exact trial-division factorization, JSON-friendly."""

    factors: list[list[int]] = []
    prime = 2
    while prime * prime <= n:
        exponent = 0
        while n % prime == 0:
            n //= prime
            exponent += 1
        if exponent:
            factors.append([prime, exponent])
        prime = 3 if prime == 2 else prime + 2
    if n > 1:
        factors.append([n, 1])
    return factors


def canonical_summary(ranks: int) -> dict[str, Any]:
    bits = load_canonical_bits(ranks)
    orbit = reconstruct_orbit(bits, target_digits(1, 21, ranks), ranks)
    records = orbit.strict_records
    mature = [rank for rank in records if rank > 19]
    repair_margins = [
        int(orbit.loads[rank])
        - int(orbit.defects[rank - 1])
        - int(orbit.digits[rank])
        for rank in range(1, ranks + 1)
    ]
    repairs = [
        rank for rank in range(1, ranks + 1) if repair_margins[rank - 1] >= 0
    ]
    repair_gaps = [
        repairs[index] - repairs[index - 1]
        for index in range(1, len(repairs))
    ]
    multiple_120_rows = [
        (rank, repair_margins[rank - 1])
        for rank in range(120, ranks + 1, 120)
    ]
    multiple_120_proper_rows = []
    multiple_120_primorial_rows = []
    multiple_240_primorial_rows = []
    primorial_margin_by_cofactor: dict[int, int] = {}
    cofactor_class_rows: dict[str, list[tuple[int, int]]] = {
        "unit": [],
        "prime": [],
        "composite": [],
    }
    for rank, _ in multiple_120_rows:
        defect = int(orbit.defects[rank - 1])
        proper_load = int(orbit.loads[rank]) - int(bits[rank])
        # Inclusion-exclusion for selected d dividing at least one of
        # n/2, n/3, n/5.  Every such d is a proper divisor of n.
        primorial_union_load = (
            int(orbit.loads[rank // 2])
            + int(orbit.loads[rank // 3])
            + int(orbit.loads[rank // 5])
            - int(orbit.loads[rank // 6])
            - int(orbit.loads[rank // 10])
            - int(orbit.loads[rank // 15])
            + int(orbit.loads[rank // 30])
        )
        multiple_120_proper_rows.append(
            (rank, proper_load - defect - 1)
        )
        primorial_margin = primorial_union_load - defect - 1
        multiple_120_primorial_rows.append((rank, primorial_margin))
        primorial_margin_by_cofactor[rank // 120] = primorial_margin
        if rank % 240 == 0:
            multiple_240_primorial_rows.append((rank, primorial_margin))
        cofactor_factorization = prime_factorization(rank // 120)
        cofactor_big_omega = sum(
            exponent for _, exponent in cofactor_factorization
        )
        cofactor_class = (
            "unit"
            if not cofactor_factorization
            else "prime"
            if cofactor_big_omega == 1
            else "composite"
        )
        cofactor_class_rows[cofactor_class].append((rank, primorial_margin))

    primorial_equality_anatomy = []
    for rank, margin in multiple_120_primorial_rows:
        if margin != 0:
            continue
        selected_union = [
            divisor
            for divisor in positive_divisors(rank)
            if bits[divisor]
            and any(
                (rank // prime) % divisor == 0
                for prime in (2, 3, 5)
            )
        ]
        primorial_equality_anatomy.append(
            {
                "rank": rank,
                "rank_factorization": prime_factorization(rank),
                "cofactor_over_120": rank // 120,
                "cofactor_factorization": prime_factorization(rank // 120),
                "previous_defect": int(orbit.defects[rank - 1]),
                "primorial_union_load": len(selected_union),
                "selected_union_ranks": selected_union,
                "seven_columns": {
                    str(quotient): int(orbit.loads[rank // quotient])
                    for quotient in (2, 3, 5, 6, 10, 15, 30)
                },
            }
        )

    # The cheapest explanation of the composite-cofactor slack would be a
    # factor-descent induction: adjoining one prime factor never lowers the
    # repair margin, or at least every composite cofactor has one
    # prime-deletion parent whose margin is no larger.  Test both exact
    # statements on the same canonical rows.  The second statement is the
    # genuinely useful induction socket; an all-parent decrease falsifies it.
    factor_descent_edges: list[dict[str, int]] = []
    all_parent_decrease_rows: list[dict[str, Any]] = []
    composite_cofactor_count = 0
    for cofactor, child_margin in sorted(primorial_margin_by_cofactor.items()):
        factorization = prime_factorization(cofactor)
        if sum(exponent for _, exponent in factorization) < 2:
            continue
        composite_cofactor_count += 1
        parent_edges: list[dict[str, int]] = []
        for prime, _ in factorization:
            parent_cofactor = cofactor // prime
            parent_margin = primorial_margin_by_cofactor[parent_cofactor]
            edge = {
                "cofactor": cofactor,
                "prime_removed": prime,
                "parent_cofactor": parent_cofactor,
                "child_margin": child_margin,
                "parent_margin": parent_margin,
                "difference": child_margin - parent_margin,
            }
            factor_descent_edges.append(edge)
            parent_edges.append(edge)
        if all(edge["difference"] < 0 for edge in parent_edges):
            all_parent_decrease_rows.append(
                {
                    "cofactor": cofactor,
                    "child_margin": child_margin,
                    "parent_edges": parent_edges,
                }
            )

    decreasing_edges = [
        edge for edge in factor_descent_edges if edge["difference"] < 0
    ]
    factor_descent_falsifier = {
        "status": "falsified_exact_finite",
        "strong_statement": (
            "adjoining a prime factor to the cofactor never decreases "
            "U_30(120*m)-Q_(120*m-1)-1"
        ),
        "inductive_statement": (
            "every composite cofactor has a prime-deletion parent whose "
            "primorial repair margin is no larger"
        ),
        "composite_cofactor_count": composite_cofactor_count,
        "factor_descent_edge_count": len(factor_descent_edges),
        "decreasing_edge_count": len(decreasing_edges),
        "minimum_difference": min(
            edge["difference"] for edge in factor_descent_edges
        ),
        "first_decreasing_edge": min(
            decreasing_edges,
            key=lambda edge: (edge["cofactor"], edge["prime_removed"]),
        ),
        "tightest_edges": sorted(
            factor_descent_edges,
            key=lambda edge: (
                edge["difference"],
                edge["cofactor"],
                edge["prime_removed"],
            ),
        )[:20],
        "all_parent_decrease_count": len(all_parent_decrease_rows),
        "all_parent_decrease_rows": all_parent_decrease_rows,
        "consequence": (
            "The observed composite unit slack is not inherited by static "
            "factor descent.  Any proof of PU240+ must couple the selected "
            "divisor-layer gain to the simultaneous live-defect change."
        ),
    }

    # The doubled-layer identity has a better factor coordinate because it
    # retains the simultaneous live defect.  Put
    #
    #   P(m) = f(120m) + g(40m) + g(24m),
    #   D(m) = Q_(240m-1) + g(8m),
    #
    # where g(a)=f(2a)-f(a).  Then DL240 makes PU240+ exactly
    # D(m)+2 <= P(m).  Test the named strong-induction socket: deletion of
    # the largest prime factor does not lower P-D, except at the isolated
    # directly-safe cofactor 16.
    def top_two_adic_layer_load(rank: int) -> int:
        return int(orbit.loads[2 * rank]) - int(orbit.loads[rank])

    coupled_rows: dict[int, dict[str, int]] = {}
    for cofactor in range(1, ranks // 240 + 1):
        payment = (
            int(orbit.loads[120 * cofactor])
            + top_two_adic_layer_load(40 * cofactor)
            + top_two_adic_layer_load(24 * cofactor)
        )
        debt = (
            int(orbit.defects[240 * cofactor - 1])
            + top_two_adic_layer_load(8 * cofactor)
        )
        coupled_rows[cofactor] = {
            "cofactor": cofactor,
            "payment": payment,
            "debt": debt,
            "balance": payment - debt,
            "pu240_slack": payment - debt - 2,
        }

    coupled_factor_edges: list[dict[str, int]] = []
    for cofactor, child in coupled_rows.items():
        factorization = prime_factorization(cofactor)
        if sum(exponent for _, exponent in factorization) < 2:
            continue
        largest_prime = max(prime for prime, _ in factorization)
        parent_cofactor = cofactor // largest_prime
        parent = coupled_rows[parent_cofactor]
        coupled_factor_edges.append(
            {
                "cofactor": cofactor,
                "largest_prime_removed": largest_prime,
                "parent_cofactor": parent_cofactor,
                "child_balance": child["balance"],
                "parent_balance": parent["balance"],
                "difference": child["balance"] - parent["balance"],
            }
        )

    coupled_factor_violations = [
        edge for edge in coupled_factor_edges if edge["difference"] < 0
    ]
    coupled_factor_violations_away_from_16 = [
        edge for edge in coupled_factor_violations if edge["cofactor"] != 16
    ]
    prime_boundary_rows = [
        row
        for cofactor, row in coupled_rows.items()
        if cofactor == 1
        or sum(
            exponent
            for _, exponent in prime_factorization(cofactor)
        ) == 1
    ]
    # For a prime p>5, supportCoeff(A,p*c) splits into the old c-column and
    # the p-pullback column.  Inclusion-exclusion cancels the duplicated
    # 16p contribution against g(8p), leaving one literal finite set
    # C=Div(120) union {16,48,80}.  Test that exact identity, and then the
    # phase-sensitive p mod 6 strengthening suggested by the tight rows.
    prime_coefficient_set = sorted(set(positive_divisors(120)) | {16, 48, 80})
    fixed_selected_columns = [
        column for column in prime_coefficient_set if bits[column]
    ]
    base_column_constant = (
        coupled_rows[1]["payment"] - top_two_adic_layer_load(8)
    )
    prime_column_rows: list[dict[str, Any]] = []
    for cofactor, row in coupled_rows.items():
        factorization = prime_factorization(cofactor)
        if cofactor <= 5 or factorization != [[cofactor, 1]]:
            continue
        scaled_word = [
            column
            for column in prime_coefficient_set
            if bits[column * cofactor]
        ]
        previous_defect = int(orbit.defects[240 * cofactor - 1])
        predicted_balance = (
            base_column_constant + len(scaled_word) - previous_defect
        )
        prime_column_rows.append(
            {
                "prime": cofactor,
                "prime_mod_6": cofactor % 6,
                "previous_defect": previous_defect,
                "scaled_column_load": len(scaled_word),
                "scaled_column_word": scaled_word,
                "coupled_balance": row["balance"],
                "predicted_balance": predicted_balance,
                "identity_holds": row["balance"] == predicted_balance,
            }
        )
    prime_column_failures = [
        row for row in prime_column_rows if not row["identity_holds"]
    ]
    prime_column_phase_rows = {
        residue: [
            row for row in prime_column_rows if row["prime_mod_6"] == residue
        ]
        for residue in (1, 5)
    }
    prime_column_normal_form = {
        "status": "exact_identity_and_named_phase_candidate_survive_finite_discrimination",
        "coefficient_set": prime_coefficient_set,
        "coefficient_set_description": "Div(120) union {16,48,80}",
        "coefficient_set_cardinality": len(prime_coefficient_set),
        "fixed_selected_columns": fixed_selected_columns,
        "base_column_constant": base_column_constant,
        "identity": (
            "for prime p>5, P(p)-D(p)=7+|{c in C:c*p in A}|-Q_(240*p-1)"
        ),
        "identity_check_count": len(prime_column_rows),
        "identity_failure_count": len(prime_column_failures),
        "identity_failures": prime_column_failures,
        "boundary_equality_rows": [
            row for row in prime_column_rows if row["coupled_balance"] == 2
        ],
        "mod_6_candidate": {
            "statement": (
                "Q_(240*p-1)<=columnLoad(p)+5 for p=1 mod 6, and "
                "Q_(240*p-1)<=columnLoad(p)+4 for p=5 mod 6"
            ),
            "classes": {
                str(residue): {
                    "row_count": len(rows),
                    "minimum_balance": min(
                        row["coupled_balance"] for row in rows
                    ),
                    "violation_count": sum(
                        row["coupled_balance"] < (2 if residue == 1 else 3)
                        for row in rows
                    ),
                    "equality_count": sum(
                        row["coupled_balance"] == (2 if residue == 1 else 3)
                        for row in rows
                    ),
                    "tightest_rows": sorted(
                        rows,
                        key=lambda row: (
                            row["coupled_balance"], row["prime"]
                        ),
                    )[:20],
                }
                for residue, rows in prime_column_phase_rows.items()
            },
        },
        "consequence": (
            "The Lean prime-boundary equivalence removes every moving "
            "payment term except this fixed 19-column pullback.  The "
            "remaining all-prime problem is a defect-versus-selected-column "
            "inequality, with an observed extra unit on p=5 mod 6."
        ),
    }
    coupled_factor_descent = {
        "status": "survives_exact_finite_discrimination",
        "payment": "P(m)=f(120m)+g(40m)+g(24m)",
        "debt": "D(m)=Q_(240m-1)+g(8m)",
        "target": "D(m)+2<=P(m), exactly equivalent to PU240+ by DL240",
        "deterministic_descent_statement": (
            "for composite m!=16, deleting the largest prime factor does "
            "not decrease P(m)-D(m)"
        ),
        "row_count": len(coupled_rows),
        "factor_descent_edge_count": len(coupled_factor_edges),
        "violation_count": len(coupled_factor_violations),
        "violation_count_away_from_16":
            len(coupled_factor_violations_away_from_16),
        "violations": coupled_factor_violations,
        "minimum_difference_away_from_16": min(
            edge["difference"]
            for edge in coupled_factor_edges
            if edge["cofactor"] != 16
        ),
        "tightest_edges_away_from_16": sorted(
            (
                edge for edge in coupled_factor_edges
                if edge["cofactor"] != 16
            ),
            key=lambda edge: (
                edge["difference"],
                edge["cofactor"],
            ),
        )[:20],
        "exception_16": coupled_rows[16],
        "prime_or_unit_boundary_count": len(prime_boundary_rows),
        "prime_or_unit_minimum_balance": min(
            row["balance"] for row in prime_boundary_rows
        ),
        "prime_or_unit_equality_rows": [
            row for row in prime_boundary_rows if row["balance"] == 2
        ],
        "all_row_minimum_balance": min(
            row["balance"] for row in coupled_rows.values()
        ),
        "prime_column_normal_form": prime_column_normal_form,
        "consequence": (
            "The Lean strong-induction consumer reduces PU240+ to the "
            "coupled proper-divisor descent and the unit/16/prime boundary. "
            "Finite survival does not prove either all-depth premise."
        ),
    }

    def candidate_summary(
        rows: list[tuple[int, int]], statement: str
    ) -> dict[str, Any]:
        return {
            "row_count": len(rows),
            "violation_count": sum(margin < 0 for _, margin in rows),
            "equality_count": sum(margin == 0 for _, margin in rows),
            "minimum_margin": min(margin for _, margin in rows),
            "tightest_rows": sorted(rows, key=lambda row: row[1])[:20],
            "statement": statement,
        }
    return {
        "ranks": ranks,
        "strict_record_count": len(records),
        "strict_record_ranks": records,
        "mature_record_successor_mod_4": dict(
            sorted(Counter((rank + 1) % 4 for rank in mature).items())
        ),
        "mature_phase_violation_count": sum(
            (rank + 1) % 4 != 0 for rank in mature
        ),
        "nonrecord_count": ranks - len(records),
        "longest_consecutive_record_run": longest_consecutive_run(records),
        "last_record_rank": records[-1],
        "one_step_repairs": {
            "count": len(repairs),
            "maximum_gap": max(repair_gaps),
            "last_repair": repairs[-1],
        },
        "multiple_120_repair_candidate": candidate_summary(
            multiple_120_rows,
            "f(120*k) >= Q_(120*k-1) + t_(120*k)",
        ),
        "multiple_120_proper_load_candidate": candidate_summary(
            multiple_120_proper_rows,
            "sum_(d|120*k,d<120*k) b_d >= Q_(120*k-1)+1",
        ),
        "multiple_120_primorial_union_candidate": candidate_summary(
            multiple_120_primorial_rows,
            "U_30(120*k) >= Q_(120*k-1)+1, where U_30(n) counts "
            "selected d dividing at least one of n/2,n/3,n/5",
        ),
        "multiple_240_primorial_unit_slack_candidate": candidate_summary(
            multiple_240_primorial_rows,
            "U_30(240*k) >= Q_(240*k-1)+2; this cofinal doubled-row "
            "producer alone would imply 1/21 membership",
        ),
        "multiple_120_primorial_cofactor_classes": {
            cofactor_class: candidate_summary(
                rows,
                "U_30(120*k)-Q_(120*k-1)-1 grouped by whether k is "
                f"{cofactor_class}",
            )
            for cofactor_class, rows in cofactor_class_rows.items()
        },
        "multiple_120_primorial_equality_anatomy": primorial_equality_anatomy,
        "multiple_120_primorial_factor_descent_falsifier":
            factor_descent_falsifier,
        "multiple_240_coupled_factor_descent_candidate":
            coupled_factor_descent,
    }


def unbounded_defect_orbit(
    bits: bytearray,
    digits: bytearray,
    ranks: int,
) -> tuple[list[int], list[int], list[int]]:
    """Reconstruct using Python integers so fatal exponential escape cannot overflow."""

    loads = [0] * (ranks + 1)
    for divisor in range(1, ranks + 1):
        if bits[divisor]:
            for multiple in range(divisor, ranks + 1, divisor):
                loads[multiple] += 1
    defects = [0] * (ranks + 1)
    records: list[int] = []
    maximum = 0
    for rank in range(1, ranks + 1):
        defects[rank] = (
            2 * defects[rank - 1] + digits[rank] - loads[rank]
        )
        if defects[rank] < 0:
            raise AssertionError("negative reconstructed defect")
        if defects[rank] > maximum:
            maximum = defects[rank]
            records.append(rank)
    return loads, defects, records


def gap_splice_summary(death_rank: int, depth_multiplier: int) -> dict[str, Any]:
    depth = death_rank * depth_multiplier
    canonical = load_canonical_bits(death_rank - 1)
    prefix = sum(
        (
            Fraction(1, (1 << rank) - 1)
            for rank in range(1, death_rank)
            if canonical[rank]
        ),
        Fraction(),
    )
    death_coin = Fraction(1, (1 << death_rank) - 1)
    upper = tail_upper_bound(death_rank)
    if not upper < death_coin:
        raise AssertionError("tail upper bound did not expose a strict gap")
    gap_residual = (upper + death_coin) / 2
    target = prefix + gap_residual

    bits = bytearray(depth + 1)
    residual = target
    for rank in range(1, depth + 1):
        coin = Fraction(1, (1 << rank) - 1)
        if residual >= coin:
            bits[rank] = 1
            residual -= coin
    if any(bits[rank] != canonical[rank] for rank in range(1, death_rank)):
        raise AssertionError("canonical prefix was not preserved")
    if bits[death_rank] != 0:
        raise AssertionError("prescribed fatal rank was not skipped")
    if any(bits[rank] != 1 for rank in range(death_rank + 1, depth + 1)):
        raise AssertionError("gap did not force an all-take tail")

    loads, defects, records = unbounded_defect_orbit(
        bits,
        target_digits(target.numerator, target.denominator, depth),
        depth,
    )
    record_set = set(records)
    suffix_start = depth + 1
    while suffix_start > 1 and suffix_start - 1 in record_set:
        suffix_start -= 1
    if suffix_start <= death_rank:
        raise AssertionError("terminal record suffix did not begin after the gap")
    if any(defects[n] <= defects[n - 1] for n in range(suffix_start, depth + 1)):
        raise AssertionError("terminal record suffix lost strict one-step growth")
    phase_violations = [
        rank
        for rank in records
        if rank >= death_rank and (rank + 1) % 4 != 0
    ]
    primorial_rows: list[tuple[int, int]] = []
    for rank in range(120, depth + 1, 120):
        primorial_union_load = (
            loads[rank // 2]
            + loads[rank // 3]
            + loads[rank // 5]
            - loads[rank // 6]
            - loads[rank // 10]
            - loads[rank // 15]
            + loads[rank // 30]
        )
        primorial_rows.append(
            (rank, primorial_union_load - defects[rank - 1] - 1)
        )
    primorial_failures = [row for row in primorial_rows if row[1] < 0]
    return {
        "death_rank": death_rank,
        "depth": depth,
        "canonical_prefix_preserved_through": death_rank - 1,
        "fatal_skip_bit": bits[death_rank],
        "all_later_bits_are_one": True,
        "first_post_gap_record": next(rank for rank in records if rank >= death_rank),
        "first_mod_four_phase_violation": phase_violations[0],
        "post_gap_phase_violation_count": len(phase_violations),
        "terminal_every_rank_record_suffix_start": suffix_start,
        "terminal_record_suffix_length": depth - suffix_start + 1,
        "multiple_120_primorial_union": {
            "row_count": len(primorial_rows),
            "first_failure": primorial_failures[0] if primorial_failures else None,
            "failure_count": len(primorial_failures),
            "predeath_failure_count": sum(
                rank < death_rank for rank, _ in primorial_failures
            ),
        },
        "defect_at_suffix_start_bit_length": defects[suffix_start].bit_length(),
        "maximum_load_on_terminal_suffix": max(loads[suffix_start:]),
        "gap_certificate": {
            "tail_upper_below_death_coin": upper < death_coin,
            "gap_residual_above_tail_upper": gap_residual > upper,
            "gap_residual_below_death_coin": gap_residual < death_coin,
        },
    }


def anchor_universality_countermodel() -> dict[str, Any]:
    """Exact proof data killing an anchor-only explanation of M120R."""

    n = 1_962_960
    successor = n + 1
    divisors = [d for d in range(1, successor + 1) if successor % d == 0]
    anchors = {5, 8, 10, 20, 24, 60}
    nontrivial = set(divisors) - {1}
    if len(divisors) != 32 or min(nontrivial) != 7:
        raise AssertionError("countermodel factorization drifted")
    if any(n % anchor for anchor in anchors):
        raise AssertionError("anchor stopped dividing the M120 row")
    if any(n % d == 0 for d in nontrivial):
        raise AssertionError("successor divisor unexpectedly divided its predecessor")
    target_upper = Fraction(6, 31) + Fraction(31, 127)
    c_lower = Fraction(6, 2) + Fraction(31, 4)
    return {
        "row": n,
        "successor": successor,
        "successor_factorization": "7*11*13*37*53",
        "successor_divisor_count": len(divisors),
        "support": (
            "the six anchors {5,8,10,20,24,60} together with every "
            "nontrivial divisor of 1962961"
        ),
        "support_size": len(anchors | nontrivial),
        "target_is_below_one": target_upper < 1,
        "target_upper_bound": str(target_upper),
        "load_at_row": 6,
        "predecessor_tail_coordinate_strict_lower_bound": str(c_lower),
        "predecessor_defect_lower_bound": 10,
        "repair_margin_upper_bound": -4,
        "consequence": (
            "Containing the six anchor exponents does not imply M120R. "
            "A proof for 1/21 must use source-reachable prefix/boundary "
            "ancestry, not the anchors or a support-independent divisor law."
        ),
    }


def build_receipt(args: argparse.Namespace) -> dict[str, Any]:
    return {
        "schema": "erdos257_record_cofiniteness_boundary_v1",
        "analysis_ref": ANALYSIS_REF,
        "claim_status": "exact finite discrimination plus analytic theorem selector",
        "canonical_twenty_one": canonical_summary(args.canonical_ranks),
        "exact_fatal_gap_splices": [
            gap_splice_summary(death, args.depth_multiplier)
            for death in args.fatal_death
        ],
        "exact_algebra": {
            "unconditional_m120_equivalence": (
                "Q_n=2*Q_(n-1)+t_n-f(n), so for n=120*k, "
                "M120R is equivalent to Q_n <= Q_(n-1)"
            ),
            "phase_free_primorial_form": (
                "at n=120*k the U_30 target-digit pulse equals t_n=1; "
                "therefore U_30(n)>=Q_(n-1)+1 is equivalent to "
                "2*J^-(n)-J(n)>=Q_(n-1), where J is the seven-scale "
                "inclusion-exclusion operator on Q"
            ),
            "future_tail_coordinate": (
                "conditional on sum_A 1/(2^d-1)=x: "
                "Q_(n-1)=floor(sum_(r>=0) f(n+r)/2^(r+1))"
            ),
            "conditional_future_column_equivalence": (
                "if the support already represents 1/21, then for n=120*k "
                "M120R is equivalent to sum_(r>=1) f(n+r)/2^r < f(n)"
            ),
            "conditional_margin_quantization": (
                "under the same representation hypothesis, if "
                "m=f(n)-Q_(n-1)-1, then "
                "f(n)-sum_(r>=1)f(n+r)/2^r = 2*m+20/21"
            ),
            "circularity_guard": (
                "future-column dominance cannot prove membership because the "
                "identification of Q with the support tail already assumes it"
            ),
        },
        "anchor_universality_countermodel": anchor_universality_countermodel(),
        "analytic_boundary": {
            "proved_on_paper": (
                "A final skip gives a positive limiting residual delta. "
                "The exact defect decomposition yields Q_n/2^n -> delta. "
                "Since f(n)<=n, eventually Q_(n-1)>f(n)-t_n, so Q_n>Q_(n-1); "
                "after surpassing the finite earlier maximum, every rank is strict."
            ),
            "consequence": (
                "Any cofinal supply of non-record ranks excludes the fatal branch. "
                "FAPL4 is sufficient but much stronger than necessary."
            ),
        },
        "not_claimed": [
            "an all-depth cofinal non-record producer for 1/21",
            "membership of 1/21 in the Mersenne achievement set",
            "a proof or disproof of Erdos problem 257",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--canonical-ranks", type=int, default=200_000)
    parser.add_argument("--fatal-death", type=int, action="append")
    parser.add_argument("--depth-multiplier", type=int, default=5)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.fatal_death is None:
        args.fatal_death = [40, 80, 140, 200]
    receipt = build_receipt(args)
    rendered = canonical_json(receipt)
    if args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
