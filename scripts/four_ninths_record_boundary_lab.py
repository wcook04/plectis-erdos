#!/usr/bin/env python3
"""Probe a cofinal non-record producer for the exact 4/9 greedy word.

The finite word is obtained from the existing exact even-cylinder recurrence,
not from floating point.  Computation selects and falsifies conjectures; the
all-depth three-scale inequality recorded by this lab remains unproved.
"""

from __future__ import annotations

import argparse
from array import array
from collections import Counter
import heapq
import json
from pathlib import Path
import sys
from typing import Any

from totient_four_ninths_even_cylinder_audit import (
    full_prefix_dp,
    initialize_cylinder,
    raw_carry,
    target_bit,
)


ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/"
    "FourNinthsRecordCofinitenessBoundary.md"
)


def canonical_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def certified_common_prefix(ranks: int) -> tuple[bytearray, array, dict[str, int]]:
    """Return the cylinder-forced prefix and its selected proper-divisor loads."""

    if ranks < 12:
        raise ValueError("ranks must be at least 12")
    horizon = 2 * ranks + 2
    snapshots = full_prefix_dp(6)
    prefix_word, prefix_length, suffix_length, suffix_top = initialize_cylinder(
        snapshots
    )
    fixed = bytearray(horizon + 3)
    proper_load = array("H", [0]) * (horizon + 3)

    def fix_rank(rank: int, bit: int) -> None:
        fixed[rank] = bit
        if bit:
            for multiple in range(2 * rank, horizon + 3, rank):
                proper_load[multiple] += 1

    for rank in range(1, prefix_length + 1):
        fix_rank(rank, (prefix_word >> (rank - 1)) & 1)

    even_horizon = 6
    while prefix_length < ranks:
        n = even_horizon
        carry = raw_carry(n)
        t1, t2 = target_bit(n + 1), target_bit(n + 2)
        g1, g2 = proper_load[n + 1], proper_load[n + 2]
        shift = 2 * (t1 - g1) + (t2 - g2)

        parent = max(0, (-shift + 3) // 4)
        digit = 4 * parent + shift
        if not 0 <= digit <= 3:
            raise AssertionError("endpoint-zero base-four digit escaped")
        next_top = 4 * suffix_top + shift
        next_width = suffix_length + 2
        next_carry = raw_carry(n + 2)
        if not 0 <= next_top - next_carry <= next_top < 1 << next_width:
            raise AssertionError("cylinder interval escaped its binary width")

        difference = next_top ^ (next_top - next_carry)
        common = next_width - (difference.bit_length() if difference else 0)
        for index in range(common):
            bit = (next_top >> (next_width - 1 - index)) & 1
            prefix_length += 1
            fix_rank(prefix_length, bit)
        suffix_length = next_width - common
        suffix_top = next_top & (
            (1 << suffix_length) - 1 if suffix_length else 0
        )
        even_horizon = n + 2
        if prefix_length < even_horizon // 2 + 1:
            raise AssertionError("first midpoint seam")
        if even_horizon > horizon:
            raise AssertionError("doubling horizon failed to force requested prefix")

    expected = bytearray(int(bit) for bit in "010110110001")
    if fixed[1:13] != expected:
        raise AssertionError("forced prefix disagrees with the Lean-checked seed")
    return (
        fixed[: ranks + 1],
        proper_load[: ranks + 1],
        {
            "requested_ranks": ranks,
            "cylinder_even_horizon": even_horizon,
            "forced_prefix_length": prefix_length,
            "unresolved_suffix_width": suffix_length,
        },
    )


def fixed_point_crosscheck(bits: bytearray, ranks: int) -> dict[str, Any]:
    """Independently compare a bounded prefix with the certified real greedy."""

    if ranks == 0:
        return {"ranks": 0, "status": "not_requested"}
    from cantor_staircase_run_length_lab import Engine

    result = Engine(ranks).run(4, 9)
    if result["status"] != "alive":
        raise AssertionError(f"fixed-point crosscheck status {result['status']}")
    mismatches = [
        rank
        for rank, bit in enumerate(result["word"], start=1)
        if bits[rank] != bit
    ]
    if mismatches:
        raise AssertionError(f"cylinder/real-greedy mismatch at {mismatches[0]}")
    return {
        "ranks": ranks,
        "status": "exact_agreement",
        "mismatch_count": 0,
    }


def prime_sieve(limit: int) -> bytearray:
    """Return the exact primality table through ``limit``."""

    sieve = bytearray(b"\x01") * (limit + 1)
    if limit >= 0:
        sieve[0] = 0
    if limit >= 1:
        sieve[1] = 0
    for prime in range(2, int(limit**0.5) + 1):
        if sieve[prime]:
            start = prime * prime
            sieve[start : limit + 1 : prime] = b"\x00" * (
                (limit - start) // prime + 1
            )
    return sieve


def largest_prime_factor_sieve(limit: int) -> array:
    factors = array("I", [0]) * (limit + 1)
    for prime in range(2, limit + 1):
        if factors[prime] != 0:
            continue
        for multiple in range(prime, limit + 1, prime):
            factors[multiple] = prime
    return factors


def divisors(number: int) -> list[int]:
    small: list[int] = []
    large: list[int] = []
    candidate = 1
    while candidate * candidate <= number:
        if number % candidate == 0:
            small.append(candidate)
            if candidate * candidate != number:
                large.append(number // candidate)
        candidate += 1
    return small + list(reversed(large))


def prime_cofactor_column_summary(
    bits: bytearray, defects: array, ranks: int
) -> dict[str, Any]:
    """Resolve the moving prime pullback column in the Lean normal form."""

    column_divisors = sorted(set(divisors(60) + divisors(40) + divisors(24)))
    if len(column_divisors) != 15:
        raise AssertionError("unexpected prime pullback column width")
    primality = prime_sieve(ranks // 120)
    rows: list[dict[str, Any]] = []
    margin_histogram: Counter[int] = Counter()
    signature_histogram: Counter[str] = Counter()
    for prime in range(7, len(primality)):
        if not primality[prime]:
            continue
        rank = 120 * prime
        signature = "".join(str(bits[prime * divisor]) for divisor in column_divisors)
        column_load = signature.count("1")
        defect = int(defects[rank - 1])
        margin = column_load + 10 - defect
        margin_histogram[margin] += 1
        signature_histogram[signature] += 1
        rows.append(
            {
                "rank": rank,
                "prime": prime,
                "prime_mod_120": prime % 120,
                "defect_before": defect,
                "pullback_column_load": column_load,
                "margin": margin,
                "signature": signature,
                "selected_divisors": [
                    divisor
                    for digit, divisor in zip(signature, column_divisors)
                    if digit == "1"
                ],
            }
        )
    return {
        "statement": "Q_(120*p-1) <= PullbackColumn(p)+10 for prime p>5",
        "column_divisors": column_divisors,
        "row_count": len(rows),
        "violation_count": sum(row["margin"] < 0 for row in rows),
        "equality_count": sum(row["margin"] == 0 for row in rows),
        "minimum_margin": min((row["margin"] for row in rows), default=None),
        "maximum_defect_before": max(
            (row["defect_before"] for row in rows), default=None
        ),
        "maximum_pullback_column_load": max(
            (row["pullback_column_load"] for row in rows), default=None
        ),
        "phase_mod_6": {
            str(residue): {
                "row_count": sum(row["prime"] % 6 == residue for row in rows),
                "minimum_margin": min(
                    (
                        row["margin"]
                        for row in rows
                        if row["prime"] % 6 == residue
                    ),
                    default=None,
                ),
                "equality_count": sum(
                    row["prime"] % 6 == residue and row["margin"] == 0
                    for row in rows
                ),
            }
            for residue in (1, 5)
        },
        "margin_histogram": {
            str(margin): count for margin, count in sorted(margin_histogram.items())
        },
        "distinct_signature_count": len(signature_histogram),
        "most_common_signatures": [
            {"signature": signature, "count": count}
            for signature, count in signature_histogram.most_common(20)
        ],
        "tightest_rows": sorted(rows, key=lambda row: (row["margin"], row["rank"]))[:50],
    }


def heptadic_prime_cofactor_column_summary(
    bits: bytearray, defects: array, ranks: int
) -> dict[str, Any]:
    """Resolve the moving prime pullback column for the modulus-84 producer."""

    column_divisors = sorted(set(divisors(42) + divisors(28) + divisors(12)))
    if len(column_divisors) != 11:
        raise AssertionError("unexpected heptadic prime pullback column width")
    base_load = sum(bits[divisor] for divisor in column_divisors)
    if base_load != 6:
        raise AssertionError("unexpected modulus-84 base union load")
    primality = prime_sieve(ranks // 84)
    rows: list[dict[str, Any]] = []
    margin_histogram: Counter[int] = Counter()
    signature_histogram: Counter[str] = Counter()
    for prime in range(11, len(primality)):
        if not primality[prime]:
            continue
        rank = 84 * prime
        signature = "".join(str(bits[prime * divisor]) for divisor in column_divisors)
        column_load = signature.count("1")
        defect = int(defects[rank - 1])
        margin = column_load + base_load - defect
        margin_histogram[margin] += 1
        signature_histogram[signature] += 1
        rows.append(
            {
                "rank": rank,
                "prime": prime,
                "prime_mod_84": prime % 84,
                "defect_before": defect,
                "pullback_column_load": column_load,
                "margin": margin,
                "signature": signature,
                "selected_divisors": [
                    divisor
                    for digit, divisor in zip(signature, column_divisors)
                    if digit == "1"
                ],
            }
        )
    return {
        "statement": "Q_(84*p-1) <= PullbackColumn84(p)+6 for prime p>7",
        "base_union_load": base_load,
        "column_divisors": column_divisors,
        "row_count": len(rows),
        "violation_count": sum(row["margin"] < 0 for row in rows),
        "equality_count": sum(row["margin"] == 0 for row in rows),
        "minimum_margin": min((row["margin"] for row in rows), default=None),
        "maximum_defect_before": max(
            (row["defect_before"] for row in rows), default=None
        ),
        "maximum_pullback_column_load": max(
            (row["pullback_column_load"] for row in rows), default=None
        ),
        "margin_histogram": {
            str(margin): count for margin, count in sorted(margin_histogram.items())
        },
        "distinct_signature_count": len(signature_histogram),
        "most_common_signatures": [
            {"signature": signature, "count": count}
            for signature, count in signature_histogram.most_common(20)
        ],
        "tightest_rows": sorted(rows, key=lambda row: (row["margin"], row["rank"]))[:50],
    }


def tetraprime_prime_cofactor_column_summary(
    bits: bytearray, defects: array, ranks: int
) -> dict[str, Any]:
    """Resolve the moving prime pullback column for the modulus-420 producer."""

    column_divisors = sorted(
        set(divisors(210) + divisors(140) + divisors(84) + divisors(60))
    )
    if len(column_divisors) != 23:
        raise AssertionError("unexpected tetraprime pullback column width")
    base_load = sum(bits[divisor] for divisor in column_divisors)
    if base_load != 12:
        raise AssertionError("unexpected modulus-420 base union load")
    primality = prime_sieve(ranks // 420)
    rows: list[dict[str, Any]] = []
    margin_histogram: Counter[int] = Counter()
    signature_histogram: Counter[str] = Counter()
    for prime in range(11, len(primality)):
        if not primality[prime]:
            continue
        rank = 420 * prime
        signature = "".join(str(bits[prime * divisor]) for divisor in column_divisors)
        column_load = signature.count("1")
        defect = int(defects[rank - 1])
        margin = column_load + base_load - defect
        margin_histogram[margin] += 1
        signature_histogram[signature] += 1
        rows.append(
            {
                "rank": rank,
                "prime": prime,
                "prime_mod_420": prime % 420,
                "defect_before": defect,
                "pullback_column_load": column_load,
                "margin": margin,
                "signature": signature,
                "selected_divisors": [
                    divisor
                    for digit, divisor in zip(signature, column_divisors)
                    if digit == "1"
                ],
            }
        )
    return {
        "statement": "Q_(420*p-1) <= PullbackColumn420(p)+12 for prime p>7",
        "base_union_load": base_load,
        "column_divisors": column_divisors,
        "row_count": len(rows),
        "violation_count": sum(row["margin"] < 0 for row in rows),
        "equality_count": sum(row["margin"] == 0 for row in rows),
        "minimum_margin": min((row["margin"] for row in rows), default=None),
        "maximum_defect_before": max(
            (row["defect_before"] for row in rows), default=None
        ),
        "maximum_pullback_column_load": max(
            (row["pullback_column_load"] for row in rows), default=None
        ),
        "margin_histogram": {
            str(margin): count for margin, count in sorted(margin_histogram.items())
        },
        "distinct_signature_count": len(signature_histogram),
        "most_common_signatures": [
            {"signature": signature, "count": count}
            for signature, count in signature_histogram.most_common(20)
        ],
        "tightest_rows": sorted(rows, key=lambda row: (row["margin"], row["rank"]))[:50],
    }


def factor_descent_summary(
    rows: list[tuple[int, int]],
    modulus: int = 120,
    bits: bytearray | None = None,
    defects: array | None = None,
) -> dict[str, Any]:
    """Test descent after deleting the largest prime factor of the cofactor."""

    margins = {rank // modulus: margin for rank, margin in rows}
    cofactor_limit = max(margins)
    largest_prime_factor = largest_prime_factor_sieve(cofactor_limit)
    edges: list[dict[str, int]] = []
    for cofactor, child_margin in margins.items():
        if cofactor <= 1:
            continue
        prime = int(largest_prime_factor[cofactor])
        parent = cofactor // prime
        if parent == 1 or prime == cofactor:
            continue
        difference = child_margin - margins[parent]
        edges.append(
            {
                "cofactor": cofactor,
                "largest_prime_removed": prime,
                "parent_cofactor": parent,
                "child_margin": child_margin,
                "parent_margin": margins[parent],
                "difference": difference,
            }
        )
    best_parent_margin = array("i", [2**31 - 1]) * (cofactor_limit + 1)
    best_parent = array("I", [0]) * (cofactor_limit + 1)
    for parent, parent_margin in margins.items():
        for child in range(2 * parent, cofactor_limit + 1, parent):
            if parent_margin < best_parent_margin[child]:
                best_parent_margin[child] = parent_margin
                best_parent[child] = parent
    existential_rows: list[dict[str, int]] = []
    for cofactor, child_margin in margins.items():
        if cofactor <= 1 or largest_prime_factor[cofactor] == cofactor:
            continue
        difference = child_margin - int(best_parent_margin[cofactor])
        existential_rows.append(
            {
                "cofactor": cofactor,
                "best_parent_cofactor": int(best_parent[cofactor]),
                "child_margin": child_margin,
                "best_parent_margin": int(best_parent_margin[cofactor]),
                "difference": difference,
            }
        )
    return {
        "statement": (
            f"M(k)>=M(k/lpf(k)) for composite k, "
            f"M=U({modulus}*k)-Q_({modulus}*k-1)"
        ),
        "edge_count": len(edges),
        "violation_count": sum(edge["difference"] < 0 for edge in edges),
        "minimum_difference": min(edge["difference"] for edge in edges),
        "first_violations": [
            edge for edge in edges if edge["difference"] < 0
        ][:50],
        "tightest_edges": sorted(
            edges, key=lambda edge: (edge["difference"], edge["cofactor"])
        )[:50],
        "composite_margin_census": {
            "row_count": len(existential_rows),
            "minimum_margin": min(row["child_margin"] for row in existential_rows),
            "margin_histogram": {
                str(margin): count
                for margin, count in sorted(
                    Counter(row["child_margin"] for row in existential_rows).items()
                )
            },
            "tightest_rows": sorted(
                existential_rows,
                key=lambda row: (row["child_margin"], row["cofactor"]),
            )[:50],
        },
        "existential_proper_divisor_descent": {
            "statement": "every composite k has a proper divisor a with M(a)<=M(k)",
            "edge_count": len(existential_rows),
            "violation_count": sum(
                row["difference"] < 0 for row in existential_rows
            ),
            "minimum_difference": min(
                row["difference"] for row in existential_rows
            ),
            "first_violations": [
                row for row in existential_rows if row["difference"] < 0
            ][:50],
            "tightest_rows": sorted(
                existential_rows,
                key=lambda row: (row["difference"], row["cofactor"]),
            )[:50],
        },
        "composite_margin_at_least_five": {
            "statement": "M(k)>=5 for every composite k",
            "row_count": len(existential_rows),
            "violation_count": sum(
                row["child_margin"] < 5 for row in existential_rows
            ),
            "minimum_margin": min(
                row["child_margin"] for row in existential_rows
            ),
        },
        "all_prime_factor_deletions": all_prime_factor_deletion_summary(
            margins,
            largest_prime_factor,
            modulus=modulus,
            bits=bits,
            defects=defects,
        ),
    }


def all_prime_factor_deletion_summary(
    margins: dict[int, int],
    largest_prime_factor: array,
    modulus: int = 120,
    bits: bytearray | None = None,
    defects: array | None = None,
) -> dict[str, Any]:
    """Test every distinct prime-factor deletion, not only the largest one."""

    edges: list[dict[str, int | str]] = []
    for cofactor, child_margin in margins.items():
        if cofactor <= 1 or largest_prime_factor[cofactor] == cofactor:
            continue
        remaining = cofactor
        factors: list[int] = []
        while remaining > 1:
            prime = int(largest_prime_factor[remaining])
            factors.append(prime)
            while remaining % prime == 0:
                remaining //= prime
        factors.sort()
        for index, prime in enumerate(factors):
            parent = cofactor // prime
            difference = child_margin - margins[parent]
            position = (
                "only" if len(factors) == 1 else
                "smallest" if index == 0 else
                "largest" if index + 1 == len(factors) else
                "interior"
            )
            edges.append(
                {
                    "cofactor": cofactor,
                    "removed_prime": prime,
                    "factor_position": position,
                    "parent_cofactor": parent,
                    "child_margin": child_margin,
                    "parent_margin": margins[parent],
                    "difference": difference,
                }
            )
    violations = [edge for edge in edges if edge["difference"] < 0]
    if modulus == 420 and bits is not None and defects is not None:
        def selected_tetraprime_union(rank: int) -> set[int]:
            return {
                divisor
                for prime in (2, 3, 5, 7)
                for divisor in divisors(rank // prime)
                if bits[divisor]
            }

        for edge in violations:
            child_rank = modulus * int(edge["cofactor"])
            parent_rank = modulus * int(edge["parent_cofactor"])
            child_union = selected_tetraprime_union(child_rank)
            parent_union = selected_tetraprime_union(parent_rank)
            edge.update(
                {
                    "child_union_load": len(child_union),
                    "parent_union_load": len(parent_union),
                    "union_load_difference": len(child_union) - len(parent_union),
                    "child_defect_before": int(defects[child_rank - 1]),
                    "parent_defect_before": int(defects[parent_rank - 1]),
                    "defect_difference": int(defects[child_rank - 1])
                    - int(defects[parent_rank - 1]),
                    "selected_union_added": sorted(child_union - parent_union),
                    "selected_union_removed": sorted(parent_union - child_union),
                }
            )
    by_position: dict[str, dict[str, Any]] = {}
    for position in ("only", "smallest", "interior", "largest"):
        position_edges = [
            edge for edge in edges if edge["factor_position"] == position
        ]
        by_position[position] = {
            "edge_count": len(position_edges),
            "violation_count": sum(
                edge["difference"] < 0 for edge in position_edges
            ),
            "minimum_difference": min(
                (edge["difference"] for edge in position_edges), default=None
            ),
            "first_violations": [
                edge for edge in position_edges if edge["difference"] < 0
            ][:30],
        }
    return {
        "statement": "M(k)>=M(k/q) for every distinct prime q dividing k",
        "edge_count": len(edges),
        "violation_count": sum(edge["difference"] < 0 for edge in edges),
        "minimum_difference": min(
            (edge["difference"] for edge in edges), default=None
        ),
        "by_removed_factor_position": by_position,
        "first_violations": violations[:50],
        "tightest_edges": sorted(
            edges,
            key=lambda edge: (edge["difference"], edge["cofactor"]),
        )[:50],
    }


def orbit_summary(ranks: int, crosscheck: int) -> dict[str, Any]:
    bits, proper_load, prefix_receipt = certified_common_prefix(ranks)
    loads = array("H", [0]) * (ranks + 1)
    defects = array("I", [0]) * (ranks + 1)
    records: list[int] = []
    maximum = 0
    repair_count = 0
    last_repair: int | None = None
    maximum_repair_gap = 0
    maximum_repair_gap_start: int | None = None
    repair_gap_histogram: Counter[int] = Counter()
    largest_repair_gaps: list[tuple[int, int, int]] = []
    largest_repair_loads: list[tuple[int, int, int, int]] = []
    for rank in range(1, ranks + 1):
        loads[rank] = proper_load[rank] + bits[rank]
        defect = (
            2 * defects[rank - 1] + target_bit(rank) - loads[rank]
        )
        if defect < 0:
            raise AssertionError(f"negative rational defect at rank {rank}")
        defects[rank] = defect
        if defect > maximum:
            maximum = defect
            records.append(rank)
        if defect <= defects[rank - 1]:
            repair_count += 1
            load_item = (
                int(loads[rank]), rank, int(defects[rank - 1]), defect
            )
            if len(largest_repair_loads) < 20:
                heapq.heappush(largest_repair_loads, load_item)
            elif load_item > largest_repair_loads[0]:
                heapq.heapreplace(largest_repair_loads, load_item)
            if last_repair is not None:
                gap = rank - last_repair
                repair_gap_histogram[gap] += 1
                if gap > maximum_repair_gap:
                    maximum_repair_gap = gap
                    maximum_repair_gap_start = last_repair
                item = (gap, last_repair, rank)
                if len(largest_repair_gaps) < 20:
                    heapq.heappush(largest_repair_gaps, item)
                elif item > largest_repair_gaps[0]:
                    heapq.heapreplace(largest_repair_gaps, item)
            last_repair = rank

    rows_120: list[tuple[int, int]] = []
    rows_420: list[tuple[int, int]] = []
    rows_84: list[tuple[int, int]] = []
    rows_60: list[tuple[int, int]] = []
    rows_48: list[tuple[int, int]] = []
    rows_24: list[tuple[int, int]] = []
    for modulus, rows in ((48, rows_48), (24, rows_24)):
        for rank in range(modulus, ranks + 1, modulus):
            union_load = (
                int(loads[rank // 2])
                + int(loads[rank // 3])
                - int(loads[rank // 6])
            )
            rows.append(
                (
                    rank,
                    union_load
                    - int(defects[rank - 1])
                    - target_bit(rank),
                )
            )
    for modulus, rows in ((120, rows_120), (60, rows_60)):
        for rank in range(modulus, ranks + 1, modulus):
            union_load = (
                int(loads[rank // 2])
                + int(loads[rank // 3])
                + int(loads[rank // 5])
                - int(loads[rank // 6])
                - int(loads[rank // 10])
                - int(loads[rank // 15])
                + int(loads[rank // 30])
            )
            rows.append(
                (
                    rank,
                    union_load
                    - int(defects[rank - 1])
                    - target_bit(rank),
                )
            )
    for rank in range(84, ranks + 1, 84):
        union_load = (
            int(loads[rank // 2])
            + int(loads[rank // 3])
            + int(loads[rank // 7])
            - int(loads[rank // 6])
            - int(loads[rank // 14])
            - int(loads[rank // 21])
            + int(loads[rank // 42])
        )
        rows_84.append(
            (
                rank,
                union_load
                - int(defects[rank - 1])
                - target_bit(rank),
            )
        )
    for rank in range(420, ranks + 1, 420):
        union_load = (
            sum(int(loads[rank // divisor]) for divisor in (2, 3, 5, 7))
            - sum(
                int(loads[rank // divisor])
                for divisor in (6, 10, 14, 15, 21, 35)
            )
            + sum(
                int(loads[rank // divisor])
                for divisor in (30, 42, 70, 105)
            )
            - int(loads[rank // 210])
        )
        rows_420.append(
            (
                rank,
                union_load
                - int(defects[rank - 1])
                - target_bit(rank),
            )
        )

    periodic_repair_census: dict[str, dict[str, Any]] = {}
    for modulus in (
        2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15,
        20, 21, 24, 28, 30, 35, 40, 42, 48, 56, 60, 70, 84,
        105, 120, 140, 168, 210, 280, 420, 840,
    ):
        violations: list[tuple[int, int]] = []
        row_count = 0
        minimum_margin: int | None = None
        for rank in range(modulus, ranks + 1, modulus):
            margin = int(defects[rank - 1]) - int(defects[rank])
            row_count += 1
            minimum_margin = (
                margin if minimum_margin is None else min(minimum_margin, margin)
            )
            if margin < 0 and len(violations) < 20:
                violations.append((rank, margin))
        periodic_repair_census[str(modulus)] = {
            "statement": f"Q_({modulus}*k)<=Q_({modulus}*k-1)",
            "row_count": row_count,
            "minimum_repair_margin": minimum_margin,
            "first_violations": violations,
            "zero_violations_in_audit": not violations,
        }
    def candidate(rows: list[tuple[int, int]], statement: str) -> dict[str, Any]:
        failures = [row for row in rows if row[1] < 0]
        return {
            "statement": statement,
            "row_count": len(rows),
            "violation_count": len(failures),
            "equality_count": sum(margin == 0 for _, margin in rows),
            "minimum_margin": min(margin for _, margin in rows),
            "first_violations": failures[:20],
            "tightest_rows": sorted(rows, key=lambda row: row[1])[:20],
        }

    return {
        "ranks": ranks,
        "prefix_authority": prefix_receipt,
        "fixed_point_crosscheck": fixed_point_crosscheck(
            bits, min(crosscheck, ranks)
        ),
        "support_size": sum(bits),
        "maximum_defect": maximum,
        "strict_record_count": len(records),
        "last_strict_record": records[-1],
        "one_step_repair_count": repair_count,
        "one_step_repair_density": repair_count / ranks,
        "last_one_step_repair": last_repair,
        "maximum_one_step_repair_gap": maximum_repair_gap,
        "maximum_one_step_repair_gap_start": maximum_repair_gap_start,
        "one_step_repair_gap_histogram": {
            str(gap): count
            for gap, count in sorted(repair_gap_histogram.items())
        },
        "largest_one_step_repair_gaps": [
            {"gap": gap, "start": start, "end": end}
            for gap, start, end in sorted(largest_repair_gaps, reverse=True)
        ],
        "largest_one_step_repair_gap_windows": [
            {
                "gap": gap,
                "start": start,
                "end": end,
                "end_divisor_count": len(divisors(end)),
                "end_selected_divisors": [
                    divisor for divisor in divisors(end) if bits[divisor]
                ],
                "rows": [
                    {
                        "rank": rank,
                        "target_bit": target_bit(rank),
                        "selected_bit": int(bits[rank]),
                        "divisor_load": int(loads[rank]),
                        "defect_before": int(defects[rank - 1]),
                        "defect_after": int(defects[rank]),
                        "is_repair": defects[rank] <= defects[rank - 1],
                    }
                    for rank in range(max(1, start - 2), min(ranks, end + 2) + 1)
                ],
            }
            for gap, start, end in sorted(largest_repair_gaps, reverse=True)
        ],
        "largest_one_step_repair_loads": [
            {
                "rank": rank,
                "divisor_load": load,
                "defect_before": defect_before,
                "defect_after": defect_after,
                "divisor_count": len(divisors(rank)),
                "selected_divisors": [
                    divisor for divisor in divisors(rank) if bits[divisor]
                ],
            }
            for load, rank, defect_before, defect_after in sorted(
                largest_repair_loads, reverse=True
            )
        ],
        "periodic_actual_repair_census": periodic_repair_census,
        "prime_cofactor_pullback_column": prime_cofactor_column_summary(
            bits, defects, ranks
        ),
        "heptadic_prime_cofactor_pullback_column":
            heptadic_prime_cofactor_column_summary(bits, defects, ranks),
        "tetraprime_prime_cofactor_pullback_column":
            tetraprime_prime_cofactor_column_summary(bits, defects, ranks),
        "multiple_120_largest_prime_factor_descent": factor_descent_summary(
            rows_120
        ),
        "multiple_420_largest_prime_factor_descent": factor_descent_summary(
            rows_420, modulus=420, bits=bits, defects=defects
        ),
        "multiple_84_seven_column_candidate": candidate(
            rows_84,
            "f(42*k)+f(28*k)+f(12*k)-f(14*k)-f(6*k)-f(4*k)"
            "+f(2*k) >= Q_(84*k-1)",
        ),
        "multiple_420_fifteen_column_candidate": candidate(
            rows_420,
            "the 2-3-5-7 inclusion-exclusion union at 420*k clears Q_(420*k-1)",
        ),
        "multiple_120_seven_column_candidate": candidate(
            rows_120,
            "f(60*k)+f(40*k)+f(24*k)-f(20*k)-f(12*k)-f(8*k)"
            "+f(4*k) >= Q_(120*k-1)",
        ),
        "multiple_60_falsifier": candidate(
            rows_60,
            "f(30*k)+f(20*k)+f(12*k)-f(10*k)-f(6*k)-f(4*k)"
            "+f(2*k) >= Q_(60*k-1)",
        ),
        "multiple_48_falsifier": candidate(
            rows_48,
            "f(24*k)+f(16*k)-f(8*k) >= Q_(48*k-1)",
        ),
        "multiple_24_falsifier": candidate(
            rows_24,
            "f(12*k)+f(8*k)-f(4*k) >= Q_(24*k-1)",
        ),
    }


def build_receipt(args: argparse.Namespace) -> dict[str, Any]:
    return {
        "schema": "erdos257_four_ninths_record_boundary_v1",
        "analysis_ref": ANALYSIS_REF,
        "claim_status": "exact finite theorem selection; all-depth producer open",
        "canonical_four_ninths": orbit_summary(
            args.ranks, args.fixed_point_crosscheck
        ),
        "exact_algebra": {
            "repair_equivalence": (
                "Q_n<=Q_(n-1) iff f(n)>=Q_(n-1)+t_n"
            ),
            "seven_column_union": (
                "U_30(n)=f(n/2)+f(n/3)+f(n/5)-f(n/6)-f(n/10)"
                "-f(n/15)+f(n/30) counts selected d whose codivisor "
                "shares a prime factor with 30"
            ),
            "phase_cancellation": (
                "for n=120*k, t_n=0 and the U_30 inclusion-exclusion "
                "combination of target digits is zero"
            ),
            "phase_free_form": (
                "with J the U_30 inclusion-exclusion operator on Q at "
                "n/2,n/3,n/5,n/6,n/10,n/15,n/30, the conjecture is "
                "2*J^-(n)-J(n)>=Q_(n-1)"
            ),
            "prime_cofactor_endpoint_slack": (
                "if n=120*p with prime p>5, U_30(n) omits exactly the "
                "selected divisors n and 120; the exact word has b_120=1, "
                "so f(n)=U_30(n)+b_n+1 and U_30(n)>=Q_(n-1)-1 already "
                "implies a one-step repair"
            ),
            "prime_pullback_column": (
                "for prime p>5, the moving U_30 column is exactly the bits "
                "b_(p*d) over the fifteen proper divisors d of 120"
            ),
            "tetraprime_pullback_column": (
                "for prime p>7, U_210(420*p) is its base load 12 plus "
                "the bits b_(p*d) over the twenty-three proper divisors "
                "d of 420"
            ),
            "tetraprime_descent_coordinate": (
                "M(k)=U_210(420*k)-Q_(420*k-1); a nondecreasing proper-"
                "divisor edge M(a)<=M(k), together with prime repair, is "
                "the exact strong-induction interface"
            ),
        },
        "analytic_selector": (
            "a final greedy skip forces a terminal strict-record suffix; "
            "therefore an all-depth multiple-of-120 repair law proves 4/9 "
            "membership, and denominator 9 admits no finite Mersenne sum"
        ),
        "not_claimed": [
            "the all-depth multiple-of-48 three-column inequality",
            "cofinality or a uniform bound for the observed repair gaps",
            "membership of 4/9 in the Mersenne achievement set",
            "a proof or disproof of Erdos problem 257",
            "the all-depth modulus-420 prime boundary or factor descent",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ranks", type=int, default=500_000)
    parser.add_argument("--fixed-point-crosscheck", type=int, default=2_000)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    rendered = canonical_json(build_receipt(args))
    if args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
