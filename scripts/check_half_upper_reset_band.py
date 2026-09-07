#!/usr/bin/env python3
"""Exact invariant search for the remaining Erdős #257 upper-reset band.

This mirrors the executable definitions in ``HalfCylinderIntegerGreedy.lean``:

* ``truncatedMersenneWeight s d = 4^s / (2^d - 1)``;
* ``seamSubsetTarget s = 2^(2s-1) - 2^s``;
* descending ``integerGreedyBits`` and its remainder.

The bridge proved in ``HalfCylinderConcreteSeamAdapter.lean`` identifies the
next-row greedy word with the adjacent-cut successor.  Consequently an upper
reset at row ``d`` is detected exactly when the old-rank prefix of the row
``d+1`` greedy word differs from the row ``d`` greedy word.  On such a row,
``HalfCylinderMiddleCarryLowerBound.lean`` proves

    reset_charge = 2^(d+1) - remainder(d+1).

The unresolved ``SeamUpperResetDyadicBandEscape`` proposition therefore has
an entirely executable formulation: for every ``j <= d``, the reset charge
must avoid the width ``2*(d+j)`` interval immediately below
``2^(d-j+1)``.  This script checks that formulation with exact integers and
reports the closest observed approach to a forbidden band.  Its output is
experimental evidence and an induction-invariant finder, not a proof.
"""

from __future__ import annotations

problem_id = "erdos_257"

import argparse
import json
from dataclasses import asdict, dataclass
from typing import Iterable


# Native-decide values already sealed in HalfCylinderUpperResetBandCertificates.lean.
KNOWN_REMAINDERS = {
    14: 392,
    15: 34_333,
    16: 71_791,
    17: 156_085,
    18: 362_187,
    19: 924_455,
    20: 549_353,
    21: 100_251,
    22: 4_595_307,
    23: 9_992_613,
    24: 23_193_229,
    25: 59_218_477,
    26: 35_546_625,
    27: 7_968_765,
    28: 300_310_513,
    29: 664_371_133,
    30: 1_583_742_700,
    31: 4_187_487_147,
}


@dataclass(frozen=True)
class GreedyRow:
    row: int
    bits: tuple[bool, ...]
    remainder: int


@dataclass(frozen=True)
class BandWitness:
    row: int
    j: int
    reset_charge: int
    dyadic_power: int
    width: int
    side: str
    slack: int


@dataclass(frozen=True)
class CriticalRunWitness:
    """Exact support-sensitive data for one completed upper/right cylinder."""

    reset_row: int
    right_run_length: int
    critical_index: int
    terminal_row: int
    terminal_kind: str
    reset_charge: int
    critical_power: int
    critical_gap: int
    affine_charge: int
    terminal_remainder: int
    scaled_critical_gap: int
    exact_row_slack: int
    loose_band_slack: int
    pulse_digits: tuple[int, ...]


def truncated_mersenne_weight(s: int, d: int) -> int:
    return 4**s // (2**d - 1)


def seam_subset_target(s: int) -> int:
    return 2 ** (2 * s - 1) - 2**s


def greedy_row(s: int) -> GreedyRow:
    """Evaluate the Lean row definitions, preserving descending rank order."""
    remainder = seam_subset_target(s)
    bits: list[bool] = []
    for d in range(2, s):
        weight = truncated_mersenne_weight(s, d)
        selected = weight <= remainder
        bits.append(selected)
        if selected:
            remainder -= weight
    return GreedyRow(s, tuple(bits), remainder)


def row_pulse(s: int, d: int) -> int:
    """Mirror ``HalfCylinderIntegerGreedy.rowPulse`` exactly."""
    return int((2 * s + 2) % d == 0) + 2 * int((2 * s + 1) % d == 0)


def word_pulse(row: GreedyRow) -> int:
    return sum(
        row_pulse(row.row, d)
        for d, selected in enumerate(row.bits, start=2)
        if selected
    )


def is_upper_reset(row: GreedyRow, successor: GreedyRow) -> bool:
    if successor.row != row.row + 1:
        raise ValueError("successor must be the immediately following row")
    if len(successor.bits) != len(row.bits) + 1:
        raise ValueError("unexpected greedy-word lengths")
    return successor.bits[:-1] != row.bits


def transition_kind(row: GreedyRow, successor: GreedyRow) -> str:
    """Classify the exact three-way greedy transition at ``row.row``."""
    if is_upper_reset(row, successor):
        return "upper"
    return "right" if successor.bits[-1] else "middle"


def critical_index(d: int, reset_charge: int) -> int:
    """Largest dyadic boundary at or above the reset charge."""
    admissible = [j for j in range(d + 1) if reset_charge <= 2 ** (d - j + 1)]
    if not admissible:
        raise ValueError(f"reset charge above every dyadic boundary at row {d}")
    return max(admissible)


def completed_critical_run_witness(
    d: int, by_row: dict[int, GreedyRow], max_row: int
) -> CriticalRunWitness | None:
    """Follow the actual right run after an upper reset to its next producer.

    Returning ``None`` at the scan boundary prevents a truncated final run
    from masquerading as a mathematical mismatch.
    """
    reset_successor = by_row[d + 1]
    reset_charge = 2 ** (d + 1) - reset_successor.remainder
    pulses: list[int] = []
    terminal_row = d + 1
    while terminal_row < max_row:
        kind = transition_kind(by_row[terminal_row], by_row[terminal_row + 1])
        if kind != "right":
            break
        pulses.append(word_pulse(by_row[terminal_row]))
        terminal_row += 1
    if terminal_row == max_row:
        return None

    k = len(pulses)
    if k > d:
        raise ValueError(f"right run longer than reset row at {d}: {k}")
    critical = critical_index(d, reset_charge)
    power = 2 ** (d - k + 1)
    gap = power - reset_charge
    charge = 0
    for pulse in pulses:
        charge = 4 * charge + pulse + 4
    remainder = by_row[terminal_row].remainder
    scaled_gap = 4**k * gap
    return CriticalRunWitness(
        reset_row=d,
        right_run_length=k,
        critical_index=critical,
        terminal_row=terminal_row,
        terminal_kind=transition_kind(
            by_row[terminal_row], by_row[terminal_row + 1]
        ),
        reset_charge=reset_charge,
        critical_power=power,
        critical_gap=gap,
        affine_charge=charge,
        terminal_remainder=remainder,
        scaled_critical_gap=scaled_gap,
        exact_row_slack=remainder - terminal_row,
        loose_band_slack=gap - 2 * (d + k),
        pulse_digits=tuple(pulses),
    )


def band_witnesses(d: int, successor_remainder: int) -> Iterable[BandWitness]:
    reset_charge = 2 ** (d + 1) - successor_remainder
    if reset_charge < 0:
        raise ValueError(f"negative reset charge at row {d}")
    for j in range(d + 1):
        power = 2 ** (d - j + 1)
        width = 2 * (d + j)
        if power < reset_charge:
            # Strict upper-side escape is first true at charge = power + 1.
            yield BandWitness(
                d, j, reset_charge, power, width, "above", reset_charge - power - 1
            )
        else:
            # Lower-side escape permits equality at charge + width = power.
            yield BandWitness(
                d, j, reset_charge, power, width, "below", power - reset_charge - width
            )


def scan(max_row: int) -> dict[str, object]:
    if max_row < 31:
        raise ValueError("max_row must be at least 31 to run the sealed-value checks")

    rows = [greedy_row(s) for s in range(5, max_row + 1)]
    by_row = {row.row: row for row in rows}

    sealed_mismatches = {
        s: {"expected": expected, "actual": by_row[s].remainder}
        for s, expected in KNOWN_REMAINDERS.items()
        if by_row[s].remainder != expected
    }

    row_bound_failures = [
        {"row": row.row, "remainder": row.remainder}
        for row in rows
        if row.row >= 14 and row.remainder < row.row
    ]

    upper_resets: list[int] = []
    band_failures: list[dict[str, int]] = []
    closest: BandWitness | None = None
    minimum_reset_remainder_margin: dict[str, int] | None = None
    critical_runs: list[CriticalRunWitness] = []

    for row, successor in zip(rows, rows[1:]):
        d = row.row
        if d < 13 or not is_upper_reset(row, successor):
            continue
        upper_resets.append(d)

        critical_run = completed_critical_run_witness(d, by_row, max_row)
        if critical_run is not None:
            critical_runs.append(critical_run)

        margin = successor.remainder - 2 * d
        if (
            minimum_reset_remainder_margin is None
            or margin < minimum_reset_remainder_margin["margin"]
        ):
            minimum_reset_remainder_margin = {
                "row": d,
                "successor_remainder": successor.remainder,
                "margin": margin,
            }

        for witness in band_witnesses(d, successor.remainder):
            if closest is None or witness.slack < closest.slack:
                closest = witness
            if witness.slack < 0:
                band_failures.append(
                    {
                        "row": d,
                        "j": witness.j,
                        "reset_charge": witness.reset_charge,
                        "dyadic_power": witness.dyadic_power,
                        "width": witness.width,
                    }
                )

    minimum_row_margin_row = min(
        (row for row in rows if row.row >= 14),
        key=lambda row: row.remainder - row.row,
    )

    critical_index_mismatches = [
        asdict(witness)
        for witness in critical_runs
        if witness.critical_index != witness.right_run_length
    ]
    critical_cylinder_failures = [
        asdict(witness)
        for witness in critical_runs
        if witness.terminal_remainder + witness.affine_charge
        != witness.scaled_critical_gap
    ]
    minimum_exact_run_slack = min(
        critical_runs, key=lambda witness: witness.exact_row_slack, default=None
    )
    minimum_loose_band_slack = min(
        critical_runs, key=lambda witness: witness.loose_band_slack, default=None
    )
    terminal_kind_counts = {
        kind: sum(witness.terminal_kind == kind for witness in critical_runs)
        for kind in ("upper", "middle", "right")
    }

    return {
        "schema": "erdos257_upper_reset_band_scan_v1",
        "max_row": max_row,
        "rows_checked": len(rows),
        "sealed_value_mismatches": sealed_mismatches,
        "late_row_bound_failures": row_bound_failures,
        "upper_reset_count": len(upper_resets),
        "first_upper_reset_rows": upper_resets[:20],
        "last_upper_reset_rows": upper_resets[-20:],
        "upper_reset_band_failures": band_failures,
        "closest_safe_band_witness": asdict(closest) if closest is not None else None,
        "minimum_late_row_margin": {
            "row": minimum_row_margin_row.row,
            "remainder": minimum_row_margin_row.remainder,
            "margin": minimum_row_margin_row.remainder - minimum_row_margin_row.row,
        },
        # At j=0, band escape is exactly successor_remainder >= 2*d.
        "minimum_upper_reset_j0_margin": minimum_reset_remainder_margin,
        "completed_critical_run_count": len(critical_runs),
        "critical_index_run_length_mismatches": critical_index_mismatches,
        "critical_cylinder_identity_failures": critical_cylinder_failures,
        "critical_run_terminal_kind_counts": terminal_kind_counts,
        "minimum_exact_critical_run_slack": (
            asdict(minimum_exact_run_slack)
            if minimum_exact_run_slack is not None
            else None
        ),
        "minimum_loose_critical_band_slack": (
            asdict(minimum_loose_band_slack)
            if minimum_loose_band_slack is not None
            else None
        ),
        "all_checks_pass": not (
            sealed_mismatches
            or row_bound_failures
            or band_failures
            or critical_index_mismatches
            or critical_cylinder_failures
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--max-row",
        type=int,
        default=256,
        help="largest exact greedy row to scan (default: 256)",
    )
    parser.add_argument(
        "--assert-property",
        action="store_true",
        help="exit nonzero if a sealed value, row bound, or upper-reset band fails",
    )
    args = parser.parse_args()

    result = scan(args.max_row)
    print(json.dumps(result, indent=2, sort_keys=True))
    return int(args.assert_property and not result["all_checks_pass"])


if __name__ == "__main__":
    raise SystemExit(main())
