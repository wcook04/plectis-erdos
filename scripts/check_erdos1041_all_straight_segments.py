#!/usr/bin/env python3
"""Exact cubic no-go for straight root-pair segments in Erdős #1041.

The computation takes place in ``Q(ω) = Q[x]/(x²+x+1)``.  It checks the
three roots ``r, rω, rω²`` of ``z³-r³`` at ``r=99/100`` and evaluates the
polynomial at every pair midpoint.  No floating point or root finder is used.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any

from system.lib.formal_math_experiment_contract import (
    build_experiment_contract,
    source_record,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
SCRIPT_PATH = Path(__file__).resolve()
SOURCE_REF = str(SCRIPT_PATH.relative_to(REPO_ROOT))
LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "CriticalTwoRootProximity.lean"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "AllStraightSegmentsCounterexampleComputationalLab.md"
)
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "erdos1041_all_straight_segments_counterexample_receipt.json"
)


@dataclass(frozen=True)
class EisensteinRational:
    """Element ``a+bω`` with ``ω²+ω+1=0``."""

    a: Fraction
    b: Fraction

    def __add__(self, other: "EisensteinRational") -> "EisensteinRational":
        return EisensteinRational(self.a + other.a, self.b + other.b)

    def __sub__(self, other: "EisensteinRational") -> "EisensteinRational":
        return EisensteinRational(self.a - other.a, self.b - other.b)

    def __mul__(self, other: "EisensteinRational") -> "EisensteinRational":
        # (a+bω)(c+dω)=(ac-bd)+(ad+bc-bd)ω.
        return EisensteinRational(
            self.a * other.a - self.b * other.b,
            self.a * other.b + self.b * other.a - self.b * other.b,
        )

    def scale(self, value: Fraction) -> "EisensteinRational":
        return EisensteinRational(value * self.a, value * self.b)

    def pow(self, exponent: int) -> "EisensteinRational":
        if exponent < 0:
            raise ValueError("negative exponents are not needed")
        result = EisensteinRational(Fraction(1), Fraction(0))
        base = self
        power = exponent
        while power:
            if power & 1:
                result = result * base
            base = base * base
            power //= 2
        return result

    def norm_sq(self) -> Fraction:
        # For ω=(-1+i√3)/2, |a+bω|²=a²-ab+b².
        return self.a * self.a - self.a * self.b + self.b * self.b

    def as_json(self) -> dict[str, str]:
        return {"a": str(self.a), "b": str(self.b)}


def canonical_hash(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def build_result() -> dict[str, Any]:
    one = EisensteinRational(Fraction(1), Fraction(0))
    omega = EisensteinRational(Fraction(0), Fraction(1))
    omega_sq = omega * omega
    units = (one, omega, omega_sq)
    radius = Fraction(99, 100)
    radius_scalar = EisensteinRational(radius, Fraction(0))
    radius_cube = radius**3
    roots = tuple(unit.scale(radius) for unit in units)
    zero = EisensteinRational(Fraction(0), Fraction(0))

    if omega_sq + omega + one != zero or omega.pow(3) != one:
        raise AssertionError("cyclotomic arithmetic failed")
    if any(root.norm_sq() != radius**2 for root in roots):
        raise AssertionError("root norm mismatch")
    if not radius**2 < 1:
        raise AssertionError("roots are not in the open unit disk")

    pair_rows = []
    expected_value = EisensteinRational(Fraction(-9, 8) * radius_cube, Fraction(0))
    for left in range(3):
        for right in range(left + 1, 3):
            midpoint = (roots[left] + roots[right]).scale(Fraction(1, 2))
            value = midpoint.pow(3) - radius_scalar.pow(3)
            if value != expected_value:
                raise AssertionError((left, right, value, expected_value))
            value_norm_sq = value.norm_sq()
            if not 1 < value_norm_sq:
                raise AssertionError((left, right, value_norm_sq))
            pair_rows.append(
                {
                    "pair": [left, right],
                    "midpoint": midpoint.as_json(),
                    "polynomial_value": value.as_json(),
                    "polynomial_value_norm_sq": str(value_norm_sq),
                    "escapes_strict_unit_lemniscate": True,
                }
            )

    result_summary = (
        "For f(z)=z^3-(99/100)^3, all three roots lie in the open unit disk, "
        "but every distinct root pair has midpoint value -9(99/100)^3/8, "
        "whose modulus is greater than one. Thus every straight root-pair "
        "segment exits the strict unit lemniscate."
    )
    if not 2 * radius < 2:
        raise AssertionError("critical-point hub length is not below two")
    payload = {
        "schema": "erdos1041-all-straight-segments-counterexample/1",
        "problem_id": "erdos_1041",
        "claim_ceiling": (
            "This eliminates every proof that tries to choose a straight segment "
            "between two roots. It does not exclude a broken-line path and does not solve "
            "Erdős #1041."
        ),
        "exact_configuration": {
            "polynomial": "z^3-r^3",
            "radius": str(radius),
            "root_units": [unit.as_json() for unit in units],
            "cyclotomic_relation": "omega^2+omega+1=0",
            "root_norm_sq": str(radius**2),
            "all_roots_in_open_unit_disk": True,
        },
        "pair_midpoint_certificates": pair_rows,
        "all_distinct_pair_midpoints_escape": len(pair_rows) == 3,
        "common_midpoint_value": expected_value.as_json(),
        "common_midpoint_modulus": str(Fraction(9, 8) * radius_cube),
        "strict_escape_integer_inequality": {
            "left": 9 * 99**3,
            "right": 8 * 100**3,
            "holds": 9 * 99**3 > 8 * 100**3,
        },
        "critical_point_hub_repair": {
            "status": "exact_algebraic_path_not_lean_checked",
            "path": "r -> 0 -> r*omega",
            "radial_leg_formula": "|f(s*r*u)|=r^3*(1-s^3)<1 for 0<=s<1",
            "hub_value_modulus": str(radius_cube),
            "hub_value_modulus_lt_one": radius_cube < 1,
            "length_argument": (
                "the two radial legs each have length r, so total length 2r<2"
            ),
            "strict_length_upper_bound": str(2 * radius),
            "meaning": (
                "The cubic kills every direct chord but admits a short two-segment "
                "path through its critical point."
            ),
        },
        "lean_theorems": [
            "ErdosProblems.Erdos1041.allStraightCubic_roots_in_unitDisk",
            "ErdosProblems.Erdos1041.allStraightCubic_roots",
            "ErdosProblems.Erdos1041.allStraightCubic_every_pair_midpoint_escapes",
        ],
        "result_status": "exact_all_pair_straight_segment_mechanism_elimination",
        "result_summary": result_summary,
        "experiment_contract": build_experiment_contract(
            problem_id="erdos_1041",
            target_statement=(
                "Find two roots joined by a curve of length less than two inside "
                "the strict unit lemniscate."
            ),
            claim_ceiling=(
                "The exact cubic eliminates straight root-pair segments only; "
                "critical-point hubs, multi-segment, curved, and topological routes remain open."
            ),
            hypothesis_id="some_straight_root_pair_always_stays_in_lemniscate",
            hypothesis_statement=(
                "Every monic polynomial with roots in the open unit disk has two "
                "roots whose straight segment is contained in |f|<1."
            ),
            probe_id="exact_radial_cubic_all_pair_midpoints",
            probe_question=(
                "Can a symmetric cubic force every straight root-pair midpoint "
                "outside the strict unit lemniscate?"
            ),
            computation=(
                "Evaluate z^3-r^3 exactly in Q(omega) at all three pair midpoints "
                "for r=99/100."
            ),
            falsifier=(
                "One pair midpoint with polynomial modulus at most one, or one root "
                "outside the open unit disk."
            ),
            stop_condition=(
                "After all three exact midpoint evaluations agree and exceed one, "
                "retire every straight-root-pair proof geometry."
            ),
            survival_consequence=(
                "If some pair were safe, isolate its symmetry-breaking feature as a "
                "candidate root-selection lemma."
            ),
            falsification_consequence=(
                "Any general proof must leave the single-chord geometry; the same "
                "cubic keeps critical-point hubs and more general paths live."
            ),
            consumer_ref=LEAN_REF,
            analysis_refs=[ANALYSIS_REF],
            source_refs=[SOURCE_REF, LEAN_REF],
            result_status="exact_one_way_result",
            result_summary=result_summary,
        ),
        "sources": [
            source_record(REPO_ROOT, SOURCE_REF),
            source_record(REPO_ROOT, LEAN_REF),
            source_record(REPO_ROOT, ANALYSIS_REF),
        ],
    }
    return {**payload, "receipt_payload_sha256": canonical_hash(payload)}


def emit(result: dict[str, Any], output: Path, check: bool) -> int:
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    output = output.resolve()
    if check:
        if not output.exists() or output.read_text(encoding="utf-8") != rendered:
            print(f"stale receipt: {output}")
            return 1
        print(json.dumps({"status": "current", "output": str(output)}))
        return 0
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(rendered, encoding="utf-8")
    print(json.dumps({"status": "written", "output": str(output)}))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    return emit(build_result(), args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
