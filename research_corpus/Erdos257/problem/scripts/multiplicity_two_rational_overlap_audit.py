#!/usr/bin/env python3
"""Exact audit for the multiplicity-two rational overlap theorem.

The theorem is measure-theoretic.  This script checks its rational constants
and maps the necessary outer-cylinder corridor at bounded depths.  The latter
is diagnostic only and is never used as proof of an infinite representation.
"""

from __future__ import annotations

import argparse
import bisect
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path


def weight(n: int) -> Fraction:
    return Fraction(1, (1 << n) - 1)


def ceil_div(a: int, b: int) -> int:
    return -((-a) // b)


def corridor_row(depth: int) -> dict[str, object]:
    denominators = [(1 << n) - 1 for n in range(1, depth + 1)]
    common = 1
    for denominator in denominators:
        common = math.lcm(common, denominator)

    # Units are 1/(2*common), so the target 3/2 is the integer 3*common.
    atom_units = [(2 * common) // denominator for denominator in denominators]
    sums = [0]
    for atom in atom_units:
        sums += [value + atom for value in sums]
    sums.sort()

    target_units = 3 * common
    next_mersenne = (1 << (depth + 1)) - 1
    # Each one-copy tail is at most 2*w_(depth+1), hence the two-copy
    # remainder is at most 4*w_(depth+1).  In the chosen units this is
    # 8*common/next_mersenne.
    corridor_lower_units = ceil_div(
        target_units * next_mersenne - 8 * common, next_mersenne
    )
    corridor_upper_units = target_units

    ordered_pair_count = 0
    for left in sums:
        lo = bisect.bisect_left(sums, corridor_lower_units - left)
        hi = bisect.bisect_right(sums, corridor_upper_units - left)
        ordered_pair_count += hi - lo

    total_ordered_pairs = 1 << (2 * depth)
    return {
        "depth": depth,
        "prefix_count": len(sums),
        "ordered_outer_corridor_pair_count": ordered_pair_count,
        "total_ordered_prefix_pair_count": total_ordered_pairs,
        "outer_corridor_pair_fraction": str(Fraction(ordered_pair_count, total_ordered_pairs)),
        "common_denominator_bits": common.bit_length(),
        "tail_bound": f"two-copy tail <= 4/(2^{depth + 1}-1)",
        "claim_boundary": "necessary outer-cylinder corridor only; not an existence proof at this depth",
    }


def run(max_depth: int) -> dict[str, object]:
    if max_depth < 8:
        raise ValueError("max_depth must be at least 8")

    lower_partial = sum((weight(n) for n in range(1, 5)), Fraction())
    erdos_borwein_upper = weight(1) + weight(2) + 2 * weight(3)
    target = Fraction(3, 2)
    overlap_lower = Fraction(7, 2) - 2 * erdos_borwein_upper
    sufficient_interval_left = 2 * erdos_borwein_upper - 2

    depths = [depth for depth in (8, 10, 12, 14, 16, 18) if depth <= max_depth]
    if max_depth not in depths:
        depths.append(max_depth)
    rows = [corridor_row(depth) for depth in depths]

    assertions = {
        "erdos_borwein_strictly_above_three_halves": lower_partial > target,
        "erdos_borwein_at_most_34_over_21": erdos_borwein_upper == Fraction(34, 21),
        "three_halves_inside_certified_overlap_interval": target > sufficient_interval_left,
        "overlap_measure_lower_bound_positive": overlap_lower > 0,
        "overlap_measure_lower_bound_is_11_over_42": overlap_lower == Fraction(11, 42),
        "all_outer_corridors_nonempty": all(
            row["ordered_outer_corridor_pair_count"] > 0 for row in rows
        ),
    }
    if not all(assertions.values()):
        raise AssertionError(assertions)

    payload: dict[str, object] = {
        "schema": "erdos257_multiplicity_two_rational_overlap_audit_v0",
        "proved_all_scale_result": {
            "achievement_set_measure": "volume(Acal)=1",
            "symmetry": "Acal=E-Acal",
            "convolution_overlap": "(1_Acal*1_Acal)(s)=volume(Acal intersect (Acal+s-E))",
            "general_lower_bound": "convolution(s) >= 2-E-abs(s-E)",
            "concrete_target": "s=3/2",
            "concrete_lower_bound": "convolution(3/2) >= 7/2-2E >= 11/42 > 0",
            "certified_interval": "convolution(s)>0 for every real s in (26/21,2)",
            "construction": "continuum many pairs of Boolean Mersenne supports have combined coefficients in {0,1,2} and total value 3/2; a pair can be chosen with both supports of natural density 1/2 and divergent reciprocal sum",
            "density_consequence": "for a density-half pair, the Cesaro mean of c_n=b_n+b'_n is 1",
        },
        "exact_rational_inputs": {
            "partial_sum_n_1_to_4": str(lower_partial),
            "partial_sum_exceeds_three_halves": lower_partial > target,
            "erdos_borwein_upper": str(erdos_borwein_upper),
            "certified_rational_sum_interval": f"({sufficient_interval_left}, 2)",
            "target": str(target),
            "overlap_measure_lower_bound": str(overlap_lower),
        },
        "outer_cylinder_diagnostic": {
            "rows": rows,
            "role": "maps bounded prefix geometry; theorem proof uses measure, symmetry, containment, and inclusion-exclusion",
        },
        "assertions": assertions,
        "claim_boundary": [
            "This constructs a rational subseries with coefficients in {0,1,2}, not a Boolean {0,1} counterexample.",
            "Positive overlap is the all-scale proof; finite cylinder counts are diagnostic only.",
            "Separating the multiplicity-two representation into one rational Boolean subseries remains open and would decide Erdos 257 negatively.",
        ],
        "consequence_decisions": [
            {
                "surface": "MultiplicityRenormalisationAttack.md",
                "decision": "update_candidate_input_not_claim",
                "reason": "The no-go now receives an actual infinite multiplicity-two rational construction as input; its local defect obstruction still prevents Booleanisation.",
            },
            {
                "surface": "rational_boolean_membership_and_universal_257",
                "decision": "verified_no_change",
                "reason": "No individual Boolean support is proved rational.",
            },
            {
                "surface": "generic_lexical_consequence_candidates",
                "decision": "outside_scope",
                "reason": "Unrelated sum, overlap, and indicator matches do not consume this theorem.",
            },
        ],
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    payload["payload_sha256_without_hash_field"] = hashlib.sha256(canonical).hexdigest()
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-depth", type=int, default=18)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(
            "state/formal_math/erdos257_period_noncollapse/"
            "multiplicity_two_rational_overlap_receipt.json"
        ),
    )
    args = parser.parse_args()
    result = run(args.max_depth)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(
        json.dumps(
            {
                "output": str(args.output),
                "all_assertions": all(result["assertions"].values()),
                "overlap_lower_bound": result["exact_rational_inputs"][
                    "overlap_measure_lower_bound"
                ],
                "diagnostic_depths": [
                    row["depth"]
                    for row in result["outer_cylinder_diagnostic"]["rows"]
                ],
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
