#!/usr/bin/env python3
"""Exact degree-three witness: the chord-or-centre-hub disjunction fails at n=3.

The recorded elimination of the adaptive disjunction

    one safe root chord  OR  two safe radial arms through the minimum
    enclosing disk centre

is a degree-five statement (``adaptive_mec_chord_or_radial_counterexample``).
This script exhibits the same failure at **degree three**, which is the minimal
possible degree: for ``n = 2`` the chord between the two roots always works,
since on ``[a, b]`` one has ``|f| = t(1-t)|a-b|^2 <= |a-b|^2/4 <= 1``.

The witness is
    a_1 = L (7 + 24i)/25,   a_2 = L (7 - 24i)/25,   a_3 = -L,
    L   = 999/1000,
three distinct Gaussian rationals of common modulus ``L < 1``.  Positive
rational barycentric weights put the origin strictly inside their convex hull,
so ``D(0, L)`` is their minimum enclosing disk and the centre hub *is* the
origin.  Exact rational arithmetic then shows

  * every one of the three root chords carries a midpoint with ``|f|^2 > 1``;
  * two of the three origin spokes carry the waypoint ``t = 1/10`` with
    ``|f|^2 > 1``.

Hence no chord is safe and at most one radial arm is safe, so neither branch of
the disjunction is available.  This eliminates that mechanism at degree three;
it does not touch Erdős #1041, whose degree-three case is proved elsewhere in
this directory by a critical-point hub (``CubicCriticalHub.md``).

The structural reason is recorded in ``TwoSegmentContainmentReduction.md``: with
all roots on a common circle of radius ``L`` and ``L -> 1``, the origin spoke to
``a_j`` starts at ``|f(0)| = L^n -> 1`` and its initial log-derivative is
``-Re(conj(p_1) a_j)/L``, so only roots in the closed half plane
``Re(conj(p_1) z) >= 0`` can carry a spoke.  Here exactly one of the three does.
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from itertools import combinations
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "scripts/check_erdos1041_two_segment_containment.py"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "TwoSegmentContainmentReduction.md"
)
PACKET_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "research_packet.json"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1041_two_segment_containment_receipt.json"
)

GaussianQ = tuple[Fraction, Fraction]


def qadd(left: GaussianQ, right: GaussianQ) -> GaussianQ:
    return left[0] + right[0], left[1] + right[1]


def qsub(left: GaussianQ, right: GaussianQ) -> GaussianQ:
    return left[0] - right[0], left[1] - right[1]


def qmul(left: GaussianQ, right: GaussianQ) -> GaussianQ:
    return (
        left[0] * right[0] - left[1] * right[1],
        left[0] * right[1] + left[1] * right[0],
    )


def qscale(scale: Fraction, value: GaussianQ) -> GaussianQ:
    return scale * value[0], scale * value[1]


def norm_sq(value: GaussianQ) -> Fraction:
    return value[0] * value[0] + value[1] * value[1]


def encode_gaussian(value: GaussianQ) -> dict[str, str]:
    return {"real": str(value[0]), "imag": str(value[1])}


def encode_fraction(value: Fraction) -> dict[str, int | str]:
    return {
        "value": str(value),
        "numerator": value.numerator,
        "denominator": value.denominator,
    }


def polynomial_value(point: GaussianQ, roots: list[GaussianQ]) -> GaussianQ:
    value: GaussianQ = (Fraction(1), Fraction(0))
    for root in roots:
        value = qmul(value, qsub(point, root))
    return value


def build_witness() -> dict[str, Any]:
    scale = Fraction(999, 1000)
    directions: list[GaussianQ] = [
        (Fraction(7, 25), Fraction(24, 25)),
        (Fraction(7, 25), Fraction(-24, 25)),
        (Fraction(-1), Fraction(0)),
    ]
    assert all(norm_sq(direction) == 1 for direction in directions)
    roots = [qscale(scale, direction) for direction in directions]
    assert len(set(roots)) == 3
    assert all(norm_sq(root) < 1 for root in roots)

    # The origin is the minimum-enclosing-disc centre: positive rational
    # barycentric weights on the three unit directions, summing to one.
    weights = [Fraction(25, 64), Fraction(25, 64), Fraction(7, 32)]
    assert sum(weights) == 1
    assert all(weight > 0 for weight in weights)
    combination: GaussianQ = (Fraction(0), Fraction(0))
    for weight, direction in zip(weights, directions):
        combination = qadd(combination, qscale(weight, direction))
    assert combination == (Fraction(0), Fraction(0))

    # Every root chord escapes: the midpoint already has |f|^2 > 1.
    chord_rows: list[dict[str, Any]] = []
    for left, right in combinations(range(3), 2):
        midpoint = qscale(Fraction(1, 2), qadd(roots[left], roots[right]))
        value_norm_sq = norm_sq(polynomial_value(midpoint, roots))
        assert value_norm_sq > 1
        chord_rows.append(
            {
                "root_indices": [left, right],
                "waypoint_parameter": "1/2",
                "waypoint": encode_gaussian(midpoint),
                "value_norm_sq": encode_fraction(value_norm_sq),
                "escape_margin": encode_fraction(value_norm_sq - 1),
            }
        )

    # Two of the three origin spokes escape at t = 1/10.
    spoke_parameter = Fraction(1, 10)
    spoke_rows: list[dict[str, Any]] = []
    for index in (0, 1):
        point = qscale(spoke_parameter, roots[index])
        value_norm_sq = norm_sq(polynomial_value(point, roots))
        assert value_norm_sq > 1
        spoke_rows.append(
            {
                "root_index": index,
                "root": encode_gaussian(roots[index]),
                "waypoint_parameter": str(spoke_parameter),
                "waypoint": encode_gaussian(point),
                "value_norm_sq": encode_fraction(value_norm_sq),
                "escape_margin": encode_fraction(value_norm_sq - 1),
            }
        )

    # First-order half-plane count, exact.
    power_sum: GaussianQ = (Fraction(0), Fraction(0))
    for root in roots:
        power_sum = qadd(power_sum, root)
    half_plane = [
        power_sum[0] * root[0] + power_sum[1] * root[1] for root in roots
    ]
    assert sum(1 for value in half_plane if value >= 0) == 1

    origin_value_norm_sq = norm_sq(polynomial_value((Fraction(0), Fraction(0)), roots))
    assert origin_value_norm_sq < 1

    return {
        "scale": str(scale),
        "roots": [encode_gaussian(root) for root in roots],
        "root_norm_sq": encode_fraction(norm_sq(roots[0])),
        "origin_value_norm_sq": encode_fraction(origin_value_norm_sq),
        "minimum_enclosing_disc_centre_is_origin": {
            "barycentric_weights": [str(weight) for weight in weights],
            "weighted_sum": encode_gaussian(combination),
        },
        "escaping_chords": chord_rows,
        "escaping_origin_spokes": spoke_rows,
        "safe_chord_count_upper_bound": 0,
        "safe_origin_spoke_count_upper_bound": 1,
        "first_order_half_plane": {
            "power_sum_p1": encode_gaussian(power_sum),
            "re_conj_p1_times_root": [str(value) for value in half_plane],
            "roots_in_closed_half_plane": 1,
        },
    }


def build_receipt() -> dict[str, Any]:
    witness = build_witness()
    contract = build_experiment_contract(
        problem_id="erdos_1041",
        target_statement=(
            "Join two roots by a curve of length less than two inside the "
            "strict unit lemniscate."
        ),
        claim_ceiling=(
            "Exact degree-three counterexample to the chord-or-centre-hub "
            "disjunction; not a counterexample to Erdős #1041, whose "
            "degree-three case is proved by a critical-point hub."
        ),
        hypothesis_id="chord_or_centre_hub_disjunction",
        hypothesis_statement=(
            "Every monic polynomial with roots in the open unit disk admits "
            "either one root chord or two minimum-enclosing-disc-centre radial "
            "arms inside the strict unit lemniscate."
        ),
        probe_id="degree_three_rational_boundary_disjunction_falsifier",
        probe_question=(
            "Can the disjunction already fail at degree three, the minimal "
            "degree at which no chord need be safe?"
        ),
        computation=(
            "Evaluate the factored polynomial in Gaussian rational arithmetic "
            "at the midpoint of each of the three root chords and at t=1/10 on "
            "two of the three origin spokes, plus exact barycentric weights "
            "certifying that the minimum-enclosing-disc centre is the origin."
        ),
        falsifier=(
            "A three-root polynomial whose every chord midpoint and two of "
            "whose origin-spoke waypoints satisfy |f|^2 > 1."
        ),
        stop_condition=(
            "Stop once no chord is safe and at most one radial arm is safe."
        ),
        survival_consequence=(
            "The disjunction would give a two-segment path of length below two "
            "with no curvature and no branch-length integral."
        ),
        falsification_consequence=(
            "The critical-hub family is not redundant: chords and the centre "
            "hub can fail at the same configuration, already at degree three. "
            "Any two-segment mechanism must admit hubs beyond the centre."
        ),
        consumer_ref=PACKET_REF,
        analysis_refs=[ANALYSIS_REF],
        source_refs=[SOURCE_REF, ANALYSIS_REF],
        result_status="finite_counterexample",
        result_summary=(
            "Three exact chord midpoints and two exact spoke waypoints escape "
            "the unit lemniscate, so at degree three neither branch of the "
            "chord-or-centre-hub disjunction is available."
        ),
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos1041-two-segment-containment-witness/1",
        "status": "verified_exact_mechanism_elimination",
        "experiment_contract": contract,
        "witness": witness,
        "consequence_decisions": [
            {
                "mechanism": "chord_or_centre_hub_disjunction",
                "decision": "eliminated_from_degree_three",
            },
            {
                "mechanism": "free_hub_two_segment_containment",
                "decision": "remains_open_and_not_touched_by_witness",
            },
            {
                "mechanism": "erdos_1041",
                "decision": "not_claimed",
            },
        ],
        "source_records": [
            source_record(REPO_ROOT, SOURCE_REF),
            source_record(REPO_ROOT, ANALYSIS_REF),
            source_record(REPO_ROOT, PACKET_REF),
        ],
    }


def emit(payload: dict[str, Any], output: Path, check: bool) -> int:
    rendered = json.dumps(payload, indent=2, ensure_ascii=False, sort_keys=True)
    if check:
        if not output.exists():
            print(f"missing receipt: {output}", file=sys.stderr)
            return 1
        if output.read_text(encoding="utf-8").strip() != rendered.strip():
            print(f"stale receipt: {output}", file=sys.stderr)
            return 1
        print(f"receipt current: {output}")
        return 0
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(rendered + "\n", encoding="utf-8")
    print(f"wrote {output}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    return emit(build_receipt(), args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
