#!/usr/bin/env python3
"""Search and exact replay for adaptive minimum-enclosing-disk mechanisms.

Pendyala's degree-four proof joins two roots through the centre of their
minimum enclosing disk.  After normalising that disk, the required geometric
lemma says that two radial arms have product at most one.  This program tests
the literal degree-five extension on five points of the unit circle.

The literal radial extension is false in degree five, but that witness has a
safe root chord.  The optimisation mode can therefore test either the radial
lemma alone or the stronger adaptive dichotomy: some safe chord, or two safe
radial arms.  A normalized score above one falsifies the chosen mechanism.
The default/check modes remain reserved for exact replay after a robust
configuration has been selected.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any

import numpy as np
from scipy.optimize import differential_evolution, minimize_scalar


REPO_ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


SOURCE_REF = (
    "research_corpus/Erdos1041/"
    "scripts/check_erdos1041_pendyala_radial_extension.py"
)
ANALYSIS_REF = (
    "research_corpus/Erdos1041/"
    "AdaptiveMecDichotomyLab.md"
)
PACKET_REF = (
    "research_corpus/Erdos1041/"
    "research_packet.json"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "source-provenance://private-authoring-project/receipts/"
    "erdos1041_adaptive_mec_dichotomy_receipt.json"
)

GaussianQ = tuple[Fraction, Fraction]

# The first random falsifier, rotated so that the first point is one.  It has
# only a 1.3e-4 second-arm margin and is merely the seed for --optimize.
SEED_ANGLES = np.array(
    [0.0, 1.54114832, 3.00126382, 3.65999812, 5.77636063],
    dtype=np.float64,
)

# A first falsifier that also lies beyond the degree-five direct-chord cutoff:
# all five cyclic gaps exceed 2 asin(1/(2 sqrt(2))).
SEPARATED_SEED_GAPS = np.array(
    [0.91714520, 1.63050785, 1.04381319, 1.31588298, 1.37583608],
    dtype=np.float64,
)

# Rational half-angle parameters for the robust adaptive counterexample.
# The unit direction attached to s is ((1-s^2)/(1+s^2), 2s/(1+s^2)).
EXACT_HALF_TANGENTS = (
    Fraction(0),
    Fraction(48031, 76394),
    Fraction(347397, 99299),
    Fraction(-203651, 55446),
    Fraction(-67203, 94835),
)
EXACT_SCALE = Fraction(9999, 10000)
EXACT_RADIAL_PARAMETERS = {
    1: Fraction(23241, 96436),
    2: Fraction(3137, 12779),
    3: Fraction(9981, 95215),
    4: Fraction(27303, 88342),
}
EXACT_CHORD_PARAMETERS = {
    (0, 1): Fraction(20748, 40441),
    (0, 2): Fraction(40487, 60684),
    (0, 3): Fraction(63985, 98208),
    (0, 4): Fraction(33882, 65725),
    (1, 2): Fraction(15602, 31193),
    (1, 3): Fraction(29776, 89057),
    (1, 4): Fraction(6684, 9629),
    (2, 3): Fraction(3963, 7997),
    (2, 4): Fraction(66925, 98577),
    (3, 4): Fraction(27239, 53751),
}


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


def cross(left: GaussianQ, right: GaussianQ) -> Fraction:
    return left[0] * right[1] - left[1] * right[0]


def unit_direction(parameter: Fraction) -> GaussianQ:
    denominator = 1 + parameter * parameter
    return (
        (1 - parameter * parameter) / denominator,
        2 * parameter / denominator,
    )


def polynomial_value(point: GaussianQ, roots: list[GaussianQ]) -> GaussianQ:
    value: GaussianQ = (Fraction(1), Fraction(0))
    for root in roots:
        value = qmul(value, qsub(point, root))
    return value


def encode_fraction(value: Fraction) -> dict[str, int | str]:
    return {
        "value": str(value),
        "numerator": value.numerator,
        "denominator": value.denominator,
    }


def encode_gaussian(value: GaussianQ) -> dict[str, str]:
    return {"real": str(value[0]), "imag": str(value[1])}


def unit_points(angles: np.ndarray) -> np.ndarray:
    return np.exp(1j * np.asarray(angles, dtype=np.float64))


def arm_product(points: np.ndarray, root_index: int, t: np.ndarray | float) -> np.ndarray:
    parameter = np.asarray(t, dtype=np.float64)
    return np.prod(
        np.abs(parameter[..., None] * points[root_index] - points),
        axis=-1,
    )


def sampled_arm_maxima(angles: np.ndarray, sample_count: int) -> list[float]:
    points = unit_points(angles)
    parameters = np.linspace(0.0, 1.0, sample_count)
    return [
        float(np.max(arm_product(points, index, parameters)))
        for index in range(len(points))
    ]


def sampled_chord_maxima(angles: np.ndarray, sample_count: int) -> list[float]:
    points = unit_points(angles)
    parameters = np.linspace(0.0, 1.0, sample_count)
    maxima: list[float] = []
    for left in range(len(points)):
        for right in range(left + 1, len(points)):
            chord = (
                (1.0 - parameters[..., None]) * points[left]
                + parameters[..., None] * points[right]
            )
            values = np.prod(np.abs(chord - points), axis=-1)
            maxima.append(float(np.max(values)))
    return maxima


def adaptive_score(angles: np.ndarray, sample_count: int) -> float:
    """Best normalized construction cost: a chord or two radial arms."""

    radial_cost = sorted(sampled_arm_maxima(angles, sample_count))[1]
    chord_cost = min(sampled_chord_maxima(angles, sample_count))
    return min(radial_cost, chord_cost)


def refined_arm_maxima(angles: np.ndarray, sample_count: int = 4097) -> list[dict[str, float]]:
    points = unit_points(angles)
    parameters = np.linspace(0.0, 1.0, sample_count)
    rows: list[dict[str, float]] = []
    for index in range(len(points)):
        values = arm_product(points, index, parameters)
        peak = int(np.argmax(values))
        left = float(parameters[max(0, peak - 1)])
        right = float(parameters[min(sample_count - 1, peak + 1)])
        result = minimize_scalar(
            lambda parameter: -float(arm_product(points, index, parameter)),
            bounds=(left, right),
            method="bounded",
            options={"xatol": 1.0e-15},
        )
        rows.append({"t": float(result.x), "maximum": float(-result.fun)})
    return rows


def canonical_angles(raw: np.ndarray) -> np.ndarray:
    angles = np.sort(np.mod(np.concatenate(([0.0], raw)), 2.0 * math.pi))
    angles = np.mod(angles - angles[0], 2.0 * math.pi)
    return np.sort(angles)


def angles_from_gap_coordinates(raw: np.ndarray, minimum_gap: float) -> np.ndarray:
    degree = len(raw)
    slack = 2.0 * math.pi - degree * minimum_gap
    if slack <= 0.0:
        raise ValueError("degree times the minimum gap must be below 2*pi")
    shifted = raw - float(np.max(raw))
    weights = np.exp(shifted)
    weights /= float(np.sum(weights))
    gaps = minimum_gap + slack * weights
    return np.concatenate(([0.0], np.cumsum(gaps[:-1])))


def optimize(
    degree: int,
    seed: int,
    maxiter: int,
    popsize: int,
    samples: int,
    minimum_gap: float,
    objective_name: str,
) -> dict[str, object]:
    rng = np.random.default_rng(seed)

    def objective(raw: np.ndarray) -> float:
        angles = (
            angles_from_gap_coordinates(raw, minimum_gap)
            if minimum_gap > 0.0
            else canonical_angles(raw)
        )
        gaps = np.diff(np.concatenate((angles, [2.0 * math.pi])))
        if float(np.max(gaps)) > math.pi:
            # The unit circle is then not the minimum enclosing circle.
            return 0.0
        score = (
            adaptive_score(angles, samples)
            if objective_name == "radial-or-chord"
            else sorted(sampled_arm_maxima(angles, samples))[1]
        )
        return -score

    if minimum_gap > 0.0:
        seed_gaps = (
            SEPARATED_SEED_GAPS
            if degree == 5
            else np.full(degree, 2.0 * math.pi / degree)
        )
        slack_weights = seed_gaps - minimum_gap
        if np.min(slack_weights) <= 0.0:
            raise ValueError("the initial gaps do not satisfy the requested minimum gap")
        x0 = np.log(slack_weights / float(np.sum(slack_weights)))
        bounds = [(-8.0, 8.0)] * degree
    else:
        x0 = (
            SEED_ANGLES[1:]
            if degree == 5
            else np.linspace(0.0, 2.0 * math.pi, degree, endpoint=False)[1:]
        )
        bounds = [(0.0, 2.0 * math.pi)] * (degree - 1)

    result = differential_evolution(
        objective,
        bounds=bounds,
        x0=x0,
        seed=rng,
        maxiter=maxiter,
        popsize=popsize,
        tol=1.0e-10,
        polish=True,
        updating="immediate",
        workers=1,
    )
    angles = (
        angles_from_gap_coordinates(result.x, minimum_gap)
        if minimum_gap > 0.0
        else canonical_angles(result.x)
    )
    rows = refined_arm_maxima(angles)
    ordered = sorted(row["maximum"] for row in rows)
    chord_maxima = sampled_chord_maxima(angles, max(samples, 4097))
    combined_score = min(float(ordered[1]), float(min(chord_maxima)))
    return {
        "success": bool(result.success),
        "message": str(result.message),
        "objective_evaluations": int(result.nfev),
        "angles": [float(angle) for angle in angles],
        "cyclic_gaps": [
            float(gap)
            for gap in np.diff(np.concatenate((angles, [2.0 * math.pi])))
        ],
        "minimum_gap_constraint": float(minimum_gap),
        "objective": objective_name,
        "arm_rows": rows,
        "second_smallest_maximum": float(ordered[1]),
        "minimum_chord_maximum": float(min(chord_maxima)),
        "adaptive_score": combined_score,
        "degree": degree,
        "scale_threshold": float(ordered[1] ** (-1.0 / degree)),
    }


def exact_escape_row(
    roots: list[GaussianQ],
    *,
    kind: str,
    left: int,
    parameter: Fraction,
    right: int | None = None,
) -> dict[str, Any]:
    if kind == "radial":
        normalized_point = qscale(parameter, qscale(1 / EXACT_SCALE, roots[left]))
    else:
        assert right is not None
        normalized_left = qscale(1 / EXACT_SCALE, roots[left])
        normalized_right = qscale(1 / EXACT_SCALE, roots[right])
        normalized_point = qadd(
            qscale(1 - parameter, normalized_left),
            qscale(parameter, normalized_right),
        )
    point = qscale(EXACT_SCALE, normalized_point)
    value = polynomial_value(point, roots)
    value_norm_sq = norm_sq(value)
    margin = value_norm_sq - 1
    assert margin > 0
    row: dict[str, Any] = {
        "kind": kind,
        "left_root_index": left,
        "waypoint_parameter": str(parameter),
        "waypoint": encode_gaussian(point),
        "polynomial_value": encode_gaussian(value),
        "polynomial_value_norm_sq": encode_fraction(value_norm_sq),
        "strict_unit_escape_margin_sq": encode_fraction(margin),
    }
    if right is not None:
        row["right_root_index"] = right
    return row


def build_exact_witness() -> dict[str, Any]:
    directions = [unit_direction(value) for value in EXACT_HALF_TANGENTS]
    assert all(norm_sq(direction) == 1 for direction in directions)
    roots = [qscale(EXACT_SCALE, direction) for direction in directions]
    assert len(set(roots)) == 5
    assert all(norm_sq(root) == EXACT_SCALE**2 < 1 for root in roots)

    radial_rows = [
        exact_escape_row(
            roots,
            kind="radial",
            left=index,
            parameter=parameter,
        )
        for index, parameter in EXACT_RADIAL_PARAMETERS.items()
    ]
    chord_rows = [
        exact_escape_row(
            roots,
            kind="chord",
            left=left,
            right=right,
            parameter=parameter,
        )
        for (left, right), parameter in EXACT_CHORD_PARAMETERS.items()
    ]
    assert len(radial_rows) == 4
    assert len(chord_rows) == 10

    # Positive barycentric weights for directions 0, 2, 4 certify that the
    # origin lies in their convex hull.  Since all three have norm one, every
    # disk containing the five directions has radius at least one.  Therefore
    # the unit disk centered at the origin is their minimum enclosing disk.
    selected = (directions[0], directions[2], directions[4])
    raw_weights = (
        cross(selected[1], selected[2]),
        cross(selected[2], selected[0]),
        cross(selected[0], selected[1]),
    )
    assert all(weight > 0 for weight in raw_weights)
    total_weight = sum(raw_weights, Fraction(0))
    barycentric = tuple(weight / total_weight for weight in raw_weights)
    assert sum(barycentric, Fraction(0)) == 1
    barycenter = qadd(
        qadd(qscale(barycentric[0], selected[0]), qscale(barycentric[1], selected[1])),
        qscale(barycentric[2], selected[2]),
    )
    assert barycenter == (0, 0)
    assert sum(
        (weight * norm_sq(point) for weight, point in zip(barycentric, selected)),
        Fraction(0),
    ) == 1

    minimum_margin = min(
        Fraction(row["strict_unit_escape_margin_sq"]["numerator"],
                 row["strict_unit_escape_margin_sq"]["denominator"])
        for row in radial_rows + chord_rows
    )
    return {
        "scale": str(EXACT_SCALE),
        "half_angle_parameters": [str(value) for value in EXACT_HALF_TANGENTS],
        "unit_directions": [encode_gaussian(value) for value in directions],
        "roots": [encode_gaussian(value) for value in roots],
        "all_roots_distinct": True,
        "all_root_norms_strictly_below_one": True,
        "minimum_enclosing_disk": {
            "center": encode_gaussian((Fraction(0), Fraction(0))),
            "radius": str(EXACT_SCALE),
            "barycentric_direction_indices": [0, 2, 4],
            "positive_barycentric_weights": [str(value) for value in barycentric],
            "weighted_barycenter": encode_gaussian(barycenter),
            "weighted_squared_norm_average": "1",
            "certificate_consequence": (
                "Every disk containing these unit directions has squared radius "
                "at least their weighted mean squared distance from its center, "
                "which equals 1 plus the center norm squared."
            ),
        },
        "unsafe_radial_arm_count": len(radial_rows),
        "safe_radial_arm_count_upper_bound": len(roots) - len(radial_rows),
        "unsafe_radial_arms": radial_rows,
        "unsafe_root_chord_count": len(chord_rows),
        "root_chord_count": len(roots) * (len(roots) - 1) // 2,
        "unsafe_root_chords": chord_rows,
        "minimum_strict_escape_margin_sq": encode_fraction(minimum_margin),
    }


def build_receipt() -> dict[str, Any]:
    witness = build_exact_witness()
    contract = build_experiment_contract(
        problem_id="erdos_1041",
        target_statement=(
            "Join two roots by a curve of length less than two inside the "
            "strict unit lemniscate."
        ),
        claim_ceiling=(
            "Exact degree-five counterexample to the adaptive dichotomy using "
            "either a root chord or two radial arms through the minimum-"
            "enclosing-disk center; not a counterexample to Erdős #1041."
        ),
        hypothesis_id="root_chord_or_two_mec_radial_arms",
        hypothesis_statement=(
            "For every finite root set in the open unit disk, either one root "
            "chord stays in the strict unit lemniscate or two root spokes "
            "through the minimum-enclosing-disk center do."
        ),
        probe_id="rational_degree_five_adaptive_mec_falsifier",
        probe_question=(
            "Can all ten root chords and four of five minimum-enclosing-center "
            "radial arms be forced outside the unit lemniscate simultaneously?"
        ),
        computation=(
            "Evaluate the factored polynomial in Gaussian rational arithmetic "
            "at fourteen explicit rational waypoints and certify the exact "
            "minimum-enclosing disk by positive rational barycentric weights."
        ),
        falsifier=(
            "Five rational-complex roots in the open unit disk for which every "
            "root chord and all but one center radial arm have a waypoint with "
            "squared polynomial modulus strictly above one."
        ),
        stop_condition=(
            "Stop the adaptive MEC mechanism after exact certification of all "
            "ten chord escapes, four radial escapes, and the MEC center."
        ),
        survival_consequence=(
            "The chord-or-radial dichotomy would extend the quartic proof to "
            "arbitrary degree with an immediate strict length budget."
        ),
        falsification_consequence=(
            "A full proof must use a polynomial-adapted non-MEC hub, curved "
            "paths, or genuinely global component/Reeb geometry."
        ),
        consumer_ref=PACKET_REF,
        analysis_refs=[ANALYSIS_REF],
        source_refs=[SOURCE_REF, ANALYSIS_REF],
        result_status="finite_counterexample",
        result_summary=(
            "Exact rational arithmetic certifies all ten chord escapes and "
            "four radial escapes in a degree-five MEC-normalized configuration."
        ),
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos1041-adaptive-mec-dichotomy-counterexample/1",
        "status": "verified_exact_mechanism_elimination",
        "experiment_contract": contract,
        "witness": witness,
        "consequence_decisions": [
            {
                "mechanism": "root_chord_or_two_mec_radial_arms",
                "decision": "eliminated_in_degree_five",
            },
            {
                "mechanism": "minimal_critical_value_or_curved_hub",
                "decision": "remains_open_and_not_touched_by_witness",
            },
            {"mechanism": "erdos_1041", "decision": "not_claimed"},
        ],
        "source_records": [
            source_record(REPO_ROOT, SOURCE_REF),
            source_record(REPO_ROOT, ANALYSIS_REF),
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
    print(json.dumps({"status": "written", "output": str(output)}))
    return 0


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--degree", type=int, default=5)
    parser.add_argument("--optimize", action="store_true")
    parser.add_argument("--seed", type=int, default=104106)
    parser.add_argument("--maxiter", type=int, default=240)
    parser.add_argument("--popsize", type=int, default=20)
    parser.add_argument("--samples", type=int, default=769)
    parser.add_argument("--minimum-gap", type=float, default=0.0)
    parser.add_argument(
        "--objective",
        choices=("radial", "radial-or-chord"),
        default="radial",
    )
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.degree < 2:
        raise SystemExit("degree must be at least two")
    if args.optimize:
        print(
            json.dumps(
                optimize(
                    args.degree,
                    args.seed,
                    args.maxiter,
                    args.popsize,
                    args.samples,
                    args.minimum_gap,
                    args.objective,
                ),
                indent=2,
                sort_keys=True,
            )
        )
        return 0
    return emit(build_receipt(), args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
