#!/usr/bin/env python3
"""Numerical reconnaissance for structural routes in Erdős #1041.

This is deliberately a candidate finder, not a certificate.  It rasterizes the
open lemniscate |prod(z-z_i)| < 1, labels its components, and computes the
shortest eight-neighbour grid path between any two roots in a common component.
A candidate whose grid distance is near or above 2 must subsequently be checked
on larger boxes and finer meshes and then replaced by interval-certified
continuous geometry.

The optional ``critical-hub`` objective tests a different mechanism: every
critical point and every root spoke is sampled, and the score is the cheapest
two-spoke hub after simultaneously charging spoke containment and total path
length.  A score above one is a candidate eliminating all straight critical-
point hubs, not a counterexample to the original problem.

The ``minimum-critical-newton-hub`` objective isolates the canonical first
merge in the lemniscate tree: among admissible simple critical points it selects
one with minimum critical-value modulus and charges half the total length of
its two descending inverse-ray branches.  Those branches have automatic
lemniscate containment; a score above one would falsify the proposed metric
completion of the first-merge reduction.
"""

from __future__ import annotations

import argparse
import heapq
import json
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy import ndimage
from scipy.integrate import solve_ivp

from system.lib.formal_math_experiment_contract import build_experiment_contract


REPO_ROOT = Path(__file__).resolve().parents[5]
SOURCE_REF = str(Path(__file__).resolve().relative_to(REPO_ROOT))
NEWTON_BRANCH_ANALYSIS_REF = (
    "research_corpus/Erdos1041/"
    "NewtonBranchHubCounterexampleComputationalLab.md"
)
INVERSE_RAY_AGGREGATE_ANALYSIS_REF = (
    "research_corpus/Erdos1041/"
    "InverseRayAggregateComputationalLab.md"
)
STRAIGHT_HUB_ANALYSIS_REF = (
    "research_corpus/Erdos1041/"
    "CriticalTwoRootProximity.lean"
)
RESEARCH_REF = (
    "research_corpus/Erdos1041/"
    "research_packet.json"
)


@dataclass(frozen=True)
class Grid:
    axis: np.ndarray
    points: np.ndarray
    step: float


def make_grid(radius: float, size: int) -> Grid:
    axis = np.linspace(-radius, radius, size)
    xx, yy = np.meshgrid(axis, axis)
    return Grid(axis=axis, points=xx + 1j * yy, step=float(axis[1] - axis[0]))


def root_pixel(grid: Grid, root: complex) -> tuple[int, int]:
    col = int(np.clip(np.rint((root.real - grid.axis[0]) / grid.step), 0, len(grid.axis) - 1))
    row = int(np.clip(np.rint((root.imag - grid.axis[0]) / grid.step), 0, len(grid.axis) - 1))
    return row, col


def lemniscate_mask(grid: Grid, roots: np.ndarray) -> np.ndarray:
    values = np.ones(grid.points.shape, dtype=np.complex128)
    for root in roots:
        values *= grid.points - root
    return np.abs(values) < 1.0


NEIGHBOURS = (
    (-1, 0, 1.0),
    (1, 0, 1.0),
    (0, -1, 1.0),
    (0, 1, 1.0),
    (-1, -1, math.sqrt(2.0)),
    (-1, 1, math.sqrt(2.0)),
    (1, -1, math.sqrt(2.0)),
    (1, 1, math.sqrt(2.0)),
)


def closest_pair_grid_distance(
    component: np.ndarray, seeds: list[tuple[int, int]], step: float
) -> float:
    """Multi-source Dijkstra, stopping at the first collision of root fronts."""
    shape = component.shape
    distance = np.full(shape, np.inf)
    owner = np.full(shape, -1, dtype=np.int32)
    queue: list[tuple[float, int, int]] = []
    for seed_owner, (row, col) in enumerate(seeds):
        if owner[row, col] >= 0:
            return 0.0
        distance[row, col] = 0.0
        owner[row, col] = seed_owner
        heapq.heappush(queue, (0.0, row, col))

    best = math.inf
    rows, cols = shape
    while queue:
        current, row, col = heapq.heappop(queue)
        if current != distance[row, col]:
            continue
        if current >= best:
            break
        for drow, dcol, edge_units in NEIGHBOURS:
            next_row, next_col = row + drow, col + dcol
            if not (0 <= next_row < rows and 0 <= next_col < cols):
                continue
            if not component[next_row, next_col]:
                continue
            edge = step * edge_units
            next_owner = owner[next_row, next_col]
            if next_owner >= 0 and next_owner != owner[row, col]:
                best = min(best, current + edge + distance[next_row, next_col])
                continue
            proposal = current + edge
            if proposal < distance[next_row, next_col]:
                distance[next_row, next_col] = proposal
                owner[next_row, next_col] = owner[row, col]
                heapq.heappush(queue, (proposal, next_row, next_col))
    return best


def score(grid: Grid, roots: np.ndarray) -> tuple[float, list[list[int]]]:
    mask = lemniscate_mask(grid, roots)
    pixels = [root_pixel(grid, root) for root in roots]
    for pixel in pixels:
        mask[pixel] = True
    labels, _ = ndimage.label(mask, structure=np.ones((3, 3), dtype=np.int8))
    groups: dict[int, list[int]] = {}
    for index, pixel in enumerate(pixels):
        groups.setdefault(int(labels[pixel]), []).append(index)

    eligible = [indices for label, indices in groups.items() if label != 0 and len(indices) >= 2]
    if not eligible:
        return -math.inf, []

    best = math.inf
    for indices in eligible:
        label = int(labels[pixels[indices[0]]])
        component = labels == label
        seeds = [pixels[index] for index in indices]
        best = min(best, closest_pair_grid_distance(component, seeds, grid.step))
    return best, eligible


def random_roots(rng: np.random.Generator, degree: int) -> np.ndarray:
    """Mix boundary-biased and cluster-biased configurations."""
    mode = int(rng.integers(3))
    if mode == 0:
        radii = rng.uniform(0.72, 0.995, degree)
        angles = rng.uniform(-math.pi, math.pi, degree)
    elif mode == 1:
        radii = rng.uniform(0.88, 0.998, degree)
        angles = np.linspace(0.0, 2.0 * math.pi, degree, endpoint=False)
        angles += rng.normal(0.0, 0.34, degree) + rng.uniform(-math.pi, math.pi)
    else:
        centres = rng.uniform(-math.pi, math.pi, 3)
        radii = rng.uniform(0.78, 0.998, degree)
        angles = rng.choice(centres, degree) + rng.normal(0.0, 0.22, degree)
    return radii * np.exp(1j * angles)


def perturbed_regular_roots(
    rng: np.random.Generator, degree: int, scale: float
) -> np.ndarray:
    """Boundary-near regular polygons, where the hub score approaches one."""

    base_angles = np.linspace(0.0, 2.0 * math.pi, degree, endpoint=False)
    angles = base_angles + rng.normal(0.0, scale, degree)
    radii = 0.9999 - np.abs(rng.normal(0.0, scale / 3.0, degree))
    return np.clip(radii, 0.5, 0.99999) * np.exp(1j * angles)


def mutate_roots(
    rng: np.random.Generator, roots: np.ndarray, scale: float
) -> np.ndarray:
    """Perturb an elite configuration while keeping every root in the unit disk."""

    noise = scale * (
        rng.normal(0.0, 1.0, len(roots))
        + 1j * rng.normal(0.0, 1.0, len(roots))
    )
    candidate = roots + noise
    radii = np.abs(candidate)
    outside = radii >= 0.99999
    candidate[outside] *= 0.99999 / radii[outside]
    return candidate


def roots_from_receipt(path: Path, degree: int) -> np.ndarray:
    """Load a previously persisted best configuration for bounded continuation."""

    payload = json.loads(path.read_text(encoding="utf-8"))
    raw_roots = payload.get("roots")
    if raw_roots is None and isinstance(payload.get("witness"), dict):
        raw_roots = payload["witness"].get("roots")
    if not isinstance(raw_roots, list) or len(raw_roots) != degree:
        raise ValueError(
            f"resume receipt {path} does not contain {degree} complex roots"
        )
    parsed: list[complex] = []
    for pair in raw_roots:
        if isinstance(pair, dict) and "real" in pair and "imag" in pair:
            parsed.append(
                complex(float(Fraction(pair["real"])), float(Fraction(pair["imag"])))
            )
        else:
            parsed.append(complex(float(pair[0]), float(pair[1])))
    roots = np.asarray(parsed, dtype=np.complex128)
    if np.any(np.abs(roots) >= 1.0):
        raise ValueError(f"resume receipt {path} contains a root outside the unit disk")
    return roots


def factored_values(points: np.ndarray, roots: np.ndarray) -> np.ndarray:
    values = np.ones(points.shape, dtype=np.complex128)
    for root in roots:
        values *= points - root
    return values


def critical_hub_score(
    roots: np.ndarray, spoke_samples: int
) -> tuple[float, dict[str, object]]:
    """Return the least normalized cost of a two-root straight critical hub.

    For a critical point ``c`` and roots ``i,j``, the cost is the maximum of
    the sampled polynomial moduli on the two spokes and half their total
    Euclidean length.  Cost below one supplies a sampled path of length below
    two inside the strict lemniscate.  The routine checks every critical point
    and root pair; numerical output remains candidate evidence only.
    """

    coefficients = np.poly(roots)
    critical_points = np.roots(np.polyder(coefficients))
    parameters = np.linspace(0.0, 1.0, spoke_samples)
    best = math.inf
    best_row: dict[str, object] = {}
    for critical_index, critical in enumerate(critical_points):
        spokes = []
        for root_index, root in enumerate(roots):
            points = critical + parameters * (root - critical)
            moduli = np.abs(factored_values(points, roots))
            maximum_index = int(np.argmax(moduli))
            maximum_modulus = float(moduli[maximum_index])
            spokes.append(
                {
                    "root_index": root_index,
                    "maximum_sampled_modulus": maximum_modulus,
                    "argmax_sample_parameter": float(parameters[maximum_index]),
                    "length": float(abs(root - critical)),
                }
            )
        for left in range(len(roots)):
            for right in range(left + 1, len(roots)):
                cost = max(
                    spokes[left]["maximum_sampled_modulus"],
                    spokes[right]["maximum_sampled_modulus"],
                    (spokes[left]["length"] + spokes[right]["length"]) / 2.0,
                )
                if cost < best:
                    best = cost
                    best_row = {
                        "critical_index": critical_index,
                        "critical_point": [float(critical.real), float(critical.imag)],
                        "left": spokes[left],
                        "right": spokes[right],
                    }
    return best, best_row


def minimum_critical_straight_hub_score(
    roots: np.ndarray, spoke_samples: int
) -> tuple[float, dict[str, object]]:
    """Restrict the straight-spoke selector to the first critical-value level."""

    coefficients = np.poly(roots)
    critical_points = np.roots(np.polyder(coefficients))
    critical_moduli = np.abs(np.polyval(coefficients, critical_points))
    minimum_modulus = float(critical_moduli.min())
    tolerance = 1.0e-9 * max(1.0, minimum_modulus)
    selected_indices = [
        index
        for index, modulus in enumerate(critical_moduli)
        if float(modulus) <= minimum_modulus + tolerance
    ]
    parameters = np.linspace(0.0, 1.0, spoke_samples)
    best = math.inf
    best_row: dict[str, object] = {}
    for critical_index in selected_indices:
        critical = critical_points[critical_index]
        spokes = []
        for root_index, root in enumerate(roots):
            points = critical + parameters * (root - critical)
            moduli = np.abs(factored_values(points, roots))
            maximum_index = int(np.argmax(moduli))
            maximum_modulus = float(moduli[maximum_index])
            spokes.append(
                {
                    "root_index": root_index,
                    "maximum_sampled_modulus": maximum_modulus,
                    "argmax_sample_parameter": float(parameters[maximum_index]),
                    "length": float(abs(root - critical)),
                }
            )
        for left in range(len(roots)):
            for right in range(left + 1, len(roots)):
                cost = max(
                    spokes[left]["maximum_sampled_modulus"],
                    spokes[right]["maximum_sampled_modulus"],
                    (spokes[left]["length"] + spokes[right]["length"]) / 2.0,
                )
                if cost < best:
                    best = cost
                    best_row = {
                        "minimum_critical_value_modulus": minimum_modulus,
                        "simultaneous_first_critical_count": len(selected_indices),
                        "critical_index": critical_index,
                        "critical_point": [float(critical.real), float(critical.imag)],
                        "left": spokes[left],
                        "right": spokes[right],
                        "all_spokes": spokes,
                    }
    return best, best_row


def strict_minimum_critical_straight_hub_score(
    roots: np.ndarray, spoke_samples: int
) -> tuple[float, dict[str, object]]:
    """Charge both the straight-hub obstruction and strict critical ordering."""

    hub_score, hub = minimum_critical_straight_hub_score(roots, spoke_samples)
    coefficients = np.poly(roots)
    critical_points = np.roots(np.polyder(coefficients))
    critical_moduli = sorted(
        float(abs(value)) for value in np.polyval(coefficients, critical_points)
    )
    if len(critical_moduli) < 2 or critical_moduli[0] == 0.0:
        return -math.inf, {
            "minimum_critical_straight_hub": hub,
            "critical_ordering_accepted": False,
        }
    ordering_ratio = critical_moduli[1] / critical_moduli[0]
    return min(hub_score, ordering_ratio), {
        "minimum_critical_straight_hub": hub,
        "straight_hub_cost": hub_score,
        "smallest_critical_value_modulus": critical_moduli[0],
        "second_smallest_critical_value_modulus": critical_moduli[1],
        "critical_value_ordering_ratio": ordering_ratio,
        "critical_ordering_accepted": True,
    }


def balanced_origin_minimum_straight_hub_score(
    roots: np.ndarray, spoke_samples: int
) -> tuple[float, dict[str, object]]:
    """Jointly charge origin minimality and failure of every origin spoke pair.

    The generator must impose ``sum 1/root = 0``.  A score above one then means
    that the origin critical value is strictly smaller than every other
    critical value *and* no two origin spokes give a valid short hub.
    """

    coefficients = np.poly(roots)
    critical_points = np.roots(np.polyder(coefficients))
    origin_index = int(np.argmin(np.abs(critical_points)))
    origin_residual = float(abs(critical_points[origin_index]))
    origin_value_modulus = float(abs(np.polyval(coefficients, 0.0)))
    other_moduli = [
        float(abs(np.polyval(coefficients, point)))
        for index, point in enumerate(critical_points)
        if index != origin_index
    ]
    if origin_residual > 1.0e-6 or not other_moduli:
        return -math.inf, {
            "origin_critical_residual": origin_residual,
            "origin_balance_accepted": False,
        }
    ordering_ratio = min(other_moduli) / origin_value_modulus
    parameters = np.linspace(0.0, 1.0, spoke_samples)
    spokes = []
    for root_index, root in enumerate(roots):
        points = parameters * root
        moduli = np.abs(factored_values(points, roots))
        maximum_index = int(np.argmax(moduli))
        maximum_modulus = float(moduli[maximum_index])
        spokes.append(
            {
                "root_index": root_index,
                "maximum_sampled_modulus": maximum_modulus,
                "argmax_sample_parameter": float(parameters[maximum_index]),
                "length": float(abs(root)),
            }
        )
    best_hub_cost = math.inf
    best_pair: dict[str, object] = {}
    for left in range(len(roots)):
        for right in range(left + 1, len(roots)):
            cost = max(
                spokes[left]["maximum_sampled_modulus"],
                spokes[right]["maximum_sampled_modulus"],
                (spokes[left]["length"] + spokes[right]["length"]) / 2.0,
            )
            if cost < best_hub_cost:
                best_hub_cost = cost
                best_pair = {"left": spokes[left], "right": spokes[right]}
    score = min(best_hub_cost, ordering_ratio)
    return score, {
        "origin_critical_residual": origin_residual,
        "origin_balance_accepted": True,
        "origin_critical_value_modulus": origin_value_modulus,
        "smallest_other_critical_value_modulus": min(other_moduli),
        "critical_value_ordering_ratio": ordering_ratio,
        "best_origin_two_spoke_cost": best_hub_cost,
        "best_origin_pair": best_pair,
        "all_origin_spokes": spokes,
    }


def newton_branch_hub_score(
    roots: np.ndarray, flow_max_step: float
) -> tuple[float, dict[str, object]]:
    """Track the two descending inverse-image branches at every simple saddle.

    If ``v=f(c)`` and ``u`` runs from zero to one, a descending branch is
    parameterized by ``f(z(u))=(1-u^2)v``.  Hence

    ``z'(u) = -2uv/f'(z(u))``.

    Every exact point on a branch lies in the strict unit lemniscate whenever
    ``|v|<1`` and ``u>0``.  The reported score is half the least total arc
    length of the two branches from a common admissible simple critical point;
    score above one is a candidate obstruction to *all* such two-branch hubs.
    Numerical continuation remains candidate evidence, not a certificate.
    """

    coefficients = np.poly(roots)
    derivative = np.polyder(coefficients)
    second_derivative = np.polyder(derivative)
    critical_points = np.roots(derivative)
    start_u = 1.0e-5
    best = math.inf
    best_row: dict[str, object] = {}
    admissible_hubs: list[dict[str, object]] = []
    admissible_count = 0
    for critical_index, critical in enumerate(critical_points):
        critical_value = np.polyval(coefficients, critical)
        second_value = np.polyval(second_derivative, critical)
        if abs(critical_value) >= 1.0 or abs(second_value) < 1.0e-8:
            continue
        level_coefficients = coefficients.astype(np.complex128, copy=True)
        level_coefficients[-1] -= (1.0 - start_u**2) * critical_value
        start_candidates = sorted(
            np.roots(level_coefficients), key=lambda z: abs(z - critical)
        )[:2]
        branches: list[dict[str, object]] = []
        valid = True
        for start in start_candidates:
            def ode(u: float, state: np.ndarray) -> tuple[float, float, float]:
                point = state[0] + 1j * state[1]
                derivative_value = np.polyval(derivative, point)
                velocity = -2.0 * u * critical_value / derivative_value
                return float(velocity.real), float(velocity.imag), float(abs(velocity))

            solution = solve_ivp(
                ode,
                (start_u, 1.0),
                (start.real, start.imag, abs(start - critical)),
                rtol=2.0e-9,
                atol=2.0e-11,
                max_step=flow_max_step,
            )
            endpoint = solution.y[0, -1] + 1j * solution.y[1, -1]
            root_index = int(np.argmin(abs(roots - endpoint)))
            endpoint_error = float(abs(roots[root_index] - endpoint))
            sampled_points = solution.y[0] + 1j * solution.y[1]
            level_residual = np.abs(
                np.polyval(coefficients, sampled_points)
                - (1.0 - solution.t**2) * critical_value
            )
            maximum_level_residual = float(level_residual.max())
            valid = bool(
                valid
                and solution.success
                and endpoint_error < 1.0e-5
                and maximum_level_residual < 1.0e-6
            )
            branches.append(
                {
                    "root_index": root_index,
                    "length": float(solution.y[2, -1]),
                    "endpoint_error": endpoint_error,
                    "maximum_level_residual": maximum_level_residual,
                }
            )
        if not valid or branches[0]["root_index"] == branches[1]["root_index"]:
            continue
        admissible_count += 1
        total_length = float(branches[0]["length"] + branches[1]["length"])
        hub_row: dict[str, object] = {
            "critical_index": critical_index,
            "critical_point": [float(critical.real), float(critical.imag)],
            "critical_value_modulus": float(abs(critical_value)),
            "branches": branches,
            "total_length": total_length,
        }
        admissible_hubs.append(hub_row)
        if total_length / 2.0 < best:
            best = total_length / 2.0
            best_row = hub_row
    best_row = dict(best_row)
    best_row["admissible_simple_critical_hub_count"] = admissible_count
    best_row["all_admissible_simple_critical_hubs"] = sorted(
        admissible_hubs, key=lambda row: float(row["total_length"])
    )
    return best, best_row


def inverse_ray_aggregate_score(
    roots: np.ndarray, flow_max_step: float
) -> tuple[float, dict[str, object]]:
    """Return the normalized mean length over every admissible Newton hub.

    A score at least one is the numerical falsifier for the all-critical
    aggregate candidate ``sum_c L_c < 2h``.  Continuation and residual gates
    are inherited from :func:`newton_branch_hub_score`.
    """

    _, detail = newton_branch_hub_score(roots, flow_max_step)
    hubs = list(detail.get("all_admissible_simple_critical_hubs", []))
    if not hubs:
        return -math.inf, {
            "admissible_simple_critical_hub_count": 0,
            "all_admissible_simple_critical_hubs": [],
        }
    lengths = [float(hub["total_length"]) for hub in hubs]
    total_length = sum(lengths)
    normalized_average = total_length / (2.0 * len(hubs))
    return normalized_average, {
        "admissible_simple_critical_hub_count": len(hubs),
        "total_inverse_ray_edge_length": total_length,
        "normalized_average_length": normalized_average,
        "minimum_edge_length": min(lengths),
        "maximum_edge_length": max(lengths),
        "all_admissible_simple_critical_hubs": hubs,
    }


def minimum_critical_newton_hub_score(
    roots: np.ndarray, flow_max_step: float
) -> tuple[float, dict[str, object]]:
    """Measure the Newton hub at the first admissible critical-value level.

    Generic polynomials have distinct critical-value moduli.  In that case the
    selected hub is the first merge of two root components as the lemniscate
    level grows from zero.  For numerical ties we retain the shortest hub among
    values equal to the minimum up to a scale-aware tolerance; this matches the
    existential selector available at an exactly simultaneous first merge.
    """

    _, detail = newton_branch_hub_score(roots, flow_max_step)
    hubs = list(detail.get("all_admissible_simple_critical_hubs", []))
    if not hubs:
        return -math.inf, {
            "admissible_simple_critical_hub_count": 0,
            "all_admissible_simple_critical_hubs": [],
        }
    minimum_modulus = min(float(hub["critical_value_modulus"]) for hub in hubs)
    tolerance = 1.0e-9 * max(1.0, minimum_modulus)
    first_hubs = [
        hub
        for hub in hubs
        if float(hub["critical_value_modulus"]) <= minimum_modulus + tolerance
    ]
    selected = min(first_hubs, key=lambda hub: float(hub["total_length"]))
    return float(selected["total_length"]) / 2.0, {
        "minimum_critical_value_modulus": minimum_modulus,
        "simultaneous_first_hub_count": len(first_hubs),
        "selected_first_merge_hub": selected,
        "admissible_simple_critical_hub_count": len(hubs),
        "all_admissible_simple_critical_hubs": hubs,
    }


def scale_normalized_minimum_critical_newton_hub_score(
    roots: np.ndarray, flow_max_step: float
) -> tuple[float, dict[str, object]]:
    """Charge the first-merge length after scaling the outermost root to one."""

    _, detail = minimum_critical_newton_hub_score(roots, flow_max_step)
    selected = detail.get("selected_first_merge_hub")
    if not isinstance(selected, dict):
        return -math.inf, detail
    root_radius = float(np.abs(roots).max())
    total_length = float(selected["total_length"])
    normalized_length = total_length / (2.0 * root_radius)
    return normalized_length, {
        **detail,
        "maximum_root_modulus": root_radius,
        "scale_normalized_first_merge_length": normalized_length,
    }


def critical_scale_normalized_minimum_critical_newton_hub_score(
    roots: np.ndarray, flow_max_step: float
) -> tuple[float, dict[str, object]]:
    """Charge first-merge length against ``2*|f(c)|^(1/n)``.

    Minimum-critical ordering and the discriminant/Fekete sandwich prove that
    this critical scale is at most the maximum root modulus.  Consequently the
    objective tests a strictly stronger analytic completion than the closed-
    disk scale-normalized objective.  A crossing kills only the stronger
    completion; it does not kill the ``2R`` theorem needed for Erdős #1041.
    """

    _, detail = minimum_critical_newton_hub_score(roots, flow_max_step)
    selected = detail.get("selected_first_merge_hub")
    if not isinstance(selected, dict):
        return -math.inf, detail
    degree = len(roots)
    minimum_modulus = float(detail["minimum_critical_value_modulus"])
    if minimum_modulus <= 0.0:
        return -math.inf, detail
    critical_scale = minimum_modulus ** (1.0 / degree)
    total_length = float(selected["total_length"])
    normalized_length = total_length / (2.0 * critical_scale)
    return normalized_length, {
        **detail,
        "critical_geometric_mean_scale": critical_scale,
        "critical_scale_normalized_first_merge_length": normalized_length,
    }


def newton_branch_probe_contract(
    *, degree: int, trials: int, score: float
) -> dict[str, object]:
    candidate_found = bool(score > 1.0)
    return build_experiment_contract(
        problem_id="erdos_1041",
        target_statement=(
            "Find two roots joined by a curve of length less than two inside "
            "the strict unit lemniscate."
        ),
        claim_ceiling=(
            "Numerical inverse-ray continuation is candidate evidence only. A "
            "score above one must be exactified; a score below one proves nothing "
            "outside the sampled configurations."
        ),
        hypothesis_id="some_simple_critical_point_has_short_newton_hub",
        hypothesis_statement=(
            "Some simple critical point with |f(c)|<1 has two descending "
            "inverse-ray branches to distinct roots with total length below two."
        ),
        probe_id="random_all_critical_point_inverse_ray_continuation",
        probe_question=(
            "Can every admissible simple critical hub in one sampled polynomial "
            "be forced to total length at least two?"
        ),
        computation=(
            "Continue both local inverse-ray branches at every admissible simple "
            "critical point and maximize the minimum normalized hub length over "
            "the sampled root configurations."
        ),
        falsifier=(
            "A validated objective score above one, meaning every admissible "
            "simple critical hub in that candidate has total length above two."
        ),
        stop_condition=(
            "Exactify the first score above one; otherwise stop at the declared "
            "trial bound and use the all-critical hub table to select an analytic "
            "critical-point selection principle."
        ),
        survival_consequence=(
            "Search for an averaged or extremal selection theorem over critical "
            "points, especially near the degenerate regular-polygon boundary."
        ),
        falsification_consequence=(
            "An exactified candidate would eliminate all simple two-branch Newton "
            "hubs and force global component/Reeb geometry."
        ),
        consumer_ref=RESEARCH_REF,
        analysis_refs=[NEWTON_BRANCH_ANALYSIS_REF],
        source_refs=[SOURCE_REF],
        result_status="finite_counterexample" if candidate_found else "finite_support",
        result_summary=(
            f"Bounded degree-{degree} search over {trials} samples produced maximum "
            f"normalized minimum hub score {score:.12g}; "
            + ("a candidate requires exactification." if candidate_found else "no obstruction candidate was found.")
        ),
        resource_bounds={"degree": degree, "trials": trials},
        progress_class="inconclusive",
        decision_basis=(
            "The run maps all critical hubs in its finite sample but has no proof "
            "authority in either direction."
        ),
        next_analytic_target=(
            "Control the minimum two-branch length across all critical points, with "
            "separate treatment of multiple-critical regular-polygon limits."
        ),
    )


def inverse_ray_aggregate_probe_contract(
    *, degree: int, trials: int, score: float
) -> dict[str, object]:
    candidate_found = bool(score >= 1.0)
    return build_experiment_contract(
        problem_id="erdos_1041",
        target_statement=(
            "Find two roots joined by a curve of length less than two inside "
            "the strict unit lemniscate."
        ),
        claim_ceiling=(
            "Adversarial numerical continuation is candidate evidence only. A "
            "normalized aggregate at least one must be exactified before it "
            "eliminates the aggregate mechanism."
        ),
        hypothesis_id="all_critical_inverse_ray_average_below_two",
        hypothesis_statement=(
            "The sum of all admissible two-branch inverse-ray edge lengths is "
            "strictly less than twice the number of those critical hubs."
        ),
        probe_id="elite_mutation_inverse_ray_aggregate_adversary",
        probe_question=(
            "Can direct optimization of the complete critical-tree average "
            "cross its sharp normalized threshold one?"
        ),
        computation=(
            "Mix global root restarts with mutations of the current aggregate "
            "maximizer, recomputing every admissible simple critical hub and "
            "retaining each improving configuration atomically."
        ),
        falsifier=(
            "One residual-gated configuration with normalized aggregate at "
            "least one; exactify that first candidate before mathematical use."
        ),
        stop_condition=(
            "Stop at the declared trial bound or the first threshold crossing. "
            "Do not count a subthreshold best score as mathematical progress."
        ),
        survival_consequence=(
            "No theorem follows. Rotate to an edge-disjoint or multiplicity-aware "
            "Reeb charge rather than merely increasing the sample horizon."
        ),
        falsification_consequence=(
            "Exactify the candidate and abandon every unweighted all-critical "
            "average-selection proof."
        ),
        consumer_ref=RESEARCH_REF,
        analysis_refs=[INVERSE_RAY_AGGREGATE_ANALYSIS_REF],
        source_refs=[SOURCE_REF],
        result_status=(
            "finite_counterexample"
            if candidate_found
            else "finite_support"
        ),
        result_summary=(
            f"The degree-{degree} adversarial run over {trials} trials reached "
            f"normalized aggregate {score:.12g}; "
            + (
                "the first threshold candidate requires exactification."
                if candidate_found
                else "the threshold was not crossed and no theorem is claimed."
            )
        ),
        resource_bounds={"degree": degree, "trials": max(1, trials)},
        progress_class="inconclusive",
        decision_basis=(
            "This optimizes the complete-tree aggregate directly, rather than "
            "reusing the already eliminated metric-selected pointwise hub."
        ),
        next_analytic_target=(
            "If subthreshold, seek an edge-disjoint Reeb charge with critical-ray "
            "multiplicity divided out; if superthreshold, exactify immediately."
        ),
    )


def minimum_critical_newton_hub_probe_contract(
    *, degree: int, trials: int, score: float
) -> dict[str, object]:
    candidate_found = bool(score > 1.0)
    return build_experiment_contract(
        problem_id="erdos_1041",
        target_statement=(
            "Find two roots joined by a curve of length less than two inside "
            "the strict unit lemniscate."
        ),
        claim_ceiling=(
            "Numerical inverse-ray continuation is candidate evidence only. A "
            "score above one must be exactified before it refutes the first-merge "
            "metric hypothesis."
        ),
        hypothesis_id="minimum_critical_value_newton_hub_is_short",
        hypothesis_statement=(
            "At a critical point of minimum critical-value modulus, the two "
            "descending inverse-ray branches have combined length below two."
        ),
        probe_id="minimum_critical_value_inverse_ray_adversary",
        probe_question=(
            "Can the canonical first lemniscate merge have total descending "
            "branch length greater than two?"
        ),
        computation=(
            "Continue both inverse-ray branches at every admissible simple "
            "critical point, select the minimum critical-value level, and "
            "maximize half its total branch length over root configurations."
        ),
        falsifier=(
            "A residual-gated configuration with objective score above one; "
            "exactify its critical ordering and branch-length lower bound."
        ),
        stop_condition=(
            "Stop at the first robust threshold crossing or the declared trial "
            "bound; do not promote a subthreshold search maximum to a theorem."
        ),
        survival_consequence=(
            "Prove the first-merge topological reduction and attack only its "
            "two-branch metric bound, preserving data-dependent strict slack."
        ),
        falsification_consequence=(
            "Abandon minimum-critical selection and return to a weighted "
            "all-critical edge charge or a non-Newton path."
        ),
        consumer_ref=RESEARCH_REF,
        analysis_refs=[INVERSE_RAY_AGGREGATE_ANALYSIS_REF],
        source_refs=[SOURCE_REF],
        result_status="finite_counterexample" if candidate_found else "finite_support",
        result_summary=(
            f"The degree-{degree} adversarial run over {trials} trials reached "
            f"normalized first-merge length {score:.12g}; "
            + (
                "the threshold candidate requires exactification."
                if candidate_found
                else "the threshold was not crossed and no theorem is claimed."
            )
        ),
        resource_bounds={"degree": degree, "trials": max(1, trials)},
        progress_class="inconclusive",
        decision_basis=(
            "This isolates the first critical-value merge instead of choosing a "
            "metric-favourable or globally shortest critical point."
        ),
        next_analytic_target=(
            "If subthreshold, bound the two conformal inverse branches in the "
            "two one-root components meeting at the first critical level."
        ),
    )


def scale_normalized_minimum_critical_newton_hub_probe_contract(
    *, degree: int, trials: int, score: float
) -> dict[str, object]:
    candidate_found = bool(score > 1.0)
    return build_experiment_contract(
        problem_id="erdos_1041",
        target_statement=(
            "Find two roots joined by a curve of length less than two inside "
            "the strict unit lemniscate."
        ),
        claim_ceiling=(
            "Numerical inverse-ray continuation is candidate evidence only. A "
            "scale-normalized score above one must be exactified."
        ),
        hypothesis_id="closed_disk_first_merge_newton_length_at_most_two",
        hypothesis_statement=(
            "For roots in the closed unit disk, the two descending branches at "
            "a minimum-modulus critical value have total length at most two."
        ),
        probe_id="scale_normalized_first_merge_inverse_ray_adversary",
        probe_question=(
            "After scaling the outermost root to the unit circle, can the first "
            "Newton hub exceed total length two?"
        ),
        computation=(
            "Divide the numerically continued first-merge total length by twice "
            "the maximum root modulus and maximize the ratio."
        ),
        falsifier=(
            "A residual-gated normalized score above one, followed by exact "
            "critical ordering and branch-length certification."
        ),
        stop_condition=(
            "Exactify the first robust crossing; otherwise stop at the declared "
            "trial bound and attack the closed-disk inequality analytically."
        ),
        survival_consequence=(
            "Prove the closed-disk non-strict bound. Uniform scaling back by the "
            "strict maximum root modulus then solves the generic open-disk case."
        ),
        falsification_consequence=(
            "Abandon the canonical first-merge Newton curve and select a later "
            "critical point or a non-Newton path."
        ),
        consumer_ref=RESEARCH_REF,
        analysis_refs=[INVERSE_RAY_AGGREGATE_ANALYSIS_REF],
        source_refs=[SOURCE_REF],
        result_status="finite_counterexample" if candidate_found else "finite_support",
        result_summary=(
            f"The degree-{degree} scale-normalized run over {trials} trials "
            f"reached score {score:.12g}; "
            + (
                "the candidate requires exactification."
                if candidate_found
                else "the threshold was not crossed."
            )
        ),
        resource_bounds={"degree": degree, "trials": max(1, trials)},
        progress_class="inconclusive",
        decision_basis=(
            "Uniform root scaling preserves critical ordering and rescales the "
            "entire inverse-ray geometry, so this is the theorem's natural ratio."
        ),
        next_analytic_target=(
            "Bound the two first-merge inverse branches in the closed unit disk "
            "by the diameter two, with equality only in a boundary degeneration."
        ),
    )


def critical_scale_normalized_minimum_critical_newton_hub_probe_contract(
    *, degree: int, trials: int, score: float
) -> dict[str, object]:
    candidate_found = bool(score > 1.0)
    return build_experiment_contract(
        problem_id="erdos_1041",
        target_statement=(
            "Find two roots joined by a curve of length less than two inside "
            "the strict unit lemniscate."
        ),
        claim_ceiling=(
            "Numerical inverse-ray continuation is candidate evidence only. A "
            "critical-scale score above one refutes only the stronger "
            "L_1+L_2<=2|f(c)|^(1/n) completion after exactification."
        ),
        hypothesis_id="first_merge_newton_length_at_most_two_critical_scales",
        hypothesis_statement=(
            "At a minimum-modulus critical value, the two descending branches "
            "have total length at most 2|f(c)|^(1/n)."
        ),
        probe_id="critical_scale_first_merge_inverse_ray_adversary",
        probe_question=(
            "Can the first Newton hub exceed twice the geometric mean of the "
            "root distances from its critical point?"
        ),
        computation=(
            "Divide the residual-gated first-merge total length by "
            "2|f(c)|^(1/n) and maximize the ratio."
        ),
        falsifier=(
            "A robust score above one, followed by exact critical ordering and "
            "a certified branch-length lower bound."
        ),
        stop_condition=(
            "Exactify the first robust crossing; otherwise stop at the declared "
            "trial bound and retain only finite support."
        ),
        survival_consequence=(
            "Attack the stronger critical-scale theorem. The discriminant/Fekete "
            "sandwich then implies the solution-producing 2R theorem."
        ),
        falsification_consequence=(
            "Retain the weaker scale-normalized 2R theorem; a critical-scale "
            "crossing does not refute Erdős #1041 or the canonical first merge."
        ),
        consumer_ref=RESEARCH_REF,
        analysis_refs=[NEWTON_BRANCH_ANALYSIS_REF],
        source_refs=[SOURCE_REF],
        result_status="finite_counterexample" if candidate_found else "finite_support",
        result_summary=(
            f"The degree-{degree} critical-scale run over {trials} trials "
            f"reached score {score:.12g}; "
            + (
                "the stronger completion candidate requires exactification."
                if candidate_found
                else "the stronger threshold was not crossed."
            )
        ),
        resource_bounds={"degree": degree, "trials": max(1, trials)},
        progress_class="inconclusive",
        decision_basis=(
            "Minimum-critical ordering proves |f(c)|^(1/n) is no larger than "
            "the outer root radius, so this cleanly separates strong and weak "
            "metric completions."
        ),
        next_analytic_target=(
            "Either prove the critical-scale branch bound or use a crossing to "
            "focus exclusively on the weaker 2R inequality."
        ),
    )


def critical_hub_probe_contract(
    *, degree: int, trials: int, score: float
) -> dict[str, object]:
    candidate_found = bool(score > 1.0)
    return build_experiment_contract(
        problem_id="erdos_1041",
        target_statement=(
            "Find two roots joined by a curve of length less than two inside "
            "the strict unit lemniscate."
        ),
        claim_ceiling=(
            "Sampled straight spokes are candidate evidence only. A score above "
            "one requires exact containment and length certification; a score "
            "below one proves nothing outside the sampled configurations."
        ),
        hypothesis_id="some_critical_point_has_two_short_contained_straight_spokes",
        hypothesis_statement=(
            "Some critical point has two straight spokes to distinct roots that "
            "remain in the strict lemniscate and have total length below two."
        ),
        probe_id="random_all_critical_point_straight_spoke_scan",
        probe_question=(
            "Can every critical point in one sampled polynomial be denied a "
            "two-root straight-spoke hub?"
        ),
        computation=(
            "Sample every root spoke from every critical point and maximize the "
            "minimum of spoke modulus and normalized total length."
        ),
        falsifier=(
            "A validated score above one, meaning every critical/root pair fails "
            "containment or the strict length-two bound."
        ),
        stop_condition=(
            "Exactify the first score above one; otherwise stop at the declared "
            "trial bound and retain the run only as route-selection evidence."
        ),
        survival_consequence=(
            "Seek an all-critical selection theorem with a data-dependent strict "
            "margin; boundary-near regular polygons preclude uniform slack."
        ),
        falsification_consequence=(
            "An exactified candidate would eliminate all adaptive straight "
            "critical hubs and force curved or global component geometry."
        ),
        consumer_ref=RESEARCH_REF,
        analysis_refs=[STRAIGHT_HUB_ANALYSIS_REF],
        source_refs=[SOURCE_REF],
        result_status="finite_counterexample" if candidate_found else "finite_support",
        result_summary=(
            f"Bounded degree-{degree} search over {trials} completed samples has "
            f"best normalized minimum straight-hub score {score:.12g}; "
            + ("a candidate requires exactification." if candidate_found else "no obstruction candidate was found.")
        ),
        resource_bounds={"degree": degree, "trials": max(1, trials)},
        progress_class="inconclusive",
        decision_basis=(
            "The run maps every critical/root pair in its finite sample but has "
            "no proof authority in either direction."
        ),
        next_analytic_target=(
            "Control the best critical hub across all critical points while "
            "preserving the data-dependent strict slack."
        ),
    )


def minimum_critical_straight_hub_probe_contract(
    *, degree: int, trials: int, score: float
) -> dict[str, object]:
    candidate_found = bool(score > 1.0)
    return build_experiment_contract(
        problem_id="erdos_1041",
        target_statement=(
            "Find two roots joined by a curve of length less than two inside "
            "the strict unit lemniscate."
        ),
        claim_ceiling=(
            "Sampled straight spokes are candidate evidence only. A score above "
            "one requires exact containment and length certification."
        ),
        hypothesis_id="minimum_critical_value_has_two_short_contained_spokes",
        hypothesis_statement=(
            "A critical point at the first critical-value level has two straight "
            "spokes to distinct roots inside the strict lemniscate with total "
            "length below two."
        ),
        probe_id="minimum_critical_value_straight_spoke_adversary",
        probe_question=(
            "Can every hub at the first lemniscate merge be denied two short "
            "contained straight spokes?"
        ),
        computation=(
            "Select all numerically tied minimum-modulus critical values, sample "
            "every root spoke, and maximize the cheapest normalized two-spoke cost."
        ),
        falsifier=(
            "A validated score above one at every minimum-modulus critical point."
        ),
        stop_condition=(
            "Exactify the first robust crossing; otherwise stop at the declared "
            "trial bound and retain only finite support."
        ),
        survival_consequence=(
            "Combine the first-merge reduction with the logarithmic-balance metric "
            "theorem and prove containment for a selected pair."
        ),
        falsification_consequence=(
            "Retain the first-merge topology but use curved paths or select a later "
            "critical point."
        ),
        consumer_ref=RESEARCH_REF,
        analysis_refs=[STRAIGHT_HUB_ANALYSIS_REF],
        source_refs=[SOURCE_REF],
        result_status="finite_counterexample" if candidate_found else "finite_support",
        result_summary=(
            f"The degree-{degree} run over {trials} trials reached normalized "
            f"minimum-critical straight-hub score {score:.12g}; "
            + (
                "the threshold candidate requires exactification."
                if candidate_found
                else "the threshold was not crossed and no theorem is claimed."
            )
        ),
        resource_bounds={"degree": degree, "trials": max(1, trials)},
        progress_class="inconclusive",
        decision_basis=(
            "This is the exact straight-path completion of the canonical "
            "first-merge reduction."
        ),
        next_analytic_target=(
            "Relate minimum critical-value ordering to the maximum modulus on "
            "the two logarithmically closest root spokes."
        ),
    )


def balanced_origin_minimum_straight_hub_probe_contract(
    *, degree: int, trials: int, score: float
) -> dict[str, object]:
    candidate_found = bool(score > 1.0)
    return build_experiment_contract(
        problem_id="erdos_1041",
        target_statement=(
            "Find two roots joined by a curve of length less than two inside "
            "the strict unit lemniscate."
        ),
        claim_ceiling=(
            "The reciprocal-balance generator makes zero a numerical critical "
            "point, but a threshold crossing still requires exact rational "
            "critical-value ordering and spoke-waypoint certificates."
        ),
        hypothesis_id="minimum_critical_origin_has_two_short_contained_spokes",
        hypothesis_statement=(
            "When zero is the strict minimum-modulus critical point, two root "
            "spokes from zero form a path of length below two in the lemniscate."
        ),
        probe_id="balanced_origin_joint_ordering_and_spoke_adversary",
        probe_question=(
            "Can reciprocal-balanced roots make zero strictly first while every "
            "two-spoke origin hub fails?"
        ),
        computation=(
            "Charge the minimum of the other/origin critical-value modulus ratio "
            "and the cheapest normalized origin two-spoke cost."
        ),
        falsifier=(
            "A score above one, followed by an exact certificate for both charged "
            "inequalities."
        ),
        stop_condition=(
            "Exactify the first robust crossing; otherwise stop at the declared "
            "trial bound."
        ),
        survival_consequence=(
            "Origin balance does not expose a simple exact obstruction; retain "
            "algebraic critical-point isolation for the unconstrained candidate."
        ),
        falsification_consequence=(
            "Eliminate the straight first-merge completion with a rationally "
            "anchored critical point and continue only with curved branches."
        ),
        consumer_ref=RESEARCH_REF,
        analysis_refs=[STRAIGHT_HUB_ANALYSIS_REF],
        source_refs=[SOURCE_REF],
        result_status="finite_counterexample" if candidate_found else "finite_support",
        result_summary=(
            f"The degree-{degree} reciprocal-balanced run over {trials} trials "
            f"reached joint score {score:.12g}; "
            + (
                "the candidate requires exactification."
                if candidate_found
                else "the threshold was not crossed."
            )
        ),
        resource_bounds={"degree": degree, "trials": max(1, trials)},
        progress_class="inconclusive",
        decision_basis=(
            "A crossing simultaneously certifies the two numerical conditions "
            "needed for an origin-anchored mechanism counterexample."
        ),
        next_analytic_target=(
            "Rationalize the first n-1 roots, define the last by reciprocal "
            "balance, and certify all remaining derivative roots."
        ),
    )


def atomic_write_json(path: Path, payload: dict[str, object]) -> None:
    """Replace a durable best-so-far receipt without exposing partial JSON."""

    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.tmp")
    temporary.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    temporary.replace(path)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--degree", type=int, default=5)
    parser.add_argument("--trials", type=int, default=500)
    parser.add_argument("--grid-size", type=int, default=161)
    parser.add_argument("--radius", type=float, default=1.6)
    parser.add_argument("--seed", type=int, default=1041)
    parser.add_argument(
        "--objective",
        choices=(
            "grid-path",
            "critical-hub",
            "minimum-critical-straight-hub",
            "strict-minimum-critical-straight-hub",
            "balanced-origin-minimum-straight-hub",
            "newton-branch-hub",
            "minimum-critical-newton-hub",
            "scale-normalized-minimum-critical-newton-hub",
            "critical-scale-normalized-minimum-critical-newton-hub",
            "inverse-ray-aggregate",
        ),
        default="grid-path",
    )
    parser.add_argument("--spoke-samples", type=int, default=257)
    parser.add_argument("--flow-max-step", type=float, default=0.01)
    parser.add_argument(
        "--regular-perturbation-scale",
        type=float,
        help="sample only perturbations of a boundary-near regular polygon",
    )
    parser.add_argument(
        "--common-radius",
        type=float,
        help=(
            "after each restart or mutation, project every root direction to "
            "this common radius in (0,1); useful for isolating angular geometry"
        ),
    )
    parser.add_argument(
        "--balance-critical-origin",
        action="store_true",
        help=(
            "replace the last root so that the reciprocal-root sum vanishes, "
            "then scale all roots to the requested maximum radius"
        ),
    )
    parser.add_argument(
        "--balanced-max-radius",
        type=float,
        default=0.999999,
        help="maximum root modulus after --balance-critical-origin (default: 0.999999)",
    )
    parser.add_argument(
        "--output",
        type=Path,
        help=(
            "atomically persist every improving best-so-far candidate and the "
            "terminal or interrupted run status"
        ),
    )
    parser.add_argument(
        "--resume-from",
        type=Path,
        help="seed the search from the roots in a prior atomic search receipt",
    )
    parser.add_argument(
        "--elite-mutation-probability",
        type=float,
        default=0.0,
        help="probability that a trial mutates the current best roots instead of restarting",
    )
    parser.add_argument(
        "--mutation-scale",
        type=float,
        default=0.03,
        help="complex Gaussian scale used by elite-mutation trials",
    )
    args = parser.parse_args()

    rng = np.random.default_rng(args.seed)
    if args.spoke_samples < 3:
        parser.error("--spoke-samples must be at least three")
    if not 0.0 < args.flow_max_step <= 0.1:
        parser.error("--flow-max-step must lie in (0, 0.1]")
    if not 0.0 <= args.elite_mutation_probability <= 1.0:
        parser.error("--elite-mutation-probability must lie in [0, 1]")
    if not 0.0 < args.mutation_scale < 1.0:
        parser.error("--mutation-scale must lie in (0, 1)")
    if args.common_radius is not None and not 0.0 < args.common_radius < 1.0:
        parser.error("--common-radius must lie in (0, 1)")
    if not 0.0 < args.balanced_max_radius < 1.0:
        parser.error("--balanced-max-radius must lie in (0, 1)")
    if args.balance_critical_origin and args.common_radius is not None:
        parser.error("--balance-critical-origin and --common-radius are incompatible")
    if (
        args.objective == "balanced-origin-minimum-straight-hub"
        and not args.balance_critical_origin
    ):
        parser.error(
            "balanced-origin-minimum-straight-hub requires --balance-critical-origin"
        )
    grid = make_grid(args.radius, args.grid_size) if args.objective == "grid-path" else None
    best_score = -math.inf
    best_roots: np.ndarray | None = None
    best_groups: list[list[int]] = []
    best_detail: dict[str, object] = {}
    completed_trials = 0
    resumed_roots = (
        roots_from_receipt(args.resume_from, args.degree)
        if args.resume_from is not None
        else None
    )

    def snapshot(status: str) -> dict[str, object]:
        payload: dict[str, object] = {
            "schema": "erdos1041-structural-candidate-search/1",
            "status": status,
            "claim_ceiling": (
                "Numerical candidate reconnaissance only; no sampled score is a "
                "continuous-geometric certificate or an Erdős #1041 result."
            ),
            "parameters": {
                "degree": args.degree,
                "requested_trials": args.trials,
                "completed_trials": completed_trials,
                "grid_size": args.grid_size,
                "radius": args.radius,
                "seed": args.seed,
                "objective": args.objective,
                "spoke_samples": args.spoke_samples,
                "flow_max_step": args.flow_max_step,
                "regular_perturbation_scale": args.regular_perturbation_scale,
                "common_radius": args.common_radius,
                "balance_critical_origin": args.balance_critical_origin,
                "balanced_max_radius": args.balanced_max_radius,
                "resume_from": (
                    None if args.resume_from is None else str(args.resume_from)
                ),
                "elite_mutation_probability": args.elite_mutation_probability,
                "mutation_scale": args.mutation_scale,
            },
            "objective_score": best_score,
            "root_groups": best_groups,
            **best_detail,
            "roots": (
                []
                if best_roots is None
                else [[float(z.real), float(z.imag)] for z in best_roots]
            ),
            "links": {
                "source_ref": SOURCE_REF,
                "research_ref": RESEARCH_REF,
                "analysis_ref": (
                    INVERSE_RAY_AGGREGATE_ANALYSIS_REF
                    if args.objective == "inverse-ray-aggregate"
                    else (
                        NEWTON_BRANCH_ANALYSIS_REF
                        if args.objective in (
                            "newton-branch-hub",
                            "minimum-critical-newton-hub",
                            "scale-normalized-minimum-critical-newton-hub",
                            "critical-scale-normalized-minimum-critical-newton-hub",
                        )
                        else STRAIGHT_HUB_ANALYSIS_REF
                    )
                ),
            },
        }
        if best_roots is not None and args.objective == "newton-branch-hub":
            payload["experiment_contract"] = newton_branch_probe_contract(
                degree=args.degree,
                trials=completed_trials,
                score=best_score,
            )
        elif (
            best_roots is not None
            and args.objective == "minimum-critical-newton-hub"
        ):
            payload["experiment_contract"] = minimum_critical_newton_hub_probe_contract(
                degree=args.degree,
                trials=completed_trials,
                score=best_score,
            )
        elif (
            best_roots is not None
            and args.objective == "scale-normalized-minimum-critical-newton-hub"
        ):
            payload["experiment_contract"] = scale_normalized_minimum_critical_newton_hub_probe_contract(
                degree=args.degree,
                trials=completed_trials,
                score=best_score,
            )
        elif (
            best_roots is not None
            and args.objective
            == "critical-scale-normalized-minimum-critical-newton-hub"
        ):
            payload["experiment_contract"] = critical_scale_normalized_minimum_critical_newton_hub_probe_contract(
                degree=args.degree,
                trials=completed_trials,
                score=best_score,
            )
        elif best_roots is not None and args.objective == "inverse-ray-aggregate":
            payload["experiment_contract"] = inverse_ray_aggregate_probe_contract(
                degree=args.degree,
                trials=completed_trials,
                score=best_score,
            )
        elif best_roots is not None and args.objective == "critical-hub":
            payload["experiment_contract"] = critical_hub_probe_contract(
                degree=args.degree,
                trials=completed_trials,
                score=best_score,
            )
        elif (
            best_roots is not None
            and args.objective in (
                "minimum-critical-straight-hub",
                "strict-minimum-critical-straight-hub",
            )
        ):
            payload["experiment_contract"] = minimum_critical_straight_hub_probe_contract(
                degree=args.degree,
                trials=completed_trials,
                score=best_score,
            )
        elif (
            best_roots is not None
            and args.objective == "balanced-origin-minimum-straight-hub"
        ):
            payload["experiment_contract"] = balanced_origin_minimum_straight_hub_probe_contract(
                degree=args.degree,
                trials=completed_trials,
                score=best_score,
            )
        return payload

    interrupted = False
    try:
        for trial in range(args.trials):
            if trial == 0 and resumed_roots is not None:
                roots = resumed_roots.copy()
            elif (
                best_roots is not None
                and rng.random() < args.elite_mutation_probability
            ):
                roots = mutate_roots(rng, best_roots, args.mutation_scale)
            else:
                roots = (
                    perturbed_regular_roots(
                        rng, args.degree, args.regular_perturbation_scale
                    )
                    if args.regular_perturbation_scale is not None
                    else random_roots(rng, args.degree)
                )
            if args.common_radius is not None:
                moduli = np.abs(roots)
                if np.any(moduli == 0.0):
                    continue
                roots = args.common_radius * roots / moduli
            if args.balance_critical_origin:
                if np.any(np.abs(roots[:-1]) < 1.0e-10):
                    continue
                reciprocal_sum = np.sum(1.0 / roots[:-1])
                if abs(reciprocal_sum) < 1.0e-10:
                    continue
                roots[-1] = -1.0 / reciprocal_sum
                largest_modulus = float(np.abs(roots).max())
                roots *= args.balanced_max_radius / largest_modulus
            if args.objective == "grid-path":
                assert grid is not None
                candidate_score, groups = score(grid, roots)
                detail: dict[str, object] = {"root_groups": groups}
            elif args.objective == "critical-hub":
                candidate_score, hub = critical_hub_score(roots, args.spoke_samples)
                groups = []
                detail = {"best_two_spoke_hub": hub}
            elif args.objective == "minimum-critical-straight-hub":
                candidate_score, hub = minimum_critical_straight_hub_score(
                    roots, args.spoke_samples
                )
                groups = []
                detail = {"minimum_critical_straight_hub": hub}
            elif args.objective == "strict-minimum-critical-straight-hub":
                candidate_score, hub = strict_minimum_critical_straight_hub_score(
                    roots, args.spoke_samples
                )
                groups = []
                detail = {"strict_minimum_critical_straight_hub": hub}
            elif args.objective == "balanced-origin-minimum-straight-hub":
                candidate_score, hub = balanced_origin_minimum_straight_hub_score(
                    roots, args.spoke_samples
                )
                groups = []
                detail = {"balanced_origin_minimum_straight_hub": hub}
            elif args.objective == "newton-branch-hub":
                candidate_score, hub = newton_branch_hub_score(roots, args.flow_max_step)
                groups = []
                detail = {"best_two_branch_newton_hub": hub}
            elif args.objective == "minimum-critical-newton-hub":
                candidate_score, hub = minimum_critical_newton_hub_score(
                    roots, args.flow_max_step
                )
                groups = []
                detail = {"minimum_critical_newton_hub": hub}
            elif args.objective == "scale-normalized-minimum-critical-newton-hub":
                candidate_score, hub = scale_normalized_minimum_critical_newton_hub_score(
                    roots, args.flow_max_step
                )
                groups = []
                detail = {"scale_normalized_minimum_critical_newton_hub": hub}
            elif (
                args.objective
                == "critical-scale-normalized-minimum-critical-newton-hub"
            ):
                candidate_score, hub = critical_scale_normalized_minimum_critical_newton_hub_score(
                    roots, args.flow_max_step
                )
                groups = []
                detail = {
                    "critical_scale_normalized_minimum_critical_newton_hub": hub
                }
            else:
                candidate_score, aggregate = inverse_ray_aggregate_score(
                    roots, args.flow_max_step
                )
                groups = []
                detail = {"inverse_ray_aggregate": aggregate}
            completed_trials = trial + 1
            if candidate_score > best_score:
                best_score = candidate_score
                best_roots = roots.copy()
                best_groups = groups
                best_detail = detail
                current = snapshot("running_best_so_far_candidate_only")
                if args.output is not None:
                    atomic_write_json(args.output, current)
                print(
                    json.dumps(
                        {
                            "status": current["status"],
                            "completed_trials": completed_trials,
                            "objective_score": best_score,
                            "output": None if args.output is None else str(args.output),
                        }
                    ),
                    flush=True,
                )
    except KeyboardInterrupt:
        interrupted = True

    if best_roots is None:
        if args.output is not None:
            atomic_write_json(args.output, snapshot("no_candidate_completed"))
        return 1
    final_status = (
        "interrupted_best_so_far_candidate_only"
        if interrupted
        else "completed_candidate_only_not_a_certificate"
    )
    final = snapshot(final_status)
    if args.output is not None:
        atomic_write_json(args.output, final)
        print(
            json.dumps(
                {
                    "status": final_status,
                    "completed_trials": completed_trials,
                    "objective_score": best_score,
                    "output": str(args.output),
                }
            )
        )
    else:
        print(json.dumps(final, indent=2))
    return 130 if interrupted else 0


if __name__ == "__main__":
    raise SystemExit(main())
