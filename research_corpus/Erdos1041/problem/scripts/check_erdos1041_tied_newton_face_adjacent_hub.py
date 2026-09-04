#!/usr/bin/env python3
"""Pressure the adjacent critical-hub metric selector on tied Newton faces.

For ``Q(z)=sum_{m<n/2} A_m z^m-z^n`` and an ``n``-th root of unity ``omega``,
all containment maxima are located from the real stationary polynomial; no
segment or tail is accepted from sampling.  The tested certificate consists of
one critical point ``c`` with ``Re Q(c)<=0``, two adjacent asymptotic directions,
the two straight segments from ``c`` to ``R omega``, their complete outward
tails, and the exact Euclidean defect

    |R omega_j-c|+|R omega_(j+1)-c|-2R.

The computation is evidence and a falsifier.  It is not a proof of the selector.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from typing import Iterable

import numpy as np
from scipy.optimize import differential_evolution, minimize_scalar


@dataclass(frozen=True)
class Certificate:
    score: float
    hub: complex
    pair: tuple[int, int]
    radius: float
    arm_maxima: tuple[float, float]
    tail_maxima: tuple[float, float]
    metric_defect: float


def model_value(z: complex | np.ndarray, n: int, active: np.ndarray):
    value = -(z**n)
    for m in range(1, len(active)):
        value = value + active[m] * z**m
    return value


def critical_points(n: int, active: np.ndarray) -> np.ndarray:
    derivative = np.zeros(n, dtype=np.complex128)
    derivative[0] = -n
    for m in range(1, len(active)):
        derivative[n - m] = m * active[m]
    return np.roots(derivative)


def real_line_polynomial(
    n: int, active: np.ndarray, origin: complex, direction: complex
) -> np.ndarray:
    """Ascending real coefficients of ``Re Q(origin+t*direction)``."""

    out = np.zeros(n + 1, dtype=float)
    for m in range(1, len(active)):
        for k in range(m + 1):
            out[k] += (
                active[m]
                * math.comb(m, k)
                * origin ** (m - k)
                * direction**k
            ).real
    for k in range(n + 1):
        out[k] -= (
            math.comb(n, k) * origin ** (n - k) * direction**k
        ).real
    return out


def real_stationary_points(coefficients: np.ndarray) -> list[float]:
    derivative = np.asarray(
        [k * coefficients[k] for k in range(1, len(coefficients))], dtype=float
    )
    scale = max(1.0, float(np.max(np.abs(derivative))))
    roots = np.roots((derivative / scale)[::-1])
    return [
        float(root.real)
        for root in roots
        if abs(root.imag) <= 2.0e-7 * (1.0 + abs(root.real))
    ]


def interval_maximum(coefficients: np.ndarray, left: float, right: float) -> float:
    points = [left, right]
    points.extend(x for x in real_stationary_points(coefficients) if left < x < right)
    return float(max(np.polynomial.polynomial.polyval(x, coefficients) for x in points))


def halfline_maximum(coefficients: np.ndarray, left: float) -> float:
    points = [left]
    points.extend(x for x in real_stationary_points(coefficients) if x > left)
    return float(max(np.polynomial.polynomial.polyval(x, coefficients) for x in points))


def coefficient_scale(n: int, active: np.ndarray) -> float:
    return max(
        [
            abs(active[m]) ** (1.0 / (n - m))
            for m in range(1, len(active))
            if active[m] != 0
        ]
        + [1.0e-4]
    )


def radius_score(
    n: int,
    active: np.ndarray,
    hub: complex,
    roots: np.ndarray,
    tail_polynomials: list[np.ndarray],
    pair: tuple[int, int],
    radius: float,
) -> Certificate:
    arm_maxima = []
    tail_maxima = []
    distances = []
    for index in pair:
        endpoint = radius * roots[index]
        arm = real_line_polynomial(n, active, hub, endpoint - hub)
        arm_maxima.append(interval_maximum(arm, 0.0, 1.0))
        tail_maxima.append(halfline_maximum(tail_polynomials[index], radius))
        distances.append(abs(endpoint - hub))
    defect = distances[0] + distances[1] - 2.0 * radius
    score = max(*arm_maxima, *tail_maxima, defect)
    return Certificate(
        score=float(score),
        hub=hub,
        pair=pair,
        radius=float(radius),
        arm_maxima=(float(arm_maxima[0]), float(arm_maxima[1])),
        tail_maxima=(float(tail_maxima[0]), float(tail_maxima[1])),
        metric_defect=float(defect),
    )


def best_adjacent_certificate(n: int, active: np.ndarray) -> Certificate | None:
    roots = np.exp(2j * np.pi * np.arange(n) / n)
    tail_polynomials = [
        real_line_polynomial(n, active, 0.0 + 0.0j, root) for root in roots
    ]
    scale = coefficient_scale(n, active)
    grid = np.geomspace(0.02 * scale, 12.0 * scale, 42)
    best: Certificate | None = None
    for hub in critical_points(n, active):
        if model_value(hub, n, active).real > 2.0e-8:
            continue
        for first in range(n):
            pair = (first, (first + 1) % n)
            rows = [
                radius_score(
                    n, active, hub, roots, tail_polynomials, pair, float(radius)
                )
                for radius in grid
            ]
            local = min(rows, key=lambda row: row.score)
            index = rows.index(local)
            left = grid[max(0, index - 1)]
            right = grid[min(len(grid) - 1, index + 1)]
            if left < right:
                optimum = minimize_scalar(
                    lambda radius: radius_score(
                        n,
                        active,
                        hub,
                        roots,
                        tail_polynomials,
                        pair,
                        float(radius),
                    ).score,
                    bounds=(float(left), float(right)),
                    method="bounded",
                    options={"xatol": 2.0e-9 * scale},
                )
                refined = radius_score(
                    n,
                    active,
                    hub,
                    roots,
                    tail_polynomials,
                    pair,
                    float(optimum.x),
                )
                if refined.score < local.score:
                    local = refined
            if best is None or local.score < best.score:
                best = local
    return best


def normalized_coefficients(raw: np.ndarray) -> np.ndarray:
    norm = float(np.max(np.abs(raw)))
    if norm == 0.0:
        raw = raw.copy()
        raw[0] = 1.0
        norm = 1.0
    return np.concatenate(([0.0 + 0.0j], raw / norm))


def random_pressure(degrees: Iterable[int], trials: int, seed: int) -> list[dict]:
    rng = np.random.default_rng(seed)
    output = []
    for n in degrees:
        modes = (n - 1) // 2
        worst: tuple[float, np.ndarray, Certificate] | None = None
        failures = 0
        for _ in range(trials):
            raw = rng.normal(size=modes) + 1j * rng.normal(size=modes)
            active = normalized_coefficients(raw)
            certificate = best_adjacent_certificate(n, active)
            if certificate is None:
                failures += 1
                continue
            if certificate.score > 2.0e-6:
                failures += 1
            if worst is None or certificate.score > worst[0]:
                worst = (certificate.score, active, certificate)
        assert worst is not None
        output.append(
            {
                "degree": n,
                "trial_count": trials,
                "sampled_failures": failures,
                "worst_best_score": worst[0],
                "worst_coefficients": [
                    [float(value.real), float(value.imag)] for value in worst[1][1:]
                ],
                "worst_certificate": certificate_json(worst[2]),
            }
        )
    return output


def outer_face_search(n: int, face: int, seed: int, maxiter: int) -> dict:
    """Maximise the best certificate on the normalized face ``|A_face|=1``."""

    modes = (n - 1) // 2
    bounds = []
    for m in range(1, modes + 1):
        bounds.append((0.0, 2.0 * math.pi) if m == face else (0.0, 1.0))
        if m != face:
            bounds.append((0.0, 2.0 * math.pi))

    def decode(parameters: np.ndarray) -> np.ndarray:
        active = np.zeros(modes + 1, dtype=np.complex128)
        cursor = 0
        for m in range(1, modes + 1):
            if m == face:
                radius = 1.0
                phase = parameters[cursor]
                cursor += 1
            else:
                radius = parameters[cursor]
                phase = parameters[cursor + 1]
                cursor += 2
            active[m] = radius * np.exp(1j * phase)
        return active

    def objective(parameters: np.ndarray) -> float:
        certificate = best_adjacent_certificate(n, decode(parameters))
        return 1.0e3 if certificate is None else -certificate.score

    result = differential_evolution(
        objective,
        bounds,
        seed=seed,
        maxiter=maxiter,
        popsize=10,
        tol=2.0e-5,
        polish=True,
        workers=1,
        updating="immediate",
    )
    active = decode(result.x)
    certificate = best_adjacent_certificate(n, active)
    assert certificate is not None
    return {
        "degree": n,
        "normalized_face": face,
        "optimizer_success": bool(result.success),
        "outer_iterations": int(result.nit),
        "best_adversarial_score": float(certificate.score),
        "coefficients": [
            [float(value.real), float(value.imag)] for value in active[1:]
        ],
        "certificate": certificate_json(certificate),
    }


def translated_ray_average_check(n: int, active: np.ndarray) -> float:
    """Replay ``average_j Re Q(c+s omega_j)=Re Q(c)-s^n`` numerically."""

    roots = np.exp(2j * np.pi * np.arange(n) / n)
    maximum = 0.0
    for hub in critical_points(n, active):
        for radius in np.geomspace(1.0e-3, 8.0, 40):
            left = np.mean(
                [model_value(hub + radius * root, n, active).real for root in roots]
            )
            right = model_value(hub, n, active).real - radius**n
            maximum = max(maximum, abs(left - right))
    return float(maximum)


def pure_first_mode_translated_ray_no_go() -> dict:
    """Degree six: the stronger complete translated-ray selector already fails.

    For ``Q(z)=z-z^6``, both critical points with negative real critical value
    have only one complete safe translated sixth-root ray.  Stationary points
    of every ray restriction are located, so this is a deterministic numerical
    no-go diagnostic; an exact algebraic certificate would be needed before
    promoting it to a theorem.
    """

    n = 6
    active = np.zeros(3, dtype=np.complex128)
    active[1] = 1.0
    roots = np.exp(2j * np.pi * np.arange(n) / n)
    rows = []
    for hub in critical_points(n, active):
        critical_value = float(model_value(hub, n, active).real)
        if critical_value >= -1.0e-9:
            continue
        maxima = [
            halfline_maximum(real_line_polynomial(n, active, hub, root), 0.0)
            for root in roots
        ]
        safe = [index for index, maximum in enumerate(maxima) if maximum <= 1.0e-8]
        rows.append(
            {
                "hub": [float(hub.real), float(hub.imag)],
                "critical_value_real": critical_value,
                "safe_translated_direction_indices": safe,
                "safe_translated_direction_count": len(safe),
                "ray_maxima": maxima,
            }
        )
    return {
        "model": "Q(z)=z-z^6",
        "negative_critical_point_count": len(rows),
        "maximum_safe_translated_ray_count": max(
            row["safe_translated_direction_count"] for row in rows
        ),
        "rows": rows,
        "interpretation": (
            "The finite adjacent segments may work even though complete rays "
            "from every negative critical point do not; truncation is load-bearing."
        ),
    }


def quintic_equality_calibration() -> dict:
    """Replay the exact equality chart identified by the paired-trace theorem."""

    n = 5
    u = (27.0 / 320.0) ** (1.0 / 3.0)
    active = np.asarray(
        [
            0.0 + 0.0j,
            u * np.exp(8j * math.pi / 5.0),
            np.exp(7j * math.pi / 10.0),
        ],
        dtype=np.complex128,
    )
    certificate = best_adjacent_certificate(n, active)
    assert certificate is not None
    return {
        "u_cubed": 27.0 / 320.0,
        "leading_score": certificate.score,
        "score_is_zero_to_roundoff": abs(certificate.score) <= 2.0e-12,
        "certificate": certificate_json(certificate),
        "interpretation": (
            "The adjacent metric theorem is sharp at the known zero-leading-"
            "trace quintic chart; the paired high-mode trace supplies the strict "
            "next-order sign."
        ),
    }


def certificate_json(certificate: Certificate) -> dict:
    return {
        "score": certificate.score,
        "hub": [float(certificate.hub.real), float(certificate.hub.imag)],
        "pair": list(certificate.pair),
        "radius": certificate.radius,
        "arm_maxima": list(certificate.arm_maxima),
        "tail_maxima": list(certificate.tail_maxima),
        "metric_defect": certificate.metric_defect,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--degrees", default="5,6,7,8")
    parser.add_argument("--trials", type=int, default=24)
    parser.add_argument("--seed", type=int, default=20260826)
    parser.add_argument("--outer-degree", type=int)
    parser.add_argument("--outer-face", type=int)
    parser.add_argument("--maxiter", type=int, default=30)
    args = parser.parse_args()

    degrees = [int(value) for value in args.degrees.split(",") if value]
    rows = random_pressure(degrees, args.trials, args.seed)
    calibration = np.asarray([0.0 + 0.0j, 0.37 - 0.21j, 1.0 + 0.0j])
    payload = {
        "schema": "erdos1041_tied_newton_face_adjacent_hub_probe_v1",
        "status": "evidence_only",
        "claim_boundary": (
            "Stationary-point location makes each reported containment maximum "
            "a deterministic numerical certificate for its row. Survival of the "
            "finite coefficient search is not a proof of the universal selector."
        ),
        "translated_ray_average_max_residual": translated_ray_average_check(
            5, calibration
        ),
        "pure_first_mode_translated_ray_no_go": pure_first_mode_translated_ray_no_go(),
        "quintic_equality_calibration": quintic_equality_calibration(),
        "random_pressure": rows,
    }
    if args.outer_degree is not None:
        if args.outer_face is None:
            raise SystemExit("--outer-face is required with --outer-degree")
        payload["outer_face_search"] = outer_face_search(
            args.outer_degree, args.outer_face, args.seed, args.maxiter
        )
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
