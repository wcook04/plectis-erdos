#!/usr/bin/env python3
"""Probe the minimax stationarity mechanism behind the CE--GM free hub.

Every final segment maximum is evaluated from the exact float polynomial
``|f(h+t(a-h))|^2``.  Hub optimization remains numerical, so this script is a
mechanism probe and falsifier, never a proof of CE--GM.
"""

from __future__ import annotations

import importlib.util
import math
from pathlib import Path

import numpy as np


HERE = Path(__file__).resolve().parent


def load_sibling(name: str):
    path = HERE / f"{name}.py"
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


CE = load_sibling("check_erdos1041_critical_ellipse_free_hub")
LEVEL = load_sibling("check_erdos1041_two_segment_level_identity")


def segment_extrema(
    roots: np.ndarray, hub: complex, root: complex
) -> list[tuple[float, float, complex]]:
    coefficients = LEVEL.seg_poly(roots, hub, root)
    derivative = coefficients[1:] * np.arange(1, len(coefficients))
    parameters = [0.0, 1.0]
    if derivative.size and np.any(derivative != 0):
        for candidate in np.roots(derivative[::-1]):
            if abs(candidate.imag) < 2.0e-8 and -1.0e-11 < candidate.real < 1.0 + 1.0e-11:
                parameters.append(min(1.0, max(0.0, float(candidate.real))))
    values = [float(max(np.polyval(coefficients[::-1], t), 0.0)) for t in parameters]
    return [
        (math.sqrt(value), t, complex(hub + t * (root - hub)))
        for value, t in zip(values, parameters)
    ]


def segment_argmax(
    roots: np.ndarray, hub: complex, root: complex
) -> tuple[float, float, complex]:
    return max(segment_extrema(roots, hub, root), key=lambda item: item[0])


def optimized_hub(
    roots: np.ndarray, a: complex, b: complex, rho: float
) -> complex:
    hubs = CE.ellipse_hubs(a, b, 2.0 * rho, radial=23, angular=144)
    scores = np.maximum(
        CE.FREE_HUB.segment_max_sampled(roots, hubs, a, samples=193),
        CE.FREE_HUB.segment_max_sampled(roots, hubs, b, samples=193),
    )
    hub = complex(hubs[int(np.argmin(scores))])
    best = CE.exact_pair_score(roots, hub, a, b)
    step = 0.06 * rho
    for _ in range(180):
        trial = hub + step * np.exp(2j * math.pi * np.arange(24) / 24)
        trial = trial[np.abs(trial - a) + np.abs(trial - b) <= 2.0 * rho + 1.0e-11]
        if len(trial) == 0:
            step *= 0.74
            continue
        sampled = np.maximum(
            CE.FREE_HUB.segment_max_sampled(roots, trial, a, samples=193),
            CE.FREE_HUB.segment_max_sampled(roots, trial, b, samples=193),
        )
        candidates = np.argsort(sampled)[: min(3, len(trial))]
        improved = False
        for index in candidates:
            exact = CE.exact_pair_score(roots, complex(trial[index]), a, b)
            if exact < best:
                best = exact
                hub = complex(trial[index])
                improved = True
        if not improved:
            step *= 0.74
    return hub


def logarithmic_gradient(
    roots: np.ndarray, point: complex, t: float
) -> np.ndarray:
    value = complex(np.prod(point - roots))
    derivative = value * complex(np.sum(1.0 / (point - roots)))
    quotient = (1.0 - t) * derivative / value
    return np.array([quotient.real, -quotient.imag], dtype=float)


def row(name: str, roots: np.ndarray) -> dict[str, object]:
    from scipy.optimize import minimize

    n = len(roots)
    critical = np.roots(np.polyder(np.poly(roots)))
    critical_values = np.array([abs(np.prod(c - roots)) for c in critical])
    c = complex(critical[int(np.argmin(critical_values))])
    mu = float(np.min(critical_values))
    rho = mu ** (1.0 / n)
    gcrit = float(np.prod(critical_values) ** (1.0 / (n - 1)))
    nearest = np.argsort(np.abs(roots - c))[:2]
    a, b = complex(roots[nearest[0]]), complex(roots[nearest[1]])
    hub = optimized_hub(roots, a, b, rho)
    va, ta, za = segment_argmax(roots, hub, a)
    vb, tb, zb = segment_argmax(roots, hub, b)
    ga = logarithmic_gradient(roots, za, ta)
    gb = logarithmic_gradient(roots, zb, tb)
    direction = ga - gb
    if float(direction @ direction) > 1.0e-30:
        weight = float(np.clip(-(gb @ direction) / (direction @ direction), 0.0, 1.0))
    else:
        weight = 0.5
    balance = weight * ga + (1.0 - weight) * gb
    scale = max(float(np.linalg.norm(ga)), float(np.linalg.norm(gb)), 1.0e-300)
    cosine = float((ga @ gb) / max(np.linalg.norm(ga) * np.linalg.norm(gb), 1.0e-300))
    global_value = max(va, vb)
    active: list[tuple[int, float, np.ndarray]] = []
    for arm, root in enumerate((a, b)):
        for value, t, point in segment_extrema(roots, hub, root):
            if value >= global_value * (1.0 - 2.0e-6):
                active.append((arm, t, logarithmic_gradient(roots, point, t)))
    gradients = np.asarray([item[2] for item in active], dtype=float)
    if len(gradients):
        initial = np.full(len(gradients), 1.0 / len(gradients))
        fit = minimize(
            lambda weights: float(np.linalg.norm(weights @ gradients) ** 2),
            initial,
            method="SLSQP",
            bounds=[(0.0, 1.0)] * len(gradients),
            constraints={"type": "eq", "fun": lambda weights: float(np.sum(weights) - 1.0)},
            options={"ftol": 1.0e-18, "maxiter": 1000},
        )
        hull_residual = float(np.linalg.norm(np.asarray(fit.x) @ gradients)) / max(
            float(np.max(np.linalg.norm(gradients, axis=1))), 1.0e-300
        )
        max_active_gradient_norm = float(np.max(np.linalg.norm(gradients, axis=1)))
    else:
        hull_residual = math.inf
        max_active_gradient_norm = math.inf
    same_arm_opposed = []
    for arm, root in enumerate((a, b)):
        direction = root - hub
        normal = np.array([-direction.imag, direction.real], dtype=float)
        normal_norm_sq = float(normal @ normal)
        scalars = [
            float(gradient @ normal) / max(normal_norm_sq, 1.0e-300)
            for contact_arm, t, gradient in active
            if contact_arm == arm and 1.0e-8 < t < 1.0 - 1.0e-8
        ]
        same_arm_opposed.append(
            len(scalars) >= 2 and min(scalars) <= 0.0 <= max(scalars)
        )
    reciprocal_sum = complex(np.sum(1.0 / (hub - roots)))
    inverse_square_sum = float(np.sum(1.0 / np.abs(hub - roots) ** 2))
    inverse_square_barycenter = hub - np.conj(reciprocal_sum) / inverse_square_sum
    descent = inverse_square_barycenter - hub
    descent_disc_arm_fractions = []
    for root in (a, b):
        arm_vector = root - hub
        arm_length = abs(arm_vector)
        unit = arm_vector / max(arm_length, 1.0e-300)
        entry_length = max(0.0, 2.0 * float(np.real(descent * np.conj(unit))))
        descent_disc_arm_fractions.append(entry_length / max(arm_length, 1.0e-300))
    return {
        "name": name,
        "degree": n,
        "optimized_over_gcrit": max(va, vb) / gcrit,
        "gcrit_over_mu": gcrit / mu,
        "hub_displacement_over_rho": abs(hub - c) / rho,
        "arm_relative_gap": abs(va - vb) / max(va, vb, 1.0e-300),
        "ellipse_ratio": (abs(hub - a) + abs(hub - b)) / (2.0 * rho),
        "active_parameters": [ta, tb],
        "gradient_cosine": cosine,
        "balance_weight": weight,
        "normalized_balance_residual": float(np.linalg.norm(balance)) / scale,
        "near_active_gradient_count": len(active),
        "hub_endpoint_active": any(t <= 1.0e-8 for _, t, _ in active),
        "same_arm_opposed_interior_pair": same_arm_opposed,
        "inverse_square_descent_over_rho": abs(descent) / rho,
        "descent_disc_arm_fractions": descent_disc_arm_fractions,
        "active_convex_hull_residual": hull_residual,
        "max_active_gradient_norm": max_active_gradient_norm,
    }


def main() -> int:
    rows = [row(name, roots) for name, roots in CE.hard_witnesses().items()]
    for result in rows:
        print(result)
    print("claim boundary: numerical hub minimization; exact-float segment rescoring")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
