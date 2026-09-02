#!/usr/bin/env python3
"""Falsifier for the critical-ellipse geometric-mean free-hub target.

The inner hub search is numerical.  Segment maxima at every reported winner
are rescored from all real critical points of the exact float polynomial
``|f(h+t(a-h))|^2``.
"""

from __future__ import annotations

import argparse
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


FREE_HUB = load_sibling("check_erdos1041_free_hub_two_segment")
LEVEL_REFUTER = load_sibling("check_erdos1041_two_segment_level_identity_refutation")


def ellipse_hubs(
    left: complex,
    right: complex,
    major: float,
    radial: int,
    angular: int,
) -> np.ndarray:
    separation = abs(left - right)
    semimajor = major / 2.0
    if separation > major + 1.0e-10:
        return np.array([], dtype=np.complex128)
    direction = (right - left) / max(separation, 1.0e-300)
    normal = 1j * direction
    center = (left + right) / 2.0
    semiminor = math.sqrt(max(semimajor**2 - (separation / 2.0) ** 2, 0.0))
    scale = np.linspace(0.0, 1.0, radial)[:, None]
    angle = np.linspace(0.0, 2.0 * math.pi, angular, endpoint=False)[None, :]
    return (
        center
        + scale
        * (semimajor * np.cos(angle) * direction + semiminor * np.sin(angle) * normal)
    ).ravel()


def exact_pair_score(roots: np.ndarray, hub: complex, a: complex, b: complex) -> float:
    return max(
        FREE_HUB.segment_max_exact(roots, hub, a),
        FREE_HUB.segment_max_exact(roots, hub, b),
    )


def configuration_score(
    roots: np.ndarray,
    *,
    radial: int = 15,
    angular: int = 80,
    refine_rounds: int = 90,
    refine_directions: int = 16,
    segment_samples: int = 129,
) -> dict[str, float | int]:
    n = len(roots)
    critical = np.roots(np.polyder(np.poly(roots)))
    values = np.array([abs(np.prod(c - roots)) for c in critical])
    least_index = int(np.argmin(values))
    center = complex(critical[least_index])
    mu = float(values[least_index])
    rho = mu ** (1.0 / n)
    gcrit = float(np.prod(values) ** (1.0 / (n - 1)))
    order = np.argsort(np.abs(roots - center))
    a, b = complex(roots[order[0]]), complex(roots[order[1]])

    critical_score = exact_pair_score(roots, center, a, b)
    hubs = ellipse_hubs(a, b, 2.0 * rho, radial=radial, angular=angular)
    sampled = np.maximum(
        FREE_HUB.segment_max_sampled(roots, hubs, a, samples=97),
        FREE_HUB.segment_max_sampled(roots, hubs, b, samples=97),
    )
    hub = complex(hubs[int(np.argmin(sampled))])
    best_sampled = float(np.min(sampled))
    step = 0.08 * rho
    for _ in range(refine_rounds):
        trial = hub + step * np.exp(
            2j * math.pi * np.arange(refine_directions) / refine_directions
        )
        trial = trial[np.abs(trial - a) + np.abs(trial - b) <= 2.0 * rho + 1.0e-11]
        if len(trial) == 0:
            step *= 0.72
            continue
        scores = np.maximum(
            FREE_HUB.segment_max_sampled(roots, trial, a, samples=segment_samples),
            FREE_HUB.segment_max_sampled(roots, trial, b, samples=segment_samples),
        )
        index = int(np.argmin(scores))
        if scores[index] < best_sampled:
            best_sampled = float(scores[index])
            hub = complex(trial[index])
        else:
            step *= 0.72
    optimized_score = min(critical_score, exact_pair_score(roots, hub, a, b))
    return {
        "degree": n,
        "mu": mu,
        "rho": rho,
        "gcrit": gcrit,
        "critical_hub_ratio": critical_score / gcrit,
        "optimized_hub_ratio": optimized_score / gcrit,
        "ellipse_ratio_at_critical": (abs(center - a) + abs(center - b)) / (2.0 * rho),
        "hub_displacement_over_rho": abs(hub - center) / rho,
    }


def adversarial_boundary_search(
    degree: int, steps: int, seed: int
) -> tuple[dict[str, float | int], np.ndarray]:
    """Bounded hill climb on angular perturbations of a regular boundary polygon.

    The score is only a falsifier: it is an upper bound produced by a numerical
    hub search.  Any apparent violation must therefore be re-solved at higher
    fidelity and then certified independently before it could count as a
    counterexample.
    """
    rng = np.random.default_rng(seed)
    base = 2.0 * math.pi * np.arange(degree) / degree
    eta = rng.normal(0.0, 0.12, degree)
    eta -= float(np.mean(eta))

    def roots_of(parameters: np.ndarray) -> np.ndarray:
        return np.exp(1j * (base + parameters))

    roots = roots_of(eta)
    row = configuration_score(
        roots,
        radial=9,
        angular=48,
        refine_rounds=36,
        refine_directions=12,
        segment_samples=81,
    )
    best_eta = eta.copy()
    best_row = row
    step = 0.08
    for iteration in range(steps):
        trial_eta = eta + step * rng.normal(size=degree)
        trial_eta -= float(np.mean(trial_eta))
        trial_roots = roots_of(trial_eta)
        trial_row = configuration_score(
            trial_roots,
            radial=9,
            angular=48,
            refine_rounds=36,
            refine_directions=12,
            segment_samples=81,
        )
        trial_score = float(trial_row["optimized_hub_ratio"])
        current_score = float(row["optimized_hub_ratio"])
        temperature = max(2.0e-5, 2.0e-3 * (1.0 - iteration / max(steps, 1)))
        if trial_score >= current_score or rng.random() < math.exp(
            (trial_score - current_score) / temperature
        ):
            eta = trial_eta
            row = trial_row
        if trial_score > float(best_row["optimized_hub_ratio"]):
            best_eta = trial_eta.copy()
            best_row = trial_row
        step = max(0.002, step * 0.9985)

    best_roots = roots_of(best_eta)
    rescored = configuration_score(
        best_roots,
        radial=23,
        angular=144,
        refine_rounds=180,
        refine_directions=24,
        segment_samples=193,
    )
    return rescored, best_roots


def simplex_linear_arm_certificate(roots: np.ndarray, seed: int) -> dict[str, object]:
    """Search the barycentric envelope's finite-dimensional arm certificate.

    For a probability vector ``p``, interpolate linearly to a root vertex.
    The barycentre then traces the literal straight arm.  The variance-mixture
    identity reduces containment of that whole arm to one scalar inequality in
    the interpolation parameter.  This is a sufficient certificate, not an
    equivalent reformulation of segment containment.
    """
    from scipy.optimize import minimize

    n = len(roots)
    critical = np.roots(np.polyder(np.poly(roots)))
    values = np.array([abs(np.prod(c - roots)) for c in critical])
    least = int(np.argmin(values))
    c = complex(critical[least])
    mu = float(values[least])
    rho = mu ** (1.0 / n)
    level = float(np.prod(values) ** (1.0 / (n - 1)))
    nearest = np.argsort(np.abs(roots - c))[:2]
    a, b = complex(roots[nearest[0]]), complex(roots[nearest[1]])
    inverse = 1.0 / np.maximum(np.abs(c - roots) ** 2, 1.0e-300)
    p0 = inverse / np.sum(inverse)
    grid = np.concatenate(
        (
            np.linspace(0.0, 0.95, 257),
            1.0 - 10.0 ** np.linspace(-2.0, -10.0, 96),
        )
    )

    def unpack(logits: np.ndarray) -> np.ndarray:
        shifted = logits - float(np.max(logits))
        raw = np.exp(shifted)
        return raw / float(np.sum(raw))

    def exact_rows(p: np.ndarray) -> tuple[float, float, complex]:
        hub = complex(np.sum(p * roots))
        variance = float(np.sum(p * np.abs(roots - hub) ** 2))
        geom = math.exp(float(np.mean(np.log(np.maximum(p, 1.0e-300)))))
        scale = n * level ** (2.0 / n) * geom
        worst = 0.0
        for index in nearest:
            distance2 = abs(roots[index] - hub) ** 2
            s = grid
            factor = np.exp(
                np.log1p(s / ((1.0 - s) * p[index])) / n
            )
            ratio = (variance + s * distance2) / (scale * factor)
            worst = max(worst, float(np.max(ratio)))
        ellipse_ratio = (abs(hub - a) + abs(hub - b)) / (2.0 * rho)
        return worst, float(ellipse_ratio), hub

    def objective(logits: np.ndarray) -> float:
        arm, ellipse, _ = exact_rows(unpack(logits))
        excess = max(0.0, ellipse - 1.0)
        return arm + 40.0 * excess + 200.0 * excess**2

    rng = np.random.default_rng(seed)
    best = None
    initial = np.log(np.maximum(p0, 1.0e-300))
    for restart in range(5):
        start = initial if restart == 0 else initial + rng.normal(0.0, 0.35, n)
        result = minimize(
            objective,
            start,
            method="Powell",
            options={"maxiter": 700, "xtol": 2.0e-9, "ftol": 2.0e-11},
        )
        p = unpack(np.asarray(result.x, dtype=float))
        arm, ellipse, hub = exact_rows(p)
        score = max(arm, ellipse)
        if best is None or score < best[0]:
            best = (score, arm, ellipse, hub, p, bool(result.success))
    assert best is not None
    _, arm, ellipse, hub, p, success = best
    return {
        "degree": n,
        "arm_certificate_ratio": arm,
        "ellipse_ratio": ellipse,
        "hub": (hub.real.hex(), hub.imag.hex()),
        "min_weight": float(np.min(p)),
        "optimizer_success": success,
        "certificate_survives": arm <= 1.0 + 2.0e-7 and ellipse <= 1.0 + 2.0e-7,
    }


def hard_witnesses() -> dict[str, np.ndarray]:
    rows = FREE_HUB.witnesses()
    rows["degree-7 V_E=mu refuter"] = np.array(
        [
            complex(float.fromhex(real), float.fromhex(imag))
            for real, imag in LEVEL_REFUTER.ROOTS_HEX
        ],
        dtype=np.complex128,
    )
    return rows


def cubic_fixed_hub_probe(samples: int, seed: int) -> dict[str, object]:
    """Probe the exact one-complex-parameter cubic spoke reduction.

    After translating a critical point to zero, a monic cubic is
    ``f(z)=f(0)+A z^2+z^3``.  For a root ``d`` put ``x=A/d``.  Along its spoke,

        f(td)/f(0)=(1-t)(x(1+t)+1+t+t^2)/(x+1),

    while the other critical value divided by ``f(0)`` is
    ``H(x)=1-4x^3/(27(x+1))``.  The chosen critical point is a least-value
    point exactly when ``|H(x)|>=1``.  Thus a universal fixed-hub cubic proof
    would follow from the scalar inequality tested here.
    """
    rng = np.random.default_rng(seed)
    t = np.linspace(0.0, 1.0, 4097)
    worst = 0.0
    worst_x = 0j
    worst_nearest_pair = 0.0
    worst_nearest_x = 0j
    worst_nearest_pair_over_mu = 0.0
    worst_nearest_mu_x = 0j
    accepted = 0
    for _ in range(samples):
        radius = 10.0 ** rng.uniform(-3.0, 3.0)
        x = radius * np.exp(2j * math.pi * rng.random())
        if abs(x + 1.0) < 1.0e-9:
            continue
        other_ratio = 1.0 - 4.0 * x**3 / (27.0 * (x + 1.0))
        if abs(other_ratio) < 1.0:
            continue
        spoke = (1.0 - t) * (x * (1.0 + t) + 1.0 + t + t**2) / (x + 1.0)
        ratio = float(np.max(np.abs(spoke)) / math.sqrt(abs(other_ratio)))
        roots = np.concatenate(
            (np.array([1.0 + 0.0j]), np.roots([1.0, x + 1.0, x + 1.0]))
        )
        spoke_ratios = []
        for root in roots:
            root_x = x / root
            root_spoke = (
                (1.0 - t)
                * (root_x * (1.0 + t) + 1.0 + t + t**2)
                / (root_x + 1.0)
            )
            spoke_ratios.append(
                float(np.max(np.abs(root_spoke)) / math.sqrt(abs(other_ratio)))
            )
        nearest = np.argsort(np.abs(roots))[:2]
        nearest_pair_ratio = max(spoke_ratios[int(j)] for j in nearest)
        nearest_pair_over_mu = nearest_pair_ratio * math.sqrt(abs(other_ratio))
        accepted += 1
        if ratio > worst:
            worst = ratio
            worst_x = complex(x)
        if nearest_pair_ratio > worst_nearest_pair:
            worst_nearest_pair = nearest_pair_ratio
            worst_nearest_x = complex(x)
        if nearest_pair_over_mu > worst_nearest_pair_over_mu:
            worst_nearest_pair_over_mu = nearest_pair_over_mu
            worst_nearest_mu_x = complex(x)
    return {
        "accepted": accepted,
        "worst_spoke_over_Gcrit": worst,
        "worst_x_hex": (worst_x.real.hex(), worst_x.imag.hex()),
        "worst_two_nearest_spokes_over_Gcrit": worst_nearest_pair,
        "worst_nearest_x_hex": (worst_nearest_x.real.hex(), worst_nearest_x.imag.hex()),
        "worst_two_nearest_spokes_over_mu": worst_nearest_pair_over_mu,
        "worst_nearest_mu_x_hex": (
            worst_nearest_mu_x.real.hex(), worst_nearest_mu_x.imag.hex()
        ),
        "two_nearest_candidate_survives": worst_nearest_pair <= 1.0 + 2.0e-7,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--random", type=int, default=0)
    parser.add_argument("--cubic-probe", type=int, default=0)
    parser.add_argument("--adversarial-steps", type=int, default=0)
    parser.add_argument("--adversarial-degree", type=int, default=6)
    parser.add_argument("--simplex-probe", action="store_true")
    parser.add_argument("--seed", type=int, default=20260825)
    args = parser.parse_args()
    worst_optimized = 0.0
    critical_refutation_count = 0
    for name, roots in hard_witnesses().items():
        row = configuration_score(roots)
        worst_optimized = max(worst_optimized, float(row["optimized_hub_ratio"]))
        critical_refutation_count += int(float(row["critical_hub_ratio"]) > 1.0 + 1.0e-7)
        print(name, row)

    rng = np.random.default_rng(args.seed)
    for _ in range(args.random):
        n = int(rng.integers(3, 13))
        if rng.random() < 0.6:
            perturbation = 10.0 ** rng.uniform(-7.0, -1.0)
            angles = 2.0 * math.pi * np.arange(n) / n + perturbation * rng.normal(size=n)
            radii = np.full(n, 1.0 - 10.0 ** rng.uniform(-10.0, -3.0))
        else:
            angles = 2.0 * math.pi * rng.random(n)
            radii = np.sqrt(rng.random(n))
        row = configuration_score(radii * np.exp(1j * angles))
        worst_optimized = max(worst_optimized, float(row["optimized_hub_ratio"]))

    print(f"critical-hub refutations among hard rows: {critical_refutation_count}")
    print(f"worst optimized/Gcrit ratio: {worst_optimized:.12g}")
    if args.cubic_probe:
        print("cubic fixed-hub scalar probe:", cubic_fixed_hub_probe(args.cubic_probe, args.seed))
    if args.adversarial_steps:
        row, roots = adversarial_boundary_search(
            args.adversarial_degree, args.adversarial_steps, args.seed
        )
        print("adversarial boundary high-fidelity rescore:", row)
        print(
            "adversarial roots hex:",
            [(complex(z).real.hex(), complex(z).imag.hex()) for z in roots],
        )
    if args.simplex_probe:
        for name, roots in hard_witnesses().items():
            print(
                "simplex linear-arm certificate",
                name,
                simplex_linear_arm_certificate(roots, args.seed),
            )
    print("candidate status: unproved; inner minimization is numerical")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
