#!/usr/bin/env python3
"""Deterministic falsifier for the all-degree FP-to-(S) bridge.

This is corroboration, not a replacement for the psh/removability proof in
FreePointTorusPshReduction.md.  It independently checks the torus identity,
the exponent conversion, scale covariance, local submean behaviour, and
near-collision continuity.
"""

from __future__ import annotations

import cmath
import json
import math
from dataclasses import asdict, dataclass

import numpy as np


TOL = 2.0e-9
RNG = np.random.default_rng(1041_0830)


def coeffs_from_roots(roots: np.ndarray) -> np.ndarray:
    return np.poly(roots).astype(np.complex128)


def critical_points(coeffs: np.ndarray) -> np.ndarray:
    return np.roots(np.polyder(coeffs))


def critical_values(coeffs: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    crit = critical_points(coeffs)
    return crit, np.polyval(coeffs, crit)


def phi(roots: np.ndarray) -> float:
    coeffs = coeffs_from_roots(roots)
    _, vals = critical_values(coeffs)
    return float(np.sum(np.abs(vals) ** (1.0 / len(roots))))


def disk_sample(n: int) -> np.ndarray:
    radii = np.sqrt(RNG.random(n))
    angles = RNG.uniform(-math.pi, math.pi, n)
    return radii * np.exp(1j * angles)


def torus_sample(n: int) -> np.ndarray:
    return np.exp(1j * RNG.uniform(-math.pi, math.pi, n))


@dataclass
class Receipt:
    torus_cases: int = 0
    torus_identity_max_abs_error: float = 0.0
    exponent_cases: int = 0
    exponent_bridge_min_slack: float = math.inf
    scale_cases: int = 0
    scale_covariance_max_abs_error: float = 0.0
    submean_cases: int = 0
    submean_min_slack: float = math.inf
    collision_cases: int = 0
    collision_formula_max_rel_error: float = 0.0
    collision_monotonicity_min_drop: float = math.inf
    regular_polygon_max_abs_error: float = 0.0


def check_torus_identity(rec: Receipt) -> None:
    for n in range(2, 10):
        for _ in range(24):
            roots = torus_sample(n)
            coeffs = coeffs_from_roots(roots)
            crit, vals = critical_values(coeffs)
            for c, value in zip(crit, vals):
                rhs = float(np.prod(np.abs(1.0 - np.conj(c) * crit)))
                err = abs(abs(value) - rhs)
                rec.torus_identity_max_abs_error = max(
                    rec.torus_identity_max_abs_error, err
                )
                rec.torus_cases += 1

    # Repeated boundary roots exercise the zero/zero branch of the identity.
    for n in range(3, 9):
        roots = torus_sample(n)
        roots[1] = roots[0]
        coeffs = coeffs_from_roots(roots)
        crit, vals = critical_values(coeffs)
        errors = [
            abs(abs(value) - np.prod(np.abs(1.0 - np.conj(c) * crit)))
            for c, value in zip(crit, vals)
        ]
        rec.torus_identity_max_abs_error = max(
            rec.torus_identity_max_abs_error, max(errors)
        )
        rec.torus_cases += len(crit)


def check_exponent_bridge(rec: Receipt) -> None:
    # Random nonnegative rows, rescaled only when their sum exceeds m.
    for m in range(1, 13):
        q = m / (m + 1.0)
        for _ in range(200):
            y = np.exp(RNG.uniform(-9.0, 2.0, m))
            if np.sum(y) > m:
                y *= m / np.sum(y)
            tangent_slack = np.min(q * y + (1.0 - q) - y**q)
            sum_slack = m - float(np.sum(y**q))
            rec.exponent_bridge_min_slack = min(
                rec.exponent_bridge_min_slack,
                float(tangent_slack),
                sum_slack,
            )
            rec.exponent_cases += 1


def check_scale_covariance(rec: Receipt) -> None:
    for n in range(2, 9):
        for _ in range(20):
            normalized = disk_sample(n)
            radius = float(np.exp(RNG.uniform(-3.0, 2.0)))
            centre = complex(*RNG.normal(size=2))
            roots = centre + radius * normalized
            normalized_crit = critical_points(coeffs_from_roots(normalized))
            scaled_crit = centre + radius * normalized_crit
            # Evaluate the two product formulae directly.  Reconstructing a
            # translated high-degree polynomial and re-solving its derivative
            # would measure monomial-basis conditioning rather than covariance.
            normalized_values = np.array(
                [np.prod(c - normalized) for c in normalized_crit]
            )
            scaled_values = np.array([np.prod(c - roots) for c in scaled_crit])
            lhs = float(np.sum(np.abs(scaled_values) ** (1.0 / n)))
            rhs = radius * float(
                np.sum(np.abs(normalized_values) ** (1.0 / n))
            )
            rec.scale_covariance_max_abs_error = max(
                rec.scale_covariance_max_abs_error, abs(lhs - rhs)
            )
            rec.scale_cases += 1


def check_local_submean(rec: Receipt) -> None:
    # Freeze n-1 roots and vary the last one on a small complex circle.
    # A psh function restricts to a subharmonic function on this line.
    for n in range(3, 9):
        for _ in range(15):
            roots = 0.72 * disk_sample(n)
            centre = roots[-1]
            radius = 0.12 * (1.0 - abs(centre))
            if radius <= 1.0e-6:
                continue
            middle = phi(roots)
            ring = []
            for k in range(96):
                moved = roots.copy()
                moved[-1] = centre + radius * cmath.exp(2j * math.pi * k / 96)
                ring.append(phi(moved))
            slack = float(np.mean(ring) - middle)
            rec.submean_min_slack = min(rec.submean_min_slack, slack)
            rec.submean_cases += 1


def check_collision_continuity(rec: Receipt) -> None:
    # Coalesce two derivative roots indirectly by perturbing a polynomial
    # with a maximally multiple critical point: z^n + eps*z.  Here the
    # exact critical radius is (|eps|/n)^(1/(n-1)) and every critical-value
    # modulus is |eps|*radius*(n-1)/n, so Phi has an exact positive power
    # law tending to zero.  Checking that law is more informative than an
    # absolute smallness cutoff, whose convergence is slow in high degree.
    for n in range(3, 10):
        base = np.zeros(n + 1, dtype=np.complex128)
        base[0] = 1.0
        previous = None
        for exponent in range(2, 11):
            eps = 10.0 ** (-exponent)
            coeffs = base.copy()
            coeffs[-2] = eps * cmath.exp(0.37j)
            _, vals = critical_values(coeffs)
            value = float(np.sum(np.abs(vals) ** (1.0 / n)))
            critical_radius = (eps / n) ** (1.0 / (n - 1))
            exact = (n - 1) * (
                eps * critical_radius * (n - 1) / n
            ) ** (1.0 / n)
            rel_error = abs(value - exact) / exact
            rec.collision_formula_max_rel_error = max(
                rec.collision_formula_max_rel_error, rel_error
            )
            if previous is not None:
                rec.collision_monotonicity_min_drop = min(
                    rec.collision_monotonicity_min_drop, previous - value
                )
            previous = value
            rec.collision_cases += 1


def check_regular_polygons(rec: Receipt) -> None:
    # f(z)=z^n-omega has n-1 critical points at zero, each value of modulus 1.
    for n in range(2, 15):
        phase = float(RNG.uniform(-math.pi, math.pi))
        roots = np.exp(1j * (phase + 2.0 * math.pi * np.arange(n) / n))
        value = phi(roots)
        rec.regular_polygon_max_abs_error = max(
            rec.regular_polygon_max_abs_error, abs(value - (n - 1))
        )


def main() -> None:
    rec = Receipt()
    check_torus_identity(rec)
    check_exponent_bridge(rec)
    check_scale_covariance(rec)
    check_local_submean(rec)
    check_collision_continuity(rec)
    check_regular_polygons(rec)

    failures: list[str] = []
    if rec.torus_identity_max_abs_error > 5.0e-7:
        failures.append("torus identity")
    if rec.exponent_bridge_min_slack < -TOL:
        failures.append("exponent bridge")
    if rec.scale_covariance_max_abs_error > 5.0e-7:
        failures.append("scale covariance")
    # Floating critical-root conditioning can produce tiny negative submean
    # slacks.  The threshold is far below the smallest structural slack seen.
    if rec.submean_min_slack < -2.0e-6:
        failures.append("local submean")
    if rec.collision_formula_max_rel_error > 2.0e-7:
        failures.append("collision power law")
    if rec.collision_monotonicity_min_drop < -TOL:
        failures.append("collision monotonicity")
    if rec.regular_polygon_max_abs_error > 5.0e-6:
        failures.append("regular polygon equality")

    payload = {
        "schema": "erdos1041_free_point_torus_psh_reduction_check_v0",
        "status": "pass" if not failures else "fail",
        "claim_boundary": (
            "Numerical corroboration of analytic interfaces; proof authority "
            "is FreePointTorusPshReduction.md and its cited standard psh theorem."
        ),
        "receipt": asdict(rec),
        "failures": failures,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
