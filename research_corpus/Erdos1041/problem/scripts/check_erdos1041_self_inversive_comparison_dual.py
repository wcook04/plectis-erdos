#!/usr/bin/env python3
"""Condition-aware falsifier for the self-inversive comparison dual.

The raw one-gap identity has value 1/omega_k and is badly conditioned when a
gap weight is tiny.  This checker tests the invariant projector identity
omega_k Q_k(v_j)/g(v_j) = delta_kj instead.  It is a numerical replay, not the
proof.
"""
from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from typing import Iterable

import numpy as np


@dataclass
class Row:
    n: int
    weight_sum_error: float
    minimum_weight: float
    weighted_projector_error: float
    quadrature_error: float
    gap_product_relative_error: float
    minimax_equioscillation_error: float
    dilation_product_relative_error: float
    dilation_geometric_mean: float


def unit_from_half_angle(q: float) -> complex:
    return complex((1 - q * q) / (1 + q * q), 2 * q / (1 + q * q))


def relative_error(a: complex, b: complex, floor: float = 1e-15) -> float:
    return float(abs(a - b) / max(abs(a), abs(b), floor))


def probe(roots: Iterable[complex], s: float) -> Row:
    w = np.asarray(list(roots), dtype=np.complex128)
    n = int(w.size)
    g = np.poly(w).astype(np.complex128)
    zgp = np.concatenate([np.polyder(g), np.array([0j])])
    A = zgp - (n / 2) * g
    Ap = np.polyder(A)
    v = np.roots(A)
    if np.max(np.abs(np.abs(v) - 1)) > 5e-7:
        raise AssertionError("critical nodes left the unit circle")
    v /= np.abs(v)
    gv = np.polyval(g, v)
    lam = np.real(gv / (v * np.polyval(Ap, v)))
    omega = (n / 4) * lam
    M = np.abs(gv)

    q_basis: list[np.ndarray] = []
    projector_error = 0.0
    for k in range(n):
        quotient, remainder = np.polydiv(A, np.array([1 + 0j, -v[k]]))
        if np.max(np.abs(remainder)) > 2e-6:
            raise AssertionError("unstable critical-factor division")
        qk = (2 / n) * np.polymul(quotient, np.array([1 + 0j, v[k]]))
        q_basis.append(qk)
        scaled = omega[k] * np.polyval(qk, v) / gv
        target = np.zeros(n, dtype=np.complex128)
        target[k] = 1
        projector_error = max(projector_error, float(np.max(np.abs(scaled - target))))

    raw = np.linspace(-0.7, 1.3, n)
    x = raw + (1 - float(np.dot(omega, raw)))
    q = np.zeros(n + 1, dtype=np.complex128)
    for k in range(n):
        q += omega[k] * x[k] * q_basis[k]
    quadrature_error = float(abs(np.dot(omega, np.polyval(q, v) / gv) - 1))

    delta2 = math.prod(abs(w[i] - w[j]) ** 2 for i in range(n) for j in range(i + 1, n))
    gap_product_error = relative_error(float(np.prod(M)), (2**n) * delta2 / (n**n))

    T = 1 / float(np.sum(omega / M))
    qstar = np.zeros(n + 1, dtype=np.complex128)
    for k in range(n):
        qstar += (T * omega[k] / M[k]) * q_basis[k]
    equioscillation_error = float(np.max(np.abs(np.abs(np.polyval(qstar, v)) - T)))

    deg = np.arange(n, -1, -1)
    qs = (g * (s**deg) + g * (s ** (n - deg))) / (1 + s**n)
    zeta = np.roots(qs)
    if np.max(np.abs(np.abs(zeta) - 1)) > 5e-7:
        raise AssertionError("dilation comparator roots left the unit circle")
    zeta /= np.abs(zeta)
    lhs = float(np.prod(np.abs(np.polyval(g, s * zeta))))
    rhs = float(np.prod(np.abs(np.polyval(g, (s * s) * w))) / ((1 + s**n) ** n))

    return Row(n, float(abs(np.sum(omega) - 1)), float(np.min(omega)),
               projector_error, quadrature_error, gap_product_error,
               equioscillation_error, relative_error(lhs, rhs), lhs ** (1 / n))


def random_roots(n: int, rng: np.random.Generator) -> np.ndarray:
    while True:
        theta = np.sort(rng.uniform(0, 2 * np.pi, size=n))
        gaps = np.diff(np.concatenate([theta, theta[:1] + 2 * np.pi]))
        if np.min(gaps) >= 2e-3:
            return np.exp(1j * theta)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1041)
    ap.add_argument("--samples", type=int, default=40)
    ap.add_argument("--max-n", type=int, default=14)
    ap.add_argument("--s", type=float, default=0.47)
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    roots = [unit_from_half_angle(q) for q in [1 / 1200, 8 / 11, 40 / 13, -83 / 27, -8 / 11]]
    rows = [probe(roots, args.s)]
    for n in range(2, args.max_n + 1):
        rows.extend(probe(random_roots(n, rng), args.s) for _ in range(args.samples))
    maxima = {
        "configuration_count": len(rows),
        "minimum_weight": min(r.minimum_weight for r in rows),
        **{field: max(getattr(r, field) for r in rows) for field in (
            "weight_sum_error", "weighted_projector_error", "quadrature_error",
            "gap_product_relative_error", "minimax_equioscillation_error",
            "dilation_product_relative_error", "dilation_geometric_mean")},
    }
    thresholds = {
        "weight_sum_error": 2e-4,
        "weighted_projector_error": 2e-4,
        "quadrature_error": 2e-4,
        "gap_product_relative_error": 2e-4,
        "minimax_equioscillation_error": 2e-4,
        "dilation_product_relative_error": 2e-4,
    }
    failures = {k: maxima[k] for k, v in thresholds.items() if maxima[k] > v}
    if maxima["minimum_weight"] <= -2e-7:
        failures["minimum_weight"] = maxima["minimum_weight"]
    if maxima["dilation_geometric_mean"] >= 1 + 2e-7:
        failures["dilation_geometric_mean"] = maxima["dilation_geometric_mean"]
    receipt = {"schema": "erdos1041_self_inversive_comparison_dual_probe_v1",
               "status": "pass" if not failures else "fail",
               "maxima": maxima, "thresholds": thresholds, "failures": failures,
               "evidence_boundary": "floating-point falsifier; analytic proof is authoritative"}
    print(json.dumps(receipt, indent=2, sort_keys=True))
    return 0 if not failures else 1


if __name__ == "__main__":
    raise SystemExit(main())
