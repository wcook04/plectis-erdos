#!/usr/bin/env python3
"""Exact and numerical replay for the tied-face critical-value trace.

The exact arm applies Newton's identities to the derivative of

    Q(z) = sum_{1 <= m < n/2} A_m z^m - z^n

over Gaussian-rational test coefficients.  It verifies that every active
critical-point power sum, and hence the critical-value trace, is identically
zero.  The numerical arm relocates the critical points and checks the same
trace independently.  It is a regression probe, not proof authority.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction

import numpy as np


Gaussian = tuple[Fraction, Fraction]


def gadd(x: Gaussian, y: Gaussian) -> Gaussian:
    return x[0] + y[0], x[1] + y[1]


def gmul(x: Gaussian, y: Gaussian) -> Gaussian:
    return x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0]


def gscale(q: Fraction, x: Gaussian) -> Gaussian:
    return q * x[0], q * x[1]


ZERO: Gaussian = (Fraction(0), Fraction(0))


def active_coefficients(n: int) -> dict[int, Gaussian]:
    return {
        m: (Fraction((3 * m + n) % 11 - 5, m + 1),
            Fraction((5 * m + 2 * n) % 13 - 6, n + m))
        for m in range(1, (n - 1) // 2 + 1)
    }


def derivative_monic_coefficients(n: int, active: dict[int, Gaussian]) -> list[Gaussian]:
    """Ascending coefficients of Q'/(-n), whose degree is N=n-1."""
    out = [ZERO for _ in range(n)]
    out[n - 1] = (Fraction(1), Fraction(0))
    for m, a in active.items():
        out[m - 1] = gscale(Fraction(-m, n), a)
    return out


def newton_power_sums(monic: list[Gaussian], upto: int) -> list[Gaussian]:
    """Power sums of the roots from the monic coefficient list."""
    degree = len(monic) - 1
    sums = [ZERO]
    for k in range(1, upto + 1):
        value = ZERO
        for j in range(1, k):
            value = gadd(value, gmul(monic[degree - j], sums[k - j]))
        value = gadd(value, gscale(Fraction(k), monic[degree - k]))
        sums.append(gscale(Fraction(-1), value))
    return sums


def exact_row(n: int) -> dict[str, object]:
    active = active_coefficients(n)
    monic = derivative_monic_coefficients(n, active)
    powers = newton_power_sums(monic, max(active))
    trace = ZERO
    for m, a in active.items():
        trace = gadd(trace, gmul(gscale(Fraction(n - m, n), a), powers[m]))
    gap_start = max(active)
    absent_upper = all(monic[k] == ZERO for k in range(gap_start, n - 1))
    return {
        "degree": n,
        "active_degrees": sorted(active),
        "derivative_upper_gap": absent_upper,
        "active_power_sums_zero": all(powers[m] == ZERO for m in active),
        "critical_value_trace": [str(trace[0]), str(trace[1])],
    }


def numerical_row(n: int) -> dict[str, object]:
    active_q = active_coefficients(n)
    active = {m: complex(float(a[0]), float(a[1])) for m, a in active_q.items()}
    derivative = np.zeros(n, dtype=np.complex128)
    derivative[0] = -n
    for m, a in active.items():
        derivative[n - 1 - (m - 1)] = m * a
    critical = np.roots(derivative)
    values = np.array([
        sum(a * c**m for m, a in active.items()) - c**n
        for c in critical
    ])
    derivative_residual = max(abs(
        -n * c ** (n - 1) + sum(m * a * c ** (m - 1) for m, a in active.items())
    ) for c in critical)
    return {
        "degree": n,
        "critical_count": len(critical),
        "trace_abs": float(abs(np.sum(values))),
        "minimum_real_critical_value": float(np.min(values.real)),
        "maximum_derivative_residual": float(derivative_residual),
    }


def evaluate_model(z: np.ndarray | complex, n: int, active: np.ndarray):
    value = -(z ** n)
    for m in range(1, len(active)):
        value = value + active[m] * z ** m
    return value


def critical_points(n: int, active: np.ndarray) -> np.ndarray:
    derivative = np.zeros(n, dtype=np.complex128)
    derivative[0] = -n
    for m in range(1, len(active)):
        derivative[n - m] = m * active[m]
    return np.roots(derivative)


def best_critical_hub_certificate(n: int, active: np.ndarray) -> float:
    """Coarse minimax for two straight hub arms plus origin-ray tails.

    A negative return is a genuine sampled certificate only after exact
    maximisation; here it is used solely to locate or pressure a mechanism.
    """
    roots = np.exp(2j * np.pi * np.arange(n) / n)
    scale = max([abs(active[m]) ** (1 / (n - m))
                 for m in range(1, len(active)) if abs(active[m]) > 0] + [1.0])
    radii = np.geomspace(0.025 * scale, 6 * scale, 34)
    segment_parameter = np.linspace(0, 1, 121)
    best = float("inf")
    for c in critical_points(n, active):
        if evaluate_model(c, n, active).real > 1e-9:
            continue
        for radius in radii:
            endpoints = radius * roots
            rows: list[tuple[int, float, float]] = []
            tail_radii = np.geomspace(radius, 10 * scale, 150)
            for j, endpoint in enumerate(endpoints):
                segment = c + (endpoint - c) * segment_parameter
                segment_max = float(np.max(evaluate_model(segment, n, active).real))
                tail = tail_radii * roots[j]
                tail_max = float(np.max(evaluate_model(tail, n, active).real))
                rows.append((j, max(segment_max, tail_max), abs(endpoint - c)))
            for x in range(n):
                for y in range(x + 1, n):
                    gap = min((y - x) % n, (x - y) % n)
                    if n % 2 == 0 and gap == n // 2:
                        continue
                    defect = rows[x][2] + rows[y][2] - 2 * radius
                    best = min(best, max(rows[x][1], rows[y][1], defect))
    return best


def metric_probe() -> dict[str, object]:
    rng = np.random.default_rng(20260825)
    rows = []
    for n in range(5, 10):
        mode_count = (n - 1) // 2
        scores = []
        for _ in range(16):
            active = np.zeros(mode_count + 1, dtype=np.complex128)
            raw = rng.normal(size=mode_count) + 1j * rng.normal(size=mode_count)
            raw /= np.max(np.abs(raw))
            active[1:] = (10 ** rng.uniform(-1, 1)) * raw
            scores.append(best_critical_hub_certificate(n, active))
        rows.append({
            "degree": n,
            "sample_count": len(scores),
            "worst_best_sampled_score": float(max(scores)),
            "sampled_failures": int(sum(score > 2e-4 for score in scores)),
        })
    return {
        "status": "evidence_only",
        "seed": 20260825,
        "rows": rows,
        "interpretation": (
            "A score below zero means the sampled critical hub, two straight arms, "
            "two outward root rays, and the metric defect all passed on the grids. "
            "Sampling cannot certify containment and the universal statement is open."
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--metric-probe", action="store_true")
    args = parser.parse_args()

    exact = [exact_row(n) for n in range(5, 41)]
    numerical = [numerical_row(n) for n in range(5, 16)]
    ok = (
        all(row["derivative_upper_gap"] for row in exact)
        and all(row["active_power_sums_zero"] for row in exact)
        and all(row["critical_value_trace"] == ["0", "0"] for row in exact)
        and all(row["minimum_real_critical_value"] <= 1e-12 for row in numerical)
        and max(row["trace_abs"] for row in numerical) < 2e-5
        and max(row["maximum_derivative_residual"] for row in numerical) < 2e-4
    )
    payload = {
        "schema": "erdos1041_tied_newton_face_critical_trace_check_v1",
        "status": "pass" if ok else "fail",
        "exact_degree_range": [5, 40],
        "numerical_degree_range": [5, 15],
        "exact_rows": exact,
        "numerical_max_trace_abs": max(row["trace_abs"] for row in numerical),
        "numerical_min_real_values": {
            str(row["degree"]): row["minimum_real_critical_value"] for row in numerical
        },
        "claim_boundary": (
            "The exact recurrence verifies the Newton-sum mechanism on deterministic "
            "Gaussian-rational instances and the analytic proof is in the companion note. "
            "The numerical root replay is evidence only. No metric connector is claimed."
        ),
    }
    if args.metric_probe:
        payload["metric_probe"] = metric_probe()
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(f"critical trace: {payload['status']}")
        print(f"exact degrees: 5..40; numerical max |trace|={payload['numerical_max_trace_abs']:.3e}")
        print("minimum real critical values:", payload["numerical_min_real_values"])
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
