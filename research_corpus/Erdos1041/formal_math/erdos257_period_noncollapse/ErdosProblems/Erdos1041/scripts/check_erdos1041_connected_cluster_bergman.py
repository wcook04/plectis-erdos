#!/usr/bin/env python3
"""Deterministic scalar audit for the connected-cluster Bergman certificate."""

from __future__ import annotations

import argparse
import json
import math


def overlap_radius(r: float) -> float:
    return 2.0 * r / (1.0 + r * r)


def logarithmic_factor(k: int, q: float) -> float:
    x = q ** (2.0 / k)
    return math.log1p(x) - math.log1p(-x)


def cluster_margin(k: int, q: float, alpha: float) -> float:
    return 2.0 - alpha * logarithmic_factor(k, q)


def capacity_threshold(k: int, kappa: float) -> float:
    return math.tanh(1.0 / (kappa * kappa)) ** (k / 2.0)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    max_overlap_identity_error = 0.0
    max_threshold_margin_error = 0.0
    row_count = 0
    certified_count = 0
    saturated_threshold_count = 0
    for k in range(2, 41):
        for q_index in range(1, 1000):
            q = q_index / 1000.0
            r = q ** (1.0 / k)
            delta = overlap_radius(r)
            lhs = 1.0 - delta * delta
            rhs = ((1.0 - r * r) / (1.0 + r * r)) ** 2
            max_overlap_identity_error = max(
                max_overlap_identity_error, abs(lhs - rhs)
            )
            for kappa in (0.25, 0.3891, 0.5811, 0.75, 1.0):
                threshold = capacity_threshold(k, kappa)
                x_threshold = math.tanh(1.0 / (kappa * kappa))
                # `log1p(-x)` is ill-conditioned once tanh rounds into the
                # last few ulps below one.  The inversion remains analytic;
                # audit it only in the representable regime and receipt the
                # skipped saturated rows explicitly.
                if x_threshold < 1.0 - 1.0e-12:
                    margin = cluster_margin(k, threshold, kappa * kappa)
                    max_threshold_margin_error = max(
                        max_threshold_margin_error, abs(margin)
                    )
                else:
                    saturated_threshold_count += 1
                certified_count += int(q <= threshold)
                row_count += 1

    passed = (
        max_overlap_identity_error <= 2.0e-14
        and max_threshold_margin_error <= 2.0e-11
    )
    receipt = {
        "schema": "erdos1041_connected_cluster_bergman_check_v1",
        "passed": passed,
        "row_count": row_count,
        "certified_count": certified_count,
        "max_overlap_identity_error": max_overlap_identity_error,
        "max_threshold_margin_error": max_threshold_margin_error,
        "saturated_threshold_count": saturated_threshold_count,
        "claim_boundary": (
            "Scalar identity and threshold inversion only; the analytic "
            "Riemann-Hurwitz, connected-cover, and Bergman steps are in the note."
        ),
    }
    if args.json:
        print(json.dumps(receipt, indent=2, sort_keys=True))
    else:
        print(receipt)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
