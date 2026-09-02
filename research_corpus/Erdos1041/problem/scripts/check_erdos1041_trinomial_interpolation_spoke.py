#!/usr/bin/env python3
"""Deterministic replay of the endpoint-vanishing interpolation identities."""

from __future__ import annotations

import cmath
import json
import math
import random


def main() -> None:
    rng = random.Random(1041_20260825)
    rows = 0
    max_identity_error = 0.0
    max_slack_identity_error = 0.0
    max_envelope_ratio = 0.0
    fixed_exponent_failures = 0

    for n in range(3, 13):
        for _ in range(24):
            radius = rng.uniform(0.15, 0.92)
            a = radius * cmath.exp(1j * rng.uniform(-math.pi, math.pi))
            b = {
                k: rng.uniform(0.0, 0.12)
                * cmath.exp(1j * rng.uniform(-math.pi, math.pi))
                for k in range(1, n)
            }
            middle = sum(b[k] * a**k for k in b)
            c = -(a**n + middle)
            if abs(c) >= 0.98:
                continue

            for j in range(1, n):
                A = middle / a**j
                failed_here = False
                for q in range(81):
                    t = q / 80.0
                    f = (t * a) ** n + sum(b[k] * (t * a) ** k for k in b) + c
                    g = (t * a) ** n + A * (t * a) ** j + c
                    remainder = sum(
                        b[k] * a**k * (t**k - t**j) for k in b
                    )
                    scale = max(1.0, abs(f), abs(g), abs(remainder))
                    max_identity_error = max(
                        max_identity_error, abs((f - g) - remainder) / scale
                    )

                    budget = (1 - t**j) * abs(c) + (t**j - t**n) * abs(a) ** n
                    slack = 1 - budget
                    decomposed = (
                        t**n
                        + (1 - t**j) * (1 - abs(c))
                        + (t**j - t**n) * (1 - abs(a) ** n)
                    )
                    max_slack_identity_error = max(
                        max_slack_identity_error, abs(slack - decomposed)
                    )

                    envelope = sum(
                        abs(k - j)
                        * abs(b[k])
                        * abs(a) ** k
                        * t ** min(k, j)
                        * (1 - t)
                        for k in b
                        if k != j
                    )
                    actual_majorant = sum(
                        abs(b[k]) * abs(a) ** k * abs(t**k - t**j)
                        for k in b
                        if k != j
                    )
                    if envelope > 0:
                        max_envelope_ratio = max(
                            max_envelope_ratio, actual_majorant / envelope
                        )
                    if actual_majorant >= slack:
                        failed_here = True
                    if abs(g) > budget + 2e-13:
                        raise AssertionError("trinomial norm budget failed")
                    rows += 1
                fixed_exponent_failures += int(failed_here)

    # A cancellation-heavy root can defeat every fixed-j majorant certificate.
    # This guards against promoting the sufficient condition to a universal
    # theorem: the next step really is a selector/gluing argument.
    n = 6
    a = 0.85 + 0j
    b = {k: 0j for k in range(1, n)}
    b[1] = 10 + 0j
    b[2] = -10 / a
    c = -(a**n + sum(b[k] * a**k for k in b))
    failed_js = []
    for j in range(1, n):
        for q in range(1, 80):
            t = q / 80.0
            slack = 1 - (
                (1 - t**j) * abs(c) + (t**j - t**n) * abs(a) ** n
            )
            majorant = sum(
                abs(b[k]) * abs(a) ** k * abs(t**k - t**j)
                for k in b
                if k != j
            )
            if majorant >= slack:
                failed_js.append(j)
                break

    result = {
        "schema": "erdos1041_trinomial_interpolation_spoke_check_v1",
        "checked_grid_points": rows,
        "max_interpolation_identity_relative_error": max_identity_error,
        "max_slack_identity_error": max_slack_identity_error,
        "max_actual_majorant_over_endpoint_envelope": max_envelope_ratio,
        "fixed_exponent_failures_observed": fixed_exponent_failures,
        "cancellation_negative_control": {
            "root_norm": abs(a),
            "constant_norm": abs(c),
            "failed_exponents": failed_js,
            "all_exponents_fail_somewhere": failed_js == list(range(1, n)),
        },
        "claim_guard": "fixed_j_certificate_not_universal_selector",
        "status": "PASS"
        if max_identity_error < 5e-13
        and max_slack_identity_error < 5e-13
        and max_envelope_ratio <= 1 + 5e-13
        and failed_js == list(range(1, n))
        else "FAIL",
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    if result["status"] != "PASS":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
