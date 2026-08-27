#!/usr/bin/env python3
"""Exact-bound replay for the tied-Newton-face complete-spoke no-go."""

from __future__ import annotations

import argparse
import json
import math


def ray_values() -> dict[str, float]:
    s = math.sqrt(5.0)
    c = (s - 1.0) / 4.0
    d = (s + 1.0) / 4.0
    return {
        "ray_0_at_1_over_10": 1 / 10 + 10 * (1 / 10) ** 2 - (1 / 10) ** 5,
        "ray_1_4_at_1_over_1000": (
            c / 1000 - 10 * d / 1000**2 - 1 / 1000**5
        ),
        "ray_2_3_at_3_over_10": (
            -d * (3 / 10) + 10 * c * (3 / 10) ** 2 - (3 / 10) ** 5
        ),
    }


def connector_values() -> dict[str, object]:
    s = math.sqrt(5.0)
    left_bernstein_after_add_five = [
        -75 / 2 - 19 * s / 2,
        -25 / 2 - 117 * s / 8,
        -25 / 6 - 107 * s / 12,
        -39 * s / 8,
        -5 * s / 2,
    ]
    right_bernstein_after_add_five = [
        -5 * s / 2,
        -s / 8,
        -25 / 6 + 7 * s / 12,
        -25 / 2 - 3 * s / 8,
        -75 / 2 + 19 * s / 2,
    ]
    c = (s - 1.0) / 4.0
    d = (s + 1.0) / 4.0
    return {
        "left_bernstein_after_add_five": left_bernstein_after_add_five,
        "right_bernstein_after_add_five": right_bernstein_after_add_five,
        "maximum_bernstein_coefficient_after_add_five": max(
            left_bernstein_after_add_five + right_bernstein_after_add_five
        ),
        "ray_one_at_two": 2 * c - 40 * d - 32,
        "ray_two_at_two": -2 * d + 40 * c - 32,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    values = ray_values()
    connector = connector_values()
    exact_rational_gates = {
        "eleven_fifths_squared_lt_five": 11**2 < 5 * 5**2,
        "five_lt_three_squared": 5 < 3**2,
        "ray_zero_rational_numerator_positive": 19999 > 0,
        "ray_two_lower_bound_positive": (
            # q_2(3/10) > 3((11/5)-2)/20 - 243/100000.
            3 * (11 / 5 - 2) / 20 - 243 / 100000 > 0
        ),
    }
    passed = (
        all(exact_rational_gates.values())
        and min(values.values()) > 0.0
        and float(connector["maximum_bernstein_coefficient_after_add_five"])
        <= 0.0
        and float(connector["ray_one_at_two"]) < 0.0
        and float(connector["ray_two_at_two"]) < 0.0
    )
    receipt = {
        "schema": "erdos1041_tied_newton_face_two_spoke_no_go_v1",
        "passed": passed,
        "model": "H(z)=Re(z+10z^2-z^5)",
        "ray_values": values,
        "connector": connector,
        "exact_rational_gates": exact_rational_gates,
        "conclusion": (
            "Every fifth-root direction has a point with H>0; no complete "
            "safe model spoke exists. The adjacent ray types 1,2 are instead "
            "rescued by the radius-two connector, with H<=-5 on its chord."
        ),
        "claim_boundary": (
            "This refutes only complete-spoke selection on general tied "
            "Newton faces. It does not refute truncated connectors, Form "
            "A-cut, the proved quintic neighbourhood, or Erdos #1041."
        ),
    }
    print(json.dumps(receipt, indent=2, sort_keys=True) if args.json else receipt)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
