#!/usr/bin/env python3
"""Exact replay for the separated-quintic centroid-spoke counterexample."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction

Q = Fraction
G = tuple[Q, Q]


def add(a: G, b: G) -> G:
    return a[0] + b[0], a[1] + b[1]


def sub(a: G, b: G) -> G:
    return a[0] - b[0], a[1] - b[1]


def mul(a: G, b: G) -> G:
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def scale(q: Q, a: G) -> G:
    return q * a[0], q * a[1]


def norm_sq(a: G) -> Q:
    return a[0] * a[0] + a[1] * a[1]


def circle(s: Q) -> G:
    den = 1 + s * s
    return (1 - s * s) / den, 2 * s / den


PARAMETERS = (
    Q(0),
    Q(5, 8),
    Q(7, 2),
    -Q(11, 3),
    -Q(5, 7),
)
RADIUS = Q(99999, 100000)
WAYPOINTS = {1: Q(23, 100), 2: Q(1, 4), 3: Q(1, 8), 4: Q(3, 10)}


def polynomial_norm_sq(roots: tuple[G, ...], z: G) -> Q:
    value: G = (Q(1), Q(0))
    for root in roots:
        value = mul(value, sub(z, root))
    return norm_sq(value)


def fraction_payload(x: Q) -> dict[str, object]:
    return {
        "numerator": str(x.numerator),
        "denominator": str(x.denominator),
        "decimal": float(x),
    }


def build_receipt() -> dict[str, object]:
    directions = tuple(circle(s) for s in PARAMETERS)
    assert all(norm_sq(u) == 1 for u in directions)
    roots = tuple(scale(RADIUS, u) for u in directions)
    assert len(set(roots)) == 5
    assert all(norm_sq(a) == RADIUS * RADIUS < 1 for a in roots)
    centroid = scale(Q(1, 5), (sum(a[0] for a in roots), sum(a[1] for a in roots)))

    pair_rows = []
    for i in range(5):
        for j in range(i):
            distance_sq = norm_sq(sub(roots[i], roots[j]))
            assert distance_sq > Q(5, 9)
            pair_rows.append((distance_sq, i, j))
    minimum_distance_sq, minimum_i, minimum_j = min(pair_rows)

    spoke_rows = []
    for j, t in WAYPOINTS.items():
        z = add(centroid, scale(t, sub(roots[j], centroid)))
        value_sq = polynomial_norm_sq(roots, z)
        gap = value_sq - 1
        assert gap > Q(1, 5000)
        spoke_rows.append(
            {
                "root_index": j,
                "parameter": f"{t.numerator}/{t.denominator}",
                "value_sq": fraction_payload(value_sq),
                "gap_above_one": fraction_payload(gap),
                "gap_gt_one_over_5000": True,
            }
        )

    return {
        "schema": "erdos1041_centroid_hub_counterexample_receipt_v1",
        "status": "exact_pass",
        "radius": f"{RADIUS.numerator}/{RADIUS.denominator}",
        "root_count": 5,
        "all_roots_strictly_inside_unit_disk": True,
        "all_pair_squares_gt_5_over_9": True,
        "minimum_pair": [minimum_i, minimum_j],
        "minimum_pair_square": fraction_payload(minimum_distance_sq),
        "centroid": {
            "re": fraction_payload(centroid[0]),
            "im": fraction_payload(centroid[1]),
        },
        "escaping_centroid_spoke_count": len(spoke_rows),
        "safe_centroid_spoke_count_upper_bound": 1,
        "spoke_certificates": spoke_rows,
        "claim_ceiling": (
            "The universal two-spoke centroid visibility mechanism is false "
            "already for a quantitatively separated quintic. Erdos 1041 is not refuted."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.parse_args()
    print(json.dumps(build_receipt(), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
