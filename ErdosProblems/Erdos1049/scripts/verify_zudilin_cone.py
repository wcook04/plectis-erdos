#!/usr/bin/env python3
"""Exact finite checks for the Erdős #1049 Zudilin-cone return.

The script verifies the finite floor, endpoint-exponent, and cyclotomic-unit
claims used to select the Lean interface.  It deliberately does not certify
the source-backed analytic asymptotics or the all-scale two-ray search.
"""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path

import sympy as sp


LOGICAL_RECEIPT_ID = "erdos1049-zudilin-cone-finite-check/1"


def parameter_rows() -> list[tuple[int, int, int, int]]:
    return [
        (a0, a1, a2, b)
        for a0 in range(1, 9)
        for a1 in range(1, 9)
        for a2 in range(a1, 9)
        for b in range(a1 + a2, a0 + a2 + 1)
    ]


def cone_data(
    a0: int, a1: int, a2: int, b: int
) -> tuple[list[int], int, int]:
    c00 = a0 + a1 + a2 - b - 1
    c01 = a0 - 1
    c11 = a1 - 1
    c21 = a2 - 1
    c12 = b - a1 - 1
    c22 = b - a2 - 1
    m = max(c00, c01, c11, c21, c12, c22)
    nu = [
        max(
            0,
            c21 // ell + c22 // ell - c11 // ell - c12 // ell,
            c01 // ell + c21 // ell - c00 // ell - c12 // ell,
        )
        for ell in range(2, m + 1)
    ]
    return nu, a2 - a1, a0 + a2 - b


def norm_exp_twice(a0: int, a1: int, a2: int, b: int) -> int:
    return (
        a1 * (a1 - 1)
        + 2 * a0 * a1
        + 2 * (b - a2) * (a2 - a1)
    )


def partial_exp_twice(a1: int, a2: int, b: int, k: int) -> int:
    return (
        a1 * (a1 - 1)
        - (b - a2) * (b - a2 - 1)
        + (b - k) * (b - k - 1)
    )


def bottom_exp_twice(a0: int, a1: int, a2: int, b: int, k: int) -> int:
    return (
        partial_exp_twice(a1, a2, b, k)
        + 2 * a0 * k
        - norm_exp_twice(a0, a1, a2, b)
    )


def raw_degree_twice(a0: int, a1: int, a2: int, b: int, k: int) -> int:
    return (
        2 * a0 * k
        + partial_exp_twice(a1, a2, b, k)
        + 2 * (a1 - 1) * (k - a1)
        + 2 * (b - k - 1) * (k - a2)
    )


def homogeneous_cyclotomic_value(ell: int) -> int:
    x = sp.symbols("x")
    polynomial = sp.Poly(sp.cyclotomic_poly(ell, x), x, domain=sp.ZZ)
    degree = polynomial.degree()
    coefficients = [int(value) for value in polynomial.all_coeffs()]
    return sum(
        coefficient * 3 ** (degree - index) * 2**index
        for index, coefficient in enumerate(coefficients)
    )


def main() -> None:
    rows = parameter_rows()
    assert len(rows) == 750

    strict_rows = [
        row
        for row in rows
        if min(row[:3]) >= 2
        and row[1] + row[2] < row[3]
        and row[3] < row[0] + row[2]
    ]
    assert len(strict_rows) == 210

    dt_positive_count = 0
    max_m = 0
    for a0, a1, a2, b in rows:
        nu, d, t = cone_data(a0, a1, a2, b)
        max_m = max(max_m, max(a0 + a1 + a2 - b - 1, a0 - 1, a1 - 1,
                               a2 - 1, b - a1 - 1, b - a2 - 1))
        assert all(value in (0, 1) for value in nu)
        if d * t > 0:
            dt_positive_count += 1

        indices = list(range(a2, b))
        bottom = [bottom_exp_twice(a0, a1, a2, b, k) for k in indices]
        raw_degrees = [raw_degree_twice(a0, a1, a2, b, k) for k in indices]

        assert bottom[0] == 2 * d * t
        assert bottom.index(min(bottom)) == 0
        assert raw_degrees.index(max(raw_degrees)) == len(raw_degrees) - 1

        for k in indices[:-1]:
            assert (
                bottom_exp_twice(a0, a1, a2, b, k + 1)
                - bottom_exp_twice(a0, a1, a2, b, k)
                == 2 * (a0 - b + k + 1)
            )
            assert (
                raw_degree_twice(a0, a1, a2, b, k + 1)
                - raw_degree_twice(a0, a1, a2, b, k)
                == 2 * (a0 + a1 + a2 - k - 2)
            )

    assert dt_positive_count == 462

    cyclotomic_rows = []
    for ell in range(1, 65):
        value = homogeneous_cyclotomic_value(ell)
        assert math.gcd(value, 6) == 1
        cyclotomic_rows.append(
            {
                "ell": ell,
                "homogeneous_value": value,
                "gcd_with_6": 1,
            }
        )

    selected_ray = []
    for n in range(1, 9):
        a0, a1, a2, b = 14 * n + 1, 12 * n + 1, 14 * n + 1, 27 * n + 2
        _, d, t = cone_data(a0, a1, a2, b)
        assert d * t == 2 * n * n
        assert bottom_exp_twice(a0, a1, a2, b, a2) == 4 * n * n
        selected_ray.append({"n": n, "d_times_t": d * t})

    script_sha256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print(
        json.dumps(
            {
                "schema": LOGICAL_RECEIPT_ID,
                "authority": (
                    "exact_finite_computation_not_all_scale_or_analytic_proof"
                ),
                "script_sha256": script_sha256,
                "parameter_box": {
                    "bounds": "1<=a0,a1,a2<=8; a1<=a2; a1+a2<=b<=a0+a2",
                    "row_count": len(rows),
                    "strict_positive_ray_count": len(strict_rows),
                    "dt_positive_count": dt_positive_count,
                    "max_c_parameter": max_m,
                    "checks": [
                        "every permutation exponent nu_l is 0 or 1",
                        "bottom exponent has its unique minimum at k=a2",
                        "raw degree has its unique maximum at k=b-1",
                        "both exact doubled first-difference identities",
                    ],
                },
                "cyclotomic_unit_check": {
                    "range": "1<=ell<=64",
                    "rows": cyclotomic_rows,
                },
                "selected_ray": selected_ray,
                "excluded_claims": [
                    "source-backed C0/C1 asymptotics",
                    "all-scale coefficient endpoint formulas for U and V",
                    "the unavailable signed-pair search harness and its winners",
                    "irrationality of the 3/2 Lambert value",
                ],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
