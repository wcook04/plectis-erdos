#!/usr/bin/env python3
"""Exact regressions for the anchored joint (3,5) transport observable."""

from __future__ import annotations

import argparse
import math

import sympy as sp


def pullback(d: int, multiplier: int) -> sp.Matrix:
    matrix = sp.zeros(d, d)
    for residue in range(d):
        matrix[residue, (multiplier * residue) % d] = 1
    return matrix


def nullity(matrix: sp.Matrix) -> int:
    # DomainMatrix keeps these sparse integer operators in exact fraction-free
    # arithmetic; Matrix.rank() densifies and is prohibitively slow near d=300.
    return matrix.cols - sp.polys.matrices.DomainMatrix.from_Matrix(matrix).rank()


def joint_fixed_nullity(d: int) -> int:
    identity = sp.eye(d)
    return nullity((pullback(d, 3) - identity).col_join(pullback(d, 5) - identity))


def operator_nullities(d: int) -> tuple[int, int, int]:
    identity = sp.eye(d)
    p3 = pullback(d, 3)
    p5 = pullback(d, 5)
    p15 = p3 * p5
    intercept = p15 - 3 * p3 - 2 * p5 + 4 * identity
    slope = 15 * p15 - 9 * p3 - 10 * p5 + 4 * identity
    return joint_fixed_nullity(d), nullity(intercept), nullity(slope)


def window(shift: int, base: int, depth: int) -> int:
    value = 0
    for j in range(depth):
        value = 2 * value + int(sp.totient(base + shift + 1 + j)) - int(
            sp.totient(base + 1 + j)
        )
    return value


def period_lcm(t: int) -> int:
    height = 1
    for value in range(1, t + 1):
        height = math.lcm(height, value)
    return height


def check_kernel_regressions(max_d: int) -> tuple[int, int]:
    unit_channels = [
        d
        for d in range(2, max_d + 1)
        if math.gcd(d, 15) == 1 and sp.mobius(d) != 0
    ]
    fixed_total = 0
    for d in unit_channels:
        fixed, intercept, slope = operator_nullities(d)
        assert intercept == fixed, (d, "intercept", intercept, fixed)
        assert slope == fixed, (d, "slope", slope, fixed)
        fixed_total += fixed

    expected_small = {
        2: (2, 2, 2),
        3: (1, 1, 1),
        6: (2, 2, 2),
        15: (1, 1, 1),
    }
    for d, expected in expected_small.items():
        assert operator_nullities(d) == expected, (d, operator_nullities(d), expected)

    identity = sp.eye(3)
    q0_intercept = pullback(3, 5) - 2 * pullback(3, 3) + identity
    assert nullity(q0_intercept) == 2
    return len(unit_channels), fixed_total


def check_window_receipt(t: int, depth: int) -> tuple[int, int, int, int]:
    height = period_lcm(t)
    value = (
        window(14 * height, height, depth)
        - 3 * window(2 * height, height, depth)
        - 2 * window(4 * height, height, depth)
    )
    modulus = 1 << depth
    residue = value % modulus
    radius = 19 * height + 5 * depth + 5
    assert radius < residue < modulus - radius
    return height, modulus, residue, radius


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-d", type=int, default=300)
    parser.add_argument("--t", type=int, default=26)
    parser.add_argument("--depth", type=int, default=42)
    args = parser.parse_args()

    channel_count, fixed_total = check_kernel_regressions(args.max_d)
    height, modulus, residue, radius = check_window_receipt(args.t, args.depth)
    print(
        "joint35_exact_regression: PASS\n"
        f"unit_squarefree_channels={channel_count}\n"
        f"joint_fixed_nullity_total={fixed_total}\n"
        f"t={args.t} H={height} L={args.depth}\n"
        f"modulus={modulus}\n"
        f"window_residue={residue}\n"
        f"radius={radius}\n"
        f"upper_endpoint={modulus - radius}"
    )


if __name__ == "__main__":
    main()
