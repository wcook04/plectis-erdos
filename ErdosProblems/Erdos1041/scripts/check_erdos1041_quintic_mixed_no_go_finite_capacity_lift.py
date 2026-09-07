#!/usr/bin/env python3
"""Exact root-box Form A-cut lift around the mixed Bernstein/J2 no-go."""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import comb

import numpy as np


@dataclass(frozen=True)
class Interval:
    lo: Fraction
    hi: Fraction

    @staticmethod
    def point(value: Fraction | int) -> "Interval":
        q = Fraction(value)
        return Interval(q, q)

    def __add__(self, other: "Interval | Fraction | int") -> "Interval":
        rhs = other if isinstance(other, Interval) else Interval.point(other)
        return Interval(self.lo + rhs.lo, self.hi + rhs.hi)

    __radd__ = __add__

    def __neg__(self) -> "Interval":
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other: "Interval | Fraction | int") -> "Interval":
        rhs = other if isinstance(other, Interval) else Interval.point(other)
        return self + (-rhs)

    def __rsub__(self, other: "Fraction | int") -> "Interval":
        return Interval.point(other) - self

    def __mul__(self, other: "Interval | Fraction | int") -> "Interval":
        rhs = other if isinstance(other, Interval) else Interval.point(other)
        products = (
            self.lo * rhs.lo,
            self.lo * rhs.hi,
            self.hi * rhs.lo,
            self.hi * rhs.hi,
        )
        return Interval(min(products), max(products))

    __rmul__ = __mul__


ComplexInterval = tuple[Interval, Interval]
RealPolynomial = list[Interval]
ComplexPolynomial = tuple[RealPolynomial, RealPolynomial]


def complex_add(left: ComplexInterval, right: ComplexInterval) -> ComplexInterval:
    return left[0] + right[0], left[1] + right[1]


def complex_neg(value: ComplexInterval) -> ComplexInterval:
    return -value[0], -value[1]


def complex_scale(value: ComplexInterval, scalar: Fraction) -> ComplexInterval:
    return value[0] * scalar, value[1] * scalar


def polynomial_multiply(left: RealPolynomial, right: RealPolynomial) -> RealPolynomial:
    out = [Interval.point(0) for _ in range(len(left) + len(right) - 1)]
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            out[i + j] = out[i + j] + a * b
    return out


def complex_polynomial_multiply(
    left: ComplexPolynomial, right: ComplexPolynomial
) -> ComplexPolynomial:
    rr = polynomial_multiply(left[0], right[0])
    ii = polynomial_multiply(left[1], right[1])
    ri = polynomial_multiply(left[0], right[1])
    ir = polynomial_multiply(left[1], right[0])
    return (
        [rr[k] - ii[k] for k in range(len(rr))],
        [ri[k] + ir[k] for k in range(len(ri))],
    )


def path_power_coefficients(
    roots: list[ComplexInterval], start: ComplexInterval, direction: ComplexInterval
) -> ComplexPolynomial:
    value: ComplexPolynomial = ([Interval.point(1)], [Interval.point(0)])
    for root in roots:
        factor: ComplexPolynomial = (
            [start[0] - root[0], direction[0]],
            [start[1] - root[1], direction[1]],
        )
        value = complex_polynomial_multiply(value, factor)
    return value


def squared_modulus_minus_one(power: ComplexPolynomial) -> RealPolynomial:
    real_sq = polynomial_multiply(power[0], power[0])
    imag_sq = polynomial_multiply(power[1], power[1])
    result = [real_sq[k] + imag_sq[k] for k in range(11)]
    result[0] = result[0] - 1
    return result


def bernstein_controls(power: RealPolynomial) -> list[Interval]:
    degree = len(power) - 1
    return [
        sum(
            (
                power[k] * Fraction(comb(j, k), comb(degree, k))
                for k in range(j + 1)
            ),
            start=Interval.point(0),
        )
        for j in range(degree + 1)
    ]


def form_a_cut_controls(
    roots: list[ComplexInterval], selected: tuple[int, int], scale: Fraction
) -> dict[str, Fraction]:
    path_data: list[tuple[str, ComplexInterval, ComplexInterval]] = []
    for root_index in selected:
        root = roots[root_index]
        path_data.append(
            (
                f"arm-{root_index}",
                complex_scale(root, scale),
                complex_scale(root, 1 - scale),
            )
        )
    first, second = (roots[index] for index in selected)
    path_data.append(
        (
            f"connector-{selected[0]}-{selected[1]}",
            complex_scale(first, scale),
            complex_scale(complex_add(complex_neg(first), second), scale),
        )
    )

    upper_controls: dict[str, Fraction] = {}
    for name, start, direction in path_data:
        power = path_power_coefficients(roots, start, direction)
        controls = bernstein_controls(squared_modulus_minus_one(power))
        upper_controls[name] = max(control.hi for control in controls)
    return upper_controls


def affine_root_box(
    regular: list[tuple[Fraction, Fraction]],
    target: list[tuple[Fraction, Fraction]],
    lo: Fraction,
    hi: Fraction,
) -> list[ComplexInterval]:
    roots: list[ComplexInterval] = []
    for start, end in zip(regular, target, strict=True):
        real_values = (
            start[0] + lo * (end[0] - start[0]),
            start[0] + hi * (end[0] - start[0]),
        )
        imag_values = (
            start[1] + lo * (end[1] - start[1]),
            start[1] + hi * (end[1] - start[1]),
        )
        roots.append(
            (
                Interval(min(real_values), max(real_values)),
                Interval(min(imag_values), max(imag_values)),
            )
        )
    return roots


def proposed_scale(
    regular: list[tuple[Fraction, Fraction]],
    target: list[tuple[Fraction, Fraction]],
    midpoint: Fraction,
) -> Fraction:
    """Float proposal only; every accepted sign is subsequently exact."""

    roots = np.array(
        [
            complex(
                float(start[0] + midpoint * (end[0] - start[0])),
                float(start[1] + midpoint * (end[1] - start[1])),
            )
            for start, end in zip(regular, target, strict=True)
        ]
    )
    polynomial = np.poly(roots)
    parameter = np.linspace(0.0, 1.0, 301)
    best = (float("inf"), Fraction(1, 100))
    for scale in (Fraction(k, 100) for k in range(1, 51)):
        value = float(scale)
        paths = (
            (value + (1 - value) * parameter) * roots[2],
            (value + (1 - value) * parameter) * roots[3],
            value * ((1 - parameter) * roots[2] + parameter * roots[3]),
        )
        score = max(float(np.max(abs(np.polyval(polynomial, path)))) for path in paths)
        if score < best[0]:
            best = score, scale
    return best[1]


def affine_chain_replay(
    target: list[tuple[Fraction, Fraction]],
) -> tuple[int, int, Fraction, list[Fraction]]:
    radius = Fraction(999999, 1000000)
    regular_directions = [
        ("1", "0"),
        ("0.30901699437494745", "0.9510565162951535"),
        ("-0.8090169943749473", "0.5877852522924732"),
        ("-0.8090169943749476", "-0.587785252292473"),
        ("0.30901699437494723", "-0.9510565162951536"),
    ]
    regular = [
        (radius * Fraction(x), radius * Fraction(y)) for x, y in regular_directions
    ]
    for endpoint in (regular, target):
        for x, y in endpoint:
            assert x * x + y * y < 1

    stack = [(Fraction(0), Fraction(1), 0)]
    accepted: list[tuple[Fraction, Fraction, Fraction, Fraction, int]] = []
    while stack:
        lo, hi, depth = stack.pop()
        scale = proposed_scale(regular, target, (lo + hi) / 2)
        roots = affine_root_box(regular, target, lo, hi)
        upper = max(form_a_cut_controls(roots, (2, 3), scale).values())
        if upper < 0:
            accepted.append((lo, hi, upper, scale, depth))
            continue
        assert depth < 24
        midpoint = (lo + hi) / 2
        stack.append((lo, midpoint, depth + 1))
        stack.append((midpoint, hi, depth + 1))

    ordered = sorted(accepted)
    assert ordered[0][0] == 0 and ordered[-1][1] == 1
    assert all(left[1] == right[0] for left, right in zip(ordered, ordered[1:]))
    assert sum(hi - lo for lo, hi, _, _, _ in ordered) == 1
    worst_upper = max(upper for _, _, upper, _, _ in ordered)
    scales = sorted({scale for _, _, _, scale, _ in ordered})
    return len(ordered), max(depth for *_, depth in ordered), worst_upper, scales


def main() -> None:
    raw = [
        ("0.9976274963", "-0.0688286176"),
        ("0.2336442603", "0.9723211196"),
        ("-0.8077935542", "0.5894638019"),
        ("-0.8347956985", "-0.5505580276"),
        ("0.3448410498", "-0.9386600292"),
    ]
    delta = Fraction(11, 100000)
    target = [(Fraction(x), Fraction(y)) for x, y in raw]
    roots: list[ComplexInterval] = []
    for x_raw, y_raw in raw:
        x, y = Fraction(x_raw), Fraction(y_raw)
        root = (Interval(x - delta, x + delta), Interval(y - delta, y + delta))
        roots.append(root)

    # This is the physical scale rho*(69/100) selected by the normalized
    # mixed atlas, rounded inward to the exact rational 87/200.
    scale = Fraction(87, 200)
    selected = (2, 3)

    upper_controls = form_a_cut_controls(roots, selected, scale)
    assert all(upper < 0 for upper in upper_controls.values())

    # The weakest box-wide margin is still larger than 1/1000 in |P|^2.
    assert max(upper_controls.values()) < Fraction(-1, 1000)

    cell_count, max_depth, chain_upper, chain_scales = affine_chain_replay(target)
    assert cell_count == 300
    assert max_depth == 16
    assert chain_upper < Fraction(-2, 5000000)

    print("quintic mixed no-go finite-capacity lift: PASS")
    print(f"root-coordinate box half-width: {float(delta):.1e}")
    print(f"fixed truncation fraction: {scale}")
    for name, upper in upper_controls.items():
        print(f"{name}: max Bernstein upper control={float(upper):.12f}")
    print("conclusion: every polynomial in the box has strict Form A-cut")
    print(
        f"affine actual-root atlas: {cell_count} exact boxes, "
        f"max depth {max_depth}, worst upper {float(chain_upper):.12g}"
    )
    print(
        "affine atlas scales: "
        + ",".join(str(scale) for scale in chain_scales)
    )


if __name__ == "__main__":
    main()
