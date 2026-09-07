#!/usr/bin/env python3
"""Deterministic finite-atlas search for the normalized quintic mixed model.

The current implementation is a fail-closed atlas generator.  It uses
stereographic phase coordinates, degree-elevated Bernstein chord controls,
and analytic sparse-ray criteria.  A box is counted only when one fixed root
pair and one fixed rational radius certifies the complete box.  Boxes wholly
inside the separately proved equality-tetrahedron neighbourhood are routed to
that theorem.
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass
from fractions import Fraction

import numpy as np


DEGREE = 2000
LOCAL_RADIUS = 17 / 2500
MAX_DEPTH = 32
SCALE = 10**24


def floor_div(numerator: int, denominator: int) -> int:
    return numerator // denominator


def ceil_div(numerator: int, denominator: int) -> int:
    return -((-numerator) // denominator)


@dataclass(frozen=True)
class Interval:
    lo: int
    hi: int

    @staticmethod
    def fraction(value: Fraction) -> "Interval":
        return Interval(
            floor_div(value.numerator * SCALE, value.denominator),
            ceil_div(value.numerator * SCALE, value.denominator),
        )

    @staticmethod
    def integer(value: int) -> "Interval":
        return Interval(value * SCALE, value * SCALE)

    def __add__(self, other: "Interval") -> "Interval":
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self) -> "Interval":
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other: "Interval") -> "Interval":
        return self + (-other)

    def __mul__(self, other: "Interval") -> "Interval":
        products = (
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        )
        return Interval(floor_div(min(products), SCALE), ceil_div(max(products), SCALE))

    def scale(self, value: Fraction) -> "Interval":
        products = (self.lo * value.numerator, self.hi * value.numerator)
        return Interval(
            floor_div(min(products), value.denominator),
            ceil_div(max(products), value.denominator),
        )

    def square(self) -> "Interval":
        return self * self

    def abs_upper(self) -> int:
        return max(abs(self.lo), abs(self.hi))


ComplexInterval = tuple[Interval, Interval]


def complex_add(left: ComplexInterval, right: ComplexInterval) -> ComplexInterval:
    return left[0] + right[0], left[1] + right[1]


def complex_scale(value: ComplexInterval, scalar: Fraction) -> ComplexInterval:
    return value[0].scale(scalar), value[1].scale(scalar)


def complex_mul(left: ComplexInterval, right: ComplexInterval) -> ComplexInterval:
    return left[0] * right[0] - left[1] * right[1], left[0] * right[1] + left[1] * right[0]


def sqrt_interval(value: Interval) -> Interval:
    if value.lo < 0:
        raise ValueError("square-root interval crosses zero")
    lo = math.isqrt(value.lo * SCALE)
    hi = math.isqrt(value.hi * SCALE)
    if hi * hi < value.hi * SCALE:
        hi += 1
    return Interval(lo, hi)


def square_interval(value: Interval) -> Interval:
    """Outward square, including intervals that cross zero."""
    endpoint_squares = (value.lo * value.lo, value.hi * value.hi)
    lower_raw = 0 if value.lo <= 0 <= value.hi else min(endpoint_squares)
    return Interval(
        floor_div(lower_raw, SCALE),
        ceil_div(max(endpoint_squares), SCALE),
    )


def interval_power(value: Interval, exponent: int) -> Interval:
    result = Interval.integer(1)
    for _ in range(exponent):
        result = result * value
    return result


def cube_root_interval(value: Interval) -> Interval:
    if value.lo < 0:
        raise ValueError("cube-root interval must be nonnegative")
    lo_raw = value.lo * SCALE**2
    hi_raw = value.hi * SCALE**2
    lo = integer_nth_root(lo_raw, 3)
    hi = integer_nth_root(hi_raw, 3)
    if hi**3 < hi_raw:
        hi += 1
    return Interval(lo, hi)


def divide_positive(numerator: Interval, denominator: Interval) -> Interval:
    if numerator.lo < 0 or denominator.lo <= 0:
        raise ValueError("positive interval division required")
    return Interval(
        floor_div(numerator.lo * SCALE, denominator.hi),
        ceil_div(numerator.hi * SCALE, denominator.lo),
    )


def minimum_interval(left: Interval, right: Interval) -> Interval:
    return Interval(min(left.lo, right.lo), min(left.hi, right.hi))


def interval_decimal(value: int) -> float:
    return value / SCALE


def integer_nth_root(value: int, exponent: int) -> int:
    if value < 0:
        raise ValueError("nonnegative integer required")
    lo, hi = 0, 1
    while hi**exponent <= value:
        hi *= 2
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid**exponent <= value:
            lo = mid
        else:
            hi = mid
    return lo


def cube_root_fraction(value: Fraction) -> Interval:
    quotient = value.numerator * SCALE**3 // value.denominator
    lo = integer_nth_root(quotient, 3)
    exact_numerator = value.numerator * SCALE**3
    hi = lo if lo**3 * value.denominator == exact_numerator else lo + 1
    return Interval(lo, hi)


def fraction_of_float(value: float) -> Fraction:
    numerator, denominator = value.as_integer_ratio()
    return Fraction(numerator, denominator)


def exact_unit_param(t: Fraction) -> tuple[Fraction, Fraction]:
    denominator = 1 + t * t
    return (1 - t * t) / denominator, 2 * t / denominator


def exact_rotate_quadrant(value: tuple[Fraction, Fraction], quadrant: int) -> tuple[Fraction, Fraction]:
    x, y = value
    return ((x, y), (-y, x), (-x, -y), (y, -x))[quadrant]


def unit_param(t: float) -> complex:
    return complex((1 - t * t) / (1 + t * t), 2 * t / (1 + t * t))


def rotate_quadrant(z: complex, quadrant: int) -> complex:
    return z * (1j) ** quadrant


def poly_power(v0: complex, delta: complex, exponent: int) -> np.ndarray:
    result = np.array([1 + 0j])
    for _ in range(exponent):
        result = np.convolve(result, np.array([v0, delta]))
    return result


@dataclass(frozen=True)
class Candidate:
    first: int
    second: int
    radius: float


@dataclass(frozen=True)
class Box:
    branch: str
    quadrant: int
    rho0: float
    rho1: float
    full0: float
    full1: float
    fund0: float
    fund1: float
    depth: int


class Atlas:
    def __init__(self) -> None:
        self.omega = np.exp(2j * np.pi * np.arange(5) / 5)
        bernstein = np.zeros((DEGREE + 1, 6))
        for index in range(DEGREE + 1):
            for power in range(min(index, 5) + 1):
                bernstein[index, power] = math.comb(index, power) / math.comb(DEGREE, power)

        sqrt5 = math.sqrt(5)
        w = math.sqrt(10 + 2 * sqrt5)
        sqrt3 = math.sqrt(3)
        equality_radii = [
            (-(13 * w**3 - 40 * w**2 - 200 * w + 520) / 160) ** (1 / 3),
            (w**3 * (3 * sqrt3 - 5) / 160) ** (1 / 3),
            (15 - w**2) ** (1 / 3),
            (w * (3 * sqrt3 + 5) * (3 * w**2 - 40) / 160) ** (1 / 3),
        ]
        radii = np.unique(
            np.concatenate(
                ([k / 1000 for k in range(10, 201, 10)],
                 [k / 1000 for k in range(200, 1501, 10)],
                 equality_radii)
            )
        )

        self.candidates: list[Candidate] = []
        bern_a: list[np.ndarray] = []
        bern_b: list[np.ndarray] = []
        bern_fixed: list[np.ndarray] = []
        sample_a: list[np.ndarray] = []
        sample_b: list[np.ndarray] = []
        sample_fixed: list[np.ndarray] = []
        sample_t = np.linspace(0, 1, 101)
        for first in range(5):
            for second in range(first + 1, 5):
                v0 = self.omega[first]
                delta = self.omega[second] - v0
                p1 = np.concatenate((np.array([v0, delta]), np.zeros(4)))
                p2 = np.concatenate((poly_power(v0, delta, 2), np.zeros(3)))
                p5 = poly_power(v0, delta, 5)
                for radius in radii:
                    self.candidates.append(Candidate(first, second, float(radius)))
                    bern_a.append(bernstein @ (radius * p1))
                    bern_b.append(bernstein @ (radius**2 * p2))
                    bern_fixed.append(bernstein @ (-radius**5 * p5))
                    z = radius * ((1 - sample_t) * v0 + sample_t * self.omega[second])
                    sample_a.append(z)
                    sample_b.append(z**2)
                    sample_fixed.append(-z**5)
        self.bern_a = np.asarray(bern_a)
        self.bern_b = np.asarray(bern_b)
        self.bern_fixed = np.asarray(bern_fixed)
        self.sample_a = np.asarray(sample_a)
        self.sample_b = np.asarray(sample_b)
        self.sample_fixed = np.asarray(sample_fixed)
        self.first = np.asarray([candidate.first for candidate in self.candidates])
        self.second = np.asarray([candidate.second for candidate in self.candidates])
        self.radius = np.asarray([candidate.radius for candidate in self.candidates])

    def coefficients(self, box: Box) -> tuple[complex, complex, float, float]:
        rho = (box.rho0 + box.rho1) / 2
        full = (box.full0 + box.full1) / 2
        fund = (box.fund0 + box.fund1) / 2
        full_value = rotate_quadrant(unit_param(full), box.quadrant)
        fundamental_value = unit_param(fund)
        if box.branch == "B_unit":
            A = rho * full_value
            B = fundamental_value
            delta_a = (box.rho1 - box.rho0) / 2 + box.rho1 * (box.full1 - box.full0)
            delta_b = box.fund1 - box.fund0
        else:
            A = fundamental_value
            B = rho * full_value
            delta_a = box.fund1 - box.fund0
            delta_b = (box.rho1 - box.rho0) / 2 + box.rho1 * (box.full1 - box.full0)
        return A, B, delta_a, delta_b

    @staticmethod
    def ray_certificate(a_upper: float, b_upper: float, radius: float) -> bool:
        linear = radius * a_upper
        quadratic = radius**2 * b_upper
        quintic = radius**5
        endpoint = linear + quadratic - quintic
        if endpoint > -2e-13:
            return False
        if quadratic <= 0:
            return True
        return quadratic - 4 * quintic <= -2e-13

    def certify(self, box: Box) -> tuple[bool, Candidate | None, float]:
        A, B, delta_a, delta_b = self.coefficients(box)
        sampled = np.max((self.sample_a * A + self.sample_b * B + self.sample_fixed).real, axis=1)
        x = np.linspace(1, 4, 60)
        scores = sampled.copy()
        for indices in (self.first, self.second):
            a = np.real(A * self.omega[indices])
            b = np.real(B * self.omega[(2 * indices) % 5])
            values = (
                self.radius[:, None] * a[:, None] * x
                + self.radius[:, None] ** 2 * b[:, None] * x**2
                - self.radius[:, None] ** 5 * x**5
            )
            scores = np.maximum(scores, np.max(values, axis=1))
        shortlist = np.argpartition(scores, 28)[:28]
        best_upper = math.inf
        best_candidate: Candidate | None = None
        for index in shortlist:
            candidate = self.candidates[index]
            chord_upper = float(
                np.max((self.bern_a[index] * A + self.bern_b[index] * B + self.bern_fixed[index]).real)
                + candidate.radius * delta_a
                + candidate.radius**2 * delta_b
            )
            ray_ok = True
            for root_index in (candidate.first, candidate.second):
                a_upper = float(np.real(A * self.omega[root_index]) + delta_a)
                b_upper = float(np.real(B * self.omega[(2 * root_index) % 5]) + delta_b)
                ray_ok = ray_ok and self.ray_certificate(a_upper, b_upper, candidate.radius)
            upper = chord_upper if ray_ok else math.inf
            if upper < best_upper:
                best_upper = upper
                best_candidate = candidate
        return best_upper < -2e-12, best_candidate, best_upper


class ExactReplay:
    """Integer-scaled outward replay of every accepted generator box."""

    def __init__(self) -> None:
        self.sqrt5 = sqrt_interval(Interval.integer(5))
        self.sqrt3 = sqrt_interval(Interval.integer(3))
        self.w = sqrt_interval(Interval.integer(10) + self.sqrt5.scale(Fraction(2)))
        self.m = sqrt_interval(Interval.integer(10) - self.sqrt5.scale(Fraction(2)))
        one = Interval.integer(1)
        zero = Interval.integer(0)
        self.roots: list[ComplexInterval] = [
            (one, zero),
            ((self.sqrt5 - one).scale(Fraction(1, 4)), self.w.scale(Fraction(1, 4))),
            (-(self.sqrt5 + one).scale(Fraction(1, 4)), self.m.scale(Fraction(1, 4))),
            (-(self.sqrt5 + one).scale(Fraction(1, 4)), -self.m.scale(Fraction(1, 4))),
            ((self.sqrt5 - one).scale(Fraction(1, 4)), -self.w.scale(Fraction(1, 4))),
        ]
        self.root_powers: dict[tuple[int, int], ComplexInterval] = {}
        for root_index in range(5):
            value: ComplexInterval = (one, zero)
            for exponent in range(6):
                self.root_powers[(root_index, exponent)] = value
                value = complex_mul(value, self.roots[root_index])

    @staticmethod
    def exact_box_coefficients(box: Box) -> tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction], Fraction, Fraction]:
        rho0, rho1 = fraction_of_float(box.rho0), fraction_of_float(box.rho1)
        full0, full1 = fraction_of_float(box.full0), fraction_of_float(box.full1)
        fund0, fund1 = fraction_of_float(box.fund0), fraction_of_float(box.fund1)
        rho = (rho0 + rho1) / 2
        full = (full0 + full1) / 2
        fund = (fund0 + fund1) / 2
        full_value = exact_rotate_quadrant(exact_unit_param(full), box.quadrant)
        fundamental_value = exact_unit_param(fund)
        if box.branch == "B_unit":
            A = (rho * full_value[0], rho * full_value[1])
            B = fundamental_value
            delta_a = (rho1 - rho0) / 2 + rho1 * (full1 - full0)
            delta_b = fund1 - fund0
        else:
            A = fundamental_value
            B = (rho * full_value[0], rho * full_value[1])
            delta_a = fund1 - fund0
            delta_b = (rho1 - rho0) / 2 + rho1 * (full1 - full0)
        return A, B, delta_a, delta_b

    def base_controls(self, first: int, second: int, degree: int) -> list[ComplexInterval]:
        controls: list[ComplexInterval] = []
        for index in range(degree + 1):
            controls.append(complex_mul(
                self.root_powers[(first, degree - index)],
                self.root_powers[(second, index)],
            ))
        return controls

    @staticmethod
    def elevate_control(base: list[ComplexInterval], degree: int, index: int) -> ComplexInterval:
        result: ComplexInterval = (Interval.integer(0), Interval.integer(0))
        low = max(0, index - (DEGREE - degree))
        high = min(degree, index)
        denominator = math.comb(DEGREE, index)
        for source in range(low, high + 1):
            weight = Fraction(
                math.comb(degree, source) * math.comb(DEGREE - degree, index - source),
                denominator,
            )
            result = complex_add(result, complex_scale(base[source], weight))
        return result

    def controls(self, candidate: Candidate) -> list[tuple[ComplexInterval, ComplexInterval, ComplexInterval]]:
        radius = fraction_of_float(candidate.radius)
        base1 = self.base_controls(candidate.first, candidate.second, 1)
        base2 = self.base_controls(candidate.first, candidate.second, 2)
        base5 = self.base_controls(candidate.first, candidate.second, 5)
        controls: list[tuple[ComplexInterval, ComplexInterval, ComplexInterval]] = []
        for index in range(DEGREE + 1):
            controls.append((
                complex_scale(self.elevate_control(base1, 1, index), radius),
                complex_scale(self.elevate_control(base2, 2, index), radius**2),
                complex_scale(self.elevate_control(base5, 5, index), -(radius**5)),
            ))
        return controls

    @staticmethod
    def point(value: tuple[Fraction, Fraction]) -> ComplexInterval:
        return Interval.fraction(value[0]), Interval.fraction(value[1])

    def exact_ray(self, A: ComplexInterval, B: ComplexInterval, delta_a: Fraction,
                  delta_b: Fraction, root_index: int, radius: Fraction) -> bool:
        projection_a = complex_mul(A, self.roots[root_index])[0]
        projection_b = complex_mul(B, self.root_powers[((2 * root_index) % 5, 1)])[0]
        a_upper = projection_a + Interval.fraction(delta_a)
        b_upper = projection_b + Interval.fraction(delta_b)
        linear = a_upper.scale(radius)
        quadratic = b_upper.scale(radius**2)
        quintic = Interval.fraction(radius**5)
        endpoint_upper = (linear + quadratic - quintic).hi
        if endpoint_upper >= 0:
            return False
        if quadratic.hi <= 0:
            return True
        return (quadratic - quintic.scale(Fraction(4))).hi < 0

    def verify_group(self, candidate: Candidate, boxes: list[Box]) -> tuple[bool, int]:
        controls = self.controls(candidate)
        radius = fraction_of_float(candidate.radius)
        verified = 0
        for box in boxes:
            A_value, B_value, delta_a, delta_b = self.exact_box_coefficients(box)
            A, B = self.point(A_value), self.point(B_value)
            robust = Interval.fraction(radius * delta_a + radius**2 * delta_b)
            chord_ok = True
            for control_a, control_b, control_fixed in controls:
                value = complex_mul(A, control_a)[0] + complex_mul(B, control_b)[0] + control_fixed[0] + robust
                if value.hi >= 0:
                    chord_ok = False
                    break
            if not chord_ok:
                return False, verified
            if not self.exact_ray(A, B, delta_a, delta_b, candidate.first, radius):
                return False, verified
            if not self.exact_ray(A, B, delta_a, delta_b, candidate.second, radius):
                return False, verified
            verified += 1
        return True, verified

    @staticmethod
    def norm_upper(value: ComplexInterval) -> int:
        square = value[0].abs_upper() ** 2 + value[1].abs_upper() ** 2
        root = math.isqrt(square)
        return root if root * root == square else root + 1

    def verify_local_box(self, box: Box) -> bool:
        ustar = cube_root_fraction(Fraction(27, 320))
        equality_a = complex_scale(self.roots[2], Fraction(1))
        equality_a = (equality_a[0] * ustar, equality_a[1] * ustar)
        equality_b = (
            self.w.scale(Fraction(1, 4)),
            (self.sqrt5 - Interval.integer(1)).scale(Fraction(1, 4)),
        )
        rho_values = (fraction_of_float(box.rho0), fraction_of_float(box.rho1))
        full_values = (fraction_of_float(box.full0), fraction_of_float(box.full1))
        fund_values = (fraction_of_float(box.fund0), fraction_of_float(box.fund1))
        a_distance = 0
        for rho in rho_values:
            for phase in full_values:
                direction = exact_rotate_quadrant(exact_unit_param(phase), box.quadrant)
                point = self.point((rho * direction[0], rho * direction[1]))
                a_distance = max(a_distance, self.norm_upper(
                    (point[0] - equality_a[0], point[1] - equality_a[1])
                ))
        b_distance = 0
        for phase in fund_values:
            point = self.point(exact_unit_param(phase))
            b_distance = max(b_distance, self.norm_upper(
                (point[0] - equality_b[0], point[1] - equality_b[1])
            ))
        radius_scaled = floor_div(Fraction(LOCAL_RADIUS).numerator * SCALE,
                                  Fraction(LOCAL_RADIUS).denominator)
        return a_distance**2 + b_distance**2 < radius_scaled**2

    @staticmethod
    def vector_sub(left: tuple[Interval, ...], right: tuple[Interval, ...]) -> tuple[Interval, ...]:
        return tuple(a - b for a, b in zip(left, right, strict=True))

    @staticmethod
    def vector_dot(left: tuple[Interval, ...], right: tuple[Interval, ...]) -> Interval:
        result = Interval.integer(0)
        for a, b in zip(left, right, strict=True):
            result = result + a * b
        return result

    @staticmethod
    def vector_cross(left: tuple[Interval, Interval, Interval],
                     right: tuple[Interval, Interval, Interval]) -> tuple[Interval, Interval, Interval]:
        return (
            left[1] * right[2] - left[2] * right[1],
            left[2] * right[0] - left[0] * right[2],
            left[0] * right[1] - left[1] * right[0],
        )

    def verify_local_constants(self) -> dict[str, object]:
        """Exact outward audit of every numerical constant in the local theorem."""
        one = Interval.integer(1)
        zero = Interval.integer(0)
        radius_bound = Interval.fraction(Fraction(17, 2500))
        w, s3, s5 = self.w, self.sqrt3, self.sqrt5
        w2, w3 = square_interval(w), interval_power(w, 3)

        q_left = (-(
            w3.scale(Fraction(13)) - w2.scale(Fraction(40))
            - w.scale(Fraction(200)) + Interval.integer(520)
        )).scale(Fraction(1, 160))
        y_direction = (-(
            w3.scale(Fraction(3)) - w.scale(Fraction(40)) - Interval.integer(40)
        )).scale(Fraction(1, 80))
        y = cube_root_interval(q_left * interval_power(y_direction, 3))
        y2 = square_interval(y)
        s3_minus = s3 - one
        s3_plus = s3 + one
        gradients: list[tuple[Interval, Interval, Interval]] = [
            (s5 * y, -y, -y2.scale(Fraction(4))),
            (zero, -(s3_minus * y), square_interval(s3_minus) * y2),
            (-(s5 * y), -y, -y2.scale(Fraction(4))),
            (zero, s3_plus * y, square_interval(s3_plus) * y2),
        ]

        support_target_sq = Fraction(59, 1000) ** 2
        facet_rows: list[dict[str, object]] = []
        support_pass = True
        support_lower = math.inf
        for omitted in range(4):
            points = [gradients[index] for index in range(4) if index != omitted]
            edge1 = self.vector_sub(points[1], points[0])
            edge2 = self.vector_sub(points[2], points[0])
            normal = self.vector_cross(edge1, edge2)
            offset = self.vector_dot(normal, points[0])
            normal_sq = sum((square_interval(component) for component in normal), Interval.integer(0))
            separation = square_interval(offset) - normal_sq.scale(support_target_sq)
            distance = sqrt_interval(divide_positive(square_interval(offset), normal_sq))
            row_pass = separation.lo > 0
            support_pass = support_pass and row_pass
            support_lower = min(support_lower, interval_decimal(distance.lo))
            facet_rows.append({
                "omitted_contact": omitted,
                "distance_lower": interval_decimal(distance.lo),
                "target_separation_lower": interval_decimal(separation.lo),
                "pass": row_pass,
            })

        q_plus = (w3 * (s3.scale(Fraction(3)) - Interval.integer(5))).scale(Fraction(1, 160))
        q_right = Interval.integer(15) - w2
        q_minus = (
            w * (s3.scale(Fraction(3)) + Interval.integer(5))
            * (w2.scale(Fraction(3)) - Interval.integer(40))
        ).scale(Fraction(1, 160))
        adjacent_distance_sq = (Interval.integer(5) - s5).scale(Fraction(1, 2))
        diagonal_distance_sq = (Interval.integer(5) + s5).scale(Fraction(1, 2))

        charts: list[tuple[str, Interval, Interval, Interval, Interval, Interval, str, tuple[int, int]]] = []
        charts.append((
            "01", q_left,
            (w3.scale(Fraction(12)) - w2.scale(Fraction(25))
             - w.scale(Fraction(170)) + Interval.integer(380)).scale(Fraction(5, 32)),
            -(w3.scale(Fraction(8)) - w2.scale(Fraction(17))
              - w.scale(Fraction(114)) + Interval.integer(260)).scale(Fraction(5, 16)),
            (w3.scale(Fraction(6)) - w2.scale(Fraction(15))
             - w.scale(Fraction(90)) + Interval.integer(220)).scale(Fraction(1, 8)),
            adjacent_distance_sq, "convex", (0, 1),
        ))
        charts.append((
            "13", q_plus,
            -(q_plus * (w2 - Interval.integer(8))).scale(Fraction(25, 8)),
            (q_plus * (w2.scale(Fraction(3)) - Interval.integer(20))).scale(Fraction(5, 4)),
            -(q_plus * w2.scale(Fraction(10)) + q_plus.scale(Fraction(40)) + w3).scale(Fraction(1, 16)),
            diagonal_distance_sq, "concave", (1, 3),
        ))
        charts.append((
            "23", q_right,
            (w2.scale(Fraction(7)) - Interval.integer(100)).scale(Fraction(25, 8)),
            (w3.scale(Fraction(2)) - w2.scale(Fraction(35))
             - w.scale(Fraction(30)) + Interval.integer(500)).scale(Fraction(5, 8)),
            -(w3 - w2.scale(Fraction(7)) - w.scale(Fraction(15))
              + Interval.integer(104)).scale(Fraction(5, 8)),
            adjacent_distance_sq, "convex", (2, 3),
        ))
        charts.append((
            "34", q_minus,
            (q_minus * (w2 - Interval.integer(12))).scale(Fraction(25, 8)),
            -(q_minus * (w2.scale(Fraction(3)) - Interval.integer(40))).scale(Fraction(5, 4)),
            (q_minus * w2.scale(Fraction(10)) - q_minus.scale(Fraction(240))
             + w3.scale(Fraction(3)) - w.scale(Fraction(40))).scale(Fraction(1, 16)),
            adjacent_distance_sq, "convex", (3, 4),
        ))

        remainder_rows: list[dict[str, object]] = []
        ray_rows: list[dict[str, object]] = []
        remainder_pass = True
        ray_pass = True
        combined_remainder_upper = 0.0
        largest_ray_endpoint_upper = -math.inf
        ustar = cube_root_fraction(Fraction(27, 320))
        for name, Q, q2, q1, q0, chord_distance_sq, kind, endpoints in charts:
            radius = cube_root_interval(Q)
            radius2 = square_interval(radius)
            if kind == "convex":
                residual_margin = minimum_interval(-q0, -(q2 + q1 + q0))
            else:
                discriminant = square_interval(q1) - (q2 * q0).scale(Fraction(4))
                residual_margin = divide_positive(-discriminant, (-q2).scale(Fraction(4)))
            kappa = radius2 * residual_margin
            cross_factor = one + (radius * (one + radius_bound)).scale(Fraction(2))
            cross_square = chord_distance_sq * radius2 * square_interval(cross_factor)
            constant_separation = (
                kappa.scale(Fraction(25)) - cross_square
                - (kappa * radius2).scale(Fraction(4))
            )
            completed_square = divide_positive(cross_square, kappa.scale(Fraction(4))) + radius2
            row_pass = residual_margin.lo > 0 and constant_separation.lo > 0
            remainder_pass = remainder_pass and row_pass
            combined_remainder_upper = max(
                combined_remainder_upper, interval_decimal(completed_square.hi)
            )
            remainder_rows.append({
                "connector": name,
                "combined_remainder_upper": interval_decimal(completed_square.hi),
                "twenty_five_over_four_separation_lower": interval_decimal(constant_separation.lo),
                "pass": row_pass,
            })

            radius5 = interval_power(radius, 5)
            for endpoint in endpoints:
                a = ustar * self.roots[endpoint][0]
                doubled_root = (2 * endpoint) % 5
                b = -self.root_powers[(doubled_root, 1)][1]
                quadratic = radius2 * (b + radius_bound)
                endpoint_value = radius * (a + radius_bound) + quadratic - radius5
                drop = quadratic - radius5.scale(Fraction(4))
                endpoint_pass = endpoint_value.hi < 0
                criterion = "nonpositive_quadratic"
                if quadratic.hi > 0:
                    criterion = "quartic_drop"
                    endpoint_pass = endpoint_pass and drop.hi < 0
                ray_pass = ray_pass and endpoint_pass
                largest_ray_endpoint_upper = max(
                    largest_ray_endpoint_upper, interval_decimal(endpoint_value.hi)
                )
                ray_rows.append({
                    "connector": name,
                    "endpoint": endpoint,
                    "criterion": criterion,
                    "endpoint_upper": interval_decimal(endpoint_value.hi),
                    "drop_upper": interval_decimal(drop.hi),
                    "pass": endpoint_pass,
                })

        full_chart_overlap = Fraction(83, 200) > 0 and (Fraction(283, 200) ** 2 > 2)
        fundamental_cover = (
            Interval.fraction(Fraction(163, 500) ** 2)
            * (Interval.integer(5) + s5.scale(Fraction(2))) - one
        ).lo > 0
        chart_cover_pass = full_chart_overlap and fundamental_cover
        overall = support_pass and remainder_pass and ray_pass and chart_cover_pass
        return {
            "tetrahedral_support_target": 59 / 1000,
            "tetrahedral_support_lower": support_lower,
            "tetrahedral_facets": facet_rows,
            "combined_remainder_target": 25 / 4,
            "largest_combined_remainder_upper": combined_remainder_upper,
            "connector_remainders": remainder_rows,
            "ray_radius": 17 / 2500,
            "largest_ray_endpoint_upper": largest_ray_endpoint_upper,
            "ray_certificates": ray_rows,
            "full_phase_chart_overlap": full_chart_overlap,
            "fundamental_phase_chart_cover": fundamental_cover,
            "pass": overall,
        }


def local_equality_box(box: Box) -> bool:
    if box.branch != "B_unit" or box.quadrant != 2:
        return False
    ustar = (27 / 320) ** (1 / 3)
    tan_pi_over_10 = 1 / math.sqrt(5 + 2 * math.sqrt(5))
    tan_pi_over_20 = math.sqrt((4 - math.sqrt(10 + 2 * math.sqrt(5))) /
                               (4 + math.sqrt(10 + 2 * math.sqrt(5))))
    equality_a = ustar * unit_param(-tan_pi_over_10) * (-1)
    equality_b = unit_param(tan_pi_over_20)
    max_a = max(
        abs(rho * rotate_quadrant(unit_param(phase), 2) - equality_a)
        for rho in (box.rho0, box.rho1)
        for phase in (box.full0, box.full1)
    )
    max_b = max(abs(unit_param(phase) - equality_b) for phase in (box.fund0, box.fund1))
    return math.hypot(max_a, max_b) < LOCAL_RADIUS * 0.999


def subdivide(box: Box) -> tuple[Box, Box]:
    rho_width = box.rho1 - box.rho0
    full_width = (box.full1 - box.full0) * max(box.rho1, 0.2)
    fund_width = box.fund1 - box.fund0
    depth = box.depth + 1
    if rho_width >= full_width and rho_width >= fund_width:
        mid = (box.rho0 + box.rho1) / 2
        return (
            Box(box.branch, box.quadrant, box.rho0, mid, box.full0, box.full1, box.fund0, box.fund1, depth),
            Box(box.branch, box.quadrant, mid, box.rho1, box.full0, box.full1, box.fund0, box.fund1, depth),
        )
    if full_width >= fund_width:
        mid = (box.full0 + box.full1) / 2
        return (
            Box(box.branch, box.quadrant, box.rho0, box.rho1, box.full0, mid, box.fund0, box.fund1, depth),
            Box(box.branch, box.quadrant, box.rho0, box.rho1, mid, box.full1, box.fund0, box.fund1, depth),
        )
    mid = (box.fund0 + box.fund1) / 2
    return (
        Box(box.branch, box.quadrant, box.rho0, box.rho1, box.full0, box.full1, box.fund0, mid, depth),
        Box(box.branch, box.quadrant, box.rho0, box.rho1, box.full0, box.full1, mid, box.fund1, depth),
    )


def initial_boxes() -> list[Box]:
    full_bound = 0.415
    fundamental_bound = 0.326
    boxes: list[Box] = []
    for branch in ("B_unit", "A_unit"):
        for quadrant in range(4):
            for rho_index in range(2):
                for full_index in range(4):
                    for fund_index in range(2):
                        boxes.append(Box(
                            branch,
                            quadrant,
                            rho_index / 2,
                            (rho_index + 1) / 2,
                            -full_bound + 2 * full_bound * full_index / 4,
                            -full_bound + 2 * full_bound * (full_index + 1) / 4,
                            fundamental_bound * fund_index / 2,
                            fundamental_bound * (fund_index + 1) / 2,
                            0,
                        ))
    return boxes


def main() -> None:
    atlas = Atlas()
    stack = initial_boxes()
    certified: list[tuple[Box, Candidate, float]] = []
    local: list[Box] = []
    failures: list[tuple[Box, float]] = []
    while stack:
        box = stack.pop()
        if local_equality_box(box):
            local.append(box)
            continue
        ok, candidate, upper = atlas.certify(box)
        if ok and candidate is not None:
            certified.append((box, candidate, upper))
            continue
        if box.depth >= MAX_DEPTH:
            failures.append((box, upper))
            continue
        stack.extend(subdivide(box))

    pair_counts: dict[str, int] = {}
    radius_counts: dict[str, int] = {}
    for _, candidate, _ in certified:
        pair = f"{candidate.first}{candidate.second}"
        pair_counts[pair] = pair_counts.get(pair, 0) + 1
        radius = f"{candidate.radius:.12g}"
        radius_counts[radius] = radius_counts.get(radius, 0) + 1

    exact_replay = ExactReplay()
    grouped: dict[Candidate, list[Box]] = {}
    for box, candidate, _ in certified:
        grouped.setdefault(candidate, []).append(box)
    exact_group_count = 0
    exact_box_count = 0
    exact_failure: str | None = None
    for candidate, boxes in grouped.items():
        ok, count = exact_replay.verify_group(candidate, boxes)
        exact_box_count += count
        if not ok:
            exact_failure = f"pair={candidate.first}{candidate.second},radius={candidate.radius:.17g},verified_before_failure={count}"
            break
        exact_group_count += 1
    exact_local_count = sum(1 for box in local if exact_replay.verify_local_box(box))
    local_constant_audit = exact_replay.verify_local_constants()
    exact_replay_pass = (
        exact_failure is None
        and exact_box_count == len(certified)
        and exact_local_count == len(local)
        and bool(local_constant_audit["pass"])
    )
    result = {
        "schema": "erdos1041_quintic_mixed_global_atlas_check_v1",
        "bernstein_degree": DEGREE,
        "candidate_count": len(atlas.candidates),
        "initial_box_count": len(initial_boxes()),
        "certified_box_count": len(certified),
        "least_certified_slack": -max((upper for _, _, upper in certified), default=-math.inf),
        "local_equality_box_count": len(local),
        "failure_count": len(failures),
        "max_failure_upper": max((upper for _, upper in failures), default=None),
        "failure_samples": [
            {
                "branch": box.branch,
                "quadrant": box.quadrant,
                "rho": [(box.rho0 + box.rho1) / 2, box.rho1 - box.rho0],
                "full": [(box.full0 + box.full1) / 2, box.full1 - box.full0],
                "fund": [(box.fund0 + box.fund1) / 2, box.fund1 - box.fund0],
                "upper": upper,
            }
            for box, upper in sorted(failures, key=lambda row: row[1], reverse=True)[:12]
        ],
        "max_depth": MAX_DEPTH,
        "pair_counts": pair_counts,
        "distinct_selected_radius_count": len(radius_counts),
        "local_radius": LOCAL_RADIUS,
        "verification_state": "floating_candidate_selection_with_exact_outward_interval_replay",
        "exact_interval_replay": {
            "scale": SCALE,
            "selected_candidate_group_count": len(grouped),
            "verified_candidate_group_count": exact_group_count,
            "verified_strict_box_count": exact_box_count,
            "verified_local_box_count": exact_local_count,
            "failure": exact_failure,
            "pass": exact_replay_pass,
        },
        "local_constant_audit": local_constant_audit,
        "status": "PASS" if not failures and exact_replay_pass else "INCOMPLETE",
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    if failures or not exact_replay_pass:
        raise SystemExit(2)


if __name__ == "__main__":
    main()
