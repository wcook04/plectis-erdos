#!/usr/bin/env python3
"""Exact rational replay of the CE--GM universal-stationarity no-go.

No floating-point operation is used for any asserted gate.
"""
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from fractions import Fraction as F
from math import comb
from typing import Iterable, Sequence


@dataclass(frozen=True)
class GQ:
    re: F = F(0)
    im: F = F(0)

    def __add__(self, other: object) -> "GQ":
        z = as_gq(other)
        return GQ(self.re + z.re, self.im + z.im)

    __radd__ = __add__

    def __neg__(self) -> "GQ":
        return GQ(-self.re, -self.im)

    def __sub__(self, other: object) -> "GQ":
        return self + (-as_gq(other))

    def __rsub__(self, other: object) -> "GQ":
        return as_gq(other) - self

    def __mul__(self, other: object) -> "GQ":
        z = as_gq(other)
        return GQ(self.re * z.re - self.im * z.im,
                  self.re * z.im + self.im * z.re)

    __rmul__ = __mul__

    def conjugate(self) -> "GQ":
        return GQ(self.re, -self.im)

    def norm_sq(self) -> F:
        return self.re * self.re + self.im * self.im

    def __truediv__(self, other: object) -> "GQ":
        z = as_gq(other)
        if z.norm_sq() == 0:
            raise ZeroDivisionError
        return self * z.conjugate() * GQ(F(1, 1) / z.norm_sq())

    def __rtruediv__(self, other: object) -> "GQ":
        return as_gq(other) / self

    def __pow__(self, n: int) -> "GQ":
        if n < 0:
            return GQ(1) / (self ** (-n))
        out, base = GQ(1), self
        while n:
            if n & 1:
                out *= base
            base *= base
            n //= 2
        return out

    def __str__(self) -> str:
        sign = "+" if self.im >= 0 else "-"
        return f"{self.re} {sign} {abs(self.im)} i"


def as_gq(x: object) -> GQ:
    if isinstance(x, GQ):
        return x
    if isinstance(x, (int, F)):
        return GQ(F(x))
    raise TypeError(type(x))


def poly_eval(coeffs: Sequence[GQ], z: GQ) -> GQ:
    out = GQ()
    for c in reversed(coeffs):
        out = out * z + c
    return out


def poly_mul(p: Sequence[GQ], q: Sequence[GQ]) -> list[GQ]:
    out = [GQ() for _ in range(len(p) + len(q) - 1)]
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            out[i + j] += x * y
    return out


def primitive_coeffs(c0: GQ, hub: GQ, c2: GQ) -> list[GQ]:
    s, p = c0 + hub, c0 * hub
    return [GQ(), -4 * c2 * p, 2 * (p + c2 * s),
            -F(4, 3) * (s + c2), GQ(1)]


def solve_c2(c0: GQ, hub: GQ, a: GQ, b: GQ) -> GQ:
    p0 = primitive_coeffs(c0, hub, GQ())
    p1 = primitive_coeffs(c0, hub, GQ(1))
    d0 = poly_eval(p0, a) - poly_eval(p0, b)
    d1 = ((poly_eval(p1, a) - poly_eval(p0, a))
          - (poly_eval(p1, b) - poly_eval(p0, b)))
    return -d0 / d1


def segment_value_poly(f: Sequence[GQ], hub: GQ, root: GQ) -> list[GQ]:
    z, out, power = [hub, root - hub], [GQ()], [GQ(1)]
    for c in f:
        if len(out) < len(power):
            out.extend(GQ() for _ in range(len(power) - len(out)))
        for i, x in enumerate(power):
            out[i] += c * x
        power = poly_mul(power, z)
    return out


def abs_square_poly(q: Sequence[GQ]) -> list[F]:
    out = poly_mul(q, [x.conjugate() for x in q])
    assert all(x.im == 0 for x in out)
    return [x.re for x in out]


def power_to_bernstein(c: Sequence[F], degree: int) -> list[F]:
    cc = list(c) + [F(0)] * (degree + 1 - len(c))
    return [sum(cc[k] * F(comb(i, k), comb(degree, k))
                for k in range(i + 1)) for i in range(degree + 1)]


def arm_gap_controls(f: Sequence[GQ], hub: GQ, root: GQ,
                     level_sq: F, divide_t_sq: bool) -> list[F]:
    sq = abs_square_poly(segment_value_poly(f, hub, root))
    gap = [level_sq - sq[0]] + [-x for x in sq[1:]]
    if divide_t_sq:
        assert gap[0] == 0 and gap[1] == 0
        return power_to_bernstein(gap[2:], 6)
    return power_to_bernstein(gap, 8)


def schur_gaps(a: GQ, b: GQ) -> tuple[F, F]:
    first = 1 - b.norm_sq()
    return first, first * first - (a - a.conjugate() * b).norm_sq()


def exact_min(xs: Iterable[F]) -> F:
    return min(list(xs))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    c_star = GQ(F(-7, 10), F(-9, 20))
    hub = GQ(F(-3, 10), F(-1, 5))
    a = GQ(F(-13, 20), F(-3, 4))
    b = GQ(F(-9, 10), F(-1, 5))
    c2 = solve_c2(c_star, hub, a, b)
    f = primitive_coeffs(c_star, hub, c2)
    f[0] -= poly_eval(f, a)

    fprime = [(k + 1) * f[k + 1] for k in range(4)]
    factor_gates = {
        "root_a": poly_eval(f, a) == GQ(),
        "root_b": poly_eval(f, b) == GQ(),
        "c_star_critical": poly_eval(fprime, c_star) == GQ(),
        "hub_critical": poly_eval(fprime, hub) == GQ(),
        "c2_critical": poly_eval(fprime, c2) == GQ(),
    }

    pair = poly_mul([-a, GQ(1)], [-b, GQ(1)])
    remainder, quotient = list(f), [GQ() for _ in range(3)]
    for k in range(4, 1, -1):
        lead = remainder[k]
        quotient[k - 2] = lead
        for j in range(3):
            remainder[j + k - 2] -= lead * pair[j]
    q0, q1, q2 = quotient
    root_gaps = schur_gaps(q1, q0)

    p_shift = q1 + 2 * c_star
    q_shift = q0 + q1 * c_star + c_star * c_star
    nearest_gaps = schur_gaps((p_shift * F(1, 2)) / q_shift,
                              GQ(F(1, 4)) / q_shift)

    v_star, v_h, v_2 = (poly_eval(f, z) for z in (c_star, hub, c2))
    vstar_sq, hub_sq, v2_sq = (v.norm_sq() for v in (v_star, v_h, v_2))
    controls = {
        "hub_a": arm_gap_controls(f, hub, a, hub_sq, True),
        "hub_b": arm_gap_controls(f, hub, b, hub_sq, True),
        "c_star_a": arm_gap_controls(f, c_star, a, vstar_sq, True),
        "c_star_b": arm_gap_controls(f, c_star, b, vstar_sq, True),
    }

    fsecond = [2 * f[2], 6 * f[3], 12 * f[4]]
    curvature = v_h.conjugate() * poly_eval(fsecond, hub)
    ua, ub = a - hub, b - hub
    bilinear = lambda x, y: (curvature * x * y).re
    qa, qb, qab = bilinear(ua, ua), bilinear(ub, ub), bilinear(ua, ub)

    descent = hub + F(1, 1000) * (ua + ub)
    descent_controls = {
        "descent_a": arm_gap_controls(f, descent, a, hub_sq, False),
        "descent_b": arm_gap_controls(f, descent, b, hub_sq, False),
    }

    gates = {
        **factor_gates,
        "quadratic_division_exact": q2 == GQ(1) and all(x == GQ() for x in remainder),
        "all_roots_in_open_disc": a.norm_sq() < 1 and b.norm_sq() < 1
        and min(root_gaps) > 0,
        "selected_pair_nearest": (c_star - a).norm_sq() < F(1, 4)
        and (c_star - b).norm_sq() < F(1, 4) and min(nearest_gaps) > 0,
        "unique_least_critical_value": 0 < vstar_sq < hub_sq and vstar_sq < v2_sq,
        "bad_hub_strictly_in_ellipse": (hub - a).norm_sq() < F(33, 50) ** 2
        and (hub - b).norm_sq() == F(3, 5) ** 2
        and vstar_sq > F(63, 100) ** 8,
        "bad_hub_unique_arm_maxima": min(controls["hub_a"] + controls["hub_b"]) > 0,
        "bad_hub_above_gcrit": hub_sq * hub_sq > vstar_sq * v2_sq,
        "c_star_two_safe_arms": min(controls["c_star_a"] + controls["c_star_b"]) > 0,
        "same_negative_saddle_cone": qa < 0 and qb < 0 and qab < 0,
        "common_quadratic_descent": bilinear(ua + ub, ua + ub) < 0
        and bilinear(ua + ub, ua) < 0 and bilinear(ua + ub, ub) < 0,
        "finite_descent_witness": min(sum(descent_controls.values(), [])) > 0,
    }
    passed = all(gates.values())
    output = {
        "schema": "erdos1041_critical_ellipse_stationary_no_go_v1",
        "passed": passed,
        "gates": gates,
        "critical_points": [str(c_star), str(hub), str(c2)],
        "selected_roots": [str(a), str(b)],
        "critical_value_squares": [str(vstar_sq), str(hub_sq), str(v2_sq)],
        "root_schur_gaps": [str(x) for x in root_gaps],
        "nearest_root_schur_gaps": [str(x) for x in nearest_gaps],
        "minimum_bernstein_control": str(min(
            [x for row in controls.values() for x in row])),
        "threshold_gap": str(hub_sq * hub_sq - vstar_sq * v2_sq),
        "second_order_signs": [str(qa), str(qb), str(qab)],
        "minimum_descent_control": str(min(sum(descent_controls.values(), []))),
        "claim_boundary": (
            "Exact no-go for a universal stationary-system upper bound; "
            "not a counterexample to CE--GM, the tied-face selector, or Erdos #1041."
        ),
    }
    if args.json:
        print(json.dumps(output, indent=2, sort_keys=True))
    else:
        print("PASS" if passed else "FAIL", output)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())

