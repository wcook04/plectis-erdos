#!/usr/bin/env python3
"""Rigorous centered-form certificate for a compact GP3 endpoint block."""

from __future__ import annotations

import hashlib
import importlib.util
import itertools
import json
import math
from pathlib import Path
import struct
import sys

BASE = Path(__file__).with_name(
    "check_erdos1041_three_exterior_stationary_compact_interior_block.py"
)
spec = importlib.util.spec_from_file_location("gp3_interval_engine", BASE)
engine = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(engine)
I = engine.Interval


class Dual:
    __slots__ = ("v", "d")

    def __init__(self, value, derivative=None):
        self.v = value if isinstance(value, I) else I(value)
        self.d = (I(0),) * 4 if derivative is None else derivative

    def __add__(self, other):
        other = dual(other)
        return Dual(self.v + other.v, tuple(a + b for a, b in zip(self.d, other.d)))

    __radd__ = __add__

    def __neg__(self):
        return Dual(-self.v, tuple(-a for a in self.d))

    def __sub__(self, other):
        return self + (-dual(other))

    def __rsub__(self, other):
        return dual(other) - self

    def __mul__(self, other):
        other = dual(other)
        return Dual(
            self.v * other.v,
            tuple(a * other.v + self.v * b for a, b in zip(self.d, other.d)),
        )

    __rmul__ = __mul__

    def inverse(self):
        return Dual(1 / self.v, tuple(-a / (self.v * self.v) for a in self.d))

    def __truediv__(self, other):
        return self * dual(other).inverse()

    def __rtruediv__(self, other):
        return dual(other) / self

    def __pow__(self, exponent):
        assert isinstance(exponent, int) and exponent >= 0
        if exponent == 0:
            return Dual(1)
        return Dual(
            self.v**exponent,
            tuple(exponent * self.v ** (exponent - 1) * a for a in self.d),
        )


def dual(value):
    return value if isinstance(value, Dual) else Dual(value)


def A(x):
    return 1 + x + x * x


def D(t, x):
    return 1 + t * x + t * t * x * x


def L(t, x):
    return (1 - x * x) / A(x) ** 2 + t * (1 - t * t * x * x) / D(t, x) ** 2


def expression(values):
    t, r, s, w = values
    u = r * s * w
    v = s * w
    radii = (u, v, w)
    lu, lv, lw = L(t, u), L(t, v), L(t, w)
    a = u * v * (lu + lv)
    b = u * w * (lu + lw)
    c = v * w * (lv + lw)

    def self_term(x):
        return x / (1 - x) + t * x * x / (1 - t * x)

    def pair_term(x, y):
        return x * (1 + y / 2) / A(y) - t * x * y * (t * y + 0.5) / D(t, y)

    raw = Dual(0) if isinstance(t, Dual) else I(0)
    for x in radii:
        raw += self_term(x)
    for i, j in ((0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)):
        raw += pair_term(radii[i], radii[j])
    product = u * v * w
    radius_sum = u + v + w
    raw -= 3 * radius_sum / (1 - product)
    raw -= 3 * t**3 * radius_sum * product / (1 - t**3 * product)
    endpoint = raw + (3 * a - b - c) / 2

    def J(x):
        return (1 - x) / (1 + x) ** 5 + t * t * (1 - t * x) / (1 + t * x) ** 5

    mu = 4 * u * v * (v * J(v) + u * J(u))
    nu = b * b * c * c / (b + c) ** 3
    lower_bound = endpoint + 9 * mu * nu / (8 * (mu + nu))
    active_test = b * c - a * (b + c)
    return lower_bound, active_test


def centered_bound(box):
    midpoints = tuple((x.lo + x.hi) / 2 for x in box)
    point_value, _ = expression(tuple(I(x) for x in midpoints))
    variables = []
    for j, x in enumerate(box):
        derivative = [I(0) for _ in range(4)]
        derivative[j] = I(1)
        variables.append(Dual(x, tuple(derivative)))
    whole, active = expression(tuple(variables))
    answer = point_value
    for j, x in enumerate(box):
        answer += whole.d[j] * I(x.lo - midpoints[j], x.hi - midpoints[j])
    return answer, active.v


DOMAIN = ((0, 1), (1 / 8, 1 / 4), (1 / 2, 5 / 8), (1 / 4, 1 / 2))
COUNTS = (16, 8, 8, 8)


def box(index):
    return tuple(
        I(a + (b - a) * k / n, a + (b - a) * (k + 1) / n)
        for k, n, (a, b) in zip(index, COUNTS, DOMAIN)
    )


def main() -> int:
    ieee_binary64 = all(
        (
            sys.float_info.radix == 2,
            sys.float_info.mant_dig == 53,
            sys.float_info.max_exp == 1024,
            sys.float_info.rounds == 1,
            math.nextafter(1.0, float("inf")).hex() == "0x1.0000000000001p+0",
        )
    )
    green = 0
    inactive = 0
    red = []
    minimum = float("inf")
    digest = hashlib.sha256()
    for index in itertools.product(*(range(n) for n in COUNTS)):
        lower, active = centered_bound(box(index))
        if active.hi < 0:
            inactive += 1
        elif lower.lo > 0:
            green += 1
            minimum = min(minimum, lower.lo)
            digest.update(struct.pack(">d", lower.lo))
        else:
            red.append(index)

    coarse_green = green
    coarse_red = len(red)
    refined_green = 0
    refined_red = []
    for index in red:
        parent = box(index)
        midpoints = tuple((x.lo + x.hi) / 2 for x in parent)
        for bits in itertools.product((0, 1), repeat=4):
            child = tuple(
                I(x.lo, midpoint) if bit == 0 else I(midpoint, x.hi)
                for x, midpoint, bit in zip(parent, midpoints, bits)
            )
            lower, active = centered_bound(child)
            if active.hi < 0:
                inactive += 1
            elif lower.lo > 0:
                refined_green += 1
                minimum = min(minimum, lower.lo)
                digest.update(struct.pack(">d", lower.lo))
            else:
                refined_red.append((*index, *bits, lower.lo.hex()))

    observed = {
        "coarse_total": math.prod(COUNTS),
        "coarse_green": coarse_green,
        "coarse_red": coarse_red,
        "refined_total": 16 * coarse_red,
        "refined_green": refined_green,
        "inactive": inactive,
        "refined_red": len(refined_red),
        "minimum_hex": minimum.hex(),
        "digest": digest.hexdigest(),
    }
    expected = {
        "coarse_total": 8192,
        "coarse_green": 6020,
        "coarse_red": 2172,
        "refined_total": 34752,
        "refined_green": 34752,
        "inactive": 0,
        "refined_red": 0,
        "minimum_hex": "0x1.e3ea730897fffp-17",
        "digest": "13f0965f34498e29e80c4f18a5e32ae1a49e91ad8730ad635de49e6dd7b2303c",
    }
    passed = ieee_binary64 and observed == expected
    print(json.dumps({
        "schema": "erdos1041_three_exterior_endpoint_strong_gain_compact_block_v1",
        "certified_box": {
            "t": ["0", "1"], "r": ["1/8", "1/4"],
            "s": ["1/2", "5/8"], "w": ["1/4", "1/2"],
        },
        "active_cone": "bc-a(b+c)>=0",
        "partition": list(COUNTS),
        "ieee_binary64_round_to_nearest_verified": ieee_binary64,
        "outward_rounding": "one math.nextafter step after every primitive operation",
        "centered_form": "B(m)+sum_j partial_j B(box_j)*(box_j-m_j)",
        "observed": observed,
        "expected": expected,
        "endpoint_strong_gain_compact_block_positive": passed,
        "claim_boundary": (
            "Proves the true endpoint surplus positive on the stated active-cone "
            "block only; it does not prove the full endpoint cone, GP3, or Erdos 1041."
        ),
        "pass": passed,
    }, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
