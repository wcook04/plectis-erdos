#!/usr/bin/env python3
"""Rigorous binary64 interval certificate for a compact GP3 block.

The ordered chart is u=r*s*w, v=s*w.  Every primitive floating operation is
expanded by one adjacent binary64 number with math.nextafter, so the returned
interval encloses the exact real operation under round-to-nearest binary64.
All partition endpoints are dyadic and hence exactly representable.
"""

from __future__ import annotations

import hashlib
import itertools
import json
import math
import struct
import sys


NEGATIVE_INFINITY = float("-inf")
POSITIVE_INFINITY = float("inf")


def downward(value: float) -> float:
    return math.nextafter(value, NEGATIVE_INFINITY)


def upward(value: float) -> float:
    return math.nextafter(value, POSITIVE_INFINITY)


class Interval:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        self.lo = float(lo)
        self.hi = float(lo if hi is None else hi)
        assert math.isfinite(self.lo) and math.isfinite(self.hi)
        assert self.lo <= self.hi

    def __add__(self, other):
        other = as_interval(other)
        return Interval(
            downward(self.lo + other.lo), upward(self.hi + other.hi)
        )

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-as_interval(other))

    def __rsub__(self, other):
        return as_interval(other) - self

    def __mul__(self, other):
        other = as_interval(other)
        products = (
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        )
        return Interval(downward(min(products)), upward(max(products)))

    __rmul__ = __mul__

    def inverse(self):
        assert self.lo > 0 or self.hi < 0
        first = 1.0 / self.hi
        second = 1.0 / self.lo
        return Interval(downward(min(first, second)), upward(max(first, second)))

    def __truediv__(self, other):
        return self * as_interval(other).inverse()

    def __rtruediv__(self, other):
        return as_interval(other) / self

    def __pow__(self, exponent):
        assert isinstance(exponent, int) and exponent >= 0
        answer = Interval(1)
        for _ in range(exponent):
            answer = answer * self
        return answer


def as_interval(value):
    return value if isinstance(value, Interval) else Interval(value)


def stationary_surplus(box):
    """Natural interval extension of the cancelled stationary surplus."""
    t, r, s, w = box
    u = r * s * w
    v = s * w
    radii = (u, v, w)

    def A(x):
        return 1 + x + x * x

    def D(x):
        return 1 + t * x + t * t * x * x

    def L(x):
        return (1 - x * x) / (A(x) ** 2) + t * (
            1 - t * t * x * x
        ) / (D(x) ** 2)

    def self_term(x):
        return x / (1 - x) + t * x * x / (1 - t * x)

    def pair_term(a, b):
        return a * (1 + b / 2) / A(b) - t * a * b * (t * b + 0.5) / D(b)

    raw = Interval(0)
    for radius in radii:
        raw += self_term(radius)
    for i, j in ((0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)):
        raw += pair_term(radii[i], radii[j])
    product = u * v * w
    radius_sum = u + v + w
    raw -= 3 * radius_sum / (1 - product)
    raw -= 3 * t**3 * radius_sum * product / (1 - t**3 * product)

    kernels = tuple(L(radius) for radius in radii)
    correction = 0.5 * (
        u * v * (kernels[0] + kernels[1])
        + u * w * (kernels[0] + kernels[2])
        + v * w * (kernels[1] + kernels[2])
    )
    correction -= (
        0.5
        * u
        * u
        * (kernels[0] + kernels[1])
        * (kernels[0] + kernels[2])
        / (kernels[1] + kernels[2])
    )
    correction -= (
        0.5
        * v
        * v
        * (kernels[0] + kernels[1])
        * (kernels[1] + kernels[2])
        / (kernels[0] + kernels[2])
    )
    correction -= (
        0.5
        * w
        * w
        * (kernels[0] + kernels[2])
        * (kernels[1] + kernels[2])
        / (kernels[0] + kernels[1])
    )
    return raw + correction


def coarse_box(it, ir, js, kw):
    return (
        Interval(it / 64, (it + 1) / 64),
        Interval(1 / 4 + ir / 128, 1 / 4 + (ir + 1) / 128),
        Interval(1 / 4 + js / 128, 1 / 4 + (js + 1) / 128),
        Interval(1 / 4 + kw / 128, 1 / 4 + (kw + 1) / 128),
    )


def refined_box(it, ir, js, kw, ar, ass, aw):
    return (
        Interval(it / 64, (it + 1) / 64),
        Interval(1 / 4 + ir / 128 + ar / 256, 1 / 4 + ir / 128 + (ar + 1) / 256),
        Interval(1 / 4 + js / 128 + ass / 256, 1 / 4 + js / 128 + (ass + 1) / 256),
        Interval(1 / 4 + kw / 128 + aw / 256, 1 / 4 + kw / 128 + (aw + 1) / 256),
    )


def main() -> int:
    ieee_binary64 = all(
        (
            sys.float_info.radix == 2,
            sys.float_info.mant_dig == 53,
            sys.float_info.max_exp == 1024,
            sys.float_info.rounds == 1,
            math.nextafter(1.0, POSITIVE_INFINITY).hex() == "0x1.0000000000001p+0",
        )
    )

    red = []
    coarse_green = 0
    minimum = POSITIVE_INFINITY
    digest = hashlib.sha256()
    for it, ir, js, kw in itertools.product(range(64), range(16), range(16), range(16)):
        lower = stationary_surplus(coarse_box(it, ir, js, kw)).lo
        if lower > 0:
            coarse_green += 1
            minimum = min(minimum, lower)
            digest.update(struct.pack(">d", lower))
        else:
            red.append((it, ir, js, kw))

    refined_green = 0
    refined_red = []
    for it, ir, js, kw in red:
        for ar, ass, aw in itertools.product(range(2), repeat=3):
            lower = stationary_surplus(
                refined_box(it, ir, js, kw, ar, ass, aw)
            ).lo
            if lower > 0:
                refined_green += 1
                minimum = min(minimum, lower)
                digest.update(struct.pack(">d", lower))
            else:
                refined_red.append((it, ir, js, kw, ar, ass, aw, lower.hex()))

    expected = {
        "coarse_total": 262144,
        "coarse_green": 224994,
        "coarse_red": 37150,
        "refined_total": 297200,
        "refined_green": 297200,
        "minimum_hex": "0x1.5054f4388ffffp-21",
        "digest": "5b11d1a225c48e8e825863b17483715f8fff7ad6b9a65fc81a00b410977357f5",
    }
    observed = {
        "coarse_total": 64 * 16**3,
        "coarse_green": coarse_green,
        "coarse_red": len(red),
        "refined_total": 8 * len(red),
        "refined_green": refined_green,
        "minimum_hex": minimum.hex(),
        "digest": digest.hexdigest(),
    }
    passed = ieee_binary64 and not refined_red and observed == expected
    result = {
        "schema": "erdos1041_three_exterior_stationary_compact_interior_block_receipt_v1",
        "ordered_chart": "u=r*s*w, v=s*w",
        "certified_box": {
            "t": ["0", "1"],
            "r": ["1/4", "3/8"],
            "s": ["1/4", "3/8"],
            "w": ["1/4", "3/8"],
        },
        "ieee_binary64_round_to_nearest_verified": ieee_binary64,
        "outward_rounding": "one math.nextafter step after every primitive operation",
        "coarse_total": observed["coarse_total"],
        "coarse_green": coarse_green,
        "coarse_dependency_red": len(red),
        "refined_total": observed["refined_total"],
        "refined_green": refined_green,
        "refined_red": len(refined_red),
        "weakest_lower_bound_hex": minimum.hex(),
        "weakest_lower_bound_decimal": minimum,
        "accepted_lower_bound_sha256": digest.hexdigest(),
        "compact_stationary_block_positive": passed,
        "claim_boundary": (
            "Proves S_stat>0 for all t in [0,1] and r,s,w in [1/4,3/8] "
            "in the ordered chart. This is one compact off-face block, not "
            "the whole ordered cone, GP3, or Erdos 1041."
        ),
        "pass": passed,
    }
    print(json.dumps(result, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
