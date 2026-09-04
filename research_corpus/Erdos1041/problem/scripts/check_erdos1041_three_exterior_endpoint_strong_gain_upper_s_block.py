#!/usr/bin/env python3
"""Centered interval replay for the upper-s GP3 endpoint rectangle."""

import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import struct

BASE = Path(__file__).with_name(
    "check_erdos1041_three_exterior_endpoint_strong_gain_compact_block.py"
)
spec = importlib.util.spec_from_file_location("gp3_strong_gain_engine", BASE)
engine = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(engine)
I = engine.I
COUNTS = (16, 8, 8, 8)


def make_box(index, domain):
    return tuple(
        I(a + (b - a) * k / n, a + (b - a) * (k + 1) / n)
        for k, n, (a, b) in zip(index, COUNTS, domain)
    )


def certify(domain, refine):
    green = 0
    inactive = 0
    red = []
    minimum = float("inf")
    digest = hashlib.sha256()
    for index in itertools.product(*(range(n) for n in COUNTS)):
        lower, active = engine.centered_bound(make_box(index, domain))
        if active.hi < 0:
            inactive += 1
        elif lower.lo > 0:
            green += 1
            minimum = min(minimum, lower.lo)
            digest.update(struct.pack(">d", lower.lo))
        else:
            red.append(index)
    coarse_green = green
    refined_green = 0
    refined_red = []
    if refine:
        for index in red:
            parent = make_box(index, domain)
            midpoints = tuple((x.lo + x.hi) / 2 for x in parent)
            for bits in itertools.product((0, 1), repeat=4):
                child = tuple(
                    I(x.lo, midpoint) if bit == 0 else I(midpoint, x.hi)
                    for x, midpoint, bit in zip(parent, midpoints, bits)
                )
                lower, active = engine.centered_bound(child)
                if active.hi < 0:
                    inactive += 1
                elif lower.lo > 0:
                    refined_green += 1
                    minimum = min(minimum, lower.lo)
                    digest.update(struct.pack(">d", lower.lo))
                else:
                    refined_red.append((*index, *bits, lower.lo.hex()))
    return {
        "coarse_total": 8192, "coarse_green": coarse_green,
        "coarse_red": len(red), "refined_total": 16 * len(red) if refine else 0,
        "refined_green": refined_green, "inactive": inactive,
        "refined_red": len(refined_red) if refine else len(red),
        "minimum_hex": minimum.hex(), "digest": digest.hexdigest(),
    }


def main() -> int:
    low = certify(((0, 1), (1 / 8, 1 / 4), (5 / 8, 3 / 4), (1 / 4, 1 / 2)), True)
    high = certify(((0, 1), (1 / 8, 1 / 4), (5 / 8, 3 / 4), (1 / 2, 3 / 4)), False)
    expected_low = {
        "coarse_total": 8192, "coarse_green": 5621, "coarse_red": 2571,
        "refined_total": 41136, "refined_green": 41136, "inactive": 0,
        "refined_red": 0, "minimum_hex": "0x1.67abdc12cffffp-19",
        "digest": "ca328f8d6115b5e6a83cf91260d06e7e67b12dcf1d99529670380025968e66f9",
    }
    expected_high = {
        "coarse_total": 8192, "coarse_green": 8192, "coarse_red": 0,
        "refined_total": 0, "refined_green": 0, "inactive": 0,
        "refined_red": 0, "minimum_hex": "0x1.3388a897a6438p-3",
        "digest": "2c8b1faaed55d21480f92a04867ab4fbddc6e9ba55d88293186cb5d18f4c3b8f",
    }
    passed = low == expected_low and high == expected_high
    print(json.dumps({
        "schema": "erdos1041_three_exterior_endpoint_strong_gain_upper_s_block_v1",
        "certified_box": {
            "t": ["0", "1"], "r": ["1/8", "1/4"],
            "s": ["5/8", "3/4"], "w": ["1/4", "3/4"],
        },
        "low_w": low, "expected_low_w": expected_low,
        "high_w": high, "expected_high_w": expected_high,
        "endpoint_strong_gain_upper_s_block_positive": passed,
        "claim_boundary": (
            "Proves the true endpoint surplus positive on this active-cone "
            "rectangle only; not the full endpoint cone, GP3, or Erdos 1041."
        ),
        "pass": passed,
    }, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
