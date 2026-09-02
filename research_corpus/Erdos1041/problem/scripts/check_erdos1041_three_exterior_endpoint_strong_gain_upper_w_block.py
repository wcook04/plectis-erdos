#!/usr/bin/env python3
"""Centered interval replay for the adjoining GP3 endpoint block."""

import hashlib
import importlib.util
import itertools
import json
import math
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

DOMAIN = ((0, 1), (1 / 8, 1 / 4), (1 / 2, 5 / 8), (1 / 2, 3 / 4))
COUNTS = (16, 8, 8, 8)


def box(index):
    return tuple(
        I(a + (b - a) * k / n, a + (b - a) * (k + 1) / n)
        for k, n, (a, b) in zip(index, COUNTS, DOMAIN)
    )


def main() -> int:
    green = 0
    inactive = 0
    red = []
    minimum = float("inf")
    digest = hashlib.sha256()
    for index in itertools.product(*(range(n) for n in COUNTS)):
        lower, active = engine.centered_bound(box(index))
        if active.hi < 0:
            inactive += 1
        elif lower.lo > 0:
            green += 1
            minimum = min(minimum, lower.lo)
            digest.update(struct.pack(">d", lower.lo))
        else:
            red.append((*index, lower.lo.hex(), active.lo.hex(), active.hi.hex()))

    observed = {
        "total": math.prod(COUNTS), "green": green, "inactive": inactive,
        "red": len(red), "minimum_hex": minimum.hex(), "digest": digest.hexdigest(),
    }
    expected = {
        "total": 8192, "green": 8192, "inactive": 0, "red": 0,
        "minimum_hex": "0x1.738de557cd736p-3",
        "digest": "c7a7f6679a117b2a33748a39d35f4377559e0dc1e18d06eac9e9e62528ba1f13",
    }
    passed = observed == expected
    print(json.dumps({
        "schema": "erdos1041_three_exterior_endpoint_strong_gain_upper_w_block_v1",
        "certified_box": {
            "t": ["0", "1"], "r": ["1/8", "1/4"],
            "s": ["1/2", "5/8"], "w": ["1/2", "3/4"],
        },
        "partition": list(COUNTS), "observed": observed, "expected": expected,
        "endpoint_strong_gain_upper_w_block_positive": passed,
        "claim_boundary": (
            "Proves the true endpoint surplus positive on this active-cone block "
            "only; it does not prove the full endpoint cone, GP3, or Erdos 1041."
        ),
        "pass": passed,
    }, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
