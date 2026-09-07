#!/usr/bin/env python3
"""Four-slab centered replay for the high-r GP3 endpoint block."""

import importlib.util
import json
from pathlib import Path

BASE = Path(__file__).with_name(
    "check_erdos1041_three_exterior_endpoint_strong_gain_upper_s_block.py"
)
spec = importlib.util.spec_from_file_location("gp3_upper_s_engine", BASE)
engine = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(engine)


def main() -> int:
    domains = {
        "low_s_low_w": ((0, 1), (5 / 8, 3 / 4), (1 / 2, 5 / 8), (1 / 4, 1 / 2)),
        "low_s_high_w": ((0, 1), (5 / 8, 3 / 4), (1 / 2, 5 / 8), (1 / 2, 3 / 4)),
        "high_s_low_w": ((0, 1), (5 / 8, 3 / 4), (5 / 8, 3 / 4), (1 / 4, 1 / 2)),
        "high_s_high_w": ((0, 1), (5 / 8, 3 / 4), (5 / 8, 3 / 4), (1 / 2, 3 / 4)),
    }
    observed = {
        "low_s_low_w": engine.certify(domains["low_s_low_w"], True),
        "low_s_high_w": engine.certify(domains["low_s_high_w"], True),
        "high_s_low_w": engine.certify(domains["high_s_low_w"], True),
        "high_s_high_w": engine.certify(domains["high_s_high_w"], True),
    }
    expected = {
        "low_s_low_w": {
            "coarse_total": 8192, "coarse_green": 2112, "coarse_red": 6080,
            "refined_total": 97280, "refined_green": 97280, "inactive": 0,
            "refined_red": 0, "minimum_hex": "0x1.dbc49a70bcfffp-16",
            "digest": "81950be61d7a84e8496cee3dc5455fc48b0b8e7032f137d50a16025b6fe02d1e",
        },
        "low_s_high_w": {
            "coarse_total": 8192, "coarse_green": 8174, "coarse_red": 18,
            "refined_total": 288, "refined_green": 288, "inactive": 0,
            "refined_red": 0, "minimum_hex": "0x1.428e74af5247fp-11",
            "digest": "e64cfd44c6a1bb8276a6d029a2448cd08466b48759246615d00029918f83f7a9",
        },
        "high_s_low_w": {
            "coarse_total": 8192, "coarse_green": 1287, "coarse_red": 6905,
            "refined_total": 110480, "refined_green": 85617, "inactive": 24863,
            "refined_red": 0, "minimum_hex": "0x1.227e99b657fffp-14",
            "digest": "10395aa7536651ab89e095066aad9d3f7a10f3d4f7b95760455f28d29376d6c8",
        },
        "high_s_high_w": {
            "coarse_total": 8192, "coarse_green": 7792, "coarse_red": 400,
            "refined_total": 6400, "refined_green": 666, "inactive": 5734,
            "refined_red": 0, "minimum_hex": "0x1.f5af578fea1ffp-13",
            "digest": "038b4a09c21397aeb8b6584a594e1ffc678087f39f23cdf32ef41cda1e658455",
        },
    }
    passed = observed == expected
    print(json.dumps({
        "schema": "erdos1041_three_exterior_endpoint_strong_gain_high_r_block_v1",
        "certified_box": {
            "t": ["0", "1"], "r": ["5/8", "3/4"],
            "s": ["1/2", "3/4"], "w": ["1/4", "3/4"],
        },
        "observed": observed, "expected": expected,
        "endpoint_strong_gain_high_r_block_positive": passed,
        "claim_boundary": (
            "Proves the true endpoint surplus positive wherever this endpoint "
            "branch is active on the stated rectangle; not GP3 or Erdos 1041."
        ),
        "pass": passed,
    }, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
