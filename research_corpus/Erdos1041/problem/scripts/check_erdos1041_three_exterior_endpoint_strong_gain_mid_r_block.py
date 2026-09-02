#!/usr/bin/env python3
"""Four-slab centered replay for the middle-r GP3 endpoint rectangle."""

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
        "low_s_low_w": ((0, 1), (3 / 8, 1 / 2), (1 / 2, 5 / 8), (1 / 4, 1 / 2)),
        "low_s_high_w": ((0, 1), (3 / 8, 1 / 2), (1 / 2, 5 / 8), (1 / 2, 3 / 4)),
        "high_s_low_w": ((0, 1), (3 / 8, 1 / 2), (5 / 8, 3 / 4), (1 / 4, 1 / 2)),
        "high_s_high_w": ((0, 1), (3 / 8, 1 / 2), (5 / 8, 3 / 4), (1 / 2, 3 / 4)),
    }
    observed = {
        "low_s_low_w": engine.certify(domains["low_s_low_w"], True),
        "low_s_high_w": engine.certify(domains["low_s_high_w"], False),
        "high_s_low_w": engine.certify(domains["high_s_low_w"], True),
        "high_s_high_w": engine.certify(domains["high_s_high_w"], False),
    }
    expected = {
        "low_s_low_w": {
            "coarse_total": 8192, "coarse_green": 3595, "coarse_red": 4597,
            "refined_total": 73552, "refined_green": 73552, "inactive": 0,
            "refined_red": 0, "minimum_hex": "0x1.c71b65f35dfffp-17",
            "digest": "ca20a1f00de6891b4a5e02bab7a312657a7dd37b5d54fb5faea1f9da0597b092",
        },
        "low_s_high_w": {
            "coarse_total": 8192, "coarse_green": 8192, "coarse_red": 0,
            "refined_total": 0, "refined_green": 0, "inactive": 0,
            "refined_red": 0, "minimum_hex": "0x1.05508a9118a13p-4",
            "digest": "ab9cda52fbcb18665c6c647531a882efa35c12cc00aa02a8637d6a6a108ba3d0",
        },
        "high_s_low_w": {
            "coarse_total": 8192, "coarse_green": 3016, "coarse_red": 5176,
            "refined_total": 82816, "refined_green": 82816, "inactive": 0,
            "refined_red": 0, "minimum_hex": "0x1.11b62c00ab7ffp-15",
            "digest": "dbd132ce7daa697aceff244f412ff15915488c4fac65ac55bc5d3fb4616ed5d7",
        },
        "high_s_high_w": {
            "coarse_total": 8192, "coarse_green": 8192, "coarse_red": 0,
            "refined_total": 0, "refined_green": 0, "inactive": 0,
            "refined_red": 0, "minimum_hex": "0x1.0c3558b31ed9fp-8",
            "digest": "89af2c1106090319694b86ed13d48a7c6308be45337e84a7bc19e2c7c75eafeb",
        },
    }
    passed = observed == expected
    print(json.dumps({
        "schema": "erdos1041_three_exterior_endpoint_strong_gain_mid_r_block_v1",
        "certified_box": {
            "t": ["0", "1"], "r": ["3/8", "1/2"],
            "s": ["1/2", "3/4"], "w": ["1/4", "3/4"],
        },
        "observed": observed, "expected": expected,
        "endpoint_strong_gain_mid_r_block_positive": passed,
        "claim_boundary": (
            "Proves the true endpoint surplus positive on this active-cone "
            "rectangle only; not the full endpoint cone, GP3, or Erdos 1041."
        ),
        "pass": passed,
    }, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
