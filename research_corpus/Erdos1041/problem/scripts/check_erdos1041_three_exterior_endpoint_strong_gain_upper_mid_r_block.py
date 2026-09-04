#!/usr/bin/env python3
"""Four-slab centered replay for the upper-middle-r GP3 endpoint block."""

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
        "low_s_low_w": ((0, 1), (1 / 2, 5 / 8), (1 / 2, 5 / 8), (1 / 4, 1 / 2)),
        "low_s_high_w": ((0, 1), (1 / 2, 5 / 8), (1 / 2, 5 / 8), (1 / 2, 3 / 4)),
        "high_s_low_w": ((0, 1), (1 / 2, 5 / 8), (5 / 8, 3 / 4), (1 / 4, 1 / 2)),
        "high_s_high_w": ((0, 1), (1 / 2, 5 / 8), (5 / 8, 3 / 4), (1 / 2, 3 / 4)),
    }
    observed = {
        "low_s_low_w": engine.certify(domains["low_s_low_w"], True),
        "low_s_high_w": engine.certify(domains["low_s_high_w"], False),
        "high_s_low_w": engine.certify(domains["high_s_low_w"], True),
        "high_s_high_w": engine.certify(domains["high_s_high_w"], True),
    }
    expected = {
        "low_s_low_w": {
            "coarse_total": 8192, "coarse_green": 2807, "coarse_red": 5385,
            "refined_total": 86160, "refined_green": 86160, "inactive": 0,
            "refined_red": 0, "minimum_hex": "0x1.f9710babaffffp-18",
            "digest": "53d4c04b1795e16d91a35a17884c112e343b853bc8223695486b2466c6aa1ed0",
        },
        "low_s_high_w": {
            "coarse_total": 8192, "coarse_green": 8192, "coarse_red": 0,
            "refined_total": 0, "refined_green": 0, "inactive": 0,
            "refined_red": 0, "minimum_hex": "0x1.a924fdd904aefp-7",
            "digest": "0272e3f31a85039e3a0c4280b450542dadd86a88426916c6838d4446a2fb5670",
        },
        "high_s_low_w": {
            "coarse_total": 8192, "coarse_green": 2073, "coarse_red": 6119,
            "refined_total": 97904, "refined_green": 96111, "inactive": 1793,
            "refined_red": 0, "minimum_hex": "0x1.e45335d816fffp-15",
            "digest": "cbb39272d6fc7ce9cf1af1eeb1b20a8161b1fec1785f45fa41eb6fb805fa20bb",
        },
        "high_s_high_w": {
            "coarse_total": 8192, "coarse_green": 8137, "coarse_red": 55,
            "refined_total": 880, "refined_green": 399, "inactive": 481,
            "refined_red": 0, "minimum_hex": "0x1.e170f919ac3ffp-13",
            "digest": "dc0e1ff3a9ce155c600c48237fb79213ff52bac9bbfac214710059e00d39f290",
        },
    }
    passed = observed == expected
    print(json.dumps({
        "schema": "erdos1041_three_exterior_endpoint_strong_gain_upper_mid_r_block_v1",
        "certified_box": {
            "t": ["0", "1"], "r": ["1/2", "5/8"],
            "s": ["1/2", "3/4"], "w": ["1/4", "3/4"],
        },
        "observed": observed, "expected": expected,
        "endpoint_strong_gain_upper_mid_r_block_positive": passed,
        "claim_boundary": (
            "Proves the true endpoint surplus positive wherever this endpoint "
            "branch is active on the stated rectangle; not GP3 or Erdos 1041."
        ),
        "pass": passed,
    }, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
