#!/usr/bin/env python3
"""Four-slab centered replay for the upper-r GP3 endpoint rectangle."""

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
        "low_s_low_w": ((0, 1), (1 / 4, 3 / 8), (1 / 2, 5 / 8), (1 / 4, 1 / 2)),
        "low_s_high_w": ((0, 1), (1 / 4, 3 / 8), (1 / 2, 5 / 8), (1 / 2, 3 / 4)),
        "high_s_low_w": ((0, 1), (1 / 4, 3 / 8), (5 / 8, 3 / 4), (1 / 4, 1 / 2)),
        "high_s_high_w": ((0, 1), (1 / 4, 3 / 8), (5 / 8, 3 / 4), (1 / 2, 3 / 4)),
    }
    observed = {
        "low_s_low_w": engine.certify(domains["low_s_low_w"], True),
        "low_s_high_w": engine.certify(domains["low_s_high_w"], False),
        "high_s_low_w": engine.certify(domains["high_s_low_w"], True),
        "high_s_high_w": engine.certify(domains["high_s_high_w"], False),
    }
    expected = {
        "low_s_low_w": {
            "coarse_total": 8192, "coarse_green": 4573, "coarse_red": 3619,
            "refined_total": 57904, "refined_green": 57904, "inactive": 0,
            "refined_red": 0, "minimum_hex": "0x1.a35be13c627ffp-15",
            "digest": "ab929b08f163dc061cd6f5a887b19f5ae8b3ff450b2a56b5e4f6b644f7ac46a2",
        },
        "low_s_high_w": {
            "coarse_total": 8192, "coarse_green": 8192, "coarse_red": 0,
            "refined_total": 0, "refined_green": 0, "inactive": 0,
            "refined_red": 0, "minimum_hex": "0x1.e296def52e22fp-4",
            "digest": "46e7b7597722081d40aa364099a3a6f01929aa458c633a72aa4fcb553687be8c",
        },
        "high_s_low_w": {
            "coarse_total": 8192, "coarse_green": 4104, "coarse_red": 4088,
            "refined_total": 65408, "refined_green": 65408, "inactive": 0,
            "refined_red": 0, "minimum_hex": "0x1.4f220d90993ffp-14",
            "digest": "0c92bf118c9d2b2a2520b7139487ceb025f29d413e0c9e42809660151c50766c",
        },
        "high_s_high_w": {
            "coarse_total": 8192, "coarse_green": 8192, "coarse_red": 0,
            "refined_total": 0, "refined_green": 0, "inactive": 0,
            "refined_red": 0, "minimum_hex": "0x1.2beb10b70cdffp-4",
            "digest": "023babaa3b56eb5ec2be969554257ff62e573de19f16e75927b46f9aa13a91cd",
        },
    }
    passed = observed == expected
    print(json.dumps({
        "schema": "erdos1041_three_exterior_endpoint_strong_gain_upper_r_block_v1",
        "certified_box": {
            "t": ["0", "1"], "r": ["1/4", "3/8"],
            "s": ["1/2", "3/4"], "w": ["1/4", "3/4"],
        },
        "observed": observed, "expected": expected,
        "endpoint_strong_gain_upper_r_block_positive": passed,
        "claim_boundary": (
            "Proves the true endpoint surplus positive on this active-cone "
            "rectangle only; not the full endpoint cone, GP3, or Erdos 1041."
        ),
        "pass": passed,
    }, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
