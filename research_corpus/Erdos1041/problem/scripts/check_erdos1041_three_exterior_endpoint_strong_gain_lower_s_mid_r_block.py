#!/usr/bin/env python3
"""Two-process exact replay for the middle-r lower-s endpoint block."""

import importlib.util
import json
import multiprocessing
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

BASE = Path(__file__).with_name(
    "check_erdos1041_three_exterior_endpoint_strong_gain_upper_s_block.py"
)
spec = importlib.util.spec_from_file_location("gp3_upper_s_engine", BASE)
engine = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(engine)


def certify_item(item):
    name, domain, refine = item
    return name, engine.certify(domain, refine)


def main() -> int:
    domains = (
        ("low_w", ((0, 1), (1 / 4, 1 / 2), (3 / 8, 1 / 2), (1 / 4, 1 / 2)), True),
        ("high_w", ((0, 1), (1 / 4, 1 / 2), (3 / 8, 1 / 2), (1 / 2, 3 / 4)), False),
    )
    with ProcessPoolExecutor(
        max_workers=2, mp_context=multiprocessing.get_context("fork")
    ) as pool:
        observed = dict(pool.map(certify_item, domains))
    expected = {
        "low_w": {
            "coarse_total": 8192, "coarse_green": 3768, "coarse_red": 4424,
            "refined_total": 70784, "refined_green": 70784, "inactive": 0,
            "refined_red": 0, "minimum_hex": "0x1.5290e5071a7ffp-15",
            "digest": "a20144e5192310a62fc41322b9dd37855e90caa4ecc62754352ec62137a65443",
        },
        "high_w": {
            "coarse_total": 8192, "coarse_green": 8192, "coarse_red": 0,
            "refined_total": 0, "refined_green": 0, "inactive": 0,
            "refined_red": 0, "minimum_hex": "0x1.1ab505a607fa3p-4",
            "digest": "7ff0c4799d6e04ceecaf78602848bfedbba63ac69e142ecbdf89902335697802",
        },
    }
    passed = observed == expected
    print(json.dumps({
        "schema": "erdos1041_three_exterior_endpoint_strong_gain_lower_s_mid_r_block_v1",
        "certified_box": {
            "t": ["0", "1"], "r": ["1/4", "1/2"],
            "s": ["3/8", "1/2"], "w": ["1/4", "3/4"],
        },
        "observed": observed, "expected": expected,
        "inactive_cells": sum(row["inactive"] for row in observed.values()),
        "unresolved_active_cells": sum(row["refined_red"] for row in observed.values()),
        "endpoint_strong_gain_lower_s_mid_r_block_positive": passed,
        "claim_boundary": (
            "Proves the true endpoint surplus positive on the stated active "
            "block; not the full lower-s face, GP3, or Erdos 1041."
        ),
        "pass": passed,
    }, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
