#!/usr/bin/env python3
"""Exact centered replay for the first lower-s GP3 endpoint block."""

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
        ("low_w", ((0, 1), (1 / 8, 1 / 4), (3 / 8, 1 / 2), (1 / 4, 1 / 2)), True),
        ("high_w", ((0, 1), (1 / 8, 1 / 4), (3 / 8, 1 / 2), (1 / 2, 3 / 4)), False),
    )
    with ProcessPoolExecutor(
        max_workers=2, mp_context=multiprocessing.get_context("fork")
    ) as pool:
        observed = dict(pool.map(certify_item, domains))
    expected = {
        "low_w": {
            "coarse_total": 8192, "coarse_green": 6572, "coarse_red": 1620,
            "refined_total": 25920, "refined_green": 25920, "inactive": 0,
            "refined_red": 0, "minimum_hex": "0x1.7bcd1b61d9bffp-15",
            "digest": "a27d81d34c5a87feb8aefd717ceff49bf324366df8006635c975fd85d4e3703c",
        },
        "high_w": {
            "coarse_total": 8192, "coarse_green": 8192, "coarse_red": 0,
            "refined_total": 0, "refined_green": 0, "inactive": 0,
            "refined_red": 0, "minimum_hex": "0x1.c2405ac076c38p-3",
            "digest": "1e880924e1d74cc85349e432dff38e01dfbb0baebb132cc58bd34eff3e3dfb4f",
        },
    }
    passed = observed == expected
    print(json.dumps({
        "schema": "erdos1041_three_exterior_endpoint_strong_gain_lower_s_block_v1",
        "certified_box": {
            "t": ["0", "1"], "r": ["1/8", "1/4"],
            "s": ["3/8", "1/2"], "w": ["1/4", "3/4"],
        },
        "observed": observed,
        "expected": expected,
        "inactive_cells": sum(row["inactive"] for row in observed.values()),
        "unresolved_active_cells": sum(row["refined_red"] for row in observed.values()),
        "endpoint_strong_gain_lower_s_block_positive": passed,
        "claim_boundary": (
            "Proves the true endpoint surplus positive on the stated active "
            "block; not the full lower-s face, GP3, or Erdos 1041."
        ),
        "pass": passed,
    }, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
