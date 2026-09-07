#!/usr/bin/env python3
"""Exact replay for the first quarter-s endpoint block."""

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
        ("low_w", ((0, 1), (1 / 8, 1 / 4), (1 / 4, 3 / 8), (1 / 4, 1 / 2)), True),
        ("high_w", ((0, 1), (1 / 8, 1 / 4), (1 / 4, 3 / 8), (1 / 2, 3 / 4)), False),
    )
    with ProcessPoolExecutor(
        max_workers=2, mp_context=multiprocessing.get_context("fork")
    ) as pool:
        observed = dict(pool.map(certify_item, domains))
    expected = {
        "low_w": {
            "coarse_total": 8192, "coarse_green": 7193, "coarse_red": 999,
            "refined_total": 15984, "refined_green": 15984, "inactive": 0,
            "refined_red": 0, "minimum_hex": "0x1.14b0644679fffp-16",
            "digest": "b83d29f5561a33bff0663972e60dfa63a91f6e6194acc3580f4a5d462229140c",
        },
        "high_w": {
            "coarse_total": 8192, "coarse_green": 8192, "coarse_red": 0,
            "refined_total": 0, "refined_green": 0, "inactive": 0,
            "refined_red": 0, "minimum_hex": "0x1.0d4c9fa258a42p-2",
            "digest": "135a90becd3d466b440578e82446a9221f6fa4760d1036f0cc5ebbadd87166b8",
        },
    }
    passed = observed == expected
    print(json.dumps({
        "schema": "erdos1041_three_exterior_endpoint_strong_gain_quarter_s_block_v1",
        "certified_box": {
            "t": ["0", "1"], "r": ["1/8", "1/4"],
            "s": ["1/4", "3/8"], "w": ["1/4", "3/4"],
        },
        "observed": observed,
        "expected": expected,
        "inactive_cells": sum(row["inactive"] for row in observed.values()),
        "unresolved_active_cells": sum(row["refined_red"] for row in observed.values()),
        "green_cells_are_strict_sign_proofs": passed,
        "inactive_cells_are_branch_exclusions_not_sign_proofs": True,
        "endpoint_strong_gain_quarter_s_block_positive": passed,
        "claim_boundary": (
            "Proves the true endpoint surplus positive on the stated active "
            "block; not the rest of the quarter-s slab, full GP3, or Erdos 1041."
        ),
        "pass": passed,
    }, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
