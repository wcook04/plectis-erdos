#!/usr/bin/env python3
"""Exact replay for terminal r on the quarter-s endpoint slab."""

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
    name, domain = item
    return name, engine.certify(domain, True)


def main() -> int:
    domains = (
        ("low_w", ((0, 1), (1 / 2, 1), (1 / 4, 3 / 8), (1 / 4, 1 / 2))),
        ("high_w", ((0, 1), (1 / 2, 1), (1 / 4, 3 / 8), (1 / 2, 3 / 4))),
    )
    with ProcessPoolExecutor(
        max_workers=2, mp_context=multiprocessing.get_context("fork")
    ) as pool:
        observed = dict(pool.map(certify_item, domains))
    expected = {
        "low_w": {
            "coarse_total": 8192, "coarse_green": 1603, "coarse_red": 6589,
            "refined_total": 105424, "refined_green": 105424, "inactive": 0,
            "refined_red": 0, "minimum_hex": "0x1.1952a5818cbffp-13",
            "digest": "0dbcd02b6d2e5e9227b1099ac0b2d78e69aa51084ee3f8578c641c9cd0e4eb8f",
        },
        "high_w": {
            "coarse_total": 8192, "coarse_green": 8151, "coarse_red": 41,
            "refined_total": 656, "refined_green": 656, "inactive": 0,
            "refined_red": 0, "minimum_hex": "0x1.351ea34ce1fffp-13",
            "digest": "25549e34133af3770d22a4cd1a7713401f34c38fd193b56846f4d3874a428a8c",
        },
    }
    passed = observed == expected
    print(json.dumps({
        "schema": "erdos1041_three_exterior_endpoint_strong_gain_quarter_s_terminal_r_block_v1",
        "certified_box": {
            "t": ["0", "1"], "r": ["1/2", "1"],
            "s": ["1/4", "3/8"], "w": ["1/4", "3/4"],
        },
        "composed_central_rectangle": {
            "t": ["0", "1"], "r": ["1/8", "1"],
            "s": ["1/4", "3/4"], "w": ["1/4", "3/4"],
            "raw_rsw_chart_volume": "7/32",
            "volume_boundary": "coordinate volume, not active-cone measure",
        },
        "observed": observed,
        "expected": expected,
        "inactive_cells": sum(row["inactive"] for row in observed.values()),
        "unresolved_active_cells": sum(row["refined_red"] for row in observed.values()),
        "green_cells_are_strict_sign_proofs": passed,
        "inactive_cells_are_branch_exclusions_not_sign_proofs": True,
        "endpoint_strong_gain_quarter_s_terminal_r_block_positive": passed,
        "claim_boundary": (
            "Together with named adjoining source-current blocks, proves the "
            "active endpoint surplus positive on the central rectangle; not "
            "the exterior slabs, full GP3, or Erdos 1041."
        ),
        "pass": passed,
    }, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
