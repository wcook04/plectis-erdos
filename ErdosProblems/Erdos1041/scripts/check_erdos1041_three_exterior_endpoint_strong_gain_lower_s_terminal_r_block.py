#!/usr/bin/env python3
"""Exact replay for the terminal-r lower-s endpoint block."""

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
        ("low_w", ((0, 1), (1 / 2, 1), (3 / 8, 1 / 2), (1 / 4, 1 / 2))),
        ("high_w", ((0, 1), (1 / 2, 1), (3 / 8, 1 / 2), (1 / 2, 3 / 4))),
    )
    with ProcessPoolExecutor(
        max_workers=2, mp_context=multiprocessing.get_context("fork")
    ) as pool:
        observed = dict(pool.map(certify_item, domains))
    expected = {
        "low_w": {
            "coarse_total": 8192, "coarse_green": 783, "coarse_red": 7409,
            "refined_total": 118544, "refined_green": 118544, "inactive": 0,
            "refined_red": 0, "minimum_hex": "0x1.2cf6f6fe167ffp-14",
            "digest": "5160646aeca4c531fbdd3bfff5972f65392bdb25ea29984c6e9251d6b73af272",
        },
        "high_w": {
            "coarse_total": 8192, "coarse_green": 7792, "coarse_red": 400,
            "refined_total": 6400, "refined_green": 6400, "inactive": 0,
            "refined_red": 0, "minimum_hex": "0x1.d65dbebb75fffp-16",
            "digest": "8b65e67b6e80bbad670f62b121d0ae30761cdae28ee0348539c1367b1522cb7d",
        },
    }
    passed = observed == expected
    print(json.dumps({
        "schema": "erdos1041_three_exterior_endpoint_strong_gain_lower_s_terminal_r_block_v1",
        "certified_box": {
            "t": ["0", "1"], "r": ["1/2", "1"],
            "s": ["3/8", "1/2"], "w": ["1/4", "3/4"],
        },
        "composed_connected_box": {
            "t": ["0", "1"], "r": ["1/8", "1"],
            "s": ["3/8", "1/2"], "w": ["1/4", "3/4"],
        },
        "observed": observed,
        "expected": expected,
        "inactive_cells": sum(row["inactive"] for row in observed.values()),
        "unresolved_active_cells": sum(row["refined_red"] for row in observed.values()),
        "green_cells_are_strict_sign_proofs": passed,
        "inactive_cells_are_branch_exclusions_not_sign_proofs": True,
        "endpoint_strong_gain_lower_s_terminal_r_block_positive": passed,
        "claim_boundary": (
            "Together with the two named adjoining source-current blocks, "
            "this proves the active endpoint surplus positive on the composed "
            "connected box; not the outer-w faces, full GP3, or Erdos 1041."
        ),
        "pass": passed,
    }, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
