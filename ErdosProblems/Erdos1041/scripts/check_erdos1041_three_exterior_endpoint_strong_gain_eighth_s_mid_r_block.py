#!/usr/bin/env python3
"""Exact replay for the middle-r eighth-s endpoint block."""

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
        ("low_w", ((0, 1), (1 / 4, 1 / 2), (1 / 8, 1 / 4), (1 / 4, 1 / 2)), True),
        ("high_w", ((0, 1), (1 / 4, 1 / 2), (1 / 8, 1 / 4), (1 / 2, 3 / 4)), False),
    )
    with ProcessPoolExecutor(
        max_workers=2, mp_context=multiprocessing.get_context("fork")
    ) as pool:
        observed = dict(pool.map(certify_item, domains))
    expected = {
        "low_w": {
            "coarse_total": 8192, "coarse_green": 5362, "coarse_red": 2830,
            "refined_total": 45280, "refined_green": 45280, "inactive": 0,
            "refined_red": 0, "minimum_hex": "0x1.c979048f77fffp-15",
            "digest": "2d2c2f4af43f6d4f475834ff4128a69111cbe0727adb6ad4c98407a6c1b16dd8",
        },
        "high_w": {
            "coarse_total": 8192, "coarse_green": 8192, "coarse_red": 0,
            "refined_total": 0, "refined_green": 0, "inactive": 0,
            "refined_red": 0, "minimum_hex": "0x1.8a43630bd80ccp-3",
            "digest": "4a5678ecb183ff4830043539db266ea10a8271064f8648fcd47fff6cd8f6144c",
        },
    }
    passed = observed == expected
    print(json.dumps({
        "schema": "erdos1041_three_exterior_endpoint_strong_gain_eighth_s_mid_r_block_v1",
        "certified_box": {
            "t": ["0", "1"], "r": ["1/4", "1/2"],
            "s": ["1/8", "1/4"], "w": ["1/4", "3/4"],
        },
        "observed": observed,
        "expected": expected,
        "inactive_cells": sum(row["inactive"] for row in observed.values()),
        "unresolved_active_cells": sum(row["refined_red"] for row in observed.values()),
        "green_cells_are_strict_sign_proofs": passed,
        "inactive_cells_are_branch_exclusions_not_sign_proofs": True,
        "endpoint_strong_gain_eighth_s_mid_r_block_positive": passed,
        "claim_boundary": (
            "Proves the true endpoint surplus positive on the stated active "
            "block; not the terminal-r eighth-s slab, full GP3, or Erdos 1041."
        ),
        "pass": passed,
    }, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
