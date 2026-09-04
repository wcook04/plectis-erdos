#!/usr/bin/env python3
"""Four-process replay for the terminal r-to-one GP3 endpoint collar."""

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
    r_interval = (31 / 32, 1)
    domains = {
        "low_s_low_w": ((0, 1), r_interval, (1 / 2, 5 / 8), (1 / 4, 1 / 2)),
        "low_s_high_w": ((0, 1), r_interval, (1 / 2, 5 / 8), (1 / 2, 3 / 4)),
        "high_s_low_w": ((0, 1), r_interval, (5 / 8, 3 / 4), (1 / 4, 1 / 2)),
        "high_s_high_w": ((0, 1), r_interval, (5 / 8, 3 / 4), (1 / 2, 3 / 4)),
    }
    with ProcessPoolExecutor(
        max_workers=4, mp_context=multiprocessing.get_context("fork")
    ) as pool:
        observed = dict(pool.map(certify_item, domains.items()))
    expected = {
        "low_s_low_w": {
            "coarse_total": 8192, "coarse_green": 1360, "coarse_red": 6832,
            "refined_total": 109312, "refined_green": 89339, "inactive": 19973,
            "refined_red": 0, "minimum_hex": "0x1.ad0c036292fffp-15",
            "digest": "7253ff8963b5491c99f5e9ee46f8e588825b2b1d8380e2d689ea33e0ddd3556a",
        },
        "low_s_high_w": {
            "coarse_total": 8192, "coarse_green": 7932, "coarse_red": 260,
            "refined_total": 4160, "refined_green": 440, "inactive": 3720,
            "refined_red": 0, "minimum_hex": "0x1.1bc2a1d795bffp-14",
            "digest": "e1000e7e877c25d172720e8d4ee25bf90c2414643afdfcbd312cc5422a705b80",
        },
        "high_s_low_w": {
            "coarse_total": 8192, "coarse_green": 380, "coarse_red": 7812,
            "refined_total": 124992, "refined_green": 12633, "inactive": 112359,
            "refined_red": 0, "minimum_hex": "0x1.cab2e828defffp-14",
            "digest": "8d6b4b83541e794e4b076bee9c209e05a4cb3a2435a7d72765dd42de5d87f033",
        },
        "high_s_high_w": {
            "coarse_total": 8192, "coarse_green": 6511, "coarse_red": 1681,
            "refined_total": 26896, "refined_green": 0, "inactive": 26896,
            "refined_red": 0, "minimum_hex": "0x1.41b7d369d83ffp-13",
            "digest": "79619f06e8a744d1b3ad6d0529cfbab4e1e4eb645965b472ca80fe3a9adda6c2",
        },
    }
    passed = observed == expected
    print(json.dumps({
        "schema": "erdos1041_three_exterior_endpoint_strong_gain_terminal_isosceles_collar_v1",
        "certified_box": {
            "t": ["0", "1"], "r": ["31/32", "1"],
            "s": ["1/2", "3/4"], "w": ["1/4", "3/4"],
        },
        "observed": observed, "expected": expected,
        "green_cells_are_strict_sign_proofs": True,
        "inactive_cells_are_branch_exclusions_not_sign_proofs": True,
        "unresolved_active_cells": sum(
            row["refined_red"] for row in observed.values()
        ),
        "endpoint_strong_gain_terminal_isosceles_collar_positive": passed,
        "claim_boundary": (
            "Proves the true endpoint surplus positive wherever this endpoint "
            "branch is active on the stated terminal collar; inactive boxes "
            "are exclusions, not sign proofs. Does not prove GP3 or Erdos 1041."
        ),
        "pass": passed,
    }, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
