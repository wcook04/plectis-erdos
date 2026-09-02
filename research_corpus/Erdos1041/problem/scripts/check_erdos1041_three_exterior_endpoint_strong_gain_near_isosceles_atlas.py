#!/usr/bin/env python3
"""Eight-slab centered replay for the near-isosceles GP3 endpoint atlas."""

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
    domains = {}
    for r_name, r_interval in (
        ("r_3_4_7_8", (3 / 4, 7 / 8)),
        ("r_7_8_15_16", (7 / 8, 15 / 16)),
    ):
        domains.update({
            f"{r_name}_low_s_low_w": ((0, 1), r_interval, (1 / 2, 5 / 8), (1 / 4, 1 / 2)),
            f"{r_name}_low_s_high_w": ((0, 1), r_interval, (1 / 2, 5 / 8), (1 / 2, 3 / 4)),
            f"{r_name}_high_s_low_w": ((0, 1), r_interval, (5 / 8, 3 / 4), (1 / 4, 1 / 2)),
            f"{r_name}_high_s_high_w": ((0, 1), r_interval, (5 / 8, 3 / 4), (1 / 2, 3 / 4)),
        })

    # Slabs are mathematically disjoint, so four isolated processes replay them
    # without changing any interval operation or digest order inside a slab.
    with ProcessPoolExecutor(
        max_workers=4, mp_context=multiprocessing.get_context("fork")
    ) as pool:
        observed = dict(pool.map(certify_item, domains.items()))
    expected = {
        "r_3_4_7_8_low_s_low_w": {
            "coarse_total": 8192, "coarse_green": 1529, "coarse_red": 6663,
            "refined_total": 106608, "refined_green": 105454, "inactive": 1154,
            "refined_red": 0, "minimum_hex": "0x1.5b98310de7fffp-16",
            "digest": "202643a320bb7b23eddab44d627306476c965880fc319657e9e31d90c32a85aa",
        },
        "r_3_4_7_8_low_s_high_w": {
            "coarse_total": 8192, "coarse_green": 8067, "coarse_red": 125,
            "refined_total": 2000, "refined_green": 1395, "inactive": 605,
            "refined_red": 0, "minimum_hex": "0x1.eba3675b457ffp-12",
            "digest": "2f96e1d3aed8a540a5e746cace712cb05adc61f523a84f4b05470f54ed0d8953",
        },
        "r_3_4_7_8_high_s_low_w": {
            "coarse_total": 8192, "coarse_green": 653, "coarse_red": 7539,
            "refined_total": 120624, "refined_green": 53195, "inactive": 67429,
            "refined_red": 0, "minimum_hex": "0x1.27b1eaeafbfffp-17",
            "digest": "4fc7e4c2090ab8eefe7373196797dc0a18ec73c84c73d79a051b9597a4e7f6eb",
        },
        "r_3_4_7_8_high_s_high_w": {
            "coarse_total": 8192, "coarse_green": 7127, "coarse_red": 1065,
            "refined_total": 17040, "refined_green": 78, "inactive": 16962,
            "refined_red": 0, "minimum_hex": "0x1.04822a2cdffffp-17",
            "digest": "53ce24f472e920834fc9466d06240716ee8d32655ba72c669a0ba962145fc118",
        },
        "r_7_8_15_16_low_s_low_w": {
            "coarse_total": 8192, "coarse_green": 1483, "coarse_red": 6709,
            "refined_total": 107344, "refined_green": 99057, "inactive": 8287,
            "refined_red": 0, "minimum_hex": "0x1.40699d4947fffp-16",
            "digest": "df370fa05ad11dbad9735725a1afb4de6c56a91fe49f2b6a9a9681e5f8f37305",
        },
        "r_7_8_15_16_low_s_high_w": {
            "coarse_total": 8192, "coarse_green": 8032, "coarse_red": 160,
            "refined_total": 2560, "refined_green": 660, "inactive": 1900,
            "refined_red": 0, "minimum_hex": "0x1.36bc7f61a8fffp-14",
            "digest": "c7ed4525446ac45600abd95d3a412b30c76d56ccc840c241bf1956583e2f4401",
        },
        "r_7_8_15_16_high_s_low_w": {
            "coarse_total": 8192, "coarse_green": 536, "coarse_red": 7656,
            "refined_total": 122496, "refined_green": 25939, "inactive": 96557,
            "refined_red": 0, "minimum_hex": "0x1.90b4f2545dfffp-13",
            "digest": "a6d61a09d6ba66d04808a7541c4b08470efdd5bb9956cfc13a77a6687a041c8b",
        },
        "r_7_8_15_16_high_s_high_w": {
            "coarse_total": 8192, "coarse_green": 6854, "coarse_red": 1338,
            "refined_total": 21408, "refined_green": 0, "inactive": 21408,
            "refined_red": 0, "minimum_hex": "0x1.7d1dd829597ffp-14",
            "digest": "25e3ded497b3996d5a6ddb9a639d7b991f109e1663ba2220103d04527776c68d",
        },
    }
    passed = observed == expected
    print(json.dumps({
        "schema": "erdos1041_three_exterior_endpoint_strong_gain_near_isosceles_atlas_v1",
        "certified_box": {
            "t": ["0", "1"], "r": ["3/4", "15/16"],
            "s": ["1/2", "3/4"], "w": ["1/4", "3/4"],
        },
        "observed": observed, "expected": expected,
        "endpoint_strong_gain_near_isosceles_atlas_positive": passed,
        "claim_boundary": (
            "Proves the true endpoint surplus positive wherever this endpoint "
            "branch is active on the stated rectangle; not the open collar to "
            "r=1, GP3, or Erdos 1041."
        ),
        "pass": passed,
    }, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
