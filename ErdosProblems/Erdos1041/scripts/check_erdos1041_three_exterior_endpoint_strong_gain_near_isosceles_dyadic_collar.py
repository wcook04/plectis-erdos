#!/usr/bin/env python3
"""Four-process exact replay for the near-isosceles dyadic endpoint collar."""

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
    r_interval = (15 / 16, 31 / 32)
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
            "coarse_total": 8192, "coarse_green": 1462, "coarse_red": 6730,
            "refined_total": 107680, "refined_green": 92812, "inactive": 14868,
            "refined_red": 0, "minimum_hex": "0x1.08db88afc4bffp-14",
            "digest": "d8bb44dda24b20dbe588f8872441eb850c991e15ed72d7079cf5a6bab925b090",
        },
        "low_s_high_w": {
            "coarse_total": 8192, "coarse_green": 8006, "coarse_red": 186,
            "refined_total": 2976, "refined_green": 399, "inactive": 2577,
            "refined_red": 0, "minimum_hex": "0x1.786f586c3b9ffp-13",
            "digest": "9cd097d913ba5a070299b17e0dd34a6035286ea65b75de20caaf5f74794176e2",
        },
        "high_s_low_w": {
            "coarse_total": 8192, "coarse_green": 486, "coarse_red": 7706,
            "refined_total": 123296, "refined_green": 16699, "inactive": 106597,
            "refined_red": 0, "minimum_hex": "0x1.1d92a32c7ffffp-22",
            "digest": "6d295b254e61fc6e446996713d95cf7f1bab68d88b52297bae2601d8f81a55b4",
        },
        "high_s_high_w": {
            "coarse_total": 8192, "coarse_green": 6719, "coarse_red": 1473,
            "refined_total": 23568, "refined_green": 0, "inactive": 23568,
            "refined_red": 0, "minimum_hex": "0x1.f5352abed9fffp-14",
            "digest": "e31588b54fd8b9511649451307876e3e54c7462338d693c3ecd181e8357366fa",
        },
    }
    passed = observed == expected
    print(json.dumps({
        "schema": "erdos1041_three_exterior_endpoint_strong_gain_near_isosceles_dyadic_collar_v1",
        "certified_box": {
            "t": ["0", "1"], "r": ["15/16", "31/32"],
            "s": ["1/2", "3/4"], "w": ["1/4", "3/4"],
        },
        "observed": observed, "expected": expected,
        "endpoint_strong_gain_near_isosceles_dyadic_collar_positive": passed,
        "claim_boundary": (
            "Proves the true endpoint surplus positive wherever this endpoint "
            "branch is active on the stated collar; not the collar to r=1, "
            "GP3, or Erdos 1041."
        ),
        "pass": passed,
    }, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
