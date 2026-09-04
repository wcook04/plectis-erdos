#!/usr/bin/env python3
"""Rigorous stationary GP3 block on s in [3/8,1/2], w in [1/4,1/2]."""

from __future__ import annotations

import hashlib
import importlib.util
import itertools
import json
import math
from pathlib import Path
import struct
import sys

ENGINE_PATH = Path(__file__).with_name("check_erdos1041_three_exterior_stationary_compact_interior_block.py")
ENGINE_SHA256 = "feeb112bfd6134947389b8998f7ed784dff5a5bf24f5d262290fa156bec8fc1f"


def load_engine():
    source = ENGINE_PATH.read_bytes()
    assert hashlib.sha256(source).hexdigest() == ENGINE_SHA256
    spec = importlib.util.spec_from_file_location("gp3_interval_engine", ENGINE_PATH)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def low_w_block(engine):
    I = engine.Interval
    digest = hashlib.sha256()
    minimum = float("inf")
    coarse_green = 0
    red = []
    for it, ir, js, kw in itertools.product(range(32), range(16), range(16), range(16)):
        box = (I(it / 32, (it + 1) / 32),
               I(ir / 128, (ir + 1) / 128),
               I(3 / 8 + js / 128, 3 / 8 + (js + 1) / 128),
               I(1 / 4 + kw / 128, 1 / 4 + (kw + 1) / 128))
        lower = engine.stationary_surplus(box).lo
        if lower > 0:
            coarse_green += 1
            minimum = min(minimum, lower)
            digest.update(struct.pack(">d", lower))
        else:
            red.append((it, ir, js, kw))
    refined_green = 0
    refined_red = []
    for it, ir, js, kw in red:
        for at, ar, ass, aw in itertools.product(range(2), repeat=4):
            box = (I(it / 32 + at / 64, it / 32 + (at + 1) / 64),
                   I(ir / 128 + ar / 256, ir / 128 + (ar + 1) / 256),
                   I(3 / 8 + js / 128 + ass / 256,
                     3 / 8 + js / 128 + (ass + 1) / 256),
                   I(1 / 4 + kw / 128 + aw / 256,
                     1 / 4 + kw / 128 + (aw + 1) / 256))
            lower = engine.stationary_surplus(box).lo
            if lower > 0:
                refined_green += 1
                minimum = min(minimum, lower)
                digest.update(struct.pack(">d", lower))
            else:
                refined_red.append((it, ir, js, kw, at, ar, ass, aw, lower.hex()))
    return {
        "coarse_total": 32 * 16**3,
        "coarse_green": coarse_green,
        "coarse_red": len(red),
        "refined_total": 16 * len(red),
        "refined_green": refined_green,
        "refined_red": refined_red,
        "minimum_hex": minimum.hex(),
        "minimum": minimum,
        "digest": digest.hexdigest(),
    }


def mid_w_block(engine):
    I = engine.Interval
    digest = hashlib.sha256()
    minimum = float("inf")
    red = []
    for it, ir, js, kw in itertools.product(range(32), range(16), range(16), range(16)):
        box = (I(it / 32, (it + 1) / 32),
               I(ir / 128, (ir + 1) / 128),
               I(3 / 8 + js / 128, 3 / 8 + (js + 1) / 128),
               I(3 / 8 + kw / 128, 3 / 8 + (kw + 1) / 128))
        lower = engine.stationary_surplus(box).lo
        minimum = min(minimum, lower)
        digest.update(struct.pack(">d", lower))
        if lower <= 0:
            red.append((it, ir, js, kw, lower.hex()))
    return {"total": 32 * 16**3, "red": red, "minimum_hex": minimum.hex(),
            "minimum": minimum, "digest": digest.hexdigest()}


def main() -> int:
    engine = load_engine()
    ieee = all((sys.float_info.radix == 2, sys.float_info.mant_dig == 53,
                sys.float_info.max_exp == 1024, sys.float_info.rounds == 1,
                math.nextafter(1.0, float("inf")).hex() == "0x1.0000000000001p+0"))
    low = low_w_block(engine)
    mid = mid_w_block(engine)
    low_expected = {
        "coarse_total": 131072, "coarse_green": 107143, "coarse_red": 23929,
        "refined_total": 382864, "refined_green": 382864,
        "minimum_hex": "0x1.50a67975affffp-21",
        "digest": "d0553d434a6048b79f2743119f0327c747d486bfccc9a038d5447043ac3b74d7",
    }
    low_observed = {key: low[key] for key in low_expected}
    mid_expected = {
        "total": 131072, "minimum_hex": "0x1.ef04a1b7b7360p-5",
        "digest": "35597198cc68a1f049b0d7d183cbe15256bdfeb58325a6c8a0998f1e44286e8f",
    }
    mid_observed = {key: mid[key] for key in mid_expected}
    passed = all((ieee, not low["refined_red"], not mid["red"],
                  low_observed == low_expected, mid_observed == mid_expected))
    result = {
        "schema": "erdos1041_three_exterior_stationary_upper_s_finite_block_receipt_v1",
        "interval_engine_sha256": ENGINE_SHA256,
        "certified_box": {"t": ["0", "1"], "r": ["0", "1/8"],
                          "s": ["3/8", "1/2"], "w": ["1/4", "1/2"]},
        "ieee_binary64_round_to_nearest_verified": ieee,
        "low_w": {**low_observed, "refined_red": len(low["refined_red"])},
        "mid_w": {**mid_observed, "red": len(mid["red"])},
        "weakest_lower_bound_decimal": low["minimum"],
        "stationary_upper_s_finite_block_positive": passed,
        "claim_boundary": ("Proves S_stat>0 on r in [0,1/8], s in [3/8,1/2], "
                           "and w in [1/4,1/2]. It does not cover "
                           "w in (1/2,31/32), prove GP3, or prove Erdos 1041."),
        "pass": passed,
    }
    print(json.dumps(result, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
