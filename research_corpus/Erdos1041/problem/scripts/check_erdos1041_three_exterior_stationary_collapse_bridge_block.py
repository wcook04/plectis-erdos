#!/usr/bin/env python3
"""Rigorous positive-width bridge from r=0 into the GP3 stationary interior."""

from __future__ import annotations

import hashlib
import importlib.util
import itertools
import json
import math
from pathlib import Path
import struct
import sys


ENGINE_PATH = Path(__file__).with_name(
    "check_erdos1041_three_exterior_stationary_compact_interior_block.py"
)
ENGINE_SHA256 = "feeb112bfd6134947389b8998f7ed784dff5a5bf24f5d262290fa156bec8fc1f"


def load_engine():
    source = ENGINE_PATH.read_bytes()
    assert hashlib.sha256(source).hexdigest() == ENGINE_SHA256
    spec = importlib.util.spec_from_file_location("gp3_interval_engine", ENGINE_PATH)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def coarse_box(engine, it, ir, js, kw):
    I = engine.Interval
    return (
        I(it / 32, (it + 1) / 32),
        I(ir / 128, (ir + 1) / 128),
        I(1 / 4 + js / 128, 1 / 4 + (js + 1) / 128),
        I(1 / 4 + kw / 128, 1 / 4 + (kw + 1) / 128),
    )


def refined_box(engine, it, ir, js, kw, at, ar, ass, aw):
    I = engine.Interval
    return (
        I(it / 32 + at / 64, it / 32 + (at + 1) / 64),
        I(ir / 128 + ar / 256, ir / 128 + (ar + 1) / 256),
        I(1 / 4 + js / 128 + ass / 256, 1 / 4 + js / 128 + (ass + 1) / 256),
        I(1 / 4 + kw / 128 + aw / 256, 1 / 4 + kw / 128 + (aw + 1) / 256),
    )


def main() -> int:
    engine = load_engine()
    ieee_binary64 = all(
        (
            sys.float_info.radix == 2,
            sys.float_info.mant_dig == 53,
            sys.float_info.max_exp == 1024,
            sys.float_info.rounds == 1,
            math.nextafter(1.0, float("inf")).hex() == "0x1.0000000000001p+0",
        )
    )

    red = []
    coarse_green = 0
    minimum = float("inf")
    digest = hashlib.sha256()
    for it, ir, js, kw in itertools.product(range(32), range(16), range(16), range(16)):
        lower = engine.stationary_surplus(
            coarse_box(engine, it, ir, js, kw)
        ).lo
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
            lower = engine.stationary_surplus(
                refined_box(engine, it, ir, js, kw, at, ar, ass, aw)
            ).lo
            if lower > 0:
                refined_green += 1
                minimum = min(minimum, lower)
                digest.update(struct.pack(">d", lower))
            else:
                refined_red.append((it, ir, js, kw, at, ar, ass, aw, lower.hex()))

    expected = {
        "coarse_total": 131072,
        "coarse_green": 119630,
        "coarse_red": 11442,
        "refined_total": 183072,
        "refined_green": 183072,
        "minimum_hex": "0x1.807c2d7f4ffffp-21",
        "digest": "4bae2574c0764401c8cbdb13f8b77505f9ee8fb9a27ff32bb75ab728d832995c",
    }
    observed = {
        "coarse_total": 32 * 16**3,
        "coarse_green": coarse_green,
        "coarse_red": len(red),
        "refined_total": 16 * len(red),
        "refined_green": refined_green,
        "minimum_hex": minimum.hex(),
        "digest": digest.hexdigest(),
    }
    passed = ieee_binary64 and not refined_red and observed == expected
    result = {
        "schema": "erdos1041_three_exterior_stationary_collapse_bridge_block_receipt_v1",
        "interval_engine_sha256": ENGINE_SHA256,
        "ordered_chart": "u=r*s*w, v=s*w",
        "certified_box": {
            "t": ["0", "1"],
            "r": ["0", "1/8"],
            "s": ["1/4", "3/8"],
            "w": ["1/4", "3/8"],
        },
        "ieee_binary64_round_to_nearest_verified": ieee_binary64,
        "coarse_total": observed["coarse_total"],
        "coarse_green": coarse_green,
        "coarse_dependency_red": len(red),
        "refined_total": observed["refined_total"],
        "refined_green": refined_green,
        "refined_red": len(refined_red),
        "weakest_lower_bound_hex": minimum.hex(),
        "weakest_lower_bound_decimal": minimum,
        "accepted_lower_bound_sha256": digest.hexdigest(),
        "collapse_bridge_stationary_block_positive": passed,
        "claim_boundary": (
            "Proves S_stat>0 for all t in [0,1], r in [0,1/8], and s,w "
            "in [1/4,3/8]. With the two adjoining blocks this gives a full "
            "positive-width bridge r in [0,3/8] on that scale slab. It does "
            "not prove the rest of the ordered cone, GP3, or Erdos 1041."
        ),
        "pass": passed,
    }
    print(json.dumps(result, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
