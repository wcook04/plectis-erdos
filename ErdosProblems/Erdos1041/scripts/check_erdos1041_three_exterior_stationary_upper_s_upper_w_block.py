#!/usr/bin/env python3
"""Rigorous upper-w blocks for stationary GP3 on s in [3/8,1/2]."""

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


def certify(engine, w0, wstep, wcount):
    I = engine.Interval
    digest = hashlib.sha256()
    minimum = float("inf")
    red = []
    for it, ir, js, kw in itertools.product(range(32), range(16), range(16), range(wcount)):
        box = (I(it / 32, (it + 1) / 32),
               I(ir / 128, (ir + 1) / 128),
               I(3 / 8 + js / 128, 3 / 8 + (js + 1) / 128),
               I(w0 + kw * wstep, w0 + (kw + 1) * wstep))
        lower = engine.stationary_surplus(box).lo
        minimum = min(minimum, lower)
        digest.update(struct.pack(">d", lower))
        if lower <= 0:
            red.append((it, ir, js, kw, lower.hex()))
    return {"total": 32 * 16 * 16 * wcount, "red": red,
            "minimum_hex": minimum.hex(), "minimum": minimum,
            "digest": digest.hexdigest()}


def main() -> int:
    engine = load_engine()
    ieee = all((sys.float_info.radix == 2, sys.float_info.mant_dig == 53,
                sys.float_info.max_exp == 1024, sys.float_info.rounds == 1,
                math.nextafter(1.0, float("inf")).hex() == "0x1.0000000000001p+0"))
    slabs = [
        certify(engine, 1 / 2, 1 / 64, 16),
        certify(engine, 3 / 4, 3 / 256, 16),
        certify(engine, 15 / 16, 1 / 256, 8),
    ]
    expected = [
        {"total": 131072, "minimum_hex": "0x1.c4e9892535f19p-3",
         "digest": "be2997d786a188cd080cc90bc31ad7225297b04c0651c7fffb1d9b796228b44b"},
        {"total": 131072, "minimum_hex": "0x1.d91a49a2b48bcp+0",
         "digest": "da247029b331ad2211f0d89d2af3dc167bdd8abca663eaae7796034475389fef"},
        {"total": 65536, "minimum_hex": "0x1.b29da30e4c7c5p+3",
         "digest": "bfd12f4150306d25cc2aba71f30e69924c72aecd09920c236fd7fe686da74bca"},
    ]
    observed = [{key: slab[key] for key in row} for slab, row in zip(slabs, expected)]
    passed = ieee and all(not slab["red"] for slab in slabs) and observed == expected
    result = {
        "schema": "erdos1041_three_exterior_stationary_upper_s_upper_w_block_receipt_v1",
        "interval_engine_sha256": ENGINE_SHA256,
        "certified_box": {"t": ["0", "1"], "r": ["0", "1/8"],
                          "s": ["3/8", "1/2"], "w": ["1/2", "31/32"]},
        "ieee_binary64_round_to_nearest_verified": ieee,
        "slabs": [
            {**row, "red": len(slab["red"]), "minimum": slab["minimum"]}
            for slab, row in zip(slabs, observed)
        ],
        "stationary_upper_s_upper_w_block_positive": passed,
        "claim_boundary": ("Proves S_stat>0 on r in [0,1/8], s in [3/8,1/2], "
                           "and w in [1/2,31/32]. With separately proved finite "
                           "and tail theorems this closes w in [1/4,1). It does "
                           "not prove GP3 or Erdos 1041."),
        "pass": passed,
    }
    print(json.dumps(result, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
