#!/usr/bin/env python3
"""Rigorous second dyadic stationary boundary slab."""

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


def main() -> int:
    engine = load_engine()
    I = engine.Interval
    ieee = all((sys.float_info.radix == 2, sys.float_info.mant_dig == 53,
                sys.float_info.max_exp == 1024, sys.float_info.rounds == 1,
                math.nextafter(1.0, float("inf")).hex() == "0x1.0000000000001p+0"))
    digest = hashlib.sha256()
    minimum = float("inf")
    red = []
    for it, ir, js, kw in itertools.product(range(32), range(16), range(16), range(8)):
        box = (I(it / 32, (it + 1) / 32),
               I(ir / 128, (ir + 1) / 128),
               I(1 / 4 + js / 128, 1 / 4 + (js + 1) / 128),
               I(15 / 16 + kw / 256, 15 / 16 + (kw + 1) / 256))
        lower = engine.stationary_surplus(box).lo
        minimum = min(minimum, lower)
        digest.update(struct.pack(">d", lower))
        if lower <= 0:
            red.append((it, ir, js, kw, lower.hex()))
    expected_digest = "53fa94acac96745932ed931da59eb5fa7146abbe13e11859f47ec5803c72577e"
    passed = all((ieee, not red,
                  minimum.hex() == "0x1.b2af126931e60p+3",
                  digest.hexdigest() == expected_digest))
    result = {
        "schema": "erdos1041_three_exterior_stationary_dyadic_boundary_slab_two_receipt_v1",
        "interval_engine_sha256": ENGINE_SHA256,
        "certified_box": {"t": ["0", "1"], "r": ["0", "1/8"],
                          "s": ["1/4", "3/8"], "w": ["15/16", "31/32"]},
        "cell_count": 32 * 16 * 16 * 8,
        "green_cells": 32 * 16 * 16 * 8 - len(red),
        "red_cells": len(red),
        "weakest_lower_bound_hex": minimum.hex(),
        "weakest_lower_bound_decimal": minimum,
        "accepted_lower_bound_sha256": digest.hexdigest(),
        "dyadic_boundary_slab_two_positive": passed,
        "claim_boundary": ("Proves S_stat>0 for all t, r in [0,1/8], s in "
                           "[1/4,3/8], and w in [15/16,31/32]. With adjoining "
                           "blocks this covers w in [1/4,31/32] on that r,s "
                           "strip. It does not include w=1, prove GP3, or "
                           "prove Erdos 1041."),
        "pass": passed,
    }
    print(json.dumps(result, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
