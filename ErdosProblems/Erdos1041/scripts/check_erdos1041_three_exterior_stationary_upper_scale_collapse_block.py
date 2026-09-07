#!/usr/bin/env python3
"""Rigorous upper-scale block adjoining the stationary collapse atlas."""

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
    for it, ir, js, kw in itertools.product(range(32), range(16), range(16), range(16)):
        box = (I(it / 32, (it + 1) / 32),
               I(ir / 128, (ir + 1) / 128),
               I(1 / 4 + js / 128, 1 / 4 + (js + 1) / 128),
               I(1 / 2 + kw / 64, 1 / 2 + (kw + 1) / 64))
        lower = engine.stationary_surplus(box).lo
        minimum = min(minimum, lower)
        digest.update(struct.pack(">d", lower))
        if lower <= 0:
            red.append((it, ir, js, kw, lower.hex()))
    passed = all((ieee, not red,
                  minimum.hex() == "0x1.eced4c2b1f62ap-3",
                  digest.hexdigest() == "bf2a5d558c4e23b7983e1dea72a719b98a84b82b9f26efcdf70dc5ff7689a9a6"))
    result = {
        "schema": "erdos1041_three_exterior_stationary_upper_scale_collapse_block_receipt_v1",
        "interval_engine_sha256": ENGINE_SHA256,
        "certified_box": {"t": ["0", "1"], "r": ["0", "1/8"],
                          "s": ["1/4", "3/8"], "w": ["1/2", "3/4"]},
        "cell_count": 32 * 16**3,
        "green_cells": 32 * 16**3 - len(red),
        "red_cells": len(red),
        "weakest_lower_bound_hex": minimum.hex(),
        "weakest_lower_bound_decimal": minimum,
        "accepted_lower_bound_sha256": digest.hexdigest(),
        "upper_scale_collapse_block_positive": passed,
        "claim_boundary": ("Proves S_stat>0 for all t, r in [0,1/8], s in "
                           "[1/4,3/8], and w in [1/2,3/4]. With adjoining "
                           "blocks this covers w in [1/4,3/4] on that r,s "
                           "strip. It does not prove GP3 or Erdos 1041."),
        "pass": passed,
    }
    print(json.dumps(result, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
