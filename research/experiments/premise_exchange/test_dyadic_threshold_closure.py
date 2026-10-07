#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Review contract for dyadic_threshold_closure.py.

Usage:
    python3 research/experiments/premise_exchange/test_dyadic_threshold_closure.py
    python3 -O research/experiments/premise_exchange/test_dyadic_threshold_closure.py

Uses only the standard library. Imports the specified reviewed module, but
intercepts its output write during the negative-control main() invocation.
It requires the exact finite identity: an earlier version that only tested
interval membership accepted the lower-endpoint mutation below.

These tests are exact finite arithmetic and program regressions, not a Lean
proof or an independent proof of Dubickas's theorem.
"""
from __future__ import annotations

import argparse
import contextlib
from fractions import Fraction
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import sys
from unittest.mock import patch


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def binary_value(digits: list[int]) -> Fraction:
    value = 0
    for digit in digits:
        value = 2 * value + digit
    return Fraction(value, 1 << len(digits))


def nearest_integer_distance(x: Fraction) -> Fraction:
    r = x - x.numerator // x.denominator
    return min(r, 1 - r)


def run_checks(source_path: Path) -> dict:
    source_path = source_path.resolve(strict=True)
    raw = source_path.read_bytes()
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location("reviewed_closure", source_path)
    if spec is None or spec.loader is None:
        raise RuntimeError("Cannot import the supplied source path")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)

    # A second construction: iterate the binary substitution rather than
    # calling the source's digit-popcount function.
    word = [0]
    while len(word) < 65536:
        word = word + [1 - digit for digit in word]
    require(module.thue_morse(len(word)) == word, "binary generators disagree")

    for m in range(13):
        length = 1 << m
        low, high = module.tau_enclosure(length)
        require(low == binary_value(word[:length]), "digit enclosure mismatch")
        require(high - low == Fraction(1, 1 << length), "enclosure width")
        require(module.product_form(m) == (low + high) / 2,
                f"finite midpoint identity at {m} factors")

    shifts = module.strict_shift_comparisons(1 << 15)
    require(shifts["shifts_checked"] == [1, 32767], "shift domain")
    require(shifts["prefix_bits"] == 65536, "prefix length")
    require(shifts["deepest_decision"] == 16384, "decision-depth regression")
    require(shifts["violations"] == 0, "strict suffix comparison")

    # Finite rational certificates for the subsequence used by the ordinary
    # convergence proof. The infinite proof is a separate mathematical object.
    for k in range(11):
        length = 1 << k
        low, high = module.tau_enclosure(4 * length)
        prefix, _ = module.tau_enclosure(length)
        a = int(prefix * (1 << length))
        r_low = (1 << length) * low - a
        r_high = (1 << length) * high - a
        require(Fraction(1, 2) < r_low < r_high < 1, "nearest-integer branch")
        gap_low = ((1 << length) + 1) * low - a - 1
        gap_high = ((1 << length) + 1) * high - a - 1
        require(0 < gap_low <= gap_high < Fraction(1, 1 << length),
                f"subsequence gap at index {length}")

    # Concrete witnesses for the hypothesis/quantifier mutation catalogue.
    require(nearest_integer_distance(Fraction(0)) >= 0,
            "zero threshold admits a rational zero orbit")
    x0, x1 = Fraction(1, 3), Fraction(2, 3)
    require(nearest_integer_distance(x1 - x0) == Fraction(1, 3),
            "h=1 alone admits a rational period-two orbit")
    x, p = Fraction(1000, 1001), Fraction(2001, 1000)
    require(2 <= p <= 30 and p * x - 1 == x
            and 0 < nearest_integer_distance(x) < Fraction(1, 31),
            "noninteger-radix witness")

    # Require stays enabled under Python -O.
    try:
        module.require(False, "intentional negative control")
    except AssertionError:
        pass
    else:
        raise AssertionError("require was disabled")

    # Changing the product to the digit lower bound stays within the old
    # tolerance interval but violates the exact finite identity.
    wrong_value = module.tau_enclosure(4096)[0]
    rejected = False
    with patch.object(module, "product_form", return_value=wrong_value), \
         patch.object(Path, "write_text", return_value=0), \
         contextlib.redirect_stdout(io.StringIO()):
        try:
            module.main()
        except AssertionError:
            rejected = True
    require(rejected, "main still accepts the finite-product identity mutation")

    return {
        "source_git_blob": hashlib.sha1(
            b"blob " + str(len(raw)).encode() + b"\0" + raw
        ).hexdigest(),
        "source_sha256": hashlib.sha256(raw).hexdigest(),
        "finite_product_cases": 13,
        "strict_shift_comparisons": shifts,
        "subsequence_enclosures": 11,
        "hypothesis_counterexample_checks": 3,
        "false_require_rejected": True,
        "lower_endpoint_product_mutation_rejected": True,
        "evidence_class": "exact finite arithmetic and Python regression tests",
        "lean_or_comparator_run": False,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, nargs="?",
                        default=Path(__file__).with_name("dyadic_threshold_closure.py"))
    args = parser.parse_args()
    result = run_checks(args.source)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
