#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact finite probes for the dyadic tail-difference threshold.

Run with Python's standard library only:
    python3 research/experiments/premise_exchange/dyadic_threshold_probe.py

The checked composition proves that an irrational dyadic tail has every
positive-length difference at distance at least 1/3 from the integers at
arbitrarily late indices.  For a shift h the fractional part of the
difference at index N is the fractional part of 2**N * (2**h - 1) * T_0, so
at h = 1 the question is about the doubling orbit of an arbitrary irrational
number.  This script records three finite facts about that orbit.

1. The rational orbit alternating 1/(B+1) and B/(B+1) under radix B and
   digits 0, B-1 stays exactly 1/(B+1) from the integers, for B = 2..30.
   It cross-checks the Lean theorem boundedRadix_threshold_attained.  The
   orbit is rational, so it bounds nothing for irrational tails.
2. The Thue-Morse number 0.0110100110010110..._2 is irrational.  In exact
   arithmetic on a finite prefix, its doubling orbit returns in every dyadic
   block of indices to distance about 0.41245 from the integers and, on the
   indices examined, never exceeds that distance.
3. For each threshold c, the number of binary words of length L all of whose
   suffixes are compatible with distance at most c from the integers.  At
   length 20 the count rises from 40 at c = 0.34 to 382 at 0.40 and 13,840
   at 0.42.  Words this short do not locate a threshold.

None of this is a proof about infinite orbits.  It selects a question: is
the best cofinal constant for irrational tails the Thue-Morse constant
rather than 1/3?  Results on the limit points of the fractional parts of
xi * b**n, where the Thue-Morse sequence is known to occur, must be read
before any proof attempt.
"""

from __future__ import annotations

from fractions import Fraction
import json
from pathlib import Path


def require(condition: bool, message: str) -> None:
    """Keep verification enabled even when Python is run with -O."""
    if not condition:
        raise AssertionError(message)


def dist(x: Fraction) -> Fraction:
    """Exact distance from a rational to the nearest integer."""
    frac = x - (x.numerator // x.denominator)
    return min(frac, 1 - frac)


def extremal_rational_orbits(max_radix: int = 30, steps: int = 12) -> list[dict]:
    rows = []
    for radix in range(2, max_radix + 1):
        x = Fraction(1, radix + 1)
        states = []
        for n in range(steps):
            digit = 0 if n % 2 == 0 else radix - 1
            require(x.denominator != 1, f"B={radix}: integral state at {n}")
            require(dist(x) == Fraction(1, radix + 1),
                    f"B={radix}: distance {dist(x)} at {n}")
            states.append(str(x))
            x = radix * x - digit
        require(x == Fraction(1, radix + 1), f"B={radix}: orbit is not 2-periodic")
        rows.append({"radix": radix, "threshold": f"1/{radix + 1}",
                     "states": states[:2], "steps_checked": steps})
    return rows


def thue_morse(length: int) -> list[int]:
    return [bin(i).count("1") % 2 for i in range(length)]


def thue_morse_orbit(max_index: int = 4096, window: int = 96) -> dict:
    """Exact bounds for dist(2**n * tau) with the tail beyond the window bounded."""
    digits = thue_morse(max_index + window)
    blocks = []
    overall_upper = Fraction(0)
    start = 16
    while start < max_index:
        stop = min(2 * start, max_index)
        best_lower = Fraction(0)
        for n in range(start, stop):
            numerator = 0
            for bit in digits[n:n + window]:
                numerator = 2 * numerator + bit
            low = Fraction(numerator, 2 ** window)
            high = low + Fraction(1, 2 ** window)
            # dist is 1-Lipschitz, so the orbit point's distance lies in
            # [min dist - 2^-window, max dist + 2^-window].
            lower = min(dist(low), dist(high)) - Fraction(1, 2 ** window)
            upper = max(dist(low), dist(high)) + Fraction(1, 2 ** window)
            best_lower = max(best_lower, lower)
            overall_upper = max(overall_upper, upper)
        blocks.append({"indices": [start, stop - 1],
                       "max_distance_lower_bound": float(best_lower)})
        start = stop
    return {
        "number": "sum_k t_k 2^-(k+1), t the Thue-Morse sequence 0110...",
        "indices_examined": [16, max_index - 1],
        "window_bits": window,
        "per_dyadic_block": blocks,
        "max_distance_upper_bound_over_indices": float(overall_upper),
    }


def admissible_word_counts(threshold: Fraction, max_length: int) -> list[int]:
    """Count words whose every suffix interval meets [0,c] or [1-c,1]."""
    p, q = threshold.numerator, threshold.denominator
    layer: list[tuple[int, ...]] = [()]
    suffixes: list[list[int]] = [[]]
    counts = []
    for length in range(1, max_length + 1):
        new_layer, new_suffixes = [], []
        for word, values in zip(layer, suffixes):
            for bit in (0, 1):
                grown = [2 * v + bit for v in values] + [bit]
                ok = True
                for offset, v in enumerate(grown):
                    scale = 1 << (length - offset)
                    if v * q > p * scale and (v + 1) * q < (q - p) * scale:
                        ok = False
                        break
                if ok:
                    new_layer.append(word + (bit,))
                    new_suffixes.append(grown)
        layer, suffixes = new_layer, new_suffixes
        counts.append(len(layer))
    return counts


def main() -> None:
    rational = extremal_rational_orbits()
    orbit = thue_morse_orbit()
    tail_blocks = [b["max_distance_lower_bound"] for b in orbit["per_dyadic_block"]]
    require(all(0.41245 < value for value in tail_blocks),
            "Thue-Morse orbit does not return near 0.41245 in every block")
    require(orbit["max_distance_upper_bound_over_indices"] < 0.412455,
            "Thue-Morse orbit exceeded 0.412455 on the examined indices")
    thresholds = ["34/100", "40/100", "41/100", "4124/10000", "4125/10000",
                  "413/1000", "42/100"]
    max_length = 20
    counts = {c: admissible_word_counts(Fraction(c), max_length) for c in thresholds}
    result = {
        "evidence": "exact rational arithmetic on finite orbits, prefixes and words",
        "boundary": (
            "Finite computations only. They prove no statement about infinite "
            "orbits and assert no optimal constant for irrational tails."
        ),
        "extremal_rational_orbits": rational,
        "thue_morse_orbit": orbit,
        "admissible_word_counts": {
            "word_length_range": [1, max_length],
            "counts_at_lengths_15_to_20": {c: v[14:] for c, v in counts.items()},
        },
        "selected_question": (
            "Is the best cofinal separation constant for irrational dyadic "
            "tails the Thue-Morse constant 0.41245... rather than 1/3?"
        ),
        "next_check": (
            "Read the literature on large limit points of the fractional parts "
            "of xi * b**n, where Thue-Morse bounds are known to occur, before "
            "any proof attempt."
        ),
    }
    out = Path(__file__).with_name("results") / "dyadic_threshold_probe.json"
    out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"written": str(out.name),
                      "thue_morse_block_lower_bounds": tail_blocks,
                      "counts_at_length_20": {c: v[-1] for c, v in counts.items()}},
                     indent=2))


if __name__ == "__main__":
    main()
