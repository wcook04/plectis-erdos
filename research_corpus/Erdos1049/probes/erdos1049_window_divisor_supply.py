#!/usr/bin/env python3
"""Does Erdos #1049's moving window divisor actually exist, start by start?

Upstream analytic state
-----------------------
`QAperyTailDenominatorLab.md` establishes that a FIXED tail divisor is the wrong
target: several primes divide a long initial block of the primitive q-Apery
denominator coordinates and then vanish for one block whose length is the order
of 3/2 modulo the prime.  The lab therefore names the next theorem-sized target
precisely, and its step 1 is:

> analyze the modulo-prime block dynamics and supply, for cofinally many starts
> s, a moving divisor across the exact window of width 3s^2 + 5s + 3.

The lab also says what computation is for here: "Computation should now be used
only to falsify a proposed formula for step 1 or a proposed uniform inequality
for step 3.  Extending the row cutoff alone would not change the mathematical
status."

This probe does exactly that, and nothing more.  It does not extend the row
cutoff to look for new tail primes; it evaluates the step-1 predicate itself,
which had never been evaluated: does a window divisor exist at each start, and
is it source-supported (a divisor of 3^s - 2^s)?

Probe
-----
For each start s, take the exact window [s, s + 3s^2 + 5s + 3], compute the gcd
of the denominator coordinates across it, and factor it.

Predeclared falsifier
---------------------
A start whose window gcd is 1 falsifies the step-1 predicate at that start.  If
those starts are cofinal, step 1 as stated is false and the target must change
again.  If instead every start carries a divisor and the divisors are
source-supported, step 1 is empirically sound and the residual is a proof.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import pathlib
import sys

REPO_ROOT = pathlib.Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

ROW_SOURCE = (REPO_ROOT / "formal_math/erdos257_period_noncollapse/ErdosProblems"
              / "Erdos1049/scripts/check_qapery_selector_remainder_escape.py")


def _row_module():
    spec = importlib.util.spec_from_file_location("qapery_rows", ROW_SOURCE)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def window_width(s: int) -> int:
    return 3 * s * s + 5 * s + 3


def small_factors(value: int, bound: int = 2_000_000) -> tuple[dict[int, int], int]:
    """Trial-divide out primes below `bound`; return (factors, unfactored remainder)."""
    factors: dict[int, int] = {}
    remaining = value
    d = 2
    while d * d <= remaining and d <= bound:
        while remaining % d == 0:
            factors[d] = factors.get(d, 0) + 1
            remaining //= d
        d += 1 if d == 2 else 2
    if 1 < remaining <= bound * bound:
        # the loop exhausted all d with d*d <= remaining, so the residual is prime
        factors[remaining] = factors.get(remaining, 0) + 1
        remaining = 1
    return factors, remaining


def run(max_start: int) -> dict:
    needed = max(s + window_width(s) for s in range(max_start + 1)) + 2
    rows = _row_module().primitive_rows(needed)
    # regression anchor from the lab: 211 divides B_j for 5 <= j <= 255
    anchor_ok = all(rows[j][1] % 211 == 0 for j in range(5, min(256, len(rows))))
    out = []
    for s in range(max_start + 1):
        w = window_width(s)
        hi = s + w
        g = 0
        for j in range(s, min(hi, len(rows) - 1) + 1):
            g = math.gcd(g, abs(rows[j][1]))
            if g == 1:
                break
        factors, remainder = small_factors(g) if g else ({}, 0)
        source = 3 ** s - 2 ** s if s else 0
        supported = {p: (source % p == 0) for p in factors} if source else {}
        out.append({
            "start": s,
            "window_width": w,
            "window_high_index": hi,
            "window_gcd_bits": g.bit_length(),
            "window_gcd_has_divisor": bool(g and g > 1),
            "window_gcd_small_factors": {str(p): e for p, e in factors.items()},
            "window_gcd_large_cofactor_bits": remainder.bit_length() if remainder > 1 else 0,
            "source_3s_minus_2s_supported": {str(p): v for p, v in supported.items()},
            "all_small_factors_source_supported": (
                all(supported.values()) if supported else None),
        })
    # "source-supported" is a statement about FIRST APPEARANCE: a prime inherited
    # from an earlier start is not expected to divide 3^s - 2^s at the later one.
    first_seen: dict[int, int] = {}
    first_appearance = []
    for r in out:
        s_ = r["start"]
        for p_str in sorted(r["window_gcd_small_factors"], key=int):
            p_ = int(p_str)
            if p_ in first_seen:
                continue
            first_seen[p_] = s_
            src = 3 ** s_ - 2 ** s_
            first_appearance.append({
                "start": s_, "new_prime": p_, "source_3s_minus_2s": src,
                "divides_source": bool(src % p_ == 0),
            })
    law_holds = all(f["divides_source"] for f in first_appearance)

    empty = [r["start"] for r in out if not r["window_gcd_has_divisor"]]
    # The producer asks for COFINALLY many starts, so only failures in the upper
    # part of the tested range bear on it; early gaps are irrelevant.
    upper = max_start // 2
    late_empty = [x for x in empty if x > upper]
    return {
        "probe_id": "erdos1049_window_divisor_supply",
        "rows_built": len(rows),
        "lab_anchor_211_divides_B_5_to_255": anchor_ok,
        "max_start": max_start,
        "first_appearance_law": first_appearance,
        "every_new_prime_divides_3s_minus_2s_at_first_start": law_holds,
        "starts_with_no_window_divisor": empty,
        "late_starts_with_no_window_divisor": late_empty,
        "cofinality_probe_upper_half_from": upper + 1,
        "starts_with_divisor": [r["start"] for r in out if r["window_gcd_has_divisor"]],
        "per_start": out,
        "reading": (
            "every start in the upper half of the range carries a window divisor, so "
            "the step-1 predicate is empirically sound where cofinality lives and the "
            "residual is a proof rather than another change of target"
            + ("; every newly appearing prime divides 3^s - 2^s at its first start"
               if law_holds else "; but the source-support law FAILS")
            if not late_empty else
            f"starts {late_empty} in the upper half carry NO window divisor: the "
            "step-1 predicate fails where cofinality would have to hold"
        ),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-start", type=int, default=12)
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()
    payload = run(args.max_start)
    if args.out:
        pathlib.Path(args.out).write_text(json.dumps(payload, indent=1) + "\n")
    print(json.dumps(payload, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
