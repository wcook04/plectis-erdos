#!/usr/bin/env python3
"""Fast, verified construction of the Erdos #269 {2,3,5} dyadic block data.

The exact engine compares literal powers, so building blocks up to index a costs
O(a^3) bit operations and stalls well before the depths the Diophantine probes
need.  Every comparison it makes is really the Beatty inequality

    j*log_2 3 + k*log_2 5  <  e

so the same data can be built from 2-D lattice-point counts under a line.  This
module does that with vectorised counting, and keeps a guard band: any pair
whose Beatty value lands within `GUARD` of an integer boundary is re-decided by
an exact big-integer comparison, so no float ever settles a close call.

`build_dyadic_blocks_fast` returns exactly what the exact engine returns and is
checked against it by `verify_against_exact`.
"""

from __future__ import annotations

import sys
from decimal import Decimal, getcontext
from pathlib import Path

import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

PRIMES = (2, 3, 5)
OTHERS = {2: (3, 5), 3: (2, 5), 5: (2, 3)}
GUARD = 1e-7          # float margin below which an exact comparison is used


def _logs() -> dict[int, float]:
    getcontext().prec = 60
    l2 = Decimal(2).ln()
    return {p: float(Decimal(p).ln() / l2) for p in PRIMES}


LOG2 = _logs()


def _exact_lt(p1: int, i: int, p2: int, j: int, base: int, e: int) -> bool:
    """Exact decision of p1^i * p2^j < base^e."""
    return p1 ** i * p2 ** j < base ** e


def _counts_under(base: int, max_exp: int) -> list[int]:
    """counts[e] = #{(i,j) >= 0 : q1^i * q2^j < base^e} for e = 0..max_exp."""
    q1, q2 = OTHERS[base]
    a1, a2 = LOG2[q1] / LOG2[base], LOG2[q2] / LOG2[base]
    hist = np.zeros(max_exp + 2, dtype=np.int64)
    borderline: list[tuple[int, int, float]] = []
    i = 0
    while i * a1 < max_exp:
        rest = max_exp - i * a1
        jmax = int(rest / a2) + 2
        js = np.arange(0, jmax + 1, dtype=np.float64)
        vals = i * a1 + js * a2
        keep = vals < max_exp
        vals = vals[keep]
        js = js[keep]
        # An exponent e counts the pair when vals < e, i.e. it enters at
        # bucket floor(vals) + 1.
        buckets = np.floor(vals).astype(np.int64) + 1
        near = np.abs(vals - np.round(vals)) < GUARD
        if near.any():
            for j_near, v_near in zip(js[near].astype(int), vals[near]):
                borderline.append((i, int(j_near), float(v_near)))
        np.add.at(hist, buckets, 1)
        i += 1
    counts = np.cumsum(hist)[: max_exp + 1].tolist()
    # Re-decide every borderline pair exactly.
    for (bi, bj, val) in borderline:
        e = int(round(val))
        if 1 <= e <= max_exp:
            float_said_in = val < e            # what the float bucketing implied
            truth = _exact_lt(*(OTHERS[base][0], bi, OTHERS[base][1], bj, base, e))
            if truth != float_said_in:
                delta = 1 if truth else -1
                for idx in range(e, max_exp + 1):
                    counts[idx] += delta
    return counts


def build_dyadic_blocks_fast(max_a: int) -> list[tuple[int, int, int]]:
    """(block_base, block_digit, ending_jump_index) for 1 <= a <= max_a."""
    if max_a < 1:
        raise ValueError("max_a must be positive")
    top = max_a + 1
    block_counts = {p: _counts_under(p, int(top / LOG2[p]) + 2) for p in PRIMES}
    cumulative = {
        p: np.cumsum(np.array(block_counts[p], dtype=np.int64)).tolist()
        for p in PRIMES
    }

    # jump list: every prime power below 2^(max_a+1), keyed by its log_2 value
    jumps: list[tuple[float, int, int]] = []
    for p in PRIMES:
        e = 1
        while e * LOG2[p] < top:
            jumps.append((e * LOG2[p], p, e))
            e += 1
    jumps.sort()
    jump_logs = np.array([v for v, _, _ in jumps])

    blocks: list[tuple[int, int, int]] = []
    for a in range(1, max_a + 1):
        left = int(np.searchsorted(jump_logs, a, side="right"))
        right = int(np.searchsorted(jump_logs, a + 1, side="left"))
        internal = jumps[left:right]
        channels = [p for _, p, _ in internal]
        if len(channels) > 2 or len(set(channels)) != len(channels):
            raise AssertionError(("dyadic internal-channel uniqueness", a, internal))
        block_base = 2
        for _, p, _ in internal:
            block_base *= p
        if block_base not in (2, 6, 10, 30):
            raise AssertionError(("unexpected block base", a, block_base))
        block_digit = block_counts[2][a + 1]
        suffix_base = 1
        for _, p, e in reversed(internal):
            strip = cumulative[p][e] - cumulative[2][a]
            block_digit += (p - 1) * suffix_base * strip
            suffix_base *= p
        blocks.append((block_base, block_digit, right))
    return blocks


def verify_against_exact(max_a: int) -> dict:
    from formal_math.probes.erdos269_engine import build_dyadic_blocks
    exact = build_dyadic_blocks(max_a)
    fast = build_dyadic_blocks_fast(max_a)
    mismatches = [
        {"a": i + 1, "exact": e, "fast": f}
        for i, (e, f) in enumerate(zip(exact, fast)) if e != f
    ]
    return {
        "max_a": max_a,
        "compared": min(len(exact), len(fast)),
        "length_match": len(exact) == len(fast),
        "mismatch_count": len(mismatches),
        "first_mismatches": mismatches[:5],
    }


if __name__ == "__main__":
    import json
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
    print(json.dumps(verify_against_exact(n), indent=1))
