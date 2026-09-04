#!/usr/bin/env python3
"""Measure the escape-depth law L*(q, a) for Erdos #269.

Motivating analytic state (upstream)
------------------------------------
The Lean bounded-radix dichotomy leaves exactly one branch: an exact integral
normalized source tail.  For an assumed odd denominator q coprime to 30 and a
dyadic start a, that branch survives at window length L iff the canonical least
positive residue r(q,a,L) = (-q F) mod B does NOT exceed the analytic cap
C(q,a,L).  Prior work chased bounded-lookahead Lyapunov functions on the gap
C - r and retired them (two-step law falsified at starts 2220 and 2602).

Predeclared question
--------------------
Escape is a thin event: heuristically r is equidistributed in [1, B] with
B ~ 8^L and C ~ 0.47 q (a+L)^2, so the first escape should occur at
    L*(q,a) ~ log_8( q * (a)^2 ) + O(1).
This probe measures L* exactly over a large (q, a) rectangle and tests the
predeclared law.

Falsifier
---------
A single (q, a) with no escape inside max_length, or an L* that grows faster
than C * log(q a^2), retires the "generic anti-concentration" reading and
forces a conspiracy mechanism instead.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from math import gcd
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formal_math.probes.erdos269_blocks import build_blocks  # noqa: E402
from formal_math.probes.erdos269_engine import (  # noqa: E402
    escape_depth,
    short_bound,
)


def run(max_start: int, max_q: int, max_length: int, block_slack: int) -> dict:
    blocks = build_blocks(max_start + block_slack)
    qs = [q for q in range(1, max_q + 1) if gcd(q, 30) == 1]
    depth_hist: dict[int, int] = {}
    no_escape: list[tuple[int, int]] = []
    worst: list[dict] = []
    max_depth = 0
    # excess = L* - log_8(q * J^2); the predeclared law says this is O(1).
    excess_max = -10.0
    excess_argmax = None
    excess_sum = 0.0
    excess_n = 0
    per_q_max: dict[int, int] = {}
    for q in qs:
        for a in range(1, max_start + 1):
            cert = escape_depth(blocks, q, a, max_length)
            depth = cert.get("depth")
            if depth is None:
                no_escape.append((q, a))
                continue
            depth_hist[depth] = depth_hist.get(depth, 0) + 1
            if depth > per_q_max.get(q, 0):
                per_q_max[q] = depth
            if depth > max_depth:
                max_depth = depth
                worst.append({"q": q, "start": a, **{k: v for k, v in cert.items()
                                                     if k != "residue"}})
            j = int(cert["ending_jump_index"])
            predicted = math.log(q * (j * j + 10 * j + 27) / 9.0, 8.0)
            excess = depth - predicted
            excess_sum += excess
            excess_n += 1
            if excess > excess_max:
                excess_max = excess
                excess_argmax = {"q": q, "start": a, "depth": depth,
                                 "predicted": round(predicted, 4),
                                 "excess": round(excess, 4)}
    return {
        "probe_id": "erdos269_escape_depth_law",
        "parameters": {"max_start": max_start, "max_q": max_q,
                       "max_length": max_length, "q_count": len(qs)},
        "pairs_tested": len(qs) * max_start,
        "no_escape_pairs": no_escape[:50],
        "no_escape_count": len(no_escape),
        "max_escape_depth": max_depth,
        "depth_histogram": {str(k): v for k, v in sorted(depth_hist.items())},
        "depth_record_trace": worst[-12:],
        "excess_max": round(excess_max, 4),
        "excess_argmax": excess_argmax,
        "excess_mean": round(excess_sum / max(excess_n, 1), 4),
        "per_q_max_depth": {str(k): v for k, v in sorted(per_q_max.items())},
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-start", type=int, default=20000)
    ap.add_argument("--max-q", type=int, default=120)
    ap.add_argument("--max-length", type=int, default=80)
    ap.add_argument("--block-slack", type=int, default=200)
    ap.add_argument("--out", type=str, required=True)
    args = ap.parse_args()
    payload = run(args.max_start, args.max_q, args.max_length, args.block_slack)
    Path(args.out).write_text(json.dumps(payload, indent=1) + "\n")
    print(json.dumps({k: v for k, v in payload.items()
                      if k not in ("per_q_max_depth", "depth_record_trace")},
                     indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
