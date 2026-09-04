#!/usr/bin/env python3
"""Unbounded denominator-exclusion certificates for Erdos #269.

Upstream analytic state
-----------------------
Lean's bounded-radix dichotomy leaves one branch: an exact integral normalized
source tail.  If the value is rational with odd denominator q coprime to 30,
then for every dyadic start a and window length L the integer

    u_L = q * X_(a+L)

satisfies 0 < u_L <= C(q, L) = q*(J^2 + 10J + 27)/9  and  u_L = -q F (mod B),

so u_L is the least positive residue of -qF modulo B.  Hence

    residue(q, a, L) > C(q, L)   ==>   q is not the denominator.

That is the existing finite Farey/escape check.  Prior work applied it by
scanning q one at a time, which caps the excluded height at the scan bound.

This probe's contribution
-------------------------
Excluding *every* q <= Q at depth L is exactly the statement

    min { q >= 1 : (q*A) mod B <= W }  >  Q,     A = (-F) mod B, W = Q*k/9,

a first-hit-of-a-rotation-in-an-interval problem solvable in O(log B) by the
Stern-Brocot recursion, not O(Q) by scanning.  Binary searching Q therefore
produces the largest certified exclusion at each depth in logarithmic time, and
the bound grows like sqrt(9 B / k) ~ 8^(L/2): a family of exclusions tending to
infinity rather than one finite Farey bound.

Predeclared falsifier
---------------------
(1) The lattice bound disagrees with a direct q-scan at any small depth.
(2) The certified bound Q*(a, L) fails to increase with L, which would mean the
    escape geometry does not in fact supply an unbounded height family.
"""

from __future__ import annotations

import argparse
import json
import sys
from math import gcd
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formal_math.probes.erdos269_blocks import build_blocks  # noqa: E402
from formal_math.probes.erdos269_engine import (  # noqa: E402
    least_positive_residue,
    short_bound,
)
from formal_math.probes.lattice_first_hit import min_multiplier_below  # noqa: E402


def window_data(blocks, start: int, length: int) -> tuple[int, int, int]:
    """Return (base B, forcing F, ending jump index J) for window (start, length)."""
    base, forcing = 1, 0
    ending = 0
    for index in range(start - 1, start - 1 + length):
        block_base, block_digit, ending = blocks[index]
        base *= block_base
        forcing = block_base * forcing + block_digit
    return base, forcing, ending


def certified_exclusion(base: int, forcing: int, ending: int) -> dict:
    """Largest certified Q with no q in [1, Q] trapped at this window.

    The cap C(q) = q*kappa_num/9 grows with q, so a single uniform window would
    over-approximate the cap badly for small q.  Staging the search dyadically
    keeps the over-approximation within a factor of two of the true cap inside
    each stage, which is what makes the certified bound track the heuristic
    sqrt(9B/kappa) rather than falling short of it.
    """
    kappa_num = ending * ending + 10 * ending + 27
    A = (-forcing) % base
    best = 0
    stage_hi = 1
    candidate_min_hit = None
    while True:
        W = stage_hi * kappa_num // 9
        if W >= base:                       # cap reaches the modulus: no content
            break
        hit = min_multiplier_below(A, base, W)
        if hit > stage_hi:
            best = stage_hi                 # every q <= stage_hi clears
            stage_hi *= 2
            continue
        # A q in [hit, stage_hi] may be trapped; everything below `hit` clears.
        best = max(best, hit - 1)
        candidate_min_hit = hit
        break
    return {
        "excluded_below_or_equal": best,
        "kappa_num": kappa_num,
        "first_candidate_hit": candidate_min_hit,
    }


def brute_min_bad_q(base: int, forcing: int, ending: int, limit: int) -> int | None:
    """Smallest q <= limit trapped at this window, by direct scan (cross-check)."""
    kappa_num = ending * ending + 10 * ending + 27
    for q in range(1, limit + 1):
        cap = q * kappa_num // 9
        if base <= cap:
            return q
        if least_positive_residue(-q * forcing, base) <= cap:
            return q
    return None


def run(start: int, max_depth: int, cross_check_depth: int,
        cross_check_limit: int) -> dict:
    blocks = build_blocks(start + max_depth + 8)
    rows = []
    base, forcing, ending = 1, 0, 0
    best = 0
    best_depth = 0
    cross_checks = []
    index = start - 1
    for length in range(1, max_depth + 1):
        block_base, block_digit, ending = blocks[index]
        base *= block_base
        forcing = block_base * forcing + block_digit
        index += 1
        cert = certified_exclusion(base, forcing, ending)
        Q = cert["excluded_below_or_equal"]
        if Q > best:
            best, best_depth = Q, length
        rows.append({
            "depth": length,
            "base_bits": base.bit_length(),
            "ending_jump_index": ending,
            "excluded_below_or_equal_bits": Q.bit_length(),
            "excluded_below_or_equal": str(Q) if Q < 10 ** 25 else f"~10^{len(str(Q))-1}",
        })
        if length <= cross_check_depth:
            observed = brute_min_bad_q(base, forcing, ending, cross_check_limit)
            # Soundness: no q <= Q may be trapped.  Tightness is reported, not required.
            sound = observed is None or observed > Q
            tightness = None
            if observed is not None and Q > 0:
                tightness = round(Q / (observed - 1), 4) if observed > 1 else 0.0
            cross_checks.append({
                "depth": length, "lattice_bound": Q,
                "scan_min_bad_q": observed, "sound": bool(sound),
                "tightness_vs_scan": tightness,
            })
    disagreements = [c for c in cross_checks if not c["sound"]]
    return {
        "probe_id": "erdos269_denominator_exclusion",
        "start": start,
        "max_depth": max_depth,
        "cross_check": {
            "depths_checked": len(cross_checks),
            "scan_limit": cross_check_limit,
            "unsound_rows": disagreements,
            "status": "sound" if not disagreements else "UNSOUND",
            "rows": cross_checks,
        },
        "best_excluded_below_or_equal_digits": len(str(best)),
        "best_excluded_below_or_equal_bits": best.bit_length(),
        "best_depth": best_depth,
        "monotone_in_depth": all(
            rows[i]["excluded_below_or_equal_bits"]
            <= rows[i + 1]["excluded_below_or_equal_bits"] + 2
            for i in range(len(rows) - 1)
        ),
        "depth_rows": rows,
        "best_excluded_value": str(best),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--start", type=int, default=1)
    ap.add_argument("--max-depth", type=int, default=120)
    ap.add_argument("--cross-check-depth", type=int, default=9)
    ap.add_argument("--cross-check-limit", type=int, default=40000)
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()
    payload = run(args.start, args.max_depth, args.cross_check_depth,
                  args.cross_check_limit)
    if args.out:
        Path(args.out).write_text(json.dumps(payload, indent=1) + "\n")
    compact = {k: v for k, v in payload.items() if k != "depth_rows"}
    compact["depth_rows_sample"] = payload["depth_rows"][::10][:14]
    print(json.dumps(compact, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
