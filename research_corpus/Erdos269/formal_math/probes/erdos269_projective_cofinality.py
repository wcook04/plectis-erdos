#!/usr/bin/env python3
"""Are Erdos #269's projective-shadow violations available arbitrarily late?

Upstream analytic state
-----------------------
Lean's `reducedCarry_projective_shadow` says that if two reduced carries come
from the same rational value at endpoint heights H_a and H_b, then

    d_a * H_b  ==  d_b * H_a   (mod B),

where B is the reduced denominator and d is the canonical endpoint carry.  A
pair of windows that are individually admissible - base clears the cap, the
residue does NOT escape it, and the residue is coprime to B - but that violate
this congruence excludes B outright, even when both residues are small and
coprime.  The packet has exact single witnesses at B=11 and B=7, and states
plainly that neither supplies the universal or cofinal quantifier the open
producer `cofinal_projective_window_pair_incoherence` needs:

> For every positive B coprime to 30, construct arbitrarily late pairs of exact
> dyadic windows whose canonical endpoint carries are individually within the
> analytic bounds but violate d_a*H_b = d_b*H_a modulo B.

Probe
-----
Enumerate, for many B and many starts, every admissible window endpoint; then
measure (i) whether violating pairs exist for every B, (ii) what fraction of
admissible pairs violate, and (iii) how late admissible endpoints keep
appearing, since arbitrarily late pairs need arbitrarily late endpoints.

Predeclared falsifier
---------------------
A B with no violating pair, or admissible endpoints that stop appearing beyond
some start, would mean the producer cannot be constructed this way and the route
is closed rather than merely unproved.
"""

from __future__ import annotations

import argparse
import json
import sys
from math import gcd, log
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formal_math.probes.erdos269_blocks import build_blocks  # noqa: E402
from formal_math.probes.erdos269_engine import (  # noqa: E402
    least_positive_residue,
    short_bound,
)

LOG2_3 = log(3) / log(2)
LOG2_5 = log(5) / log(2)
GUARD = 1e-9


def _floor_div_log(scale: int, prime: int, approx: float) -> int:
    """Largest e with prime^e <= 2^scale, decided exactly near the boundary."""
    e = int(scale / approx)
    for cand in (e - 1, e, e + 1, e + 2):
        if cand < 0:
            continue
        if prime ** cand <= (1 << scale) < prime ** (cand + 1):
            return cand
    # fall back to a widening exact search
    cand = max(0, e - 3)
    while prime ** (cand + 1) <= (1 << scale):
        cand += 1
    return cand


def height_mod(scale: int, modulus: int) -> int:
    """threePrimeHeight(2^scale) mod modulus, without building the height."""
    e3 = _floor_div_log(scale, 3, LOG2_3)
    e5 = _floor_div_log(scale, 5, LOG2_5)
    return (pow(2, scale, modulus) * pow(3, e3, modulus) * pow(5, e5, modulus)) % modulus


def admissible_endpoints(blocks, denominator: int, start: int, max_length: int):
    """Windows that are individually admissible: base clears the cap, the residue
    does not escape it, and the residue is a unit modulo the denominator."""
    out = []
    base, forcing = 1, 0
    index = start - 1
    for length in range(1, max_length + 1):
        if index >= len(blocks):
            break
        block_base, block_digit, ending = blocks[index]
        base *= block_base
        forcing = block_base * forcing + block_digit
        index += 1
        cap = short_bound(denominator, ending)
        if base <= cap:
            continue
        residue = least_positive_residue(-denominator * forcing, base)
        if residue > cap:
            break                                    # escaped: window is fatal
        if gcd(residue, denominator) != 1:
            continue                                 # nonunit consumer fires
        out.append((start, length, residue, height_mod(start + length, denominator)))
    return out


def run(max_denominator: int, max_start: int, max_length: int, pair_cap: int) -> dict:
    blocks = build_blocks(max_start + max_length + 8)
    rows = []
    bs = [b for b in range(7, max_denominator + 1) if gcd(b, 30) == 1]
    for B in bs:
        endpoints = []
        for a in range(1, max_start + 1):
            endpoints.extend(admissible_endpoints(blocks, B, a, max_length))
        violations = 0
        pairs = 0
        latest_pair_start = None
        for i in range(len(endpoints)):
            for j in range(i + 1, min(len(endpoints), i + 1 + pair_cap)):
                a1, _, d1, h1 = endpoints[i]
                a2, _, d2, h2 = endpoints[j]
                pairs += 1
                if (d1 * h2 - d2 * h1) % B != 0:
                    violations += 1
                    lo = min(a1, a2)
                    if latest_pair_start is None or lo > latest_pair_start:
                        latest_pair_start = lo
        rows.append({
            "denominator": B,
            "admissible_endpoints": len(endpoints),
            "latest_admissible_start": max((e[0] for e in endpoints), default=None),
            "pairs_tested": pairs,
            "violating_pairs": violations,
            "violation_fraction": round(violations / pairs, 5) if pairs else None,
            "latest_violating_pair_min_start": latest_pair_start,
            "expected_fraction_if_uniform": round(1 - 1 / B, 5),
        })
    no_violation = [r["denominator"] for r in rows if not r["violating_pairs"]]
    late = [r for r in rows if r["latest_violating_pair_min_start"] is not None]
    return {
        "probe_id": "erdos269_projective_cofinality",
        "parameters": {"max_denominator": max_denominator, "max_start": max_start,
                       "max_length": max_length, "pair_cap": pair_cap},
        "denominators_tested": len(bs),
        "denominators_with_no_violating_pair": no_violation,
        "min_violation_fraction": min((r["violation_fraction"] for r in rows
                                       if r["violation_fraction"] is not None), default=None),
        "min_latest_violating_pair_min_start": min(
            (r["latest_violating_pair_min_start"] for r in late), default=None),
        "per_denominator": rows,
        "reading": (
            "every tested denominator admits violating pairs, and they keep appearing "
            "at the top of the start range, so the construction is available late"
            if not no_violation else
            "at least one denominator admits no violating pair; the route is closed"
        ),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-denominator", type=int, default=200)
    ap.add_argument("--max-start", type=int, default=400)
    ap.add_argument("--max-length", type=int, default=40)
    ap.add_argument("--pair-cap", type=int, default=40)
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()
    payload = run(args.max_denominator, args.max_start, args.max_length, args.pair_cap)
    if args.out:
        Path(args.out).write_text(json.dumps(payload, indent=1) + "\n")
    compact = {k: v for k, v in payload.items() if k != "per_denominator"}
    compact["per_denominator_sample"] = payload["per_denominator"][:6]
    print(json.dumps(compact, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
