#!/usr/bin/env python3
"""What does the tail shift do, conditioned on the +-2 digit that Erdos #251 needs?

Upstream analytic state
-----------------------
The remaining producer reduces (by the landed +-2 wall) to the single event
Delta = +2 with D in (1/2, 1), or Delta = -2 with D in (-1, -1/2), where
D = T_(N+h) - T_N and Delta = g_(N+h+1) - g_(N+1).

Lean's `shift_gt_half_of_digit_eq_two` already proves half of that window: given
the successor shift exceeds -1, a +2 digit FORCES D > 1/2.  So the two halves of
the event are not independent, and the free part of the requirement is the upper
constraint D < 1.

That leaves a precise question the density probe did not answer: conditioned on
the +-2 digit, how is D actually distributed, and what fraction of the mass sits
inside the window rather than beyond it?  That conditional fraction is the factor
a proof has to supply on top of a Hardy-Littlewood count of the digit event, and
it has never been measured.

Probe
-----
Over the actual primes, restrict to Delta = +2 (and separately Delta = -2) and
histogram D; report the conditional fraction landing in the producer's window,
and how it moves across bands of N.

Predeclared falsifier
---------------------
A conditional fraction that decays toward zero would mean the digit count is not
the binding constraint and a proof needs a joint statement about the digit and
the tail together - much harder than HL input plus tail equidistribution.
A conditional fraction bounded away from zero says the two factors separate, and
names exactly what each must supply.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

from formal_math.probes.erdos251_adjacent_mismatch_density import (
    build_tails,
    primes_up_to,
)


def run(limit: int, offsets: list[int], bands: int) -> dict:
    ps = primes_up_to(limit)
    gaps = np.diff(ps).astype(np.int64)
    T = build_tails(gaps)
    rows = []
    for h in offsets:
        n = len(T) - h - 2
        idx = np.arange(0, n)
        delta = gaps[idx + h + 1] - gaps[idx + 1]
        D = T[idx + h] - T[idx]
        out = {"h": h}
        for sign, name in ((2, "plus_two"), (-2, "minus_two")):
            sel = delta == sign
            count = int(sel.sum())
            Dm = D[sel]
            if sign == 2:
                in_window = (Dm > 0.5) & (Dm < 1.0)
                # Lean forces D > 1/2 under the successor constraint, so the
                # binding half is the upper one.
                below_half = float((Dm <= 0.5).mean()) if count else None
                above_one = float((Dm >= 1.0).mean()) if count else None
            else:
                in_window = (Dm < -0.5) & (Dm > -1.0)
                below_half = float((Dm >= -0.5).mean()) if count else None
                above_one = float((Dm <= -1.0).mean()) if count else None
            frac = float(in_window.mean()) if count else None
            edges = np.linspace(0, count, bands + 1).astype(int)
            band_frac = [round(float(in_window[edges[b]:edges[b + 1]].mean()), 5)
                         for b in range(bands) if edges[b + 1] > edges[b]]
            out[name] = {
                "digit_events": count,
                "digit_rate": round(count / n, 6),
                "conditional_in_window": round(frac, 5) if frac is not None else None,
                "conditional_outside_toward_zero": round(below_half, 5) if below_half is not None else None,
                "conditional_outside_beyond_one": round(above_one, 5) if above_one is not None else None,
                "band_conditional_in_window": band_frac,
                "band_drift": (round(band_frac[-1] / band_frac[0], 4)
                               if band_frac and band_frac[0] else None),
            }
        rows.append(out)
    fracs = [r[s]["conditional_in_window"] for r in rows for s in ("plus_two", "minus_two")
             if r[s]["conditional_in_window"] is not None]
    drifts = [r[s]["band_drift"] for r in rows for s in ("plus_two", "minus_two")
              if r[s]["band_drift"] is not None]
    return {
        "probe_id": "erdos251_conditional_shift_distribution",
        "prime_limit": limit,
        "prime_count": int(len(ps)),
        "per_offset": rows,
        "min_conditional_in_window": min(fracs) if fracs else None,
        "max_conditional_in_window": max(fracs) if fracs else None,
        "min_band_drift": min(drifts) if drifts else None,
        "max_band_drift": max(drifts) if drifts else None,
        "decomposition": (
            "event density = P(digit = +-2) * P(D in window | digit); both factors are "
            "reported per offset so a proof can be aimed at each separately"),
        "conditional_bounded_below": bool(fracs and min(fracs) > 0.03),
        "conditional_stable_across_bands": bool(drifts and min(drifts) > 0.7),
        "reading": (
            "the tail factor is bounded away from zero and stable across bands, so the "
            "producer's event factorises: a proof needs a Hardy-Littlewood count for "
            "the +-2 digit and a non-concentration statement for the tail, aimed "
            "separately rather than jointly"
            if fracs and min(fracs) > 0.03 and drifts and min(drifts) > 0.7 else
            "the tail factor decays or drifts materially, so the two conditions do not "
            "separate and a joint statement is required"
        ),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=120_000_000)
    ap.add_argument("--offsets", type=str, default="1,2,3,5,8,13")
    ap.add_argument("--bands", type=int, default=6)
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()
    payload = run(args.limit, [int(x) for x in args.offsets.split(",")], args.bands)
    if args.out:
        Path(args.out).write_text(json.dumps(payload, indent=1) + "\n")
    print(json.dumps(payload, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
