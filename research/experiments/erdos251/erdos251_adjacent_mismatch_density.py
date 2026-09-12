#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Count adjacent mismatch events in a finite range of prime-gap tails.

The sieve is integer arithmetic; tails and window comparisons use float64.
Counts are numerical observations, not certified individual witnesses. Neither
a positive count nor a declining density decides a cofinality statement.
This optional scan needs NumPy; see requirements.txt in this directory.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

try:
    import numpy as np
except ModuleNotFoundError:
    np = None


def primes_up_to(limit: int) -> np.ndarray:
    sieve = np.ones(limit // 2, dtype=bool)      # odds only: index i <-> 2i+1
    sieve[0] = False                             # 1 is not prime
    for i in range(1, int(limit ** 0.5) // 2 + 1):
        if sieve[i]:
            p = 2 * i + 1
            sieve[(p * p) // 2:: p] = False
    odds = 2 * np.nonzero(sieve)[0].astype(np.int64) + 1
    return np.concatenate(([2], odds))


def build_tails(gaps: np.ndarray, burn: int = 80) -> np.ndarray:
    """T[N] = sum_{k>=1} g[N+k] 2^-k, exact to float precision after `burn` steps.

    Computed by the backward recurrence T[N] = (g[N+1] + T[N+1])/2, so any error
    in the seed is divided by 2 each step and is below float resolution after
    `burn` steps; only indices at least `burn` from the end are returned.
    """
    m = len(gaps)
    T = np.zeros(m, dtype=np.float64)
    acc = 0.0
    for n in range(m - 2, -1, -1):
        acc = (gaps[n + 1] + acc) / 2.0
        T[n] = acc
    return T[: m - burn]


def run(limit: int, max_h: int, bands: int) -> dict:
    if limit < 1000 or max_h < 1 or bands < 1:
        raise ValueError("use --limit >= 1000, --max-h >= 1, and --bands >= 1")
    ps = primes_up_to(limit)
    gaps = np.diff(ps).astype(np.int64)          # gaps[i] = p_(i+2) - p_(i+1)
    T = build_tails(gaps)
    usable = len(T)
    if usable - max_h - 2 < bands:
        raise ValueError("the prime range is too small for these offsets and bands")
    rows = []
    for h in range(1, max_h + 1):
        n = usable - h - 2
        idx = np.arange(0, n)
        delta = gaps[idx + h + 1] - gaps[idx + 1]
        D = T[idx + h] - T[idx]
        hit_pos = (delta == 2) & (D > 0.5) & (D < 1.0)
        hit_neg = (delta == -2) & (D < -0.5) & (D > -1.0)
        hit = hit_pos | hit_neg
        total = int(hit.sum())
        # dyadic bands of N to test persistence
        edges = np.linspace(0, n, bands + 1).astype(int)
        band_density = [
            round(float(hit[edges[b]:edges[b + 1]].mean()), 6) for b in range(bands)
        ]
        # Heuristically the event needs Delta = +-2, whose chance falls like
        # 1/log p, so density * log p should be roughly constant if the decline
        # is only that and not a genuine loss of the event.
        band_logp = [
            float(np.log(ps[edges[b] + 1: edges[b + 1] + 1].mean())) for b in range(bands)
        ]
        band_scaled = [round(band_density[b] * band_logp[b], 5) for b in range(bands)]
        last = int(np.nonzero(hit)[0][-1]) if total else None
        rows.append({
            "h": h,
            "candidates": int(n),
            "events": total,
            "density": round(total / n, 6),
            "band_density": band_density,
            "delta_plus_two_events": int(hit_pos.sum()),
            "delta_minus_two_events": int(hit_neg.sum()),
            "last_event_index": last,
            "last_event_prime": int(ps[last + 1]) if last is not None else None,
            "band_mean_log_prime": [round(v, 3) for v in band_logp],
            "band_density_times_log_prime": band_scaled,
            "scaled_drift": round(band_scaled[-1] / band_scaled[0], 4) if band_scaled[0] else None,
        })
    densities = [r["density"] for r in rows]
    drifts = [r["scaled_drift"] for r in rows if r["scaled_drift"] is not None]
    # persistence: does the final band hold up against the first?
    decaying = [r["h"] for r in rows
                if r["band_density"][0] > 0 and r["band_density"][-1] < 0.3 * r["band_density"][0]]
    return {
        "probe_id": "erdos251_adjacent_mismatch_density",
        "prime_limit": limit,
        "prime_count": int(len(ps)),
        "usable_tail_indices": int(usable),
        "per_h": rows,
        "min_density": min(densities),
        "max_density": max(densities),
        "h_with_zero_events": [r["h"] for r in rows if r["events"] == 0],
        "h_with_decaying_density": decaying,
        "scaled_drift_min": min(drifts) if drifts else None,
        "scaled_drift_max": max(drifts) if drifts else None,
        "scaled_law": (
            "density * log p is stable across bands: the decline is the 1/log p cost of "
            "requiring Delta = +-2, not a loss of the event"
            if drifts and min(drifts) > 0.8 and max(drifts) < 1.25 else
            "density * log p drifts; the 1/log p reading does not fully explain the decline"
        ),
        "reading": "Finite floating-point counts only; no cofinality or irrationality conclusion.",
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=50_000_000)
    ap.add_argument("--max-h", type=int, default=12)
    ap.add_argument("--bands", type=int, default=6)
    ap.add_argument("--out", type=str, default="")
    ap.add_argument("--json", action="store_true", help="print every recorded offset")
    args = ap.parse_args()
    if np is None:
        ap.error("this optional scan needs NumPy; install the requirements.txt next to this script in a virtual environment")
    try:
        payload = run(args.limit, args.max_h, args.bands)
    except ValueError as exc:
        ap.error(str(exc))
    if args.out:
        Path(args.out).write_text(json.dumps(payload, indent=1) + "\n")
    compact = {k: v for k, v in payload.items() if k != "per_h"}
    compact["per_h_sample"] = payload["per_h"][:6]
    print(json.dumps(payload if args.json else compact, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
