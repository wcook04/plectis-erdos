#!/usr/bin/env python3
"""Erdos #1041: adversarial stress of the inverse-ray (descent) construction.

Why this construction is the interesting one
--------------------------------------------
Along the curve of constant arg f descending from a critical point c, |f| falls
monotonically from |f(c)| < 1 to 0.  So the path is inside {|f| < 1} BY
CONSTRUCTION -- containment is free.  That is the exact complement of the
straight spoke, which has free length control (|z_a - c|) and no containment;
AllStraightSegmentsCounterexampleComputationalLab.md kills the chord and
CriticalBudgetLab.md shows the convexity majorant cannot certify a spoke on the
extremal family at any degree.

So for the descent path the only open question is LENGTH.  For each admissible
simple critical point c let L_c be the combined arc length of its two descending
branches to distinct roots.  Two statements:

    MIN   min_c L_c < 2         -- this alone would settle #1041, since the path
                                   is already contained.
    AVG   sum_c L_c < 2 * (number of admissible hubs)
                                -- the averaging mechanism proposed in
                                   InverseRayAggregateComputationalLab.md, which
                                   implies MIN by pigeonhole.

What that lab established, and what it did not
----------------------------------------------
It established that a single hub can exceed 2: the balanced quintic has a hub of
combined length about 2.15, while another hub in the same polynomial is short, so
MIN survives there with normalized aggregate about 0.536.  And it ran a
DETERMINISTIC probe over three structured families, all below the threshold, with
the near-regular cubic family approaching it from below.

What it did not do is maximise.  It names the one-way outcome explicitly: "A
numerical aggregate at least one would ... eliminate the unweighted average
mechanism."  This probe goes after that, and after the stronger target MIN.

Instrument
----------
The arc lengths come from inverse_ray_aggregate_score in that lab's own checker,
not from a rival implementation, so the numbers are comparable to its receipt.
Reproduced here: the balanced quintic scores 0.536025 against the lab's "about
0.536".  The integrator is adaptive: normalized aggregate, minimum edge and
maximum edge are identical to six decimals across flow_max_step from 0.04 down to
0.0025, a sixteenfold range, on the quintic and on random configurations at
degrees 3, 5 and 8.  flow_max_step is a cap, not the resolution.

Read-only dependency: search_counterexample.py is owned by a concurrent session.
This probe imports it and never writes to it.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np

from formal_math.erdos257_period_noncollapse.ErdosProblems.Erdos1041.scripts.search_counterexample import (
    inverse_ray_aggregate_score,
)

RCAP = 1.0 - 1e-9


def clamp(roots: np.ndarray, cap: float = RCAP) -> np.ndarray:
    r = np.abs(roots)
    return roots * np.where(r > cap, cap / np.maximum(r, 1e-300), 1.0)


def score(roots: np.ndarray, step: float) -> dict:
    """Both targets plus the diagnostics needed to audit a reported violation."""
    try:
        norm_avg, detail = inverse_ray_aggregate_score(roots, step)
    except Exception:
        return {"ok": False}
    hubs = int(detail.get("admissible_simple_critical_hub_count", 0))
    if hubs == 0:
        return {"ok": False}
    return {
        "ok": True,
        "normalized_average": float(norm_avg),
        "min_edge": float(detail["minimum_edge_length"]),
        "max_edge": float(detail["maximum_edge_length"]),
        "total_length": float(detail["total_inverse_ray_edge_length"]),
        "hubs": hubs,
        "degree": len(roots),
    }


def objective(roots: np.ndarray, mode: str, step: float) -> float:
    s = score(roots, step)
    if not s["ok"]:
        # a configuration with no admissible hub is not evidence about either
        # statement, so it must not be rewarded; the search is steered away.
        return -math.inf
    return s["min_edge"] if mode == "min_edge" else s["normalized_average"]


def search(n: int, mode: str, restarts: int, steps: int, step: float,
           rng: np.random.Generator, cap: float) -> dict:
    best_val, best_roots = -math.inf, None
    for t in range(restarts):
        if t == 0:
            roots = cap * np.exp(2j * np.pi * np.arange(n) / n)
        elif t == 1:
            roots = cap * np.exp(2j * np.pi * (np.arange(n) / n
                                               + 0.01 * rng.normal(size=n)))
        else:
            roots = cap * rng.uniform(0.4, 1.0, n) * np.exp(2j * np.pi * rng.uniform(0, 1, n))
        roots = clamp(roots, cap)
        val = objective(roots, mode, step)
        scale = 0.3
        for _ in range(steps):
            cand = clamp(roots + scale * (rng.normal(size=n) + 1j * rng.normal(size=n)), cap)
            cval = objective(cand, mode, step)
            if cval > val:
                roots, val = cand, cval
            else:
                scale *= 0.94
            if scale < 1e-5:
                break
        if val > best_val:
            best_val, best_roots = val, roots
    out = {"n": n, "mode": mode, "best": float(best_val)}
    if best_roots is not None:
        out["roots"] = [[float(z.real), float(z.imag)] for z in best_roots]
        out.update({k: v for k, v in score(best_roots, step).items() if k != "ok"})
    return out


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--min-n", type=int, default=3)
    ap.add_argument("--max-n", type=int, default=7)
    ap.add_argument("--restarts", type=int, default=8)
    ap.add_argument("--steps", type=int, default=120)
    ap.add_argument("--flow-max-step", type=float, default=0.02)
    ap.add_argument("--modes", type=str, default="min_edge,normalized_average")
    ap.add_argument("--seed", type=int, default=41)
    ap.add_argument("--out", type=Path, default=None)
    args = ap.parse_args()

    rng = np.random.default_rng(args.seed)
    rows = []
    for mode in [m.strip() for m in args.modes.split(",")]:
        for n in range(args.min_n, args.max_n + 1):
            rows.append(search(n, mode, args.restarts, args.steps,
                               args.flow_max_step, rng, RCAP))
            print(json.dumps(rows[-1]), flush=True)

    report = {
        "rows": rows,
        "verdict": {
            "max_min_edge": max((r["best"] for r in rows if r["mode"] == "min_edge"),
                                default=None),
            "max_normalized_average": max(
                (r["best"] for r in rows if r["mode"] == "normalized_average"),
                default=None),
            "MIN_refuted": any(r["best"] >= 2.0 for r in rows if r["mode"] == "min_edge"),
            "AVG_refuted": any(r["best"] >= 1.0 for r in rows
                               if r["mode"] == "normalized_average"),
        },
    }
    print(json.dumps(report["verdict"], indent=2))
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
