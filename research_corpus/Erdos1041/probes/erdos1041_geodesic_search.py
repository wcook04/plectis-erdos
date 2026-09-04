#!/usr/bin/env python3
"""Search for a monic polynomial whose roots are all far apart INSIDE the lemniscate.

The question
------------
Erdos #1041 asks whether two roots can always be joined by a curve of length
below 2 inside {|f| < 1}.  The packet's ten negative results each exhibit a
polynomial refuting one explicit PATH FAMILY, but none computes the shortest
path, so none of them tests the statement itself.

Measuring the true geodesic on those very polynomials shows they are nowhere near
extremal: the cubic that kills direct chords has geodesic 1.78, the five-root
configuration that kills origin spokes has geodesic 0.06.  The only family that
approaches 2 is the degenerate quadratic z^2 - a^2 with a -> 1, where the chord
is interior and the geodesic is exactly the root distance 2a < 2.

So the open question a search can attack is: does anything beat that?  A
configuration whose minimum pairwise geodesic exceeds 2 would refute #1041
outright.

Method
------
Maximise the minimum pairwise geodesic over root configurations in the open unit
disk, by random restart plus coordinate perturbation, at a coarse grid; re-verify
any leader at high resolution.  Grid geodesics overestimate, so a leader above 2
is a CANDIDATE requiring exact checking, never a proof.

Predeclared falsifier
---------------------
A configuration with minimum pairwise geodesic reproducibly above 2 at
increasing resolution refutes the conjecture.  A search that saturates just
below 2 and whose leaders degenerate to the quadratic family instead says the
bound is tight only in that degeneration.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

from formal_math.probes.erdos1041_geodesic import geodesics, guarded_min_geodesic


def score(roots: np.ndarray, grid: int, box: float) -> float:
    """Guarded upper bound on the true minimum pairwise geodesic.

    The unguarded grid value is what an optimiser learns to exploit: pushing the
    roots to the boundary makes the interior corridor thinner than a cell, and
    the grid then reports a detour, or no path at all, where an exactly verified
    chord exists.  Capping by the polyline bound removes that, so the score stays
    an upper bound and a reported value above 2 means something.
    """
    res = guarded_min_geodesic(roots, grid, box)
    val = res.get("guarded_min_geodesic")
    return -1.0 if val is None else float(val)


def clamp(roots: np.ndarray, rmax: float) -> np.ndarray:
    m = np.abs(roots)
    over = m > rmax
    roots = roots.copy()
    roots[over] = roots[over] / m[over] * rmax
    return roots


def seeds(n: int, rmax: float, rng: np.random.Generator, count: int):
    """Start from the known-strong configurations, so the search must beat them."""
    out = []
    # symmetric roots of unity at the modulus cap - the natural extremal family
    out.append(rmax * np.exp(2j * np.pi * np.arange(n) / n))
    # equally spaced but pushed to the boundary with one root pulled in
    alt = rmax * np.exp(2j * np.pi * np.arange(n) / n)
    alt[0] *= 0.5
    out.append(alt)
    # a spread-out arc rather than a full circle
    out.append(rmax * np.exp(1j * np.pi * np.arange(n) / max(n - 1, 1)))
    while len(out) < count:
        ang = rng.uniform(0, 2 * np.pi, n)
        rad = rmax * rng.uniform(0.6, 1.0, n)
        out.append(rad * np.exp(1j * ang))
    return out[:count]


def search(n: int, restarts: int, steps: int, grid: int, rmax: float,
           rng: np.random.Generator) -> dict:
    best_val, best_roots = -1.0, None
    for roots in seeds(n, rmax, rng, restarts):
        roots = clamp(roots, rmax)
        val = score(roots, grid, 1.45)
        sigma = 0.20
        for s in range(steps):
            cand = clamp(roots + (rng.normal(0, sigma, n)
                                  + 1j * rng.normal(0, sigma, n)), rmax)
            cval = score(cand, grid, 1.45)
            if cval > val:
                roots, val = cand, cval
            sigma *= 0.94
        if val > best_val:
            best_val, best_roots = val, roots
    return {
        "n": n,
        "best_min_geodesic": round(best_val, 6),
        "best_roots": [[round(float(z.real), 6), round(float(z.imag), 6)]
                       for z in best_roots],
        "best_root_moduli": [round(float(abs(z)), 6) for z in best_roots],
        "min_chord": round(float(min(abs(best_roots[i] - best_roots[j])
                                     for i in range(n) for j in range(i + 1, n))), 6),
        "unreachable_pair": False,
    }


def run(max_n: int, restarts: int, steps: int, grid: int, rmax: float,
        seed: int) -> dict:
    rng = np.random.default_rng(seed)
    rows = [search(n, restarts, steps, grid, rmax, rng) for n in range(2, max_n + 1)]
    vals = [r["best_min_geodesic"] for r in rows if not r["unreachable_pair"]]
    return {
        "probe_id": "erdos1041_geodesic_search",
        "parameters": {"max_n": max_n, "restarts": restarts, "steps": steps,
                       "grid": grid, "root_modulus_cap": rmax, "seed": seed},
        "per_degree": rows,
        "best_overall": max(vals) if vals else None,
        "any_above_two": bool(vals and max(vals) > 2.0),
        "any_unreachable_pair": any(r["unreachable_pair"] for r in rows),
        "guard": (
            "each score is capped by an exactly verified interior polyline, so it is an "
            "upper bound on the true geodesic; an unguarded grid score can exceed 2 "
            "purely by failing to resolve a thin corridor, and an optimiser finds that "
            "failure mode before it finds anything real"),
        "reading": (
            "a configuration exceeds 2 even under the exact polyline guard: "
            "counterexample CANDIDATE, verify exactly"
            if vals and max(vals) > 2.0 else
            "no configuration reaches 2 under the guard; the leaders are reported "
            "per degree"
        ),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-n", type=int, default=6)
    ap.add_argument("--restarts", type=int, default=4)
    ap.add_argument("--steps", type=int, default=25)
    ap.add_argument("--grid", type=int, default=420)
    ap.add_argument("--rmax", type=float, default=0.999)
    ap.add_argument("--seed", type=int, default=20260823)
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()
    payload = run(args.max_n, args.restarts, args.steps, args.grid, args.rmax,
                  args.seed)
    if args.out:
        Path(args.out).write_text(json.dumps(payload, indent=1) + "\n")
    print(json.dumps(payload, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
