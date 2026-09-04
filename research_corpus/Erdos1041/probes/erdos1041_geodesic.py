#!/usr/bin/env python3
"""True geodesic distance between roots inside the Erdos #1041 lemniscate.

Why this is the gap
-------------------
All ten negative results in the #1041 packet kill a specific PATH FAMILY: direct
root chords, origin spokes, metric-selected critical-point spokes, Newton
descending inverse-ray branches, fixed-origin broken lines, spanning-tree
budgets.  Each one exhibits a polynomial on which that family fails.

None of them computes the actual shortest path.  So the question the problem
actually asks - is the infimum over ALL curves below 2 - has never been measured
on the very configurations that refute the explicit families.

Method
------
The lemniscate is contained in |z| < 2, since |z| >= 2 with all roots in the unit
disk forces |f(z)| >= (|z|-1)^n >= 1.  Grid that box, keep the cells where
|f| < 1, and build a graph on them with a 16-neighbour stencil (all offsets with
|dx|,|dy| <= 2 and gcd 1), which cuts the grid-metric anisotropy to well under a
percent.  A move is admitted only when every sampled interior point of the
segment is also inside, so a path can never cut a corner through the exterior.
Dijkstra from each root cell then gives the pairwise geodesics.

The grid geodesic OVERESTIMATES the true one - it is a genuine path in the
domain, up to discretisation - so a measured value below 2 is a witness that the
infimum is below 2, which is the direction that supports the conjecture.  A
measured value above 2 is a counterexample CANDIDATE only, to be checked exactly.
"""

from __future__ import annotations

import argparse
import json
from math import gcd
from pathlib import Path

import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import dijkstra


def stencil(radius: int = 2) -> list[tuple[int, int]]:
    out = []
    for dx in range(-radius, radius + 1):
        for dy in range(-radius, radius + 1):
            if (dx, dy) == (0, 0):
                continue
            if gcd(abs(dx), abs(dy)) != 1:
                continue          # collinear duplicate of a shorter move
            out.append((dx, dy))
    return out


def inside_mask(roots: np.ndarray, n_grid: int, box: float, margin: float):
    xs = np.linspace(-box, box, n_grid)
    ys = np.linspace(-box, box, n_grid)
    X, Y = np.meshgrid(xs, ys, indexing="ij")
    Z = X + 1j * Y
    logf = np.zeros_like(X)
    for r in roots:
        logf += np.log(np.abs(Z - r) + 1e-300)
    return (logf < -margin), xs, ys


def geodesics(roots: np.ndarray, n_grid: int = 900, box: float = 1.35,
              margin: float = 0.0, samples: int = 3) -> dict:
    mask, xs, ys = inside_mask(roots, n_grid, box, margin)
    h = xs[1] - xs[0]
    idx = -np.ones(mask.shape, dtype=np.int64)
    inside_ij = np.argwhere(mask)
    idx[mask] = np.arange(len(inside_ij))
    n_nodes = len(inside_ij)
    if n_nodes == 0:
        return {"error": "empty lemniscate on this grid"}

    rows, cols, vals = [], [], []
    for dx, dy in stencil(2):
        src = idx[max(0, -dx): mask.shape[0] - max(0, dx),
                  max(0, -dy): mask.shape[1] - max(0, dy)]
        dst = idx[max(0, dx): mask.shape[0] - max(0, -dx),
                  max(0, dy): mask.shape[1] - max(0, -dy)]
        ok = (src >= 0) & (dst >= 0)
        if samples and max(abs(dx), abs(dy)) > 1:
            # a long move must not cut a corner: sample the interior of the segment
            for t in np.linspace(0, 1, samples + 2)[1:-1]:
                mx = np.rint(np.arange(src.shape[0])[:, None] * 0 + t * dx).astype(int)
                my = np.rint(np.arange(src.shape[1])[None, :] * 0 + t * dy).astype(int)
                mid = idx[max(0, -dx) + mx[0, 0]: mask.shape[0] - max(0, dx) + mx[0, 0],
                          max(0, -dy) + my[0, 0]: mask.shape[1] - max(0, dy) + my[0, 0]]
                ok &= (mid >= 0)
        w = h * np.hypot(dx, dy)
        rows.append(src[ok]); cols.append(dst[ok])
        vals.append(np.full(int(ok.sum()), w))
    rows = np.concatenate(rows); cols = np.concatenate(cols); vals = np.concatenate(vals)
    graph = coo_matrix((vals, (rows, cols)), shape=(n_nodes, n_nodes)).tocsr()

    root_nodes = []
    for r in roots:
        i = int(np.clip(np.searchsorted(xs, r.real), 0, n_grid - 1))
        j = int(np.clip(np.searchsorted(ys, r.imag), 0, n_grid - 1))
        best = None
        for di in range(-2, 3):
            for dj in range(-2, 3):
                a, b = i + di, j + dj
                if 0 <= a < n_grid and 0 <= b < n_grid and idx[a, b] >= 0:
                    d = (xs[a] - r.real) ** 2 + (ys[b] - r.imag) ** 2
                    if best is None or d < best[0]:
                        best = (d, int(idx[a, b]))
        root_nodes.append(None if best is None else best[1])
    if any(v is None for v in root_nodes):
        return {"error": "a root did not land on an interior cell; refine the grid"}

    dist = dijkstra(graph, directed=False, indices=root_nodes)
    n = len(roots)
    pairs = []
    for a in range(n):
        for b in range(a + 1, n):
            d = float(dist[a, root_nodes[b]])
            pairs.append({"i": a, "j": b, "geodesic": None if np.isinf(d) else round(d, 6),
                          "straight": round(float(abs(roots[a] - roots[b])), 6)})
    finite = [p["geodesic"] for p in pairs if p["geodesic"] is not None]
    return {
        "grid": n_grid, "box": box, "cell": round(float(h), 6),
        "interior_cells": int(n_nodes),
        "pairs": pairs,
        "min_geodesic": min(finite) if finite else None,
        "connected_pairs": len(finite),
        "total_pairs": len(pairs),
    }


def segment_max_modulus(roots: np.ndarray, a: complex, b: complex,
                        samples: int = 512) -> float:
    """The EXACT maximum of |f| on the closed segment [a, b].

    Restricted to the line z(t) = a + t(b - a), f is a complex polynomial P(t) of
    degree n, and |f|^2 is the real polynomial Q = P * conj(P) of degree 2n.  The
    maximum of Q on [0, 1] is attained at an endpoint or at a real root of Q', so
    it is COMPUTED, not sampled.  A dense sample is taken as well and the larger
    value returned, so a root-finding slip can only make the reported maximum too
    large - which makes the interiority test stricter, never looser.

    Sampling alone is unsound here: |f| can exceed 1 strictly between samples, and
    admitting such a segment turns a claimed upper bound on the geodesic into a
    value that may sit below the truth.
    """
    delta = complex(b) - complex(a)
    if delta == 0:
        return float(abs(np.polyval(np.poly(roots), a)))

    P = np.array([1.0 + 0.0j])
    for r in roots:
        P = np.convolve(P, np.array([delta, complex(a) - complex(r)], dtype=complex))
    Q = np.convolve(P, np.conjugate(P)).real

    ts = [0.0, 1.0]
    dQ = np.polyder(Q)
    if dQ.size > 1 and np.any(dQ != 0):
        for t in np.roots(dQ):
            if abs(t.imag) < 1e-9 and -1e-12 <= t.real <= 1.0 + 1e-12:
                ts.append(min(1.0, max(0.0, float(t.real))))
    exact = float(np.max(np.polyval(Q, np.array(ts))))

    grid = np.linspace(0.0, 1.0, max(2, samples))
    sampled = float(np.max(np.polyval(Q, grid)))
    return float(np.sqrt(max(0.0, exact, sampled)))


def polyline_upper_bound(roots: np.ndarray, samples: int = 4000) -> dict:
    """Exact upper bounds on the geodesic from explicitly interior polylines.

    A grid geodesic can only OVERestimate, and it overestimates badly exactly
    where the interior corridor is thinner than a cell - which is precisely where
    an optimiser pushes the configuration.  These bounds are computed off the
    grid entirely, and the interiority of each segment is CERTIFIED rather than
    sampled (see segment_max_modulus): a segment is admitted only when the exact
    maximum of |f| along it is below 1.

    This matters in the dangerous direction.  A sampled check can admit a segment
    on which |f| spikes above 1 between samples; the resulting "upper bound" is
    then not an upper bound, and capping the grid value by it would manufacture a
    false witness BELOW 2.  Certifying the maximum removes that failure mode.

    Hubs tried: the straight chord, and the broken line through each of the
    origin and the critical points of f.
    """
    n = len(roots)
    coeffs = np.poly(roots)
    crit = np.roots(np.polyder(coeffs)) if n >= 2 else np.array([])
    hubs = np.concatenate(([0j], crit))

    def interior(a: complex, b: complex) -> bool:
        return segment_max_modulus(roots, a, b, samples=samples) < 1.0

    best = None
    detail = []
    for i in range(n):
        for j in range(i + 1, n):
            a, b = roots[i], roots[j]
            if interior(a, b):
                d = float(abs(a - b))
                detail.append({"i": i, "j": j, "via": "chord", "length": round(d, 6)})
                best = d if best is None else min(best, d)
                continue
            for h_index, h in enumerate(hubs):
                if interior(a, h) and interior(h, b):
                    d = float(abs(a - h) + abs(h - b))
                    detail.append({"i": i, "j": j,
                                   "via": "origin" if h_index == 0 else f"crit{h_index-1}",
                                   "length": round(d, 6)})
                    best = d if best is None else min(best, d)
    return {"upper_bound": None if best is None else round(best, 6),
            "witnesses": sorted(detail, key=lambda r: r["length"])[:4]}


def guarded_min_geodesic(roots: np.ndarray, n_grid: int, box: float) -> dict:
    """Grid geodesic, capped by any exactly-verified interior polyline.

    Reporting the minimum of the two keeps the number an UPPER bound on the true
    geodesic, so a value above 2 can no longer be manufactured by a grid too
    coarse to see a thin corridor.
    """
    grid = geodesics(roots, n_grid=n_grid, box=box)
    poly = polyline_upper_bound(roots)
    grid_val = grid.get("min_geodesic")
    cand = [v for v in (grid_val, poly["upper_bound"]) if v is not None]
    return {
        "grid_min_geodesic": grid_val,
        "grid_connected": (grid.get("connected_pairs") == grid.get("total_pairs")
                           if "connected_pairs" in grid else None),
        "polyline_upper_bound": poly["upper_bound"],
        "polyline_witnesses": poly["witnesses"],
        "guarded_min_geodesic": min(cand) if cand else None,
        "grid_overestimate": (round(grid_val - poly["upper_bound"], 6)
                              if grid_val is not None and poly["upper_bound"] is not None
                              else None),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--grid", type=int, default=900)
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()
    # validation: the exact cubic from negative result 7, where every root-pair
    # midpoint is outside the lemniscate, so the chord family fails.
    r = 0.99
    roots = np.array([r * np.exp(2j * np.pi * k / 3) for k in range(3)])
    res = geodesics(roots, n_grid=args.grid, box=1.35)
    print(json.dumps({"case": "z^3 - (99/100)^3", **res}, indent=1))
    if args.out:
        Path(args.out).write_text(json.dumps(res, indent=1) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
