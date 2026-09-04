#!/usr/bin/env python3
"""Is the Erdos #1041 geodesic bounded by twice the largest root modulus?

The conjecture
--------------
    min over root pairs of the geodesic inside {|f|<1}  <=  2 * max_i |z_i|.

If true this PROVES Erdos #1041 immediately, since all roots lie in the open unit
disk and so max_i |z_i| < 1.

It is exactly tight on the extremal family: for f = z^n - r^n every root has
modulus r, the two radii through the origin form an interior path of length 2r,
and the sharpness theorem shows no shorter one survives as r -> 1.  So the
conjecture cannot be improved, which is the property a proof of a sharp statement
has to have.

It also survives the configuration that killed the origin-spoke family: there the
geodesic is 0.061 against 2 max|z_i| ~ 2, so a failure of the origin route is not
a failure of the bound.

Probe
-----
Measure the ratio geodesic / (2 max|z_i|) on the refuting configurations, the
extremal family, random configurations, and an optimiser trying to drive the
ratio above 1.  Every geodesic is the guarded value - capped by an exactly
verified interior polyline - so the ratio can only be overestimated, which is the
safe direction for testing an upper-bound conjecture.

Predeclared falsifier
---------------------
A configuration with ratio reproducibly above 1 refutes the conjecture, and its
structure names what the true bound must include.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

from formal_math.probes.erdos1041_geodesic import (
    geodesics,
    guarded_min_geodesic,
    polyline_upper_bound,
)


def ratio(roots: np.ndarray, grid: int, box: float = 1.4) -> float:
    g = guarded_min_geodesic(roots, grid, box)["guarded_min_geodesic"]
    if g is None:
        return -1.0
    return float(g) / (2.0 * float(np.max(np.abs(roots))))


def stronger_forms(roots: np.ndarray, grid: int, box: float = 1.4) -> dict:
    """Two sharper statements, each of which also implies Erdos 1041.

    A : some pair has geodesic(a,b) <= |z_a| + |z_b|, the length of the broken
        line through the origin - without requiring that broken line to be the
        path taken.
    A': some pair has BOTH radial segments [0,z_a] and [0,z_b] interior, so the
        origin route itself works.  The packet's five-root negative result says
        this can fail, and it is included to keep the distinction visible.
    """
    res = geodesics(roots, n_grid=grid, box=box)
    mods = np.abs(roots)
    poly = polyline_upper_bound(roots)
    # Cap EACH PAIR by its own exactly verified polyline before comparing.  Using
    # the raw grid value here reintroduces the thin-corridor overestimate: at
    # n = 2 the geodesic IS the chord, so the true slack is exactly 0, and a few
    # thousandths of grid error flips the comparison the wrong way.
    per_pair = {}
    for w in poly["witnesses"]:
        key = (w["i"], w["j"])
        per_pair[key] = min(per_pair.get(key, float("inf")), w["length"])
    best_slack = None
    for p_ in res.get("pairs", []):
        g = p_["geodesic"]
        cap = per_pair.get((p_["i"], p_["j"]))
        vals = [v for v in (g, cap) if v is not None]
        if not vals:
            continue
        slack = min(vals) - (mods[p_["i"]] + mods[p_["j"]])
        best_slack = slack if best_slack is None else min(best_slack, slack)
    origin_pairs = sum(1 for w in poly["witnesses"] if w["via"] == "origin")
    return {
        "form_A_best_slack": None if best_slack is None else round(float(best_slack), 6),
        "form_A_holds": None if best_slack is None else bool(best_slack <= 1e-3),
        "form_A_prime_origin_routes_found": origin_pairs,
        "two_smallest_moduli_sum": round(float(np.sum(np.sort(mods)[:2])), 6),
        "min_geodesic": res.get("min_geodesic"),
    }


def named_cases() -> dict:
    r = 99999 / 100000
    out = {
        "cubic_kills_chords": np.array([0.99 * np.exp(2j * np.pi * k / 3)
                                        for k in range(3)]),
        "five_root_kills_origin_spokes": np.array(
            [r + 0j, r * complex(-20, 99) / 101, r * complex(-20, -99) / 101,
             r * complex(-28, 195) / 197, r * complex(-28, -195) / 197]),
    }
    for n in (2, 3, 4, 5, 6):
        for rr in (0.9, 0.99, 0.999):
            out[f"extremal_z^{n}-{rr}^{n}"] = rr * np.exp(2j * np.pi * np.arange(n) / n)
    return out


def run(grid: int, restarts: int, steps: int, max_n: int, seed: int) -> dict:
    rows = []
    for name, roots in named_cases().items():
        row = {"case": name, "n": len(roots),
               "max_modulus": round(float(np.max(np.abs(roots))), 6),
               "ratio": round(ratio(roots, grid), 6)}
        row.update(stronger_forms(roots, grid))
        rows.append(row)

    rng = np.random.default_rng(seed)
    best = {"ratio": -1.0, "roots": None, "n": None}
    for n in range(2, max_n + 1):
        for _ in range(restarts):
            roots = 0.999 * rng.uniform(0.3, 1.0, n) * np.exp(
                1j * rng.uniform(0, 2 * np.pi, n))
            val = ratio(roots, grid)
            sigma = 0.18
            for _ in range(steps):
                cand = roots + rng.normal(0, sigma, n) + 1j * rng.normal(0, sigma, n)
                m = np.abs(cand)
                cand = np.where(m > 0.999, cand / m * 0.999, cand)
                cval = ratio(cand, grid)
                if cval > val:
                    roots, val = cand, cval
                sigma *= 0.93
            if val > best["ratio"]:
                best = {"ratio": round(val, 6), "n": n,
                        "roots": [[round(float(z.real), 6), round(float(z.imag), 6)]
                                  for z in roots]}
    all_ratios = [r["ratio"] for r in rows] + [best["ratio"]]
    return {
        "probe_id": "erdos1041_radius_bound",
        "conjecture": "min pairwise geodesic <= 2 * max_i |z_i|, which implies Erdos 1041",
        "named_cases": rows,
        "search_best": best,
        "max_ratio_seen": round(max(all_ratios), 6),
        "form_A_failures": [r["case"] for r in rows if r.get("form_A_holds") is False],
        "form_A_min_slack": min((r["form_A_best_slack"] for r in rows
                                 if r.get("form_A_best_slack") is not None), default=None),
        "any_ratio_above_one": bool(max(all_ratios) > 1.0),
        "reading": (
            "a configuration exceeds the bound: the conjecture is refuted and its "
            "structure names what a true bound must include"
            if max(all_ratios) > 1.0 else
            "no configuration exceeds the bound; it is tight on the extremal family, "
            "so it is a sharp conjecture that would imply Erdos 1041"
        ),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--grid", type=int, default=700)
    ap.add_argument("--restarts", type=int, default=3)
    ap.add_argument("--steps", type=int, default=18)
    ap.add_argument("--max-n", type=int, default=6)
    ap.add_argument("--seed", type=int, default=20260823)
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()
    payload = run(args.grid, args.restarts, args.steps, args.max_n, args.seed)
    if args.out:
        Path(args.out).write_text(json.dumps(payload, indent=1) + "\n")
    print(json.dumps({k: v for k, v in payload.items() if k != "named_cases"}, indent=1))
    for r in payload["named_cases"]:
        print("  %-32s n=%d  max|z|=%.4f  ratio=%.5f" % (r["case"], r["n"],
                                                          r["max_modulus"], r["ratio"]))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
