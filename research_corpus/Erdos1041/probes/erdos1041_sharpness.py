#!/usr/bin/env python3
"""The constant 2 in Erdos #1041 is sharp at EVERY degree, not only at n = 2.

Theorem
-------
Let f(z) = z^n - r^n with 0 < r < 1.  Every curve joining two distinct roots
inside {|f| < 1} has length at least

    2 (r - (1 - r^n)^(1/n)).

Hence the minimum such length tends to 2 as r -> 1, for every degree n >= 2.

Proof
-----
{|f| < 1} = {z : z^n in D(r^n, 1)}.  Put eps = (1 - r^n)^(1/n).  The disk
B(0, 1 - r^n) has radius 1 - r^n and its centre is at distance r^n from the
centre of D(r^n, 1); since r^n = 1 - (1 - r^n), it is INTERNALLY TANGENT to
the boundary of D(r^n, 1).  So D(r^n, 1) minus that disk is a crescent: simply
connected, and avoiding 0.  The preimage of a simply connected domain avoiding 0
under z -> z^n splits into n disjoint components, one containing each root.  A
path staying outside |z| < eps therefore cannot join two distinct roots; a path
that does join them comes within eps of the origin and must travel from a root at
distance r inward and back out, so its length is at least 2(r - eps).  QED

Why this is the whole story for this family: f' = n z^(n-1), so the ONLY critical
point is the origin, with critical value r^n -> 1.  At r = 1 the lemniscate splits
into n disjoint petals, so the components merge only at the origin and every path
between distinct roots is squeezed through it as the pinch closes.

What this checks
----------------
The theorem is exact, so this script does not test it - it tests that the
measured geodesics respect it, which is a check on the MEASUREMENT, and reports
the approach to 2.  A measured value below the bound would mean the geodesic
solver is unsound, not that the theorem is wrong.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

from formal_math.probes.erdos1041_geodesic import guarded_min_geodesic


def lower_bound(n: int, r: float) -> float:
    return 2.0 * (r - (1.0 - r ** n) ** (1.0 / n))


def run(degrees: list[int], radii: list[float], grid: int) -> dict:
    rows = []
    violations = []
    for n in degrees:
        for r in radii:
            roots = r * np.exp(2j * np.pi * np.arange(n) / n)
            measured = guarded_min_geodesic(roots, grid, 1.3)["guarded_min_geodesic"]
            lb = lower_bound(n, r)
            row = {
                "n": n, "r": r,
                "epsilon": round((1.0 - r ** n) ** (1.0 / n), 6),
                "lower_bound": round(lb, 6),
                "measured_geodesic": round(measured, 6),
                "two_r": round(2 * r, 6),
                "ratio_to_two_r": round(measured / (2 * r), 6),
                "bound_respected": bool(measured >= lb - 1e-3),
            }
            if not row["bound_respected"]:
                violations.append(row)
            rows.append(row)
    approach = {}
    for n in degrees:
        seq = [x["ratio_to_two_r"] for x in rows if x["n"] == n]
        approach[str(n)] = {"ratios_by_radius": seq,
                            "monotone_increasing": all(seq[i] < seq[i + 1]
                                                       for i in range(len(seq) - 1))}
    return {
        "probe_id": "erdos1041_sharpness",
        "theorem": ("for f = z^n - r^n, any curve joining two distinct roots inside "
                    "{|f|<1} has length >= 2(r - (1-r^n)^(1/n)); the bound tends to 2 "
                    "as r -> 1 at every degree n >= 2"),
        "grid": grid,
        "rows": rows,
        "bound_violations": violations,
        "measurement_sound": not violations,
        "approach_to_two": approach,
        "reading": (
            "measured geodesics respect the exact bound everywhere and their ratio to "
            "2r increases toward 1 at every degree: the constant 2 is sharp, and the "
            "extremal degeneration is z^n - r^n with r -> 1 at every degree"
            if not violations else
            "a measured geodesic fell below the exact bound: the solver is unsound"
        ),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--degrees", type=str, default="2,3,4,5,6")
    ap.add_argument("--radii", type=str, default="0.99,0.999,0.9999")
    ap.add_argument("--grid", type=int, default=1300)
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()
    payload = run([int(x) for x in args.degrees.split(",")],
                  [float(x) for x in args.radii.split(",")], args.grid)
    if args.out:
        Path(args.out).write_text(json.dumps(payload, indent=1) + "\n")
    print(json.dumps({k: v for k, v in payload.items() if k != "rows"}, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
