#!/usr/bin/env python3
"""Survival cost of the pseudo-greedy orbit (Erdos #243, strong form).

Every finite error prefix is realizable by some residue class of D_0, so no
finite obstruction exists in the profinite completion; the parent theorem is
a statement about INTEGER points.  The quantity that measures that is the
cost of survival

    g(L) = min { D_0 : the orbit of some (C_0, D_0), gcd = 1, C_0 < D_0,
                 survives >= L steps without E = 0 }.

The strong form (every rational terminates) is exactly g(L) -> infinity, and a
proof would be a lower bound g(L) >= h(L).  This probe measures g(L) over all
p/q with q <= qmax, records the witness orbit for each L, and classifies each
witness as lattice-type (|E_n| <= 2 on at least 80% of its steps, the regime
the corpus has Lean-closed) or generic.  It also reports, for the longest
survivors, the normalised error profile |E_n|/C_n, i.e. how far any long
survivor is from the Erdos regime |E_n|/C_n -> 0.

Usage:
    ./repo-python .../erdos243_survival_cost_probe.py --qmax 3000 [--quick] [--json out.json]
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from math import gcd
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from erdos243_orbit_engine import run_orbit  # noqa: E402


def classify(Es):
    body = [abs(e) for e in Es if e != 0]
    if not body:
        return "trivial"
    small = sum(1 for m in body if m <= 2)
    return "lattice" if small >= 0.8 * len(body) else "generic"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--qmax", type=int, default=3000)
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--json", default="")
    ap.add_argument("--top", type=int, default=12)
    args = ap.parse_args()
    qmax = 400 if args.quick else args.qmax

    t0 = time.time()
    best = {}  # L -> (D0, C0, Es)
    hist = {}
    longest = []
    orbits = 0
    for q in range(2, qmax + 1):
        for p in range(1, q):
            if gcd(p, q) != 1:
                continue
            orbits += 1
            r = run_orbit(p, q, step_cap=200, height_cap=10 ** 9)
            Es = r["E"]
            if r["status"] != "terminated":
                L = r["steps"] + 1
            else:
                L = len(Es) - 1  # steps survived before the terminating E = 0
            hist[L] = hist.get(L, 0) + 1
            if L not in best or q < best[L][0]:
                best[L] = (q, p, Es, r["C"])
            if L >= 12:
                longest.append((L, q, p, Es, r["C"]))

    rows = []
    for L in sorted(best):
        q, p, Es, Cs = best[L]
        rows.append({
            "L": L, "min_D0": q, "C0": p, "count_at_L": hist[L],
            "class": classify(Es),
            "max_abs_E": max((abs(e) for e in Es), default=0),
            "E_profile": Es[:40],
            "C_profile": Cs[:40],
        })
    # cumulative: minimal q surviving AT LEAST L
    g = {}
    cur = None
    for L in sorted(best, reverse=True):
        q = best[L][0]
        cur = q if cur is None else min(cur, q)
        g[L] = cur
    longest.sort(key=lambda t: (-t[0], t[1]))
    long_rows = []
    for L, q, p, Es, Cs in longest[: args.top]:
        norm = [round(abs(e) / c, 4) for e, c in zip(Es, Cs)]
        long_rows.append({"L": L, "q": q, "p": p, "class": classify(Es), "E": Es, "C": Cs, "absE_over_C": norm})
    out = {
        "qmax": qmax, "orbits": orbits, "wall_s": round(time.time() - t0, 1),
        "g_at_least_L": {str(k): v for k, v in sorted(g.items())},
        "witness_rows": rows, "longest": long_rows,
        "status": "pass",
    }
    if args.json:
        Path(args.json).write_text(json.dumps(out, indent=1))
    print(json.dumps({"qmax": qmax, "orbits": orbits, "wall_s": out["wall_s"],
                      "g_at_least_L": out["g_at_least_L"],
                      "classes_at_top": [(r["L"], r["min_D0"], r["class"], r["max_abs_E"]) for r in rows[-8:]]}))


if __name__ == "__main__":
    main()
