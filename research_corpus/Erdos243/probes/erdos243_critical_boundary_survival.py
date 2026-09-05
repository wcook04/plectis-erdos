#!/usr/bin/env python3
"""How deep can a non-Sylvester orbit survive at Erdos #243's critical boundary?

Upstream analytic state
-----------------------
#243 asks: if a_(n+1)/a_n^2 -> 1 and sum 1/a_n is rational, must the sequence be
eventually Sylvester, a_(n+1) = a_n^2 - a_n + 1?  Lean has the finite-mass branch
and `gap_product_criterion` (eventual Sylvester is equivalent to eventual
nonnegativity of the normalised gap-product state).  The open producer
`critical_boundary` is stated in one line: "Resolve the boundary
n*(a_n^2/a_(n+1) - 1)_+ approximately 1."  It has no computational coverage.

The exact dynamics
------------------
Write the remaining tail as a reduced fraction u/v.  Taking the next term
a = ceil(v/u) + k for an integer k >= 0 gives

    u' = u*a - v = rho + k*u,     rho = (-v) mod u,      v' = v*a.

So k = 0 is the greedy step, which strictly decreases the numerator and
therefore terminates; an infinite rational-sum sequence must take k >= 1
infinitely often, and Sylvester is exactly the k that keeps u' = u.

Since a_(n+1) is about v_n/u_n, the ratio a_(n+2)/a_(n+1)^2 is about u_n/u_(n+1),
so the hypothesis a_(n+1)/a_n^2 -> 1 is the statement that the numerator
sequence varies slowly.  With u' = rho + k*u that forces, at every single step,
rho to sit within o(u) of 0 or of u -- a congruence condition on v modulo u.

Probe
-----
Search the tree of admissible k at each step under the one-sided boundary
constraint n*(a_n^2/a_(n+1) - 1)_+ <= C, and measure how deep a path can go
while taking at least one non-Sylvester step.

Predeclared falsifier
---------------------
A non-Sylvester path that survives to the depth cap would mean the boundary
constraint does not by itself force Sylvester, and the producer needs more than
this.  Survival depths that stay bounded, and grow only slowly in C, instead say
the constraint bites immediately and locate the boundary quantitatively.
"""

from __future__ import annotations

import argparse
import json
from math import gcd
from pathlib import Path


def sylvester_next(a: int) -> int:
    return a * a - a + 1


def search(u0: int, v0: int, a0: int, boundary_c: float, max_depth: int,
           max_k: int, node_cap: int = 300_000) -> dict:
    """Deepest survival of a path that is non-Sylvester at least once.

    The hypothesis a_(n+1)/a_n^2 -> 1 is TWO-sided.  The producer states the
    boundary through the positive part (a_n^2/a_(n+1) - 1)_+, but for a search
    over larger next terms the binding side is the other one, so the constraint
    applied here is |a_(n+1)/a_n^2 - 1| <= C/n, which implies the producer's
    one-sided form.
    """
    best_depth = 0
    best_path: list[int] = []
    best_first_deviation = None
    nodes = 0
    capped = False

    def walk(u: int, v: int, a_prev: int, depth: int, path: list[int],
             first_dev: int | None) -> None:
        nonlocal best_depth, best_path, best_first_deviation, nodes, capped
        nodes += 1
        if nodes > node_cap:
            capped = True
            return
        if first_dev is not None and depth - first_dev > best_depth:
            # The quantity that matters is how long a path lives AFTER its first
            # non-Sylvester step, not how deep it got before taking one.
            best_depth, best_path = depth - first_dev, list(path)
            best_first_deviation = first_dev
        if depth >= max_depth or u == 0:
            return
        base = -(-v // u)                       # ceil(v/u)
        syl = sylvester_next(a_prev)
        for k in range(0, max_k + 1):
            a = base + k
            if a <= a_prev:
                continue
            ratio = a / (a_prev * a_prev)
            if abs(ratio - 1.0) * (depth + 1) > boundary_c:
                continue
            nu = u * a - v
            if nu <= 0:                          # 0 terminates, negative is illegal
                continue
            nv = v * a
            g = gcd(nu, nv)
            if g > 1:
                nu, nv = nu // g, nv // g
            if nv.bit_length() > 200_000:
                continue
            path.append(a)
            walk(nu, nv, a, depth + 1, path,
                 first_dev if first_dev is not None else (None if a == syl else depth + 1))
            path.pop()

    walk(u0, v0, a0, 0, [], None)
    return {
        "max_steps_survived_after_first_deviation": best_depth,
        "first_deviation_depth": best_first_deviation,
        "best_path_terms": [str(t) if t < 10 ** 18 else f"~10^{len(str(t))-1}"
                            for t in best_path[:10]],
        "nodes_visited": nodes,
        "node_cap_hit": capped,
    }


def run(boundary_values: list[float], max_depth: int, max_k: int) -> dict:
    # Start on the Sylvester orbit: after 2, 3, 7 the tail is 1/42, i.e. u/v = 1/42,
    # with the last term 7.  Every infinite continuation of a rational tail lives here.
    rows = []
    for c in boundary_values:
        res = search(1, 42, 7, c, max_depth, max_k)
        rows.append({"boundary_C": c, **res})
    depths = [r["max_steps_survived_after_first_deviation"] for r in rows]
    return {
        "probe_id": "erdos243_critical_boundary_survival",
        "start_state": {"u": 1, "v": 42, "last_term": 7,
                        "meaning": "tail after the Sylvester prefix 2, 3, 7"},
        "max_depth_cap": max_depth,
        "max_k": max_k,
        "per_boundary": rows,
        "max_steps_survived_after_first_deviation": max(depths),
        "node_cap_hit_at": [r["boundary_C"] for r in rows if r["node_cap_hit"]],
        "reading": (
            f"no non-Sylvester step survives more than {max(depths)} further step(s) at "
            "any tested boundary constant: the two-sided boundary constraint kills a "
            "deviation almost immediately"
            if max(depths) <= 2 else
            f"a deviation survives up to {max(depths)} further steps; the boundary "
            "constraint alone does not force Sylvester quickly"
        ),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--boundaries", type=str, default="0.5,1,2,4,8,16,32")
    ap.add_argument("--max-depth", type=int, default=14)
    ap.add_argument("--max-k", type=int, default=6)
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()
    payload = run([float(x) for x in args.boundaries.split(",")],
                  args.max_depth, args.max_k)
    if args.out:
        Path(args.out).write_text(json.dumps(payload, indent=1) + "\n")
    print(json.dumps(payload, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
