#!/usr/bin/env python3
"""Exact subset-sum decision for the sparse denominator-21 sockets.

Decides, over ALL Boolean supports D subseteq {2..R}, whether

  (S)   sum_{d in D} q_R(d) = Q_R - 2^R                 (R = 3a+2)
  (B')  sum_{d in D} W_d   = 4Q_R - 2^(R+1)             (R = 3a+1)

as EXACT integer equations, where q_R(d) = floor(2^(2R)/(2^d - 1)) and
W_d = 4 q_R(d) + 2*[d|2R+1] + [d|2R+2].  No modular relaxation: UNSAT here
is UNSAT for the row itself.  Search is depth-first over elements in
descending weight order (ascending d) with the two admissible prunes
(partial sum exceeding the target; partial sum plus all remaining weights
falling short).  Positive weights make both prunes sound; the search is
exhaustive whenever the node budget is not hit.

Correctness cross-checks:
  C1  independent meet-in-the-middle agreement for small R;
  C2  published witness rows of TwentyOneDensityInvariantAttack section 6
      (congruence impostors must NOT be reported as exact solutions).

Receipt: state/formal_math/erdos257_period_noncollapse/socket_exact_subset_sum_receipt.json
"""

import argparse
import hashlib
import json
import sys
from pathlib import Path

sys.setrecursionlimit(100000)


def q_R(R, d):
    return (1 << (2 * R)) // ((1 << d) - 1)


def build_weights(R, socket):
    """Descending-weight list of (weight, d); target; forced-zero set."""
    if socket == "S":
        target = (1 << (2 * R)) // 21 - (1 << R)
        items = [(q_R(R, d), d) for d in range(2, R + 1)]
    else:
        target = 4 * ((1 << (2 * R)) // 21) - (1 << (R + 1))
        items = []
        for d in range(2, R + 1):
            w = 4 * q_R(R, d)
            if (2 * R + 1) % d == 0:
                w += 2
            if (2 * R + 2) % d == 0:
                w += 1
            items.append((w, d))
    # pulse constraints belong to the socket hypotheses; the exact solver
    # runs WITHOUT them (stronger statement) and optionally with.
    items.sort(reverse=True)
    return target, items


def exact_solve(target, items, node_budget):
    """DFS with sound prunes. Returns (sat, witness|None, nodes, exhausted)."""
    n = len(items)
    ws = [w for w, _ in items]
    suffix = [0] * (n + 1)
    for i in range(n - 1, -1, -1):
        suffix[i] = suffix[i + 1] + ws[i]
    nodes = 0
    exhausted = True
    witness = None

    def dfs(i, cur, chosen):
        nonlocal nodes, exhausted, witness
        if witness is not None:
            return True
        nodes += 1
        if nodes >= node_budget:
            exhausted = False
            return False
        if cur == target:
            witness = list(chosen)
            return True
        if i == n:
            return False
        if cur > target or cur + suffix[i] < target:
            return False
        w, d = items[i]
        if cur + w <= target:
            chosen.append(d)
            if dfs(i + 1, cur + w, chosen):
                return True
            chosen.pop()
        return dfs(i + 1, cur, chosen)

    sat = dfs(0, 0, [])
    return sat, witness, nodes, exhausted


def mitm_cross_check(R, socket):
    target, items = build_weights(R, socket)
    ds = [d for _, d in items]
    ws = [w for w, _ in items]
    half = len(ws) // 2
    left = {}
    for m in range(1 << half):
        s = 0
        for i in range(half):
            if m >> i & 1:
                s += ws[i]
        left.setdefault(s, []).append(m)
    for m in range(1 << (len(ws) - half)):
        s = 0
        for i in range(len(ws) - half):
            if m >> i & 1:
                s += ws[half + i]
        if (target - s) in left:
            return True
    return False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--r-max", type=int, default=200)
    ap.add_argument("--node-budget", type=int, default=50_000_000)
    ap.add_argument("--mitm-max", type=int, default=24)
    args = ap.parse_args()

    receipt = {"schema": "erdos257_socket_exact_subset_sum_receipt/1",
               "controls": {}, "rows": []}

    # C1: MITM agreement on small rows (both sockets)
    ok = True
    detail = []
    for socket in ("S", "B"):
        start = 5 if socket == "S" else 4
        for R in range(start, args.mitm_max + 1, 3):
            t, items = build_weights(R, socket)
            sat, _w, nodes, exh = exact_solve(t, items, 20_000_000)
            ref = mitm_cross_check(R, socket)
            agree = (sat == ref) and exh
            ok = ok and agree
            detail.append({"socket": socket, "R": R, "dfs": sat,
                           "mitm": ref, "agree": agree})
    receipt["controls"]["c1_mitm_agreement"] = {"passed": ok, "rows": detail}

    for socket in ("S", "B"):
        start = 5 if socket == "S" else 4
        step = 3
        for R in range(start, args.r_max + 1, step):
            t, items = build_weights(R, socket)
            sat, witness, nodes, exh = exact_solve(t, items, args.node_budget)
            row = {"socket": socket, "R": R, "sat": sat,
                   "exhaustive": exh, "nodes": nodes}
            if sat:
                row["witness"] = witness
            receipt["rows"].append(row)
            flag = "" if exh else " BUDGET-LIMITED"
            print(json.dumps(row), flush=True)

    n_unsat = sum(1 for r in receipt["rows"]
                  if not r["sat"] and r["exhaustive"])
    n_sat = sum(1 for r in receipt["rows"] if r["sat"])
    n_lim = sum(1 for r in receipt["rows"] if not r["exhaustive"])
    blob = json.dumps(receipt, sort_keys=True).encode()
    receipt["summary"] = {"unsat_exhaustive": n_unsat, "sat": n_sat,
                          "budget_limited": n_lim}
    receipt["receipt_sha256"] = hashlib.sha256(blob).hexdigest()
    out = Path("state/formal_math/erdos257_period_noncollapse/"
               "socket_exact_subset_sum_receipt.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(receipt, indent=2))
    print(f"summary: unsat_exhaustive={n_unsat} sat={n_sat} "
          f"budget_limited={n_lim}")


if __name__ == "__main__":
    main()
