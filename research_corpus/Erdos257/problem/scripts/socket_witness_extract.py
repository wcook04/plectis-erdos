#!/usr/bin/env python3
"""Witness extraction for the relaxed sparse-socket equations.

For each probed half-depth R, find actual Boolean solutions of the socket
row equation modulo 2^B WITHOUT the cap clause (pulse forbids kept), and
report which structural families the selected supports draw from:
endpoint divisors, near-top multiples, and the induced tau_D profile on the
top window.
"""

import argparse
import json
import sys
from pathlib import Path

sys.setrecursionlimit(100000)


def weight(R, d):
    q = (1 << (2 * R)) // ((1 << d) - 1)
    w = 4 * q
    if (2 * R + 1) % d == 0:
        w += 2
    if (2 * R + 2) % d == 0:
        w += 1
    return w


def build(R, socket):
    if socket == "S":
        target = (1 << (2 * R)) // 21 - (1 << R)
        forbid = {d for d in range(2, R + 1) if (2 * R + 1) % d == 0}
        capped = {d for d in range(2, R + 1) if (2 * R + 2) % d == 0}
        weights = {}
        for d in range(2, R + 1):
            if d in forbid:
                continue
            w = (1 << (2 * R)) // ((1 << d) - 1)
            if w:
                weights[d] = w
    else:
        target = 4 * ((1 << (2 * R)) // 21) - (1 << (R + 1))
        forbid = {d for d in range(2, R + 1) if (2 * R + 3) % d == 0}
        capped = {d for d in range(2, R + 1) if (2 * R + 4) % d == 0}
        weights = {}
        for d in range(2, R + 1):
            if d in forbid:
                continue
            w = weight(R, d)
            if w:
                weights[d] = w
    return target, sorted(weights), weights, sorted(capped)


def find_witness(R, B, socket, want=6):
    """DFS over bit-reveal with parent tracking; returns up to `want` witnesses."""
    target, ds, weights, capped = build(R, socket)
    mask = (1 << B) - 1
    tlow = target & mask
    levels = {}
    for d in ds:
        e = (weights[d] & -weights[d]).bit_length() - 1
        if e < B:
            levels.setdefault(e, []).append(d)
    keys = sorted(levels)
    witnesses = []

    # per-level deduplicated pair frontier with back-pointers
    def level_pairs(b):
        pool = levels[b]
        pairs = {(0, 0): ()}
        for d in pool:
            w = weights[d] & mask
            new = dict(pairs)
            for (s, c), sel in pairs.items():
                k2 = ((s + w) & mask, c + (1 if d in capped_set else 0))
                if k2 not in new:
                    new[k2] = sel + (d,)
            pairs = new
        return [(s, c, sel) for (s, c), sel in pairs.items()]

    capped_set = set(capped)

    pair_cache = {}

    def dfs(i, states):
        if len(witnesses) >= want:
            return
        if i == len(keys):
            for (p, c), path in states.items():
                if p == tlow:
                    witnesses.append((list(path), c))
                    if len(witnesses) >= want:
                        return
            return
        b = keys[i]
        if b not in pair_cache:
            pair_cache[b] = level_pairs(b)
        pairs = pair_cache[b]
        nxt = {}
        for (p, _c), _path in states.items():
            need = ((tlow - p) >> b) & 1
            for (s, c2, sel) in pairs:
                if (s >> b) & 1 == need:
                    np_ = (p + s) & mask
                    key = (np_, c2)
                    # keep one path per state (witness diversity via states)
                    if key not in nxt:
                        nxt[key] = sel
        # explore a bounded number of successor branches for diversity
        items = list(nxt.items())
        for key, sel in items[:24]:
            dfs(i + 1, {key: (sel, key[1])})
            if len(witnesses) >= want:
                return

    dfs(0, {(0, 0): ()})
    out = []
    for sel, cap in witnesses:
        S = set(sel)
        ep2 = sorted(d for d in S if d in set(capped))
        top_hits = sorted((k for k in range(max(1, (1 << 20)), 0)), reverse=True)[:0]
        # tau_D profile near top window
        prof = {}
        for k in range(2 * R - 24, 2 * R):
            prof[k] = sum(1 for d in S if k % d == 0 and d <= R)
        out.append({
            "size": len(S),
            "support": sel,
            "capped_used": ep2,
            "n_capped": len(ep2),
            "top_window_tau": {str(k): v for k, v in prof.items() if v},
        })
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--r-list", type=str, default="22,23,26,34")
    ap.add_argument("--socket", choices=["S", "B", "both"], default="both")
    ap.add_argument("--bits", type=int, default=48)
    args = ap.parse_args()
    rows = []
    for tok in args.r_list.split(","):
        R = int(tok)
        sockets = ["S", "B"] if args.socket == "both" else [args.socket]
        for sc in sockets:
            if sc == "S" and R % 3 != 2:
                continue
            if sc == "B" and R % 3 != 1:
                continue
            ws = find_witness(R, args.bits, sc)
            for w in ws:
                w["R"] = R
                w["socket"] = sc
                rows.append(w)
                print(json.dumps(w), flush=True)
    receipt = {"schema": "erdos257_socket_witnesses/1", "rows": rows}
    out = Path("state/formal_math/erdos257_period_noncollapse/"
               "backward_forced_suffix_witnesses_receipt.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
