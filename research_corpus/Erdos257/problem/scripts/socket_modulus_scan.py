#!/usr/bin/env python3
"""Modulus-scan probe for the (B') sparse socket.

For each R = 3a+1, find the small moduli M for which
   sum_{d in D} W_d = 4Q_R - 2^(R+1)  (mod M)
has no subset solution with x_d = 0 for d | (2R+3) and at most one selected
d | (2R+4).  A uniform family of such M would be the cheapest possible
certificate for the socket exclusion and the natural target for a proof.
"""

import argparse
import json
from pathlib import Path


def weight(R, d):
    q = (1 << (2 * R)) // ((1 << d) - 1)
    w = 4 * q
    if (2 * R + 1) % d == 0:
        w += 2
    if (2 * R + 2) % d == 0:
        w += 1
    return w


def solvable_mod(R, M):
    """DP over residues mod M with capped-count dimension (<=1)."""
    target = (4 * ((1 << (2 * R)) // 21) - (1 << (R + 1))) % M
    forbid = {d for d in range(2, R + 1) if (2 * R + 3) % d == 0}
    capped = {d for d in range(2, R + 1) if (2 * R + 4) % d == 0}
    ws = []
    for d in range(2, R + 1):
        if d in forbid:
            continue
        ws.append((weight(R, d) % M, 1 if d in capped else 0))
    # reachable[c] = set of residues achievable with exactly-capped c in {0,1}
    reach = [set() for _ in range(2)]
    reach[0].add(0)
    for w, c in ws:
        nxt = [set(reach[0]), set(reach[1])]
        for src in (0, 1):
            dst = src + c
            if dst > 1:
                continue
            for r in reach[src]:
                nxt[dst].add((r + w) % M)
        reach = nxt
        if not reach[0] and not reach[1]:
            return False
    return target in reach[0] or target in reach[1]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--r-max", type=int, default=100)
    ap.add_argument("--max-m", type=int, default=200)
    args = ap.parse_args()
    out_rows = []
    for R in range(4, args.r_max + 1, 3):
        killers = []
        for M in list(range(2, args.max_m + 1)):
            if not solvable_mod(R, M):
                killers.append(M)
                if len(killers) >= 8:
                    break
        n_cap = sum(1 for d in range(2, R + 1) if (2 * R + 4) % d == 0)
        n_forb = sum(1 for d in range(2, R + 1) if (2 * R + 3) % d == 0)
        out_rows.append({"R": R, "first_killer_moduli": killers,
                         "n_capped": n_cap, "n_forbidden": n_forb})
        print(json.dumps(out_rows[-1]), flush=True)
    receipt = {"schema": "erdos257_socket_modulus_scan/1",
               "rows": out_rows}
    out = Path("state/formal_math/erdos257_period_noncollapse/"
               "backward_forced_suffix_modulus_scan_receipt.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
