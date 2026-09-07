#!/usr/bin/env python3
"""Census of rational targets under the canonical Mersenne greedy orbit.

For every reduced target a/b in (0,1) with 2 <= b <= B (odd b, since a
dyadic target is decided by parity arguments), simulate the exact greedy
orbit at fixed dyadic precision and record:

* ``finite`` -- exactly representable by a finite support (detected when
  the residual hits zero; equivalently via the denominator-order theorem);
* ``kill`` -- a fatal rank certified: residual strictly exceeds the
  remaining tail, so the greedy expansion dies;
* ``survive`` -- still alive at the depth cap.

Cross-tabulated against arithmetic features of b: ord_b(2), phi(b),
tau(b), b mod 3, number of prime factors.  The census asks whether deep
survivors concentrate in a recognisable arithmetic class.

Finite evidence only.
"""

from __future__ import annotations

import argparse
import json
import math
from math import gcd


def ord_two_mod(b: int) -> int:
    if b == 1:
        return 1
    x, k = 1 % b, 0
    while True:
        x = (x * 2) % b
        k += 1
        if x == 1:
            return k


def classify(a: int, b: int, depth: int, slack_bits: int = 512) -> str:
    # dyadic denominator -> finite by parity (even numerator check omitted;
    # reduced a/b with even b cannot occur since gcd(a,b)=1 and we skip even b)
    precision = 2 * depth + slack_bits
    scale = 1 << precision
    lower = (scale * a) // b
    upper = (scale * a + b - 1) // b
    for n in range(1, depth + 1):
        if upper <= 0:
            return "finite"
        if lower == upper:
            pass
        wf = scale // ((1 << n) - 1)
        if lower >= wf + 1:
            lower -= wf + 1
            upper -= wf
            if upper <= 0:
                return "finite"
        elif upper <= wf:
            pass
        else:
            return f"ambiguous@{n}"
        # tail bound T_n < 2^{-n} + 2^{-2n}
        cap = (1 << (precision - n)) + (1 << (precision - 2 * n)) \
            if 2 * n + 2 <= precision else 0
        if lower > cap:
            return f"kill@{n}"
    return "survive"


def prime_factors(b: int) -> list[int]:
    fs, d = [], 2
    while d * d <= b:
        while b % d == 0:
            fs.append(d)
            b //= d
        d += 1
    if b > 1:
        fs.append(b)
    return fs


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-b", type=int, default=1000)
    ap.add_argument("--depth", type=int, default=2000)
    args = ap.parse_args()
    rows = []
    counts: dict[str, int] = {}
    for b in range(3, args.max_b + 1, 2):
        order = ord_two_mod(b)
        phi = b
        for p in set(prime_factors(b)):
            phi -= phi // p
        tau = 1
        for p in set(prime_factors(b)):
            e = 0
            bb = b
            while bb % p == 0:
                bb //= p
                e += 1
            tau *= e + 1
        for a in range(1, b, 2):
            if gcd(a, b) != 1 or a / b >= 1.0:
                continue
            res = classify(a, b, args.depth)
            counts[res] = counts.get(res, 0) + 1
            if res.startswith("survive") or res.startswith("ambiguous"):
                rows.append({
                    "target": f"{a}/{b}", "ord": order, "phi": phi,
                    "tau": tau, "bmod3": b % 3,
                    "primes": sorted(set(prime_factors(b))),
                    "status": res,
                })
            elif res.startswith("kill"):
                counts.setdefault("kill_max_rank", 0)
                kr = int(res.split("@")[1])
                if kr > counts["kill_max_rank"]:
                    counts["kill_max_rank"] = kr
    out = {
        "params": {"max_b": args.max_b, "depth": args.depth},
        "counts": counts,
        "survivors_and_ambiguities": rows,
    }
    text = json.dumps(out, indent=1)
    print(text)


if __name__ == "__main__":
    main()
