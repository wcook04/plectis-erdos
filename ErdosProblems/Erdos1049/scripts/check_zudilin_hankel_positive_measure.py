#!/usr/bin/env python3
"""Finite check of the 2016 generating-function identity v_m = P^4 G_q(q^{m+1}).

This is a truncated real-arithmetic safeguard against a transcription error in
the positive-measure note.  It does not prove Theorem A, the O_q(N) residual,
or any irrationality statement.
"""

from __future__ import annotations

import argparse
import math


def pochhammer(z: float, q: float, m: int) -> float:
    acc = 1.0
    for r in range(m):
        acc *= 1.0 - z * q**r
        if acc == 0.0:
            return 0.0
    return acc


def pochhammer_inf(z: float, q: float, depth: int) -> float:
    acc = 1.0
    for r in range(depth):
        acc *= 1.0 - z * q**r
    return acc


def v_row(m: int, q: float, t_max: int) -> float:
    qq_m = pochhammer(q, q, m)
    acc = 0.0
    for t in range(t_max + 1):
        num = pochhammer(q ** (t + 1), q, m)
        den = pochhammer(q ** (m + t + 1), q, m + 1)
        acc += (q ** ((m + 1) * t)) * num / den
    return (qq_m**3) * acc


def G_q(w: float, q: float, t_max: int, depth: int) -> float:
    acc = 0.0
    for t in range(t_max + 1):
        qq_t = pochhammer(q, q, t)
        num = pochhammer_inf((q**t) * (w**2), q, depth)
        den = pochhammer_inf((q**t) * w, q, depth) ** 2
        acc += (w**t / qq_t) * num / den
    return acc / (pochhammer_inf(w, q, depth) ** 3)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--q", type=float, default=2.0 / 3.0)
    parser.add_argument("--t-max", type=int, default=40)
    parser.add_argument("--depth", type=int, default=80)
    parser.add_argument("--rel-tol", type=float, default=1e-10)
    args = parser.parse_args()
    q = args.q
    P = pochhammer_inf(q, q, args.depth)
    print(f"q={q} P≈{P}")
    worst = 0.0
    for m in (0, 1, 2, 5, 10):
        lhs = v_row(m, q, args.t_max)
        rhs = (P**4) * G_q(q ** (m + 1), q, args.t_max, args.depth)
        rel = abs(lhs - rhs) / max(abs(lhs), 1e-300)
        worst = max(worst, rel)
        print(f"m={m:2d}  v={lhs:.12e}  P^4 G={rhs:.12e}  rel={rel:.3e}")
        if rel >= args.rel_tol:
            raise SystemExit(f"identity failed at m={m}: rel={rel}")
    # Rank-1 and rank-2 Hankel positivity at this q.
    v0, v1, v2 = (v_row(m, q, args.t_max) for m in (0, 1, 2))
    V1 = v0
    V2 = v0 * v2 - v1 * v1
    print(f"V1={V1:.12e} V2={V2:.12e}")
    if not (V1 > 0 and V2 > 0):
        raise SystemExit("low-rank Hankel was not positive")
    print(f"ok  worst_rel={worst:.3e}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
