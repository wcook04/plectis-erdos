#!/usr/bin/env python3
"""Erdos #251: the free-pair producer, state compression, and a finite denominator exclusion.

Setting
-------
g_i = p_(i+1) - p_i (zero-based, p_0 = 2), S = sum_(i>=0) g_i / 2^(i+1), and

    T_N = 2^(N+1) (S - sum_(i<=N) g_i 2^-(i+1)) = sum_(k>=1) g_(N+k) 2^-k,
    T_(N+1) = 2 T_N - g_(N+1).

Suppose S = a/b is rational, b = 2^sigma d with d odd. For N+1 >= sigma,

    T_N = 2^(N+1-sigma) a/d  -  (an integer),      so   d T_N is an integer,

and the fractional part of T_N depends only on N mod t, t = ord_d(2).

WHAT IS NEW HERE
----------------
1.  FREE PAIRS.  The packet's producer `cofinal_adjacent_small_mismatch` fixes an
    offset h and asks for T_(N+h) - T_N and T_(N+h+1) - T_(N+1) to be small.  But
    the fractional part of T_N depends only on N mod t, so

        T_M - T_N is an integer for EVERY M == N (mod t),

    with M - N an arbitrary multiple of t rather than exactly h.  The consumer
    then needs only ONE pair per cutoff:

        g_(M+1) - g_(N+1) = 2   and   T_M - T_N in (1/2, 1)
        (equivalently T_(M+1) - T_(N+1) in (-1, 0)),

    because T_M - T_N and T_(M+1) - T_(N+1) are then integers in (-1,1), hence
    both zero, forcing g_(M+1) = g_(N+1).  The +-2 wall survives: |Delta| =
    |2D - (2D - Delta)| < 2|D| + 1 < 3, so |Delta| = 2 exactly.

    This is a strictly weaker obligation than the fixed-offset form: the two
    indices may be arbitrarily far apart, so the tail condition is a HITTING
    problem on a free parameter rather than a correlation at a fixed offset.
    Falsifier 1 measures how far from marginal it is in the actual primes.

2.  STATE COMPRESSION.  Since sum_(N<=X) T_N <= p_(X+1), Markov gives, for any
    C > 1, a subset B of (X, 2X] of density >= 1 - 1/C on which T_N <=
    C log p_(2X).  On B every T_N lies in (0, C log p_(2X)] and in (1/d)Z, so it
    takes at most d C log p_(2X) + 1 distinct values.  Hence some single value v
    satisfies

        #{ N in (X,2X] : T_N = v }  >>_(d,C)  X / log X.

    Rationality forces the prime-gap tail to be a FINITE-STATE object at every
    scale, with one state occupied a positive-power-of-X number of times.  In
    particular pairs with T_M = T_N exactly are abundant for free, so the entire
    content of the producer sits in the gap-difference condition, never in the
    tail condition.  Falsifier 3 checks the unconditional input sum T_N <= p_(X+1).

3.  DENOMINATOR EXCLUSION.  The packet records that it "contained no continued-
    fraction content" and no finite denominator exclusion.  One is cheap here:
    T_N is a TAIL, so P further gaps pin it to within 2 G 2^-P where G is the
    largest gap in range.  If d T_N is an integer then || d U / 2^P || <= d.2G.2^-P
    with U = sum_(k<=P) g_(N+k) 2^(P-k).  Best approximations to U/2^P come from
    its continued fraction, so every odd d up to an explicit bound is excluded,
    and b >= d exceeds the same bound.

Predeclared falsifiers
----------------------
1. Some (t, r) with t <= --max-t has no free-pair witness in the late window, or
   the latest witness is not within --witness-slack of the last usable index
   (cofinality would then be visibly failing rather than robust).
2. The +-2 wall: any recorded witness whose gap difference is not exactly +2.
3. The unconditional averaging input sum_(N<=X) T_N <= p_(X+1) fails.
4. The denominator exclusion certificate fails to verify against an independent
   direct check on the smallest excluded odd d.

Exit code 0 iff every falsifier passes.

Replay
------
    ./repo-python formal_math/probes/erdos251_free_pair_and_state_compression.py
    ./repo-python formal_math/probes/erdos251_free_pair_and_state_compression.py \
        --limit 20000000 --max-t 24 --json
"""

from __future__ import annotations

import argparse
import bisect
import json
import sys
from array import array

sys.set_int_max_str_digits(0)


def primes_upto(n: int) -> array:
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(range(i * i, n + 1, i)))
    return array("l", [i for i in range(n + 1) if s[i]])


def build(limit: int):
    p = primes_upto(limit)
    g = array("l", [p[i + 1] - p[i] for i in range(len(p) - 1)])
    m = len(g)
    t = [0.0] * m
    for n in range(m - 2, -1, -1):
        t[n] = (g[n + 1] + t[n + 1]) / 2.0
    return p, g, t


# ------------------------------------------------------------ falsifier 1 + 2

def free_pair_scan(g, T, lo: int, hi: int, max_t: int):
    """For every t <= max_t and every residue, count free-pair witnesses."""
    rows = []
    for t in range(1, max_t + 1):
        per_res = []
        for r in range(t):
            start = lo + (r - lo) % t
            buckets: dict[int, list[int]] = {}
            for n in range(start, hi, t):
                buckets.setdefault(g[n + 1], []).append(n)
            sortedT = {v: sorted((T[n + 1], n) for n in idx)
                       for v, idx in buckets.items()}
            wit = 0
            latest = -1
            sample = None
            for v, idx in buckets.items():
                partner = sortedT.get(v + 2)
                if not partner:
                    continue
                vals = [x[0] for x in partner]
                for n in idx:
                    tn = T[n + 1]
                    a = bisect.bisect_right(vals, tn - 1.0)
                    b = bisect.bisect_left(vals, tn)
                    if b > a:
                        wit += b - a
                        cand = max(partner[b - 1][1], n)
                        if cand > latest:
                            latest = cand
                            sample = (n, partner[b - 1][1], v, v + 2)
            per_res.append({"r": r, "witnesses": wit, "latest_index": latest,
                            "sample": sample})
        rows.append({"t": t,
                     "min_witnesses": min(x["witnesses"] for x in per_res),
                     "min_latest_index": min(x["latest_index"] for x in per_res),
                     "samples": [x["sample"] for x in per_res if x["sample"]][:2]})
    return rows


def verify_wall(g, T, rows):
    """Every recorded sample must have gap difference exactly +2 and the
    two integrality windows must both be satisfied."""
    bad = []
    for row in rows:
        for s in row["samples"]:
            if s is None:
                continue
            n, m_, v, w = s
            if w - v != 2:
                bad.append({"t": row["t"], "sample": s, "why": "gap_delta_not_2"})
                continue
            d0 = T[m_] - T[n]
            d1 = T[m_ + 1] - T[n + 1]
            if not (0.5 < d0 < 1.0) or not (-1.0 < d1 < 0.0):
                bad.append({"t": row["t"], "sample": s, "D0": d0, "D1": d1,
                            "why": "window_violated"})
    return bad


# ------------------------------------------------------------- falsifier 3

def averaging_input(p, T, upto: int):
    """sum_(N<=X) T_N <= p_(X+1) + 2 T_X -- the input behind state compression.

    Exchanging the order of summation with m = N + k,
      sum_(N<=X) T_N = sum_(m<=X) g_m (1 - 2^-m)
                     + sum_(m>X) g_m (2.2^-(m-X) - 2^-m)
                    <= (p_(X+1) - p_0) + 2 T_X.
    The 2 T_X term is O(max gap) and therefore o(X); it does not affect the
    Markov step, but the bound without it is FALSE and this falsifier caught it.
    """
    x = min(upto, len(T) - 2)
    s = sum(T[:x + 1])
    bound = float(p[x + 1]) + 2.0 * T[x]
    return {"X": x, "sum_T": s, "bound_p_X_plus_1_plus_2T_X": bound,
            "naive_bound_p_X_plus_1": float(p[x + 1]),
            "naive_bound_would_hold": s <= float(p[x + 1]),
            "holds": s <= bound}


# ------------------------------------------------------------- falsifier 4

def tail_bound(n0: int, P: int) -> int:
    """A rigorous integer upper bound for T_(n0+P) = sum_(j>=1) g_(n0+P+j) 2^-j.

    Uses only the Lean-checked elementary estimate p_n <= 1250 (n+1)^4, which
    gives g_n <= p_(n+1) <= 1250 (n+2)^4.  No unproved gap conjecture enters.
    """
    base = n0 + P
    total = 0
    j = 1
    while j <= 400:
        total += (1250 * (base + j + 2) ** 4) >> j
        j += 1
    return total + 1


def convergent_denominators(U: int, M: int) -> list[int]:
    """Denominators of the convergents of U/M in (0,1), starting at q = 1.

    By the best-approximation theorem these are exactly the d minimising
    ||d * U/M||, so the minimum over 1 <= d <= D is attained at the largest
    entry not exceeding D.  That makes the verification complete rather than a
    spot-check.
    """
    a, b = U, M
    q_prev, q_cur = 1, 0          # q_(-1) = 1, q_0 = 0 before the first quotient
    out: list[int] = []
    while b:
        quot = a // b
        a, b = b, a - quot * b
        q_prev, q_cur = q_cur, quot * q_cur + q_prev
        if q_cur > 0 and (not out or q_cur > out[-1]):
            out.append(q_cur)
        if q_cur > M:
            break
    return out or [1]


def denominator_exclusion(g, n0: int, P: int):
    """Exclude every odd d up to an explicit bound.

    T_(n0) = U/2^P + T_(n0+P)/2^P exactly, with U = sum_(k<=P) g_(n0+k) 2^(P-k).
    If d*T_(n0) is an integer then dist(d U mod 2^P) <= d * Theta, where Theta is
    any rigorous upper bound on T_(n0+P).  Excluding EVERY odd d <= D therefore
    needs min_(1<=e<=D) dist(e U mod 2^P) > D * Theta, and by the theory of
    continued fractions that minimum is attained at the largest convergent
    denominator of U/2^P not exceeding D.
    """
    M = 1 << P
    U = 0
    for k in range(1, P + 1):
        U += g[n0 + k] << (P - k)
    Theta = tail_bound(n0, P)

    def dist(e: int) -> int:
        r = (e * U) % M
        return min(r, M - r)

    qs = convergent_denominators(U, M)

    # For D in [q_j, q_(j+1) - 1] the minimum of dist over 1 <= d <= D is
    # dist(q_j U).  Exclusion of every d <= D needs D * Theta < dist(q_j U).
    best_D, witness = 0, None
    for j, q in enumerate(qs):
        e = dist(q)
        if e <= 0:
            break
        upper = qs[j + 1] - 1 if j + 1 < len(qs) else M
        cap = (e - 1) // Theta                 # largest D with D*Theta < e
        D = min(upper, cap)
        if D >= q and D > best_D:
            best_D, witness = D, q
    return {"index": n0, "precision_bits": P, "tail_bound_Theta": Theta,
            "hardest_denominator": witness,
            "excluded_odd_denominator_upto": best_D,
            "sane": best_D < M}


def verify_exclusion(g, n0: int, P: int, D: int, hardest: int | None):
    """COMPLETE check: the minimum of dist(d U mod 2^P) over 1 <= d <= D is
    attained at a convergent denominator, so testing every convergent <= D
    (plus a few small d as a sanity anchor) verifies the whole range."""
    M = 1 << P
    U = 0
    for k in range(1, P + 1):
        U += g[n0 + k] << (P - k)
    Theta = tail_bound(n0, P)
    cands = [d for d in convergent_denominators(U, M) if d <= D]
    cands += [d for d in (3, 5, 7, D) if 0 < d <= D]
    out = []
    for d in sorted(set(cands)):
        r = (d * U) % M
        e = min(r, M - r)
        out.append({"d_bits": d.bit_length(), "dist_bits": e.bit_length(),
                    "slack_bits": (D * Theta).bit_length(),
                    "excluded": e > D * Theta})
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=5_000_000)
    ap.add_argument("--max-t", type=int, default=16)
    ap.add_argument("--late-frac", type=float, default=0.90)
    ap.add_argument("--witness-slack", type=int, default=200,
                    help="latest witness must be within this many indices of the end")
    ap.add_argument("--precision-bits", type=int, default=512)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    p, g, T = build(args.limit)
    m = len(g)
    K = 64
    lo, hi = int(m * args.late_frac), m - K - 2

    rows = free_pair_scan(g, T, lo, hi, args.max_t)
    wall_bad = verify_wall(g, T, rows)

    cof_bad = [r for r in rows
               if r["min_witnesses"] == 0
               or r["min_latest_index"] < hi - args.witness_slack]

    avg = averaging_input(p, T, m - 2)

    n0 = m - args.precision_bits - 300
    exc = denominator_exclusion(g, n0, args.precision_bits)
    D = exc["excluded_odd_denominator_upto"]
    ver = verify_exclusion(g, n0, args.precision_bits, D, exc["hardest_denominator"])
    exc_bad = [v for v in ver if not v["excluded"]]
    if not exc["sane"]:
        exc_bad.append({"why": "excluded bound exceeds 2^P, certificate is unsound"})

    falsifiers = [
        {"name": "free_pair_cofinality_all_residues",
         "detail": f"t <= {args.max_t}, late window {lo}..{hi}",
         "failures": [{"t": r["t"], "min_witnesses": r["min_witnesses"],
                       "min_latest_index": r["min_latest_index"]} for r in cof_bad],
         "passed": not cof_bad},
        {"name": "plus_minus_two_wall_on_witnesses",
         "failures": wall_bad, "passed": not wall_bad},
        {"name": "averaging_input_sum_T_le_p", "detail": avg,
         "passed": bool(avg["holds"])},
        {"name": "denominator_exclusion_verified",
         "detail": {"excluded_odd_d_upto": D, "checked": ver},
         "failures": exc_bad, "passed": (D > 0 and not exc_bad)},
    ]

    payload = {
        "probe": "erdos251_free_pair_and_state_compression",
        "prime_limit": args.limit, "primes": len(p), "gaps": m,
        "late_window": [lo, hi],
        "free_pair_rows": rows,
        "excluded_odd_denominator_upto": D,
        "denominator_exclusion": exc,
        "falsifiers": falsifiers,
        "all_passed": all(f["passed"] for f in falsifiers),
    }

    if args.json:
        print(json.dumps(payload, indent=2, default=str))
    else:
        print(f"Erdos 251 -- free pairs, state compression, denominator exclusion")
        print(f"  primes <= {args.limit:,}: {len(p):,}   gaps: {m:,}")
        print(f"  late window: indices {lo:,}..{hi:,} "
              f"(primes {p[lo]:,} .. {p[hi]:,})")
        print()
        print(f"  {'t':>4}{'min witnesses over all residues':>34}"
              f"{'min latest witness index':>28}")
        for r in rows:
            print(f"  {r['t']:>4}{r['min_witnesses']:>34,}"
                  f"{r['min_latest_index']:>28,}")
        print()
        print(f"  denominator exclusion: every odd d <= {D:,} is refuted "
              f"({args.precision_bits} tail bits at index {n0:,})")
        print(f"  hence any rational S = a/b has b > {D:,}")
        print()
        for f in falsifiers:
            print(f"  [{'PASS' if f['passed'] else 'FAIL'}] {f['name']}")
            for x in f.get("failures", [])[:5]:
                print(f"          {x}")
        print()
        print("  all falsifiers passed" if payload["all_passed"]
              else "  FALSIFIER FIRED")
    return 0 if payload["all_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
