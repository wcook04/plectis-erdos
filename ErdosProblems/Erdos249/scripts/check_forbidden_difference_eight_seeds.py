#!/usr/bin/env python3
"""Replay the eight depth-16 seeds at N=12 and the t≥21 eight-of-nine bound.

Live Lean already records certifiedKill_all_small: K(h,12,16) holds for
h=1..8.  Type B r3 Theorem C extracts an eventual forbidden-difference
statement: for every integer t≥21, at least eight of the nine consecutive
full-depth tests K(t+j,12,t+j) for j=0..8 hold.

This script recomputes the eight exact (D, residue, B, margin) rows and the
threshold comparison at t=21.  It does not prove irrationality of S: even
eventual success on one ray is compatible with rationality (Proposition R).

Run: ./repo-python <this file> --quick
"""
from __future__ import annotations

import argparse
import json


EXPECTED = [
    # h, D, residue mod 65536, B, margin
    (1, -143140, 53468, 31, 12037),
    (2, -36224, 29312, 32, 29280),
    (3, 46558, 46558, 33, 18945),
    (4, 212108, 15500, 34, 15466),
    (5, 18924, 18924, 35, 18889),
    (6, 287912, 25768, 36, 25732),
    (7, 39464, 39464, 37, 26035),
    (8, 197916, 1308, 38, 1270),
]


def totient_sieve(limit: int) -> list[int]:
    ph = list(range(limit + 1))
    for i in range(2, limit + 1):
        if ph[i] == i:
            for j in range(i, limit + 1, i):
                ph[j] -= ph[j] // i
    ph[0] = 0
    return ph


def D_hNL(h: int, N: int, L: int, ph: list[int]) -> int:
    total = 0
    for j in range(L):
        total += (ph[N + h + 1 + j] - ph[N + 1 + j]) * (1 << (L - 1 - j))
    return total


def residue_mod(D: int, L: int) -> int:
    mod = 1 << L
    return D % mod


def margin(D: int, N: int, h: int, L: int) -> int:
    r = residue_mod(D, L)
    B = N + h + L + 2
    return min(r, (1 << L) - r) - B


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true", default=True)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()
    N, L = 12, 16
    ph = totient_sieve(N + 8 + L + 8)
    rows = []
    match = True
    for h, D_exp, r_exp, B_exp, m_exp in EXPECTED:
        D = D_hNL(h, N, L, ph)
        r = residue_mod(D, L)
        B = N + h + L + 2
        m = margin(D, N, h, L)
        ok = (D == D_exp and r == r_exp and B == B_exp and m == m_exp and m > 0)
        match = match and ok
        rows.append({
            "h": h, "D": D, "residue": r, "B": B, "margin": m,
            "matches_type_b_table": ok,
        })
    min_margin = min(row["margin"] for row in rows)
    # Type B threshold: at t=21, ε_{t+j}+2^j ε_t ≤ 2(14+2(t+8))*257 / 2^t
    t = 21
    rhs = 2 * (14 + 2 * (t + 8)) * 257
    lhs_units = min_margin << (t - L)  # min_margin / 2^L compared at denominator 2^t
    # 1270/2^16 = 40640/2^21; rhs=37008/2^21
    threshold_ok = rhs < (min_margin << (t - L))
    decreasing = True
    for tt in range(t, t + 8):
        rhs_tt = 2 * (14 + 2 * (tt + 8)) * 257
        if rhs_tt >= (min_margin << (tt - L)):
            decreasing = False
            break
    # Cyclotomic scope check requested in the same r3 credibility list:
    # every odd q divides 2^{φ(q)}-1, hence a product of Φ_m(2).
    cyclotomic_rows = []
    cyclotomic_ok = True
    ph_small = totient_sieve(64)
    for q in range(1, 65, 2):
        if q == 1:
            divides = True
        else:
            divides = (pow(2, ph_small[q]) - 1) % q == 0
        cyclotomic_ok = cyclotomic_ok and divides
        cyclotomic_rows.append({"q": q, "divides_2_phi_minus_1": divides})

    ok = match and threshold_ok and decreasing and min_margin == 1270 and cyclotomic_ok
    rep = {
        "schema": "erdos249-forbidden-difference-eight-seeds/1",
        "claim_ceiling": (
            "Exact replay of eight depth-16 seeds and the t=21 numerical "
            "threshold for Theorem C.  Does not prove S irrational: a single "
            "ray of high certificate density is compatible with rationality."
        ),
        "seeds": rows,
        "min_margin": min_margin,
        "t21_rhs_over_2_t": rhs,
        "t21_margin_over_2_t": min_margin << (t - L),
        "threshold_strict_at_21": threshold_ok,
        "threshold_persists_for_next_eight_t": decreasing,
        "odd_q_divides_mersenne_at_phi": cyclotomic_ok,
        "all_checks_pass": ok,
    }
    if args.json:
        print(json.dumps(rep, indent=1))
    else:
        print("Eight seeds: %s" % ("PASS" if match else "FAIL"))
        for row in rows:
            print("  h=%d D=%d r=%d B=%d margin=%d"
                  % (row["h"], row["D"], row["residue"], row["B"], row["margin"]))
        print("t≥21 threshold", threshold_ok, "rhs", rhs,
              "<", min_margin << (t - L))
        print("odd q | 2^{φ(q)}-1 for q<65 odd:", cyclotomic_ok)
        print("all_checks_pass", ok)
        print("NOT a proof that S is irrational.")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
