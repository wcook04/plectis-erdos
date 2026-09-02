#!/usr/bin/env python3
"""Erdos #1049: certify the step-1 window divisor from harmonic zeros alone.

The block law identified in `HarmonicZeroBlockLawLab.md`:

    p | B_j for every j >= d = ord_p(3/2), except on the whole blocks
    [dK, dK+d-1] with K in J_p = { K : p | numerator(H_K) },

the Eswarathasan-Levine set of harmonic zeros mod p.  Given that law the whole
window-divisor question is arithmetic on harmonic numerators; no q-Apery
recurrence and no factorisation of 3^s - 2^s is needed.

Window at start s is [s, s + W(s)] with W(s) = 3s^2 + 5s + 3.  A block meets it
iff 1 <= K <= (s + W(s)) // d.  A primitive prime has d = s exactly, so it is a
source-supported window divisor iff J_p misses [1, kmax], kmax = (s+W(s))//s.

Certificate (no factoring)
--------------------------
Let Q_s be the primitive part prod_{m|s} (3^m - 2^m)^{mu(s/m)} with every prime
<= s stripped -- legitimate because a primitive prime satisfies p = 1 mod s, so
p > s.  Let G_s = prod_{K <= kmax} numerator(H_K).  Strip from Q_s every prime
dividing G_s.  A cofactor above 1 contains a primitive prime p whose J_p misses
[1, kmax]: a source-supported window divisor at start s.

Predeclared falsifiers
----------------------
1. Any disagreement between J_p and the loss blocks recorded in
   `QAperyTailDenominatorLab.md` (5:8-9, 19:54-56, 13:48-51, 7:36-41, 29:91-97,
   97:88-95, 23:242-252), which are the lab's own exact rational-arithmetic runs.
2. Wolstenholme failing: p-1 not in J_p for some tested p >= 5.
3. The reflection K -> p-1-K failing on J_p n [1, p-2].
4. A cofinal run of uncertified starts would falsify step 1 as restated.

Exit code 0 iff no falsifier fires.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from fractions import Fraction

sys.set_int_max_str_digits(0)

LAB_LOSS_BLOCKS = {5: (8, 9), 19: (54, 56), 13: (48, 51), 7: (36, 41),
                   29: (91, 97), 97: (88, 95), 23: (242, 252)}


def order_of_three_halves(p: int) -> int:
    x = (3 * pow(2, -1, p)) % p
    d, y = 1, x
    while y != 1:
        y = y * x % p
        d += 1
    return d


def harmonic_zeros(p: int, kmax: int) -> list[int]:
    """J_p intersected with [1, kmax]."""
    H, out = Fraction(0), []
    for K in range(1, kmax + 1):
        H += Fraction(1, K)
        if H.numerator % p == 0:
            out.append(K)
    return out


def mobius(n: int) -> int:
    r, d, m = 1, 2, n
    while d * d <= m:
        if m % d == 0:
            m //= d
            if m % d == 0:
                return 0
            r = -r
        d += 1
    return -r if m > 1 else r


def primitive_part(s: int) -> int:
    num, den = 1, 1
    for m in range(1, s + 1):
        if s % m:
            continue
        mu = mobius(s // m)
        if mu == 1:
            num *= 3 ** m - 2 ** m
        elif mu == -1:
            den *= 3 ** m - 2 ** m
    if num % den:
        raise AssertionError("cyclotomic quotient not integral")
    Q = num // den
    for q in range(2, s + 1):
        while Q % q == 0:
            Q //= q
    return Q


def strip(Q: int, G: int) -> int:
    while True:
        g = math.gcd(Q, G)
        if g == 1:
            return Q
        Q //= g


def falsifier_checks() -> list[str]:
    issues = []
    for p, (lo, hi) in LAB_LOSS_BLOCKS.items():
        d = order_of_three_halves(p)
        J = harmonic_zeros(p, hi // d + 1)
        if not J:
            issues.append(f"falsifier 1: J_{p} empty, lab records block {lo}-{hi}")
            continue
        got = (d * J[0], d * J[0] + d - 1)
        if got != (lo, hi):
            issues.append(f"falsifier 1: p={p} predicts {got}, lab records {(lo, hi)}")
    for p in (5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61):
        J = harmonic_zeros(p, p - 1)
        if p - 1 not in J:
            issues.append(f"falsifier 2: Wolstenholme fails, {p-1} not in J_{p}")
        inner = [k for k in J if k <= p - 2]
        if inner != sorted(p - 1 - k for k in inner):
            issues.append(f"falsifier 3: reflection fails for p={p}: {inner}")
    return issues


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-start", type=int, default=260)
    ap.add_argument("--json", type=str, default=None)
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args()

    issues = falsifier_checks()
    print("falsifiers 1-3 (lab blocks, Wolstenholme, reflection):",
          "OK" if not issues else "FIRED")
    for i in issues:
        print("  !", i)

    H, G, built = Fraction(0), 1, 0
    records, uncertified = [], []
    for s in range(2, args.max_start + 1):
        W = 3 * s * s + 5 * s + 3
        kmax = (s + W) // s
        while built < kmax:
            built += 1
            H += Fraction(1, built)
            G *= H.numerator
        Q = primitive_part(s)
        if Q <= 1:
            uncertified.append((s, "no primitive part"))
            records.append({"s": s, "kmax": kmax, "certified": False})
            continue
        C = strip(Q, G)
        ok = C > 1
        if not ok:
            uncertified.append((s, "every primitive prime meets a harmonic zero"))
        records.append({"s": s, "kmax": kmax, "primitive_bits": Q.bit_length(),
                        "cofactor_bits": C.bit_length(), "certified": ok})
        if not args.quiet:
            print(f"{s:>4} kmax={kmax:>5} bits(Q_s)={Q.bit_length():>5} "
                  f"bits(cofactor)={C.bit_length():>5}  "
                  f"{'CERTIFIED' if ok else '*** NOT CERTIFIED ***'}")

    bad = [s for s, _ in uncertified]
    n_ok = sum(1 for r in records if r["certified"])
    print(f"\nstarts tested: {len(records)}   certified: {n_ok}   uncertified: {len(bad)}")
    print("uncertified starts:", bad)
    print("largest uncertified start:", max(bad) if bad else None)
    if args.json:
        with open(args.json, "w") as fh:
            json.dump({"records": records, "uncertified": uncertified,
                       "issues": issues}, fh, indent=1)
    return 1 if issues else 0


if __name__ == "__main__":
    raise SystemExit(main())
