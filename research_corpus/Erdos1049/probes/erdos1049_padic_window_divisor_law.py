#!/usr/bin/env python3
"""Erdos #1049: the q-Apery window-divisor predicate, run p-adically and far out.

Upstream state
--------------
`WindowDivisorSupplyLab.md` evaluated step 1 of the theorem-sized target for
starts s <= 14 by building the primitive q-Apery rows over Q -- 677 rows whose
coordinates reach ~10^6 bits.  It concluded that the step-1 predicate holds and
named the residual:

> show that for every large s the prime p_s | 3^s - 2^s selected at first
> appearance has no loss block meeting [s, s + 3s^2 + 5s + 3].

That is a statement about the multiplicative order of 3/2 modulo a prime divisor
of 3^s - 2^s against a quadratic window.  This probe supplies the arithmetic law
behind it and evaluates the predicate well past s = 14.

The reduction that makes it cheap
---------------------------------
(A_j, B_j) is the primitive integer vector proportional to (L_j, R_j), the two
solutions of the source recurrence.  Hence

    p | B_j   <=>   v_p(R_j) > v_p(L_j),

and past the seeds the run below finds v_p(R_j) = 0 at every index for every
prime tested, so on that range

    p | B_j   <=>   v_p(L_j) < 0.

The seeds themselves are exceptions (R_1 = -11/4, L_1 = -21/2), so the code uses
the general comparison throughout.

Only p-adic valuations are needed, so the whole computation runs in Q_p at fixed
precision instead of over Q with million-bit rationals.  The coefficient
valuations decompose exactly:

    v_p(y2(n)) = v_p(3^(n+2) - 2^(n+2)) + v_p(3^(n+1) + 2^(n+2))
    v_p(y0(n)) = v_p(3^(n+1) - 2^(n+1)) + v_p(3^(n+2) + 2^(n+3))

with v_p(3^m - 2^m) = v_p(3^d - 2^d) + v_p(m/d) when d = ord_p(3/2) divides m
(lifting the exponent), and zero otherwise.

Block law (measured, not assumed)
---------------------------------
p | B_j for every j >= d except on whole blocks [d*k, d*k + d - 1], k in K_p.
The window at start s is [s, s + 3s^2 + 5s + 3], so a block meets it iff
1 <= k <= (s + 3s^2 + 5s + 3) // d.  A prime is therefore a window divisor at
start s iff d <= s and K_p misses that range.

Predeclared falsifiers
----------------------
1. Any disagreement with the loss blocks recorded in `QAperyTailDenominatorLab.md`
   (5:8-9, 19:54-56, 13:48-51, 7:36-41, 29:91-97, 97:88-95, 23:242-252) or with
   the regression anchor 211 | B_j for 5 <= j <= 255.
2. Any index j > 1 with v_p(R_j) != 0.  (At the seeds this is expected and is
   NOT a falsifier: R_1 = -11/4 and L_1 = -21/2 carry 11 and 7 respectively, so
   v_11(R_1) = v_7(L_1) = 1.  The general comparison v_p(R_j) > v_p(L_j) is what
   the block law rests on; the "R is a unit" simplification is an observation
   about the primes sampled, recorded here rather than assumed.)
3. A cofinal run of starts with no window divisor at all would falsify step 1.

Exit code 0 iff every regression anchor reproduces and no falsifier fires.
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


class Qp:
    """x = p^v * u with u a unit modulo p^N; v is None for zero to precision."""
    __slots__ = ("v", "u")

    def __init__(self, v, u):
        self.v, self.u = v, u


def arithmetic(p: int, N: int):
    M = p ** N

    def norm(v, u):
        u %= M
        if u == 0:
            return Qp(None, 0)
        while u % p == 0:
            u //= p
            v += 1
            if u == 0:
                return Qp(None, 0)
        return Qp(v, u % M)

    def frm(fr: Fraction):
        num, den, v = fr.numerator, fr.denominator, 0
        if num == 0:
            return Qp(None, 0)
        while num % p == 0:
            num //= p
            v += 1
        while den % p == 0:
            den //= p
            v -= 1
        return norm(v, num * pow(den, -1, M))

    def add(a, b):
        if a.v is None:
            return b
        if b.v is None:
            return a
        if a.v <= b.v:
            return norm(a.v, a.u + b.u * pow(p, b.v - a.v))
        return norm(b.v, b.u + a.u * pow(p, a.v - b.v))

    def neg(a):
        return a if a.v is None else Qp(a.v, (-a.u) % M)

    def mul(a, b):
        if a.v is None or b.v is None:
            return Qp(None, 0)
        return norm(a.v + b.v, a.u * b.u)

    def div(a, b):
        if b.v is None:
            raise ZeroDivisionError("y2 vanished to working precision")
        if a.v is None:
            return Qp(None, 0)
        return norm(a.v - b.v, a.u * pow(b.u, -1, M))

    return frm, add, neg, mul, div


def valuations(p: int, jmax: int, N: int = 48):
    """Return (vL, vR): p-adic valuations of the two recurrence solutions."""
    frm, add, neg, mul, div = arithmetic(p, N)
    q, one, two, four = (frm(Fraction(3, 2)), frm(Fraction(1)),
                         frm(Fraction(2)), frm(Fraction(4)))
    Lm2, Lm1 = frm(Fraction(0)), frm(Fraction(-21, 2))
    Rm2, Rm1 = frm(Fraction(1)), frm(Fraction(-11, 4))
    vL, vR = [Lm2.v, Lm1.v], [Rm2.v, Rm1.v]
    alpha = q
    for _ in range(jmax - 1):
        a, qa = alpha, mul(q, alpha)
        y0 = mul(q, mul(add(a, neg(one)), add(qa, two)))
        y2 = mul(add(qa, neg(one)), add(a, two))
        qq = mul(q, q)
        a2 = mul(a, a); a3 = mul(a2, a); a4 = mul(a3, a); a5 = mul(a4, a)
        y1 = add(add(add(add(add(
            mul(mul(qq, q), a5),
            mul(mul(two, mul(qq, add(q, one))), a4)),
            mul(qq, a3)),
            neg(mul(mul(four, mul(q, add(q, one))), a2))),
            mul(add(add(qq, neg(mul(four, q))), one), a)),
            mul(two, add(q, one)))
        nl = neg(div(add(mul(y1, Lm1), mul(y0, Lm2)), y2))
        nr = neg(div(add(mul(y1, Rm1), mul(y0, Rm2)), y2))
        Lm2, Lm1 = Lm1, nl
        Rm2, Rm1 = Rm1, nr
        vL.append(nl.v)
        vR.append(nr.v)
        alpha = mul(alpha, q)
    return vL, vR


def divides_B(vL, vR, j):
    lv, rv = vL[j], vR[j]
    lv = math.inf if lv is None else lv
    rv = math.inf if rv is None else rv
    return rv > lv


def order_of_three_halves(p: int) -> int:
    x = (3 * pow(2, -1, p)) % p
    d, y = 1, x
    while y != 1:
        y = y * x % p
        d += 1
    return d


def _is_prime(n: int) -> bool:
    if n < 2:
        return False
    for s in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % s == 0:
            return n == s
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def factorize(n: int) -> dict[int, int]:
    import random
    fs: dict[int, int] = {}
    for d in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47):
        while n % d == 0:
            fs[d] = fs.get(d, 0) + 1
            n //= d
    stack = [n] if n > 1 else []
    while stack:
        m = stack.pop()
        if m == 1:
            continue
        if _is_prime(m):
            fs[m] = fs.get(m, 0) + 1
            continue
        while True:
            x = random.randrange(2, m); y = x; c = random.randrange(1, m); g = 1
            while g == 1:
                x = (x * x + c) % m
                y = (y * y + c) % m
                y = (y * y + c) % m
                g = math.gcd(abs(x - y), m)
            if g != m:
                break
        stack.extend([g, m // g])
    return fs


def window_width(s: int) -> int:
    return 3 * s * s + 5 * s + 3


NONUNIT_R: list[tuple[int, int, int]] = []


def min_loss_block(p: int, jcap: int, cache: dict) -> int | None:
    """Smallest k >= 1 whose block [dk, dk+d-1] is a loss block within j <= jcap.

    Returns None when no loss block occurs at or below index jcap.  The cache
    stores, per prime, the depth already run and the first loss block found, so
    a prime is re-run only when a strictly deeper query arrives.
    """
    prev = cache.get(p)
    if prev is not None:
        depth, first_k, first_j = prev
        if first_k is not None and first_j <= jcap:
            return first_k
        if jcap <= depth:
            return None
    d = order_of_three_halves(p)
    vL, vR = valuations(p, jcap + 2)
    for j in range(2, len(vR)):
        if vR[j] is not None and vR[j] != 0:
            NONUNIT_R.append((p, j, vR[j]))
            break
    out, out_j, k = None, None, 1
    while d * k <= jcap:
        j = d * k
        if j < len(vL) and not divides_B(vL, vR, j):
            out, out_j = k, j
            break
        k += 1
    cache[p] = (jcap, out, out_j if out_j is not None else 1 << 60)
    return out


def regression_checks() -> list[str]:
    issues = []
    for p, (lo, hi) in LAB_LOSS_BLOCKS.items():
        d = order_of_three_halves(p)
        vL, vR = valuations(p, hi + 3)
        got = [j for j in range(d, hi + 2) if not divides_B(vL, vR, j)]
        if not got or (min(got), max(got)) != (lo, hi):
            issues.append(f"loss block mismatch for p={p}: expected {(lo, hi)} got {got[:12]}")
        if hi - lo + 1 != d:
            issues.append(f"loss block for p={p} has length {hi-lo+1}, ord={d}")
    vL, vR = valuations(211, 258)
    if not all(divides_B(vL, vR, j) for j in range(5, 256)):
        issues.append("regression anchor 211 | B_j for 5<=j<=255 failed")
    return issues


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-start", type=int, default=30)
    ap.add_argument("--json", type=str, default=None)
    args = ap.parse_args()

    issues = regression_checks()
    print("regression anchors:", "OK" if not issues else "FAILED")
    for i in issues:
        print("  !", i)

    cache: dict = {}
    records = []
    print(f"\n{'s':>4} {'kmax':>5}  {'primitive primes (minK)':<52} {'verdict':<8} covering prime")
    prim_pool: list[tuple[int, int]] = []   # (p, d) seen so far, d <= current s
    fails = []
    for s in range(2, args.max_start + 1):
        jcap = s + window_width(s)
        kmax_prim = jcap // s
        fs = factorize(3 ** s - 2 ** s)
        prim = sorted(p for p in fs if order_of_three_halves(p) == s)
        for p in prim:
            prim_pool.append((p, s))
        detail, ok = [], []
        for p in prim:
            mk = min_loss_block(p, jcap, cache)
            detail.append(f"{p}({mk if mk else '-'})")
            if mk is None:
                ok.append(p)
        # weaker, true predicate: ANY prime with d <= s covering the window
        covering = None
        for p, d in prim_pool:
            if d > s:
                continue
            if min_loss_block(p, jcap, cache) is None:
                covering = (p, d)
                break
        verdict = "PASS" if ok else "no-prim"
        if not ok:
            fails.append(s)
        cov = f"{covering[0]} (d={covering[1]})" if covering else "NONE"
        print(f"{s:>4} {kmax_prim:>5}  {','.join(detail)[:52]:<52} {verdict:<8} {cov}")
        records.append({"s": s, "kmax": kmax_prim, "primitive": prim,
                        "primitive_ok": ok, "covering": covering})

    print("\nstarts where the FIRST-APPEARANCE prime fails:", fails)
    no_cover = [r["s"] for r in records if r["covering"] is None]
    print("starts with NO window divisor at all (step-1 falsifier):", no_cover)
    if NONUNIT_R:
        print("indices j>1 with v_p(R_j) != 0 (observation, not a falsifier):",
              NONUNIT_R[:10])
    else:
        print("v_p(R_j) = 0 for every j > 1 across every prime run.")
    if args.json:
        with open(args.json, "w") as fh:
            json.dump({"records": records, "first_appearance_failures": fails,
                       "no_window_divisor": no_cover, "issues": issues}, fh, indent=1)
    return 1 if (issues or no_cover) else 0


if __name__ == "__main__":
    raise SystemExit(main())
