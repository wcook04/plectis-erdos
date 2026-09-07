#!/usr/bin/env python3
"""Exact scalar identities for nonempty Jordan-product kernel reductions.

Type B r3 proposed Theorem J: for
    f(n) = n^a * prod_i J_{s_i}(n)^{m_i}
with a nonempty Jordan product, the same indexing family as the totient
k-kernel has rank k^e+1 and integral reductions.  Live Lean already proves
affine independence for the special case n^q φ(n)^m (m≥1).  This script does
not re-announce that theorem.  It checks the proposed reduction scalars, the
zero-channel identity, integrality of C_f, and the empty-product rank bound
that makes a Jordan factor necessary.

Arithmetic is exact integers / fractions.  A matching identity is not a proof
of affine independence or of the all-(k,e) rank formula.

Run: ./repo-python <this file> --quick
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import gcd


def lpf_sieve(limit: int) -> list[int]:
    lpf = list(range(limit + 1))
    i = 2
    while i * i <= limit:
        if lpf[i] == i:
            for j in range(i * i, limit + 1, i):
                if lpf[j] == j:
                    lpf[j] = i
        i += 1
    return lpf


def primes_of(n: int, lpf: list[int]) -> list[int]:
    if n <= 1:
        return []
    out = []
    while n > 1:
        p = lpf[n]
        out.append(p)
        while n % p == 0:
            n //= p
    return out


def jordan(s: int, n: int, lpf: list[int]) -> int:
    """Integer Jordan totient J_s(n) = n^s prod_{p|n} (1 - p^{-s})."""
    if n == 0:
        return 0
    if n == 1:
        return 1
    out = 1
    x = n
    while x > 1:
        p = lpf[x]
        v = 0
        while x % p == 0:
            x //= p
            v += 1
        out *= pow(p, s * v) - pow(p, s * (v - 1))
    return out


def f_value(a: int, jordan_factors: list[tuple[int, int]], n: int, lpf: list[int]) -> int:
    if n == 0:
        return 0
    val = pow(n, a)
    for s, m in jordan_factors:
        val *= pow(jordan(s, n, lpf), m)
    return val


def weight(a: int, jordan_factors: list[tuple[int, int]]) -> int:
    return a + sum(s * m for s, m in jordan_factors)


def reduction_scalar(
    a: int,
    jordan_factors: list[tuple[int, int]],
    k: int,
    t: int,
    u: int,
    lpf: list[int],
) -> Fraction:
    """C_f(k,t,u) as an exact rational; Theorem J claims it is a positive integer."""
    w = weight(a, jordan_factors)
    val = Fraction(pow(k, w * t), 1)
    for p in set(primes_of(k, lpf)):
        if u % p == 0:
            continue
        extra = Fraction(1, 1)
        for s, m in jordan_factors:
            extra *= (1 - Fraction(1, pow(p, s))) ** m
        val *= extra
    return val


def gaussian_rank_mod(matrix: list[list[int]], p: int) -> int:
    a = [row[:] for row in matrix]
    rows, cols = len(a), len(a[0]) if a else 0
    r = 0
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if a[i][c] % p:
                piv = i
                break
        if piv is None:
            continue
        a[r], a[piv] = a[piv], a[r]
        inv = pow(a[r][c] % p, -1, p)
        a[r] = [(x * inv) % p for x in a[r]]
        for i in range(rows):
            if i == r:
                continue
            fac = a[i][c] % p
            if fac:
                a[i] = [(a[i][j] - fac * a[r][j]) % p for j in range(cols)]
        r += 1
        if r == rows:
            break
    return r


def check_scalars(limit: int) -> dict:
    lpf = lpf_sieve(limit)
    families = [
        ("phi", 0, [(1, 1)]),
        ("n phi^2", 1, [(1, 2)]),
        ("J_2", 0, [(2, 1)]),
        ("n^2 J_1 J_3", 2, [(1, 1), (3, 1)]),
    ]
    bases = [2, 3, 4, 6, 10, 12]
    samples = [0, 1, 2, 7]
    n_ok = n_fail = n_nonint = 0
    failures = []
    for name, a, facs in families:
        if not facs:
            raise AssertionError("nonempty Jordan product required in this loop")
        w = weight(a, facs)
        for k in bases:
            for t in (1, 2, 3):
                for u in range(1, k ** 3):
                    if u % k == 0:
                        continue
                    C = reduction_scalar(a, facs, k, t, u, lpf)
                    if C.denominator != 1 or C <= 0:
                        n_nonint += 1
                        if len(failures) < 8:
                            failures.append(
                                {"kind": "nonintegral_or_nonpositive_C", "name": name,
                                 "k": k, "t": t, "u": u, "C": str(C)}
                            )
                        continue
                    C_int = int(C)
                    for n in samples:
                        arg_left = k ** (t + 1) * n + (k ** t) * u
                        arg_right = k * n + u
                        if max(arg_left, arg_right) >= limit:
                            continue
                        left = f_value(a, facs, arg_left, lpf)
                        right = C_int * f_value(a, facs, arg_right, lpf)
                        if left == right:
                            n_ok += 1
                        else:
                            n_fail += 1
                            if len(failures) < 8:
                                failures.append(
                                    {"kind": "reduction", "name": name, "k": k,
                                     "t": t, "u": u, "n": n, "left": left,
                                     "right": right}
                                )
                    for j in (1, 2, 3):
                        for n in samples:
                            if n == 0:
                                left = f_value(a, facs, 0, lpf)
                                right = pow(k, w * (j - 1)) * f_value(a, facs, 0, lpf)
                            else:
                                arg_left = k ** j * n
                                arg_right = k * n
                                if max(arg_left, arg_right) >= limit:
                                    continue
                                left = f_value(a, facs, arg_left, lpf)
                                right = pow(k, w * (j - 1)) * f_value(a, facs, arg_right, lpf)
                            if left == right:
                                n_ok += 1
                            else:
                                n_fail += 1
                                if len(failures) < 8:
                                    failures.append(
                                        {"kind": "zero_channel", "name": name,
                                         "k": k, "j": j, "n": n, "left": left,
                                         "right": right}
                                    )
    return {
        "identities_ok": n_ok,
        "identities_failed": n_fail,
        "nonintegral_C": n_nonint,
        "failures": failures,
        "all_scalar_identities_hold": n_fail == 0 and n_nonint == 0,
    }


def empty_product_rank_bound(quick: bool) -> dict:
    """f(n)=n (empty Jordan product) cannot have rank k^e+1 growing in e."""
    k, depths = 2, (1, 2, 3, 4) if not quick else (1, 2, 3)
    eval_ns = list(range(1, 40 if quick else 80))
    p = 1_000_003
    ranks = []
    for e in depths:
        cols = []
        for j in range(e + 1):
            for r in range(k ** j):
                cols.append([((k ** j) * n + r) % p for n in eval_ns])
        rank = gaussian_rank_mod(list(map(list, zip(*cols))), p)
        ranks.append({"e": e, "labelled_sections": len(cols),
                      "expected_jordan_rank": k ** e + 1, "rank_mod_p": rank})
    growing = [row["rank_mod_p"] for row in ranks]
    bounded = max(growing) <= 3
    formula_fails = any(row["rank_mod_p"] < row["expected_jordan_rank"] for row in ranks)
    return {
        "f": "n (empty Jordan product, a=1, f(0)=0)",
        "rows": ranks,
        "rank_stays_bounded": bounded,
        "jordan_formula_fails_as_required": formula_fails,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true", default=True)
    ap.add_argument("--full", action="store_true")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()
    quick = not args.full
    limit = 4000 if quick else 20000
    scalars = check_scalars(limit)
    empty = empty_product_rank_bound(quick)
    ok = (
        scalars["all_scalar_identities_hold"]
        and empty["rank_stays_bounded"]
        and empty["jordan_formula_fails_as_required"]
    )
    rep = {
        "schema": "erdos249-jordan-product-kernel-scalars/1",
        "claim_ceiling": (
            "Exact finite identities for proposed Jordan-product reductions. "
            "Not a proof of affine independence, not a re-announcement of "
            "linearIndependent_totientPowAffineForms, and not a step toward "
            "irrationality of S."
        ),
        "live_lean_already": (
            "AllBaseTotientKernel.linearIndependent_totientPowAffineForms "
            "covers n^q φ^m, m≥1; all-base rank for that class is still open "
            "in Lean."
        ),
        "scalars": scalars,
        "empty_product_countermodel": empty,
        "all_checks_pass": ok,
    }
    if args.json:
        print(json.dumps(rep, indent=1))
    else:
        print(
            "Jordan-product scalars: %s (%d ok, %d fail, %d nonintegral C)"
            % (
                "PASS" if scalars["all_scalar_identities_hold"] else "FAIL",
                scalars["identities_ok"],
                scalars["identities_failed"],
                scalars["nonintegral_C"],
            )
        )
        print(
            "Empty-product rank bound: %s"
            % ("PASS" if empty["jordan_formula_fails_as_required"] and empty["rank_stays_bounded"]
               else "FAIL")
        )
        for row in empty["rows"]:
            print("    e=%d labelled=%d jordan-formula=%d rank=%d"
                  % (row["e"], row["labelled_sections"],
                     row["expected_jordan_rank"], row["rank_mod_p"]))
        print("all_checks_pass", ok)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
