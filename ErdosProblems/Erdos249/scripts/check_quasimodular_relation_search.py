#!/usr/bin/env python3
"""Exact search for a finite quasimodular expression of the totient generating function.

Question (desk F, wave 1, Erdős 249 batch 2026-09-05): is Phi(q) = sum_{n>=1} phi(n) q^n a
Q-polynomial in E_2, E_4, E_6 (level 1), or a Q-combination of E_k(q^M) for small M?  A
positive answer would give S = Phi(1/2) = P(E_2(1/2), E_4(1/2), E_6(1/2)) and hence, by
Nesterenko's theorem (E_2, E_4, E_6 are algebraically independent at algebraic q), the
transcendence of S and a solution of Erdős #249.

Method: expand all q-series to order ORD with exact integer coefficients; for each weight W
form the level-1 quasimodular monomials E_2^a E_4^b E_6^c with 2a+4b+6c = W and compute the
exact rank over Q of the coefficient matrix with and without Phi appended.  "In span" would
be a rank that does NOT rise when Phi is appended.  The check is exact; a negative verdict is
a theorem about the tested weights and levels only.

Conductor run, 2026-09-05, order 200: NOT in span at every level-1 weight <= 12, in the
cumulative span through weight 12 with 1, in the linear span of E_k(q^M) for M <= 6, and
with all products E_2(q^M) E_2(q^M') for M, M' <= 6.

usage: check_quasimodular_relation_search.py [--quick] [--ord 200] [--wmax 12] [--mmax 6]
prints one JSON status line.
"""
import argparse
import json
from fractions import Fraction as F


def sigma_k(n, k):
    return sum(d ** k for d in range(1, n + 1) if n % d == 0)


def totient(n):
    res, m, p = n, n, 2
    while p * p <= m:
        if m % p == 0:
            while m % p == 0:
                m //= p
            res -= res // p
        p += 1
    if m > 1:
        res -= res // m
    return res


def eisenstein(k, order, M=1):
    c = {2: -24, 4: 240, 6: -504}[k]
    s = [0] * (order + 1)
    s[0] = 1
    for n in range(1, order // M + 1):
        s[n * M] = c * sigma_k(n, k - 1)
    return s


def mul(A, B, order):
    C = [0] * (order + 1)
    for i, x in enumerate(A):
        if x == 0:
            continue
        for j in range(0, order + 1 - i):
            if B[j]:
                C[i + j] += x * B[j]
    return C


def power(A, e, order):
    R = [0] * (order + 1)
    R[0] = 1
    for _ in range(e):
        R = mul(R, A, order)
    return R


def rank_q(rows):
    M = [[F(x) for x in r] for r in rows]
    rank, col = 0, 0
    nrows = len(M)
    ncols = len(M[0]) if M else 0
    while rank < nrows and col < ncols:
        piv = next((r for r in range(rank, nrows) if M[r][col] != 0), None)
        if piv is None:
            col += 1
            continue
        M[rank], M[piv] = M[piv], M[rank]
        pv = M[rank][col]
        for r in range(nrows):
            if r != rank and M[r][col] != 0:
                f = M[r][col] / pv
                M[r] = [x - f * y for x, y in zip(M[r], M[rank])]
        rank += 1
        col += 1
    return rank


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--ord", type=int, default=200)
    ap.add_argument("--wmax", type=int, default=12)
    ap.add_argument("--mmax", type=int, default=6)
    a = ap.parse_args()
    order, wmax, mmax = (120, 8, 4) if a.quick else (a.ord, a.wmax, a.mmax)

    phi = [0] + [totient(n) for n in range(1, order + 1)]
    E = {k: eisenstein(k, order) for k in (2, 4, 6)}
    one = [1] + [0] * order
    results = []
    cum = [one]
    in_span_anywhere = False
    for W in range(2, wmax + 1, 2):
        monos = [(aa, bb, (W - 2 * aa - 4 * bb) // 6)
                 for aa in range(W // 2 + 1) for bb in range((W - 2 * aa) // 4 + 1)
                 if (W - 2 * aa - 4 * bb) % 6 == 0]
        rows = [mul(mul(power(E[2], aa, order), power(E[4], bb, order), order), power(E[6], cc, order), order)
                for (aa, bb, cc) in monos]
        r0, r1 = rank_q(rows), rank_q(rows + [phi])
        cum += rows
        c0, c1 = rank_q(cum), rank_q(cum + [phi])
        in_span_anywhere |= (r1 == r0) or (c1 == c0)
        results.append({"level": 1, "weight": W, "monomials": len(monos), "rank": r0, "rank_with_phi": r1,
                        "cumulative_rank": c0, "cumulative_rank_with_phi": c1})
    gens = [one] + [eisenstein(k, order, M) for M in range(1, mmax + 1) for k in (2, 4, 6)]
    r0, r1 = rank_q(gens), rank_q(gens + [phi])
    in_span_anywhere |= (r1 == r0)
    results.append({"level_le": mmax, "family": "linear span of E_k(q^M)", "gens": len(gens), "rank": r0, "rank_with_phi": r1})
    w2 = [eisenstein(2, order, M) for M in range(1, mmax + 1)]
    prods = [mul(w2[i], w2[j], order) for i in range(len(w2)) for j in range(i, len(w2))]
    r0, r1 = rank_q(gens + prods), rank_q(gens + prods + [phi])
    in_span_anywhere |= (r1 == r0)
    results.append({"level_le": mmax, "family": "plus products E_2(q^M)E_2(q^M')", "gens": len(gens) + len(prods), "rank": r0, "rank_with_phi": r1})
    status = "phi_in_quasimodular_span_CHECK_AND_ESCALATE" if in_span_anywhere else "verified_not_in_span"
    print(json.dumps({"check": "quasimodular_relation_search", "evidence_class": "exact_computation",
                      "order": order, "wmax": wmax, "mmax": mmax, "status": status,
                      "phi_in_span_anywhere": in_span_anywhere, "rows": results}))
    return 0 if not in_span_anywhere else 2


if __name__ == "__main__":
    raise SystemExit(main())
