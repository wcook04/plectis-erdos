"""Desk F autopsy of the Erdos 1948 digit-block mechanism transferred to phi.

Erdos, "On arithmetical properties of Lambert series", J. Indian Math. Soc.
(N.S.) 12 (1948), 63-66, proves sum_r d(r)/t^r irrational by producing
arbitrarily long blocks of ZEROS in the base-t expansion.  In the corpus's
canonical tail coordinates R_N = sum_{j>=1} a(N+j) 2^-j (so that the binary
digits of S at positions N+1, N+2, ... are those of frac(R_N)), the argument
has exactly three zones:

  Z1  window, length k:  2^j | a(N+j) for 1 <= j <= k.  Then
      sum_{j<=k} a(N+j)2^-j is an INTEGER, so frac(R_N) = frac(T) with
      T = sum_{j>k} a(N+j)2^-j.  Forced by CRT on disjoint prime blocks.
  Z2  buffer, length ~10 log N:  a(r) <= 2^(k/4) there, arranged by a
      first-moment count over the free shift (Erdos eq. (6); Vandehey
      arXiv:1206.0340 Lemma 2.2).  This makes T itself small.
  Z3  far tail:  killed by a(r) <= r plus the extra 10 log_2 N of decay.

Erdos concludes T < 2^-(N+k/2), i.e. a run of about k/2 zeros.  The run length
actually delivered is L = floor(-log2 T).  This probe computes k, T and L
EXACTLY (rational arithmetic, explicit truncation error) for a = d and a = phi
and shows that L -> infinity for d and L <= 0 for phi.

Usage:  python3 wave1_F_erdos1948_transfer_audit.py [--quick]
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from math import log


def totient_sieve(n: int) -> list[int]:
    phi = list(range(n + 1))
    for p in range(2, n + 1):
        if phi[p] == p:
            for m in range(p, n + 1, p):
                phi[m] -= phi[m] // p
    return phi


def divisor_count_sieve(n: int) -> list[int]:
    d = [0] * (n + 1)
    for i in range(1, n + 1):
        for m in range(i, n + 1, i):
            d[m] += 1
    return d


def window_len(a: list[int], N: int, kmax: int) -> int:
    k = 0
    while k < kmax and N + k + 1 < len(a) and a[N + k + 1] % (2 ** (k + 1)) == 0:
        k += 1
    return k


def tail_after_window(a: list[int], N: int, k: int, depth: int) -> Fraction:
    """T = sum_{j>k} a(N+j)2^-j, truncated at j = k+depth.

    Truncation error is at most (N+k+depth+2)*2^-(k+depth) for a(n) <= n.
    """
    return sum(Fraction(a[N + j], 2 ** j)
               for j in range(k + 1, k + depth + 1) if N + j < len(a))


def odd_part(m: int) -> int:
    while m and m % 2 == 0:
        m //= 2
    return m


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()

    X = 300_000 if args.quick else 2_000_000
    DEPTH = 200
    phi = totient_sieve(X)
    dv = divisor_count_sieve(min(X, 400_000))

    print("== Z1 (window) transfers to phi: it is NOT the obstruction ==")
    for k in (3, 4, 5, 6, 8):
        m = next((N for N in range(2, X - k - 2)
                  if all(phi[N + j] % (2 ** j) == 0 for j in range(1, k + 1))),
                 None)
        print(f"   k={k}: least N with 2^j | phi(N+j) for 1<=j<=k is N={m}")

    print()
    print("== Z2 (buffer) : the coefficient budget 2^(k/4) ==")
    print(f"   {'N':>9} {'k=floor(lnN^.1)':>16} {'2^(k/4)':>9} "
          f"{'min-shift max d on block':>25} {'min phi on [N,2N)':>19}")
    for e in (10, 12, 14, 16, 18):
        N = 2 ** e
        if 2 * N > min(X, len(dv) - 1):
            break
        k = int(log(N) ** 0.1)
        budget = 2.0 ** (k / 4)
        B = int(10 * log(N)) + 1
        best_d = min(max(dv[r:r + B]) for r in range(N, 2 * N - B))
        print(f"   {N:>9} {k:>16} {budget:>9.3f} {best_d:>25} "
              f"{min(phi[N:2 * N]):>19}")
    print("   d: a shift exists whose block max is a bounded power of log N.")
    print("   phi: EVERY value on EVERY block exceeds N/(e^gamma loglog N + 3).")
    print("   Z2 is the first failing step and it fails for every shift.")

    print()
    print("== the run length actually delivered, L = floor(-log2 T) ==")
    print("   T = sum_{j>k} a(N+j)2^-j with k the maximal Z1 window at N")
    print(f"   truncation depth {DEPTH}: error < (N+k+{DEPTH}+2)*2^-{DEPTH}")
    for name, a, cap in (("d  ", dv, min(X, len(dv) - DEPTH - 4)),
                         ("phi", phi, X - DEPTH - 4)):
        bestL = None
        bestrec = None
        for N in range(2, cap):
            k = window_len(a, N, 64)
            if k == 0:
                continue
            T = tail_after_window(a, N, k, DEPTH)
            if T == 0:
                continue
            L = 0
            while T * (2 ** (L + 1)) < 1:
                L += 1
            if bestL is None or L > bestL:
                bestL, bestrec = L, (N, k, float(T))
        print(f"   a = {name}: max L over N < {cap} is {bestL}   "
              f"(N,k,T) = {bestrec}")
    print("   -> for d the mechanism delivers positive, growing runs of zeros;")
    print("      for phi it delivers L = 0, i.e. no forced zero at any base")
    print("      point and any window length.")

    print()
    print("== window length actually available vs window length required ==")
    print("   T >= 2^-k * R_{N+k} and R_m > m/(e^gamma loglog m + 3), while")
    print("   2^k | phi(N+k) forces 2^k <= phi(N+k) <= N+k-1.  Hence")
    print("     T > 1/(e^gamma loglog(N+k) + 3)   and   L < log2(e^gamma loglog N + 3).")
    print("   A single zero (L>=1) needs 2^k >= 2 R_{N+k}, i.e. k >~ log2 N.")
    print(f"   {'X':>9} {'max window k(N), N<X':>22} {'argmax N':>10} "
          f"{'log2 X (required)':>18} {'deficit':>9}")
    from math import log2 as _log2
    v2 = [0] * (X + 1)
    for m in range(2, X + 1):
        t, c = phi[m], 0
        while t % 2 == 0:
            t //= 2
            c += 1
        v2[m] = c
    cuts = [c for c in (10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6, X - 70) if c <= X - 70]
    marks: dict[int, tuple[int, int]] = {}
    for N in range(2, X - 70):
        k = 0
        while k < 64 and v2[N + k + 1] >= k + 1:
            k += 1
        for c in cuts:
            if N < c and marks.get(c, (0, 0))[0] < k:
                marks[c] = (k, N)
    for c in cuts:
        k, n0 = marks.get(c, (0, 0))
        print(f"   {c:>9} {k:>22} {n0:>10} {_log2(c):>18.2f} "
              f"{_log2(c) - k:>9.2f}")
    print("   -> the available window is far shorter than the required one and")
    print("      the gap widens; no base point in the searched range admits")
    print("      even one forced zero.")

    print()
    print("== unconditional reason ==")
    mx, arg = 0.0, 0
    for M in range(2, X + 1):
        r = (phi[M] // odd_part(phi[M])) / M
        if r > mx:
            mx, arg = r, M
    print(f"   max_{{2<=M<={X}}} 2^v2(phi(M))/M = {mx:.9f} at M={arg}")
    print("   2^v2(phi(M)) <= phi(M) <= M-1 < M for every M >= 2, so the")
    print("   2-part of phi(M) can never reach M.  The window can therefore")
    print("   never absorb the linear-size tail, at any base point.")
    print("   For d the same ratio is irrelevant because d(M) = M^o(1): the")
    print("   tail is killed by SIZE (Z2/Z3), not by the window.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
