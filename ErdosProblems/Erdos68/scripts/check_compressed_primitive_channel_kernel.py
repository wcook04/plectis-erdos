#!/usr/bin/env python3
"""Exact checks for the compressed primitive channel kernel (R1--R3).

Usage:
  ./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/scripts/check_compressed_primitive_channel_kernel.py --quick
"""

from __future__ import annotations

import argparse
from math import factorial, gcd, lcm, prod


def poly_from_roots(a_vals: list[int]) -> list[int]:
    """Coefficients of prod (a X - 1), low degree first."""
    h = [1]
    for a in a_vals:
        nxt = [0] * (len(h) + 1)
        for j, v in enumerate(h):
            nxt[j] -= v
            nxt[j + 1] += a * v
        h = nxt
    return h


def primitive_kernel(D: int, r: int, L: int) -> dict[str, object]:
    a_vals = [factorial(d) ** (L // d) for d in range(2, D + 1)]
    h = poly_from_roots(a_vals)
    idx = [r + j * L for j in range(D)]
    N = idx[-1]
    A = prod(a_vals)
    fs = [factorial(i) for i in idx]
    assert factorial(N) % A == 0
    lam = [factorial(N) * h[j] // (A * fs[j]) for j in range(D)]
    return {
        "a_vals": a_vals,
        "h": h,
        "idx": idx,
        "N": N,
        "A": A,
        "lam": lam,
        "moment": sum(lam[j] * fs[j] for j in range(D)),
        "fs": fs,
    }


def channel(lam: list[int], idx: list[int], fs: list[int], d: int) -> int:
    return sum(lam[j] * fs[j] // (factorial(d) ** (idx[j] // d)) for j in range(D_from(idx)))


def D_from(idx: list[int]) -> int:
    return len(idx)


def run_quick() -> None:
    # Equal-block divisibility: floor(i/d)! (d!)^{floor(i/d)} | i!.
    for i in range(100):
        for d in range(1, 30):
            q = i // d
            assert factorial(i) % (factorial(q) * factorial(d) ** q) == 0

    # D=2 closed form on the compressed step L=2: last coordinate 1.
    for r in (2, 3, 6, 7, 11):
        data = primitive_kernel(2, r, 2)
        lam = data["lam"]
        assert lam[-1] == 1
        assert lam[0] == -((r + 1) * (r + 2) // 2)
        assert data["moment"] == factorial(r + 2) // 2
        assert gcd(abs(lam[0]), abs(lam[1])) == 1

    # Lean-scale D=2 grid L=4, last coordinate 1.
    for r in (2, 3, 6):
        data = primitive_kernel(2, r, 4)
        lam = data["lam"]
        assert lam[-1] == 1
        assert lam[0] == -((r + 1) * (r + 2) * (r + 3) * (r + 4) // 4)
        assert data["moment"] == 3 * factorial(r + 4) // 4

    tests = 0
    for D in range(2, 7):
        L = lcm(*range(2, D + 1))
        for r in (2, 3, 6):
            data = primitive_kernel(D, r, L)
            lam = data["lam"]
            idx = data["idx"]
            fs = data["fs"]
            a_vals = data["a_vals"]
            N = data["N"]
            A = data["A"]
            h = data["h"]
            assert lam[-1] == 1
            g = 0
            for v in lam:
                g = gcd(g, abs(v))
            assert g == 1
            for d in range(2, D + 1):
                assert channel(lam, idx, fs, d) == 0
            h1 = prod(z - 1 for z in a_vals)
            assert data["moment"] == factorial(N) // A * h1
            assert data["moment"] == sum(
                factorial(N) * h[j] // A for j in range(D)
            )
            kfac = prod(factorial(L // d) for d in range(2, D + 1))
            assert (factorial(N) // A) % (factorial(r) * kfac) == 0
            assert data["moment"] % (
                factorial(r) * kfac * prod(z - 1 for z in a_vals)
            ) == 0
            tests += 1
    assert tests == 15
    print("check_compressed_primitive_channel_kernel: PASS")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--quick", action="store_true")
    parser.parse_args()
    run_quick()


if __name__ == "__main__":
    main()
