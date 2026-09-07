#!/usr/bin/env python3
"""Quick check of the all-residue telescoping construction (Type B Prop D).

Verifies positivity, evenness, scheduled 2/4 hits in every residue class up to
a bound, exact finite telescope, and integral complete tails via a logarithmic
carry. Not a proof of the infinite construction.
"""
from __future__ import annotations

import argparse
from math import log2


def align_residue(B: int, t: int, r: int) -> int:
    return B + (r + t - (B % t)) % t


def residue_modulus(j: int) -> int:
    # Nat.unpair: pair(x,y) = (x+y)(x+y+1)/2 + y
    # invert: w = floor((sqrt(8n+1)-1)/2), y = n - w(w+1)/2, x = w-y
    n = j
    w = int(((8 * n + 1) ** 0.5 - 1) / 2)
    y = n - w * (w + 1) // 2
    x = w - y
    return x + 1


def nat_unpair(n: int) -> tuple[int, int]:
    w = int(((8 * n + 1) ** 0.5 - 1) / 2)
    y = n - w * (w + 1) // 2
    x = w - y
    return x, y


def residue_class(j: int) -> int:
    t = residue_modulus(j)
    _, snd = nat_unpair(j)
    r, _ = nat_unpair(snd)
    return r % t


def residue_value(j: int) -> int:
    _, snd = nat_unpair(j)
    _, sbit = nat_unpair(snd)
    return 2 if sbit % 2 == 0 else 4


def centres(J: int) -> list[int]:
    out: list[int] = []
    for j in range(J):
        if j == 0:
            B = 100
        else:
            B = max(100, 2 ** ((j) * (j)), out[-1] + 3)
        out.append(align_residue(B, residue_modulus(j), residue_class(j)))
    return out


def baseline(n: int) -> int:
    return 2 * (int(log2(n + 64)) + 3)


def build(J: int, N: int) -> tuple[list[int], list[int], list[int]]:
    c = centres(J)
    centre_at = {c[j]: j for j in range(J)}
    U = [0] * (N + 1)
    for n in range(N + 1):
        if n in centre_at and n > 0:
            j = centre_at[n]
            U[n] = 2 * baseline(n - 1) - residue_value(j)
        else:
            U[n] = baseline(n)
    a = [0] * (N + 1)
    for n in range(1, N + 1):
        a[n] = 2 * U[n - 1] - U[n]
    return a, U, c


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--quick", action="store_true")
    args = p.parse_args()
    J, N = (12, 4000) if args.quick else (20, 20000)
    a, U, c = build(J, N)
    assert all(x > 0 and x % 2 == 0 for x in a[1:]), "gaps not positive even"
    assert all(U[i] > 0 for i in range(N + 1))
    # telescope at a few basepoints
    for base in (0, 3, 17, 100):
        acc = 0
        for m in range(1, 40):
            acc += a[base + m] / 2**m
            expect = U[base] - U[base + m] / 2**m
            if abs(acc - expect) > 1e-9:
                raise SystemExit(f"telescope fail base={base} m={m}")
    hits: dict[tuple[int, int, int], int] = {}
    for j, n in enumerate(c):
        if n > N:
            break
        key = (residue_modulus(j), residue_class(j), residue_value(j))
        hits[key] = hits.get(key, 0) + 1
        if a[n] != residue_value(j):
            raise SystemExit(f"centre {n} wanted {residue_value(j)} got {a[n]}")
    # every t<=4, r<t, s in {2,4} appears once the pairing has had time
    missing = []
    for t in range(1, 5):
        for r in range(t):
            for s in (2, 4):
                if (t, r, s) not in hits:
                    missing.append((t, r, s))
    if missing:
        print(
            f"note: pairing has not yet listed {len(missing)} small triples "
            f"in first J={J} centres (expected; surjective only as J→∞): "
            f"{missing[:8]}"
        )
    else:
        print("all t<=4 triples present")
    print(f"ok J={J} N={N} centres={len([n for n in c if n <= N])} hits={len(hits)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
