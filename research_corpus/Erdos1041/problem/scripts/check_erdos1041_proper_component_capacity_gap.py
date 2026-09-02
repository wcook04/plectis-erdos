#!/usr/bin/env python3
"""Exact/numerical checks for ProperComponentCapacityGap.md.

This checks only the scalar algebra and threshold consequences.  It does not
claim to verify the analytic exterior factorization or solve Erdős #1041.
"""

from fractions import Fraction
import math


def q_gap(n: int) -> Fraction:
    return Fraction(n - 1, n + 1)


def cluster_threshold(n: int, k: int) -> float:
    q = float(q_gap(n))
    return math.tanh(q ** (-2.0 * (n - k) / n)) ** (k / 2.0)


def main() -> None:
    # Exact peak identity on rational samples, including points arbitrarily
    # close to the sharp separation boundary from above.
    for n in range(2, 81):
        boundary = Fraction(n + 1, n - 1)
        for den in (2, 7, 101, 10007):
            r = boundary + Fraction(1, den)
            lhs = (r * r - 1) / ((r - 1) * (r - 1))
            rhs = (r + 1) / (r - 1)
            assert lhs == rhs
            assert rhs < n

    rows = []
    for n in range(3, 81):
        q = q_gap(n)
        assert 0 < q < 1
        for k in range(2, n):
            improved = cluster_threshold(n, k)
            blind = math.tanh(1.0) ** (k / 2.0)
            assert 0.0 < blind < improved < 1.0
            rows.append((n, k, improved, blind))

    print("PROPER COMPONENT CAPACITY GAP: PASS")
    print("  exact Poisson peak and radius separation: n=2..80")
    print("  all proper cluster thresholds strictly improve capacity-blind bound")
    for n, k in ((3, 2), (4, 2), (5, 2), (5, 4), (10, 2), (20, 2)):
        improved = cluster_threshold(n, k)
        blind = math.tanh(1.0) ** (k / 2.0)
        print(
            f"  n={n:2d}, k={k:2d}: threshold={improved:.12f}, "
            f"blind={blind:.12f}, gain={improved-blind:.12f}"
        )
    print(f"  checked {len(rows)} (n,k) threshold pairs")
    print("  claim ceiling: scalar consequences only; unrestricted #1041 remains open")


if __name__ == "__main__":
    main()
