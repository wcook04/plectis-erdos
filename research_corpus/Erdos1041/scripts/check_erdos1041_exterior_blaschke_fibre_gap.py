#!/usr/bin/env python3
"""Exact checks for ExteriorBlaschkeFibreCapacityGap.md.

The script checks the rational fibre algebra, comparison with the earlier
independent-factor gap, and the resulting scalar Bergman/COVER improvements.
It does not verify the analytic harmonic-measure identity or solve #1041.
"""

from fractions import Fraction
import math


def fibre_constant(n: int, k: int) -> Fraction:
    return Fraction(k, 2 * n - k)


def old_product_constant(n: int, k: int) -> Fraction:
    return Fraction(n - 1, n + 1) ** (n - k)


def bergman_threshold(n: int, k: int, product_constant: float) -> float:
    return math.tanh(product_constant ** (-2.0 / n)) ** (k / 2.0)


def cover_expression(n: int, k: int, ratio: float, product_constant: float) -> float:
    return product_constant ** (2.0 / n) * math.log(
        1.0 / (1.0 - ratio ** (2.0 / k))
    )


def main() -> None:
    checked = 0
    strict = 0
    for n in range(2, 161):
        for k in range(1, n):
            m = n - k
            new = fibre_constant(n, k)
            old = old_product_constant(n, k)
            assert 0 < new < 1
            assert new <= old
            assert (new == old) == (m == 1)

            # Exact replay of m/n < (1-p)/(1+p) => p < k/(2n-k).
            p = new - Fraction(1, 10_000 * n)
            assert 0 <= p < 1
            assert Fraction(m, n) < (1 - p) / (1 + p)
            assert p < new

            if k >= 2:
                new_threshold = bergman_threshold(n, k, float(new))
                old_threshold = bergman_threshold(n, k, float(old))
                assert new_threshold >= old_threshold
                if m >= 2:
                    assert new_threshold > old_threshold

                ratio = 0.7
                new_cover = cover_expression(n, k, ratio, float(new))
                old_cover = cover_expression(n, k, ratio, float(old))
                assert new_cover <= old_cover
                if m >= 2:
                    assert new_cover < old_cover
                    strict += 1
            checked += 1

    print("EXTERIOR BLASCHKE FIBRE CAPACITY GAP: PASS")
    print(f"  exact component constants checked: {checked}")
    print(f"  strict multi-exterior-root consumer improvements: {strict}")
    for n, k in ((4, 2), (5, 2), (6, 3), (10, 2), (20, 2)):
        new = float(fibre_constant(n, k))
        old = float(old_product_constant(n, k))
        print(
            f"  n={n:2d}, k={k:2d}: product new={new:.12f}, "
            f"old={old:.12f}, ratio={new/old:.12f}"
        )
    print("  claim ceiling: exact scalar consequences; unrestricted #1041 remains open")


if __name__ == "__main__":
    main()
