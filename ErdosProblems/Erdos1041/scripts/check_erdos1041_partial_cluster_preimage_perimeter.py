#!/usr/bin/env python3
"""Exact regressions for the partial-cluster preimage-perimeter identity.

The analytic covering-space theorem lives in
PartialClusterPreimagePerimeterIdentity.md.  This checker exactifies the finite
permutation bookkeeping and the regular-polygon scalar specialization.  It
does not certify numerical root continuation or the unrestricted problem.
"""

from __future__ import annotations

from fractions import Fraction


PI_UPPER = Fraction(355, 113)


def lollipop_sum(
    stems: tuple[Fraction, ...],
    boundary_arcs: tuple[Fraction, ...],
    permutation: tuple[int, ...],
) -> Fraction:
    """Sum forward stem, boundary lift, and permuted reverse stem costs."""

    assert len(stems) == len(boundary_arcs) == len(permutation)
    assert sorted(permutation) == list(range(len(permutation)))
    return sum(
        stems[j] + boundary_arcs[j] + stems[permutation[j]]
        for j in range(len(stems))
    )


def regular_upper_length(n: int, r: Fraction, s: Fraction) -> Fraction:
    return 2 * (r - s) + 2 * PI_UPPER * s / n


def main() -> None:
    # A deliberately asymmetric exact fixture: only the permutation property,
    # not equality of individual branches, is used by the stem bookkeeping.
    stems = (Fraction(1, 7), Fraction(2, 9), Fraction(5, 11), Fraction(3, 8))
    boundary = (Fraction(7, 20), Fraction(4, 13), Fraction(9, 17), Fraction(2, 5))
    sigma = (2, 0, 3, 1)
    total = lollipop_sum(stems, boundary, sigma)
    expected = 2 * sum(stems) + sum(boundary)
    assert total == expected

    # One rational choice works in every displayed degree.  The use of the
    # classical rational upper bound makes the strict comparison exact.
    r = Fraction(3, 4)
    s = Fraction(1, 100)
    rows: list[tuple[int, Fraction]] = []
    for n in range(2, 21):
        upper = regular_upper_length(n, r, s)
        assert s < r < 1
        assert s**n < min(r**n, 1 - r**n)
        assert upper < 2
        if n >= 4:
            assert PI_UPPER < n
            assert upper < 2 * r
        rows.append((n, 2 - upper))

    print("PARTIAL CLUSTER PREIMAGE-PERIMETER: PASS")
    print(f"exact bookkeeping total = {total}")
    for n, margin in rows:
        print(f"degree {n}: rational lower margin to 2 = {margin}")


if __name__ == "__main__":
    main()
