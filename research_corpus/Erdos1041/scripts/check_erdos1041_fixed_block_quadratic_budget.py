#!/usr/bin/env python3
"""Exact finite replay of the fixed-block quadratic-budget equivalence."""

from fractions import Fraction


def averages(velocities: tuple[Fraction, ...], weights: tuple[Fraction, ...]):
    assert len(velocities) == len(weights) and velocities
    assert all(v >= 0 for v in velocities)
    assert all(w > 0 for w in weights)
    count = Fraction(len(velocities), 1)
    length = sum(velocities, Fraction(0)) / count
    lifetime = sum(weights, Fraction(0)) / count
    energy = sum(
        (v * v / w for v, w in zip(velocities, weights, strict=True)),
        Fraction(0),
    ) / count
    return length, lifetime, energy


def main() -> None:
    velocities = tuple(map(Fraction, (0, 1, 2, 3, 5, 8)))
    arbitrary = tuple(map(Fraction, (7, 2, 11, 4, 13, 6)))
    length, lifetime, energy = averages(velocities, arbitrary)
    assert lifetime * energy >= length * length

    # When every velocity is positive, lambda=v attains equality exactly.
    positive = tuple(map(Fraction, (1, 2, 3, 5, 8, 13)))
    p_length, p_lifetime, p_energy = averages(positive, positive)
    assert p_lifetime * p_energy == p_length * p_length

    # With a zero velocity, lambda=v+epsilon approaches the same infimum.
    errors = []
    for denominator in (2, 10, 100, 1000, 10000):
        epsilon = Fraction(1, denominator)
        regularized = tuple(v + epsilon for v in velocities)
        z_length, z_lifetime, z_energy = averages(velocities, regularized)
        product = z_lifetime * z_energy
        assert product >= z_length * z_length
        assert product <= (z_length + epsilon) * z_length
        errors.append(product - z_length * z_length)
    assert all(b < a for a, b in zip(errors, errors[1:]))

    # Pigeonhole selection is on whole branch lengths, after integration.
    branch_lengths = tuple(map(Fraction, (3, 2, 1)))
    average_branch_length = sum(branch_lengths, Fraction(0)) / 3
    assert average_branch_length == 2
    assert min(branch_lengths) <= average_branch_length

    # Fixed-point compensation.  The first two sheets are moved and the last
    # two are fixed.  A whole-block C-budget plus a matching fixed-sheet lower
    # budget forces one moved complete lift below C.
    threshold = Fraction(2)
    moved = tuple(map(Fraction, (3, 1)))
    fixed = tuple(map(Fraction, (2, 2)))
    assert sum(moved + fixed, Fraction(0)) <= threshold * len(moved + fixed)
    assert sum(fixed, Fraction(0)) >= threshold * len(fixed)
    assert min(moved) <= threshold

    # A derangement has no fixed-sheet allocation loss.
    derangement_lengths = tuple(map(Fraction, (3, 2, 1)))
    assert sum(derangement_lengths, Fraction(0)) <= threshold * len(
        derangement_lengths
    )
    assert min(derangement_lengths) <= threshold

    # Sharp obstruction when the fixed sheets do not pay the baseline.  The
    # transposed sheets are both too long although the whole-block mean is C.
    delta = Fraction(1, 4)
    moved_obstruction = (threshold + delta, threshold + delta)
    fixed_obstruction = (threshold - 2 * delta,)
    obstruction = moved_obstruction + fixed_obstruction
    assert sum(obstruction, Fraction(0)) == threshold * len(obstruction)
    assert min(moved_obstruction) > threshold
    assert sum(fixed_obstruction, Fraction(0)) < threshold * len(
        fixed_obstruction
    )

    print("FIXED-BLOCK QUADRATIC BUDGET EQUIVALENCE: PASS")
    print("cauchy_gap", lifetime * energy - length * length)
    print("regularized_final_gap", errors[-1])
    print("fixed_point_compensation_obstruction", obstruction)


if __name__ == "__main__":
    main()
