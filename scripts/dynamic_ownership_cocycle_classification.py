#!/usr/bin/env python3
"""Exact receipt for the dynamic ownership cocycle classification/no-go."""

from __future__ import annotations

from fractions import Fraction
from math import gcd


def atom(d: int, n: int) -> Fraction:
    assert d >= 1
    return Fraction(1 << (n % d), (1 << d) - 1)


def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b


def purity(value: int, masses: tuple[int, ...], p: int) -> Fraction:
    assert value > 0 and p > 1 and sum(masses) == value
    return Fraction(sum(m**p for m in masses), value ** (p - 1))


def audit_local_cocycle() -> int:
    checks = 0
    for d in range(1, 25):
        for kappa in (Fraction(1), Fraction(3, 7), Fraction(11, 5)):
            phases = [kappa * (1 << a) / ((1 << d) - 1) for a in range(d)]
            for a in range(d - 1):
                assert 2 * phases[a] - phases[a + 1] == 0
                checks += 1
            assert 2 * phases[-1] - phases[0] == kappa
            checks += 1
    return checks


def audit_atom_step_and_pair_kernel() -> tuple[int, int]:
    step_checks = 0
    pair_checks = 0
    for d in range(1, 25):
        for n in range(4 * d):
            pulse = int((n + 1) % d == 0)
            assert 2 * atom(d, n) - atom(d, n + 1) == pulse
            step_checks += 1
    for d in range(1, 15):
        for e in range(1, 15):
            period = lcm(d, e)
            observed = sum(
                (atom(d, n) * atom(e, n) for n in range(period)),
                Fraction(),
            ) / period
            g = gcd(d, e)
            expected = Fraction((1 << g) + 1, 3 * period * ((1 << g) - 1))
            assert observed == expected
            pair_checks += 1
    return step_checks, pair_checks


def pair_energy(support: tuple[int, ...], n: int) -> Fraction:
    values = [atom(d, n) for d in support]
    total = sum(values, Fraction())
    return total * total - sum((value * value for value in values), Fraction())


def collision_charge(support: tuple[int, ...], n: int) -> Fraction:
    pulse_sources = tuple(d for d in support if (n + 1) % d == 0)
    pulse_count = len(pulse_sources)
    total = sum((atom(d, n) for d in support), Fraction())
    pulse_mass = sum((atom(d, n) for d in pulse_sources), Fraction())
    return (
        4 * (pulse_count * total - pulse_mass)
        - pulse_count * (pulse_count - 1)
    )


def audit_pair_energy_resolvent() -> int:
    checks = 0
    supports = ((2, 3), (2, 3, 5), (3, 4, 6, 7), (5, 7, 8, 11))
    for support in supports:
        period = 1
        for d in support:
            period = lcm(period, d)
        energy_sum = Fraction()
        charge_sum = Fraction()
        for n in range(period):
            energy = pair_energy(support, n)
            next_energy = pair_energy(support, n + 1)
            charge = collision_charge(support, n)
            pulse_count = sum((n + 1) % d == 0 for d in support)
            assert next_energy == 4 * energy - charge
            assert charge >= pulse_count * (pulse_count - 1)
            energy_sum += energy
            charge_sum += charge
            checks += 2
        assert charge_sum == 3 * energy_sum
        checks += 1

        # Periodicity converts the infinite discounted resolvent into one
        # exact geometric cycle.
        cycle = sum(
            (
                Fraction(collision_charge(support, r - 1), 4**r)
                for r in range(1, period + 1)
            ),
            Fraction(),
        )
        resolved = cycle / (1 - Fraction(1, 4**period))
        assert resolved == pair_energy(support, 0)
        checks += 1
    return checks


def audit_convex_carry_tree() -> int:
    checks = 0
    for p in (2, 3, 4):
        # The elementary equal-value merge inequality is tested on exact
        # integer source vectors.  Its general proof is convexity.
        samples = (
            ((3, 0, 1), (0, 2, 2)),
            ((1, 1, 2), (2, 1, 1)),
            ((0, 4, 0), (3, 0, 1)),
        )
        for left, right in samples:
            value = sum(left)
            assert sum(right) == value
            merged = tuple(a + b for a, b in zip(left, right, strict=True))
            assert purity(2 * value, merged, p) <= (
                purity(value, left, p) + purity(value, right, p)
            )
            checks += 1

        for depth in range(1, 13):
            source_count = 1 << depth
            output = purity(source_count, (1,) * source_count, p)
            assert output == Fraction(source_count ** (2 - p))
            assert output / source_count == Fraction(
                1, source_count ** (p - 1)
            )
            checks += 1
    return checks


def main() -> None:
    local_checks = audit_local_cocycle()
    step_checks, pair_checks = audit_atom_step_and_pair_kernel()
    energy_checks = audit_pair_energy_resolvent()
    purity_checks = audit_convex_carry_tree()
    print(
        {
            "local_cocycle_checks": local_checks,
            "source_atom_step_checks": step_checks,
            "pair_kernel_checks": pair_checks,
            "pair_energy_resolvent_checks": energy_checks,
            "convex_purity_checks": purity_checks,
            "classification": "every additive source-local cocycle is a weighted shifted atom",
            "nonlinear_no_go": "distinct-source carry trees erase convex purity relative to spendable value",
            "dense_case_solved": False,
        }
    )


if __name__ == "__main__":
    main()
