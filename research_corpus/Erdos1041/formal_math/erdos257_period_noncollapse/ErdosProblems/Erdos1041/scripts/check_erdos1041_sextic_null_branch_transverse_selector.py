#!/usr/bin/env python3
"""Exact replay for the sextic null-branch transverse selector."""

from __future__ import annotations

import random

import sympy as sp


def main() -> None:
    p, q, r, x, delta = sp.symbols("p q r x delta", real=True)
    contacts = [p + q + r, p - q - r, -p - q + r, -p + q - r]
    energy = p**2 + q**2 + r**2

    assert sp.expand(sum(contacts)) == 0
    assert sp.expand(sum(value**2 for value in contacts) - 4 * energy) == 0

    # The constant 3 is sharp: a tetrahedron vertex gives (3,-1,-1,-1).
    sharp = [sp.expand(value.subs({p: 1, q: 1, r: 1})) for value in contacts]
    assert sharp == [3, -1, -1, -1]
    assert energy.subs({p: 1, q: 1, r: 1}) == 3

    # The completing-square constant used by the chord absorption lemma.
    absorption = sp.expand(
        -x**2 / 20 + 3 * delta * x
        - (45 * delta**2 - (x - 30 * delta) ** 2 / 20)
    )
    assert absorption == 0

    # The geometric null relation agrees with the exact continued branch.
    s, radius = sp.sqrt(3), sp.symbols("radius", positive=True)
    a = radius * (3 - s) / 2
    assert sp.simplify(2 * a**2 / radius - 3 * radius * (2 - s)) == 0

    rng = random.Random(104120260825)
    least_slack = None
    for _ in range(100_000):
        values = [sp.Rational(rng.randint(-10_000, 10_000), 997) for _ in range(3)]
        pv, qv, rv = values
        cv = [
            pv + qv + rv,
            pv - qv - rv,
            -pv - qv + rv,
            -pv + qv - rv,
        ]
        m = min(cv)
        e = pv**2 + qv**2 + rv**2
        assert m <= 0
        slack = 3 * m**2 - e
        assert slack >= 0
        if least_slack is None or slack < least_slack:
            least_slack = slack

    print("contacts:", contacts)
    print("sharp fixture:", sharp)
    print("least exact random slack:", least_slack)
    print("PASS: exact tetrahedral selector and quadratic absorption identity")


if __name__ == "__main__":
    main()
