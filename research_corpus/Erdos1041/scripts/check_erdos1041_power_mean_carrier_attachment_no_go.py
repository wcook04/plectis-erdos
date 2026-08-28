#!/usr/bin/env python3
"""Exact replay of the regular-quartic `p=1` carrier-attachment no-go."""

from fractions import Fraction

import sympy as sp


def main() -> None:
    t = sp.Rational(1, 2)
    r = sp.Rational(99, 100)
    root_distances = (0, sp.sqrt(2), 2, sp.sqrt(2))
    hub_distances = (1, 1, 1, 1)
    factors = tuple(
        sp.simplify(r * (t * d + (1 - t) * e))
        for d, e in zip(hub_distances, root_distances, strict=True)
    )
    dual_product = sp.simplify(sp.prod(factors))
    expected = sp.simplify(r**4 * 3 * (3 + 2 * sp.sqrt(2)) / 16)
    assert sp.simplify(dual_product - expected) == 0

    # Fully rational strict lower certificate: sqrt(2) > 7/5.
    assert Fraction(7, 5) ** 2 < 2
    rational_lower = r**4 * sp.Rational(87, 80)
    assert rational_lower > 1
    assert sp.N(dual_product, 50) > 1

    # The certificate fails while the actual radial arm is safe.
    # For 0 <= s < 1, |(rs)^4-r^4|=r^4(1-s^4)<r^4<1.
    assert r**4 < 1

    print("POWER-MEAN CARRIER ATTACHMENT NO-GO: PASS")
    print("dual_product_at_half", sp.N(dual_product, 20))
    print("rational_lower", rational_lower)


if __name__ == "__main__":
    main()
