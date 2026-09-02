#!/usr/bin/env python3
"""Exact symbolic replay for the sextic second-mode cubic symmetry lift."""

from __future__ import annotations

import sympy as sp


def main() -> None:
    t, r, c = sp.symbols("t r c", real=True)
    sqrt_three = sp.sqrt(3)
    omega = sp.Rational(1, 2) + sp.I * sqrt_three / 2
    z = sp.expand(r * ((1 - t) + t * omega))
    cubic_im = sp.simplify(sp.im(sp.expand(z**3)))
    expected = sp.Rational(3, 2) * sqrt_three * r**3 * t * (1 - t)
    assert sp.simplify(cubic_im - expected) == 0

    b = sp.symbols("b")
    # Symbolic parity bookkeeping: even degrees survive z -> -z; degree 3 flips.
    assert sp.expand((-b) ** 2 - b**2) == 0
    assert sp.expand((-b) ** 6 - b**6) == 0
    assert sp.expand((-b) ** 3 + b**3) == 0
    assert sp.simplify(sp.re(sp.I * c * z**3) + c * cubic_im) == 0

    print("exact cubic chord shape:", cubic_im)
    print("EXACT PASS: even antipodal invariance and odd cubic sign reversal")


if __name__ == "__main__":
    main()
