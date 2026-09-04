#!/usr/bin/env python3
"""Exact replay for the all-arity smooth unique-active exclusion.

This checker is deliberately small.  It verifies the algebraic identities
used in the paper proof and then exercises the strict inequality on exact
rational samples.  Positivity in the stated domain is discharged in the proof
by visibly positive factors rather than by floating-point testing.
"""

from __future__ import annotations

import json
from fractions import Fraction

try:
    import sympy as sp
except ImportError as exc:  # pragma: no cover
    raise SystemExit("sympy is required for the symbolic replay") from exc


def symbolic_replay() -> dict[str, object]:
    q, r, alpha = sp.symbols("q r alpha", positive=True, real=True)
    n = q**2 + r**2 - 2 * q * r * sp.cos(alpha)
    d = 1 + q**2 * r**2 - 2 * q * r * sp.cos(alpha)
    angular = sp.diff(sp.log(n) / 2 - sp.log(d) / 2, alpha)
    angular_expected = q * r * (1 - q**2) * (1 - r**2) * sp.sin(alpha) / (n * d)
    assert sp.simplify(angular - angular_expected) == 0

    plus = r * sp.diff(sp.log((q - r) / (1 - q * r)), r)
    plus_expected = -r * (1 - q**2) / ((1 - q * r) * (q - r))
    assert sp.simplify(plus - plus_expected) == 0

    minus = r * sp.diff(sp.log((q + r) / (1 + q * r)), r)
    minus_expected = r * (1 - q**2) / ((1 + q * r) * (q + r))
    assert sp.simplify(minus - minus_expected) == 0

    delta = (q - r) / (1 - q * r)
    assert sp.simplify(q - delta - r * (1 - q**2) / (1 - q * r)) == 0

    arities: list[int] = []
    for m in range(2, 17):
        a_m = sum(q ** (m - 1 - i) * r**i for i in range(m))
        d_m = sum((q * r) ** i for i in range(m))
        positive_sum = sum(
            q ** (m - 1 - i) * r**i * (1 - q ** (2 * i))
            for i in range(1, m)
        )
        assert sp.expand(a_m - q ** (m - 1) * d_m - positive_sum) == 0
        regular = (q**m - r**m) / (1 - (q * r) ** m)
        assert sp.simplify(regular - delta * a_m / d_m) == 0
        arities.append(m)

    return {
        "angular_envelope_identity": True,
        "plus_scale_identity": True,
        "minus_scale_identity": True,
        "delta_below_q_identity": True,
        "finite_sum_factorisation_arities": arities,
    }


def exact_rational_replay() -> dict[str, object]:
    samples = [
        (Fraction(1, 11), Fraction(2, 7)),
        (Fraction(2, 13), Fraction(5, 9)),
        (Fraction(3, 10), Fraction(7, 10)),
        (Fraction(5, 12), Fraction(11, 13)),
        (Fraction(7, 20), Fraction(19, 20)),
    ]
    checked = 0
    for r, q in samples:
        assert 0 < r < q < 1
        delta = (q - r) / (1 - q * r)
        assert 0 < delta < q < 1
        for m in range(2, 33):
            coincident = delta**m
            regular = (q**m - r**m) / (1 - (q * r) ** m)
            assert coincident < regular
            checked += 1
    return {"exact_pairs": len(samples), "arity_range": [2, 32], "checks": checked}


def main() -> None:
    receipt = {
        "checker": "erdos1041_unique_active_all_arity",
        "symbolic": symbolic_replay(),
        "exact_rational": exact_rational_replay(),
        "status": "PASS",
        "scope_note": (
            "The replay verifies algebra. The proof's positivity steps use "
            "0 < r < q < 1 and m >= 2; it does not certify multi-active contacts."
        ),
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
