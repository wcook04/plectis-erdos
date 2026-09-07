#!/usr/bin/env python3
"""Exact replay for ThreeExteriorLowCapacityImbalanceCone.md."""

import sympy as sp


def main() -> None:
    z = sp.symbols("z", real=True)
    n_symbol = sp.symbols("n", positive=True)
    d_symbol = n_symbol - 3
    log_derivative = 1 / (z - 1) + 2 / (z + 1) - n_symbol / z
    generic_target = -(d_symbol*z*z + z - n_symbol) / (z*(z*z - 1))
    assert sp.simplify(log_derivative - generic_target) == 0
    # On z>=1 and n>3, d z^2+z-n is strictly increasing, equals -2 at
    # z=1, and hence has the single positive root displayed in the note.
    root_generic = (sp.sqrt(1 + 4*d_symbol*n_symbol) - 1) / (2*d_symbol)
    assert sp.simplify((d_symbol*z*z + z - n_symbol).subs(z, root_generic)) == 0
    assert sp.simplify((d_symbol*z*z + z - n_symbol).subs(z, 1)) == -2
    data = {
        5: {
            "root": (sp.sqrt(41) - 1) / 4,
            "M": (sp.Integer(822) + 82 * sp.sqrt(41)) / 3125,
            "C": 3 * 2 ** sp.Rational(2, 3) * 5 ** sp.Rational(1, 3) / 25,
            "derivative": -(z + 1) * (2 * z**2 + z - 5) / z**6,
            "threshold_power": 2,
        },
        6: {
            "root": (sp.sqrt(73) - 1) / 6,
            "M": (sp.Integer(12881) + 2117 * sp.sqrt(73)) / 93312,
            "C": sp.Rational(1, 4),
            "derivative": -(z + 1) * (3 * z**2 + z - 6) / z**7,
            "threshold_power": 3,
        },
    }
    for n, row in data.items():
        f = (z - 1) * (z + 1) ** 2 / z**n
        assert sp.simplify(sp.diff(f, z) - row["derivative"]) == 0
        root = row["root"]
        assert root > 1
        assert sp.simplify(f.subs(z, root) - row["M"]) == 0
        # The quadratic factor is negative on (1, root) and positive after it,
        # so the displayed derivative has the required increase/decrease sign.
        numerator = sp.factor(-row["derivative"] * z ** (n + 1) / (z + 1))
        assert sp.simplify(numerator.subs(z, 1)) < 0
        assert sp.limit(numerator, z, sp.oo) == sp.oo
        threshold = sp.root(row["M"] / row["C"], row["threshold_power"])
        assert threshold > 1
        # The threshold is merely orientation; the theorem uses the exact
        # algebraic condition B^(n-3) C_n >= M_n.
        assert sp.N(threshold, 25) > 1
        print(f"n={n} z_star={sp.N(root, 18)} M={sp.N(row['M'], 18)} "
              f"T={sp.N(threshold, 18)}")
    print("PASS exact homogeneous low-capacity imbalance-cone replay")


if __name__ == "__main__":
    main()
