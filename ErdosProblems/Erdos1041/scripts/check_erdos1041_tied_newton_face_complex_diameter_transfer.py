#!/usr/bin/env python3
"""Exact rational checks for the strict complex-diameter transfer ledger."""

from fractions import Fraction as F


def main() -> None:
    # If B_R <= 1 and t >= 2R, each lower-mode ratio gains at least R/t <= 1/2.
    weights = [F(1, 7), F(2, 9), F(5, 18), F(1, 3)]
    assert sum(weights) <= 1
    exponents = [1, 2, 3, 5]
    contraction = sum(w * F(1, 2) ** e for w, e in zip(weights, exponents))
    assert contraction <= F(1, 2) * sum(weights) <= F(1, 2)

    # The exact mesoscopic ledger in the theorem.
    assert -F(7, 8) + F(1, 2) + F(1, 8) + F(1, 8) == -F(1, 8)

    # Genuinely complex quartic tube witness inherited from the model theorem.
    A = F(2 + 8, 50)
    B = (F(1, 8) + F(1, 2)) / 50
    delta = F(1) - A
    assert A == F(1, 5)
    assert B == F(1, 80) <= 1
    assert delta == F(4, 5) > 0

    # At the transferred cutoff 2R=4 the witness has far more than half-leading
    # domination: (d1*t+d3*t^3)/t^4 = 17/3200.
    t = F(4)
    lower_ratio = (F(1, 50) * t + F(1, 50) * t**3) / t**4
    assert lower_ratio == F(17, 3200) < F(1, 2)

    # A representative exact compact/collar absorption ledger.
    compact_error = F(1, 5)
    assert compact_error < delta
    epsilon = F(1, 4)
    collar_gap = epsilon**4
    collar_error = collar_gap / 2
    assert (1 - collar_gap) + collar_error < 1

    print("PASS: exact complex-diameter finite-transfer budgets")
    print(f"model_margin={delta} cutoff_lower_ratio={lower_ratio}")
    print(f"mesoscopic_margin={F(1, 8)} collar_gap={collar_gap}")


if __name__ == "__main__":
    main()

