#!/usr/bin/env python3
"""Exact receipts for ReserveLineageTaxBudgetNoGo.md."""

from fractions import Fraction


def w(n: int) -> Fraction:
    return Fraction(1, (1 << n) - 1)


def packet(height: int, exponent: int) -> Fraction:
    return Fraction(1 << exponent, 3 * ((1 << height) - 1))


def carry_mass(r: int) -> Fraction:
    return Fraction(1, 1 << (r - 2))


def g(r: int) -> Fraction:
    return 3 * w(r) / carry_mass(r)


RHO = Fraction(31, 60)
HISTORICAL_SIBLING_FACTOR = 1 / (1 - RHO)  # 60/29
TOTAL_EPOCH_FACTOR = 1 + HISTORICAL_SIBLING_FACTOR  # 89/29


def check_tax_domination(max_rank: int = 500) -> int:
    checks = 0
    for r in range(5, max_rank + 1):
        # Worst normalized atom potential minus the universal 3/4 floor.
        tax_ratio = TOTAL_EPOCH_FACTOR * (g(r - 1) - Fraction(3, 4))
        reserve_ratio = 1 - g(r)
        assert tax_ratio < reserve_ratio
        assert TOTAL_EPOCH_FACTOR < 4
        checks += 1
    return checks


def check_lineage_handoff() -> dict[str, object]:
    reservoir = packet(15, 2)
    sibling = packet(15, 1)
    child = packet(15, 0)
    mass = carry_mass(15)

    assert reservoir == w(15) + child
    assert sibling + child == w(15)
    assert reservoir + sibling == 2 * w(15) < w(14)
    assert Fraction(1, 1 << 15) == mass / 4
    assert Fraction(2, 1 << 15) == mass / 2
    assert 2 + 15 - 1 == 16  # sibling front
    assert 2 + 15 - 0 == 17  # selected child front

    return {
        "reservoir": "P(15,2)",
        "sibling": "P(15,1)",
        "selected_child": "P(15,0)",
        "sibling_front": 16,
        "selected_child_front": 17,
        "sibling_plus_child": str(sibling + child),
        "complete_pair": str(reservoir + sibling),
        "predecessor": str(w(14)),
        "post_open_load_over_rank15_mass": "3/4",
    }


def main() -> None:
    print(
        {
            "tax_domination_checks": check_tax_domination(),
            "sibling_tree_load_factor": str(HISTORICAL_SIBLING_FACTOR),
            "reservoir_plus_sibling_factor": str(TOTAL_EPOCH_FACTOR),
            "tax_magnitude_obstruction": False,
            "lineage_handoff_counterexample": check_lineage_handoff(),
            "single_lineage_schedule_proved": False,
        }
    )


if __name__ == "__main__":
    main()
