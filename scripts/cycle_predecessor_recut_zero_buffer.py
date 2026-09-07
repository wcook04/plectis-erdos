#!/usr/bin/env python3
"""Exact receipts for CyclePredecessorRecutAndZeroBufferNoGo.md."""

from fractions import Fraction


def w(n: int) -> Fraction:
    return Fraction(1, (1 << n) - 1)


def packet(height: int, exponent: int) -> Fraction:
    return Fraction(1 << exponent, 3 * ((1 << height) - 1))


def carry_mass(r: int) -> Fraction:
    return Fraction(1, 1 << (r - 2))


def g(r: int) -> Fraction:
    return 3 * w(r) / carry_mass(r)


ALPHA_MAX = Fraction(1 << 15, (1 << 15) - 1)
RHO = ALPHA_MAX - Fraction(3, 4)


def check_full_bank(max_rank: int = 500) -> int:
    checks = 0
    for r in range(4, max_rank + 1):
        mass = carry_mass(r)
        tax = w(r - 1) - 2 * w(r)
        assert tax > 0
        assert mass / 3 >= w(r) + tax
        assert ALPHA_MAX - g(r) < 2 * (1 - g(r - 1))
        assert ALPHA_MAX < 2 * g(r - 1)
        assert ALPHA_MAX - g(r - 1) <= RHO
        checks += 1
    return checks


def check_zero_buffer_counterexample() -> dict[str, object]:
    height = 15
    leading = packet(height, 2)
    external = packet(height, 1)
    child = packet(height, 0)
    mass = carry_mass(15)

    assert leading > w(15)
    assert leading - w(15) == child
    assert external + child == w(15)
    assert leading + external == 2 * w(15)
    assert leading + external < w(14)

    child_load = Fraction(1, 1 << height)
    external_load = Fraction(2, 1 << height)
    assert child_load / mass == Fraction(1, 4)
    assert external_load / mass == Fraction(1, 2)
    assert (child_load + external_load) / mass == Fraction(3, 4)
    assert child_load + external_load < mass
    assert Fraction(1, 4) < RHO

    return {
        "leading_packet": "P(15,2)",
        "external_packet": "P(15,1)",
        "opened_child": "P(15,0)",
        "complete_value": str(leading + external),
        "predecessor_weight": str(w(14)),
        "post_open_scalar_tail": str(external + child),
        "post_open_load_over_rank15_mass": "3/4",
        "cycle_triggered": False,
        "boolean_duplicate_forced": 15,
    }


def main() -> None:
    print(
        {
            "full_bank_checks": check_full_bank(),
            "cycle_implies_predecessor_recut": True,
            "cycle_recut_load_ratio_bound": f"strictly less than {RHO}",
            "zero_buffer_counterexample": check_zero_buffer_counterexample(),
            "cycle_trigger_alone_is_complete": False,
        }
    )


if __name__ == "__main__":
    main()
