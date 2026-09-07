#!/usr/bin/env python3
"""Exact interval certificate for ReversibleLaminarRollbackNoGo.md."""

from fractions import Fraction


def w(n: int) -> Fraction:
    return Fraction(1, (1 << n) - 1)


def carry_mass(r: int) -> Fraction:
    return Fraction(1, 1 << (r - 2))


def g(r: int) -> Fraction:
    return Fraction(3 * (1 << (r - 2)), (1 << r) - 1)


HEIGHT_DIVISOR = 15
ALPHA_MAX = Fraction(1 << HEIGHT_DIVISOR, (1 << HEIGHT_DIVISOR) - 1)
HEIGHT_FACTOR_MIN = Fraction((1 << HEIGHT_DIVISOR) - 1, 1 << HEIGHT_DIVISOR)


def child_ratio_bounds(r: int) -> tuple[Fraction, Fraction]:
    """Strict lower and upper bounds for a root-genealogy component."""
    lower = HEIGHT_FACTOR_MIN * (1 - g(r))
    upper = ALPHA_MAX - g(r)
    assert 0 < lower < upper < Fraction(251, 1000)
    return lower, upper


def forced_front(lower_load: Fraction, upper_load: Fraction) -> int:
    """The common leading binary-load rank for an interval of loads."""
    for r in range(2, 100):
        mass = carry_mass(r)
        if lower_load >= mass and upper_load < 2 * mass:
            return r
    raise AssertionError("load interval does not force one front rank")


def open_front_interval(
    lower_load: Fraction, upper_load: Fraction, r: int
) -> tuple[Fraction, Fraction]:
    mass = carry_mass(r)
    lower_ratio, upper_ratio = child_ratio_bounds(r)
    return (
        lower_load - mass + lower_ratio * mass,
        upper_load - mass + upper_ratio * mass,
    )


def check_forced_return() -> dict[str, object]:
    # The anchored load of 1510 M(2,15).
    lower_load = upper_load = Fraction(1510, 1 << 15)
    trace: list[int] = []
    intervals: list[dict[str, object]] = []

    for expected in [7, 8, 9, 10, 12]:
        r = forced_front(lower_load, upper_load)
        assert r == expected
        mass = carry_mass(r)
        before = (lower_load / mass, upper_load / mass)
        lower_load, upper_load = open_front_interval(lower_load, upper_load, r)
        after = (lower_load / mass, upper_load / mass)
        trace.append(r)
        intervals.append(
            {
                "rank": r,
                "before_over_mass": tuple(map(str, before)),
                "after_over_mass": tuple(map(str, after)),
            }
        )

    # Opening the provisional rank-twelve component forces rank twelve again.
    assert forced_front(lower_load, upper_load) == 12
    trace.append(12)

    mass12 = carry_mass(12)
    # The external forest alone has load below one rank-twelve mass, but the
    # external forest plus the opened descendants has load above it.
    before_open_lower = Fraction(1510, 1 << 15)
    before_open_upper = before_open_lower
    for r in [7, 8, 9, 10]:
        before_open_lower, before_open_upper = open_front_interval(
            before_open_lower, before_open_upper, r
        )
    external_lower = before_open_lower - mass12
    external_upper = before_open_upper - mass12
    child_lower, child_upper = child_ratio_bounds(12)
    assert Fraction(3, 4) * mass12 < external_lower
    assert external_upper < mass12
    assert external_lower + child_lower * mass12 > mass12
    assert external_upper + child_upper * mass12 < 2 * mass12

    # The scalar remainder says that the correct global front is rank eleven,
    # even though local dyadic packet normalization provisionally chose twelve.
    value = w(2) * w(3) - sum((w(r) for r in [5, 7, 8, 9, 10]), Fraction())
    assert value == Fraction(508634, 806159805)
    assert w(11) < value < 2 * w(11)
    scalar_reserve = value - w(11)
    assert scalar_reserve == Fraction(235013993, 1650209120835)

    return {
        "forced_front_trace": trace,
        "intervals": intervals,
        "external_before_rank12_over_mass": (
            str(external_lower / mass12),
            str(external_upper / mass12),
        ),
        "post_open_rank12_over_mass": (
            str((external_lower + child_lower * mass12) / mass12),
            str((external_upper + child_upper * mass12) / mass12),
        ),
        "exact_scalar_tail": str(value),
        "correct_global_front": 11,
        "rank11_reserve": str(scalar_reserve),
    }


def main() -> None:
    print(
        {
            "height_divisor": HEIGHT_DIVISOR,
            "alpha_upper_bound": str(ALPHA_MAX),
            "laminar_incomparability": "false",
            "certificate": check_forced_return(),
        }
    )


if __name__ == "__main__":
    main()
