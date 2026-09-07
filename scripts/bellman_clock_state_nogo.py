#!/usr/bin/env python3
"""Exact receipts for BellmanClockStateNoGo.md."""

from fractions import Fraction


def w(n: int) -> Fraction:
    return Fraction(1, (1 << n) - 1)


def bellman_step(n: int, residual: Fraction) -> tuple[int, Fraction, int]:
    digit = int(residual >= w(n))
    return n + 1, residual - digit * w(n), digit


def normalized_step(y: Fraction, z: Fraction) -> tuple[Fraction, Fraction, int]:
    digit = int(y >= 1)
    return (2 + z) * (y - digit), z / (2 + z), digit


def check_clock_identity(max_rank: int = 200) -> int:
    for n in range(2, max_rank + 1):
        assert w(n + 1) == w(n) / (2 + w(n))
    return max_rank - 1


def check_equal_normalized_states() -> dict[str, object]:
    y = Fraction(10, 21)

    feasible = y * w(2)
    assert feasible == Fraction(10, 63)
    assert feasible == w(3) + w(6)

    impossible = y * w(4)
    assert impossible == Fraction(2, 63)
    assert impossible < w(5) < w(4)

    n, residual, digit = bellman_step(4, impossible)
    assert (n, residual, digit) == (5, impossible, 0)
    n, residual, digit = bellman_step(n, residual)
    assert (n, residual, digit) == (6, impossible, 0)
    n, residual, digit = bellman_step(n, residual)
    assert (n, residual, digit) == (7, w(6), 1)

    # The established reverse-superincreasing inequality gives
    # sum_{k>6} w_k < w_6, so this positive remainder is an exact gap.
    assert residual == Fraction(1, 63)

    return {
        "normalized_value": str(y),
        "rank_2_value": str(feasible),
        "rank_2_support": [3, 6],
        "rank_4_value": str(impossible),
        "rank_4_forced_prefix": [0, 0, 1],
        "rank_4_gap_remainder": str(residual),
        "rank_free_value_function_exists": False,
    }


def check_root_initial_state() -> dict[str, str]:
    target = Fraction(1, 21)
    y = target / w(2)
    z = w(2)
    assert (y, z) == (Fraction(1, 7), Fraction(1, 3))

    y_next, z_next, digit = normalized_step(y, z)
    assert digit == 0
    assert z_next == w(3)
    assert y_next == target / w(3)
    return {"target": str(target), "y_2": str(y), "z_2": str(z)}


def main() -> None:
    print(
        {
            "clock_identity_checks": check_clock_identity(),
            "root_initial_state": check_root_initial_state(),
            "stationary_scalar_counterexample": check_equal_normalized_states(),
            "minimal_exact_markov_state": "(y,z) or equivalently (n,x)",
            "root_policy_proved": False,
        }
    )


if __name__ == "__main__":
    main()
