#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact finite capacity probes; writes only capacity-results.json beside this file.

Dyadic case: Q_n=2^n, F_n=n². The ordinary geometric-series identity gives
U_N=Q_N sum_{n>N} F_n/Q_n=N²+4N+6. A factorial modulus schedule is frozen after
H=128, so all continuation bands have exact rational endpoints. Freezing makes
this a finite congruence check, not a proof of eventual divisibility by every q.

Repeated-denominator boundary: Q_n=2^floor(sqrt(n)), F_n=1. The full positive
index sum is 5: block j>=1 has 2j+1 terms, and sum_j (2j+1)/2^j=5. Thus the
entire remaining capacity is exactly computable, not a truncated lower estimate.
This example violates strict denominator growth. The ordinary implications
"eventual even digits imply finite support" and "eventual prefix divisibility
by every q then forces all nonnegative digits to vanish" are explanatory
observations, not assertions established by the finite test.
"""

from fractions import Fraction
from math import isqrt
from pathlib import Path
import json


START = 8
HORIZON = 128
CONTINUATION_STEPS = 32


def dyadic_capacity(n):
    return n * n + 4 * n + 6


def largest_factorial_at_most(bound):
    assert bound >= 1
    value, next_factor = 1, 2
    while value * next_factor <= bound:
        value *= next_factor
        next_factor += 1
    return value


def modulus(n, horizon=HORIZON):
    # Constant after the horizon: this does not grow to contain every modulus.
    return largest_factorial_at_most(max(1, min(n, horizon) // 4))


def ceiling(value):
    return -((-value.numerator) // value.denominator)


def build_bands(horizon=HORIZON):
    alpha = {horizon: Fraction(modulus(horizon, horizon), 2**horizon)}
    beta = {horizon: Fraction(dyadic_capacity(horizon), 2**horizon) - alpha[horizon]}
    for n in range(horizon, START - 1, -1):
        m = modulus(n, horizon)
        alpha[n - 1] = Fraction(m, 2**n) + alpha[n]
        beta[n - 1] = Fraction(n * n - m, 2**n) + beta[n]
    return alpha, beta


def band(n, alpha, beta, horizon=HORIZON):
    if n <= horizon:
        return alpha[n], beta[n]
    lower = Fraction(modulus(horizon, horizon), 2**n)
    return lower, Fraction(dyadic_capacity(n), 2**n) - lower


def verify_band_geometry(alpha, beta, horizon=HORIZON):
    end = horizon + CONTINUATION_STEPS
    for n in range(START, end + 1):
        m, q = modulus(n, horizon), 2**n
        lower, upper = band(n, alpha, beta, horizon)
        previous_lower, previous_upper = band(n - 1, alpha, beta, horizon)
        assert m % modulus(n - 1, horizon) == 0
        assert 2 * m <= n * n
        assert upper - lower >= Fraction(m, q)
        assert lower + upper == Fraction(dyadic_capacity(n), q)
        assert previous_lower == Fraction(m, q) + lower
        assert previous_upper == Fraction(n * n - m, q) + upper
        assert 2 * dyadic_capacity(n - 1) == n * n + dyadic_capacity(n)
    return {
        "checked_indices_inclusive": [START, end],
        "nested_moduli": True,
        "two_modulus_le_digit_bound": True,
        "continuation_width_ge_modulus_over_denominator": True,
        "exact_lower_and_upper_band_recurrences": True,
        "band_endpoint_sum_equals_full_tail_capacity": True,
        "dyadic_capacity_recurrence": True,
    }


def safe_continuation(target, initial_cumulative, alpha, beta, horizon=HORIZON):
    residual, cumulative, weighted_sum = target, initial_cumulative, Fraction()
    start_lower, start_upper = band(START, alpha, beta, horizon)
    assert start_lower <= residual <= start_upper
    digits = []
    first_divisibility_index = None
    end = horizon + CONTINUATION_STEPS
    for n in range(START + 1, end + 1):
        m, q, bound = modulus(n, horizon), 2**n, n * n
        lower, upper = band(n, alpha, beta, horizon)
        # The residual condition is equivalent to this closed integer interval.
        lo = max(0, ceiling(q * (residual - upper)))
        hi_fraction = q * (residual - lower)
        hi = min(bound, hi_fraction.numerator // hi_fraction.denominator)
        # Choose the least permitted digit in the required residue class.
        digit = lo + (-cumulative - lo) % m
        assert lo <= digit <= hi
        assert 0 <= digit <= bound
        assert (cumulative + digit) % m == 0
        if n > START + 1:
            assert digit % modulus(n - 1, horizon) == 0
            if first_divisibility_index is None:
                first_divisibility_index = n
        cumulative += digit
        residual -= Fraction(digit, q)
        weighted_sum += Fraction(digit, q)
        assert lower <= residual <= upper
        assert 0 <= q * residual <= dyadic_capacity(n)
        assert weighted_sum + residual == target
        digits.append(digit)
    final_lower, final_upper = band(end, alpha, beta, horizon)
    return {
        "target_exact": str(target),
        "initial_cumulative_digit_sum": initial_cumulative,
        "digit_indices_inclusive": [START + 1, end],
        "digits": digits,
        "steps_checked": len(digits),
        "prefix_divisibility_checked_at_every_step": True,
        "digit_divisibility_by_previous_modulus_from_index": first_divisibility_index,
        "digit_bounds_and_residual_bands_checked_at_every_step": True,
        "weighted_sum_plus_residual_identity_checked_at_every_step": True,
        "final_cumulative_digit_sum": cumulative,
        "final_prefix_modulus": modulus(end, horizon),
        "final_weighted_sum_exact": str(weighted_sum),
        "final_residual_exact": str(residual),
        "final_residual_band_exact": [str(final_lower), str(final_upper)],
        "final_normalized_residual_exact": str(2**end * residual),
        "final_normalized_full_capacity": dyadic_capacity(end),
    }


def dyadic_experiment():
    alpha, beta = build_bands()
    geometry = verify_band_geometry(alpha, beta)
    lower, upper = band(START, alpha, beta)
    assert 0 < lower < upper
    fractions_of_interval = [Fraction(0), Fraction(1, 4), Fraction(1, 2),
                             Fraction(3, 4), Fraction(1)]
    traces = []
    for position in fractions_of_interval:
        target = lower + position * (upper - lower)
        for initial_cumulative in [0, 137]:
            trace = safe_continuation(target, initial_cumulative, alpha, beta)
            trace["fractional_position_in_start_band"] = str(position)
            traces.append(trace)
    schedule_changes = []
    previous = None
    for n in range(START, HORIZON + 1):
        current = modulus(n)
        if current != previous:
            schedule_changes.append({"from_index": n, "modulus": current})
            previous = current
    return {
        "denominator": "Q_n=2^n",
        "digit_bound": "F_n=n^2",
        "exact_normalized_capacity": "U_N=N^2+4N+6",
        "start_index": START,
        "schedule_freeze_index": HORIZON,
        "checked_extra_steps_after_freeze": CONTINUATION_STEPS,
        "modulus_schedule": "largest factorial <= max(1, min(n,H)//4)",
        "modulus_changes_from_start": schedule_changes,
        "modulus_constant_after_horizon": modulus(HORIZON),
        "start_band_exact": [str(lower), str(upper)],
        "start_band_decimal": [float(lower), float(upper)],
        "terminal_band_at_horizon_exact": [str(alpha[HORIZON]), str(beta[HORIZON])],
        "band_geometry_checks": geometry,
        "target_count": len(fractions_of_interval),
        "initial_cumulative_sums": [0, 137],
        "total_selection_steps_checked": sum(t["steps_checked"] for t in traces),
        "traces": traces,
    }


def repeated_denominator_experiment(max_index=1000):
    prefix = Fraction()
    selected = {0, 1, 2, 3, 4, 8, 9, 99, 100, 999, 1000}
    samples = []
    for n in range(max_index + 1):
        if n:
            prefix += Fraction(1, 2**isqrt(n))
        k = isqrt(n)
        block_start, block_end = (k + 1)**2, (k + 2)**2 - 1
        assert block_start > n
        block = list(range(block_start, block_end + 1))
        assert len(block) == 2 * k + 3
        assert all(isqrt(m) == k + 1 for m in block)
        next_block_contribution = sum((Fraction(2**k, 2**isqrt(m))
                                       for m in block), Fraction())
        assert next_block_contribution == Fraction(2 * k + 3, 2)
        capacity = 2**k * (5 - prefix)
        remaining_current_block = (k + 1)**2 - 1 - n
        assert remaining_current_block >= 0
        assert capacity == remaining_current_block + 2 * k + 5
        assert capacity == k * k + 4 * k + 5 - n
        assert capacity >= next_block_contribution >= k
        if n in selected:
            samples.append({
                "N": n, "floor_sqrt_N": k,
                "next_full_block_indices_inclusive": [block_start, block_end],
                "next_full_block_count": len(block),
                "next_full_block_normalized_contribution_exact": str(next_block_contribution),
                "remaining_current_block_count": remaining_current_block,
                "full_normalized_tail_capacity_exact": str(capacity),
            })
    return {
        "denominator": "Q_n=2^floor(sqrt(n))",
        "digit_bound": "F_n=1",
        "full_positive_index_series_sum_exact": "5",
        "exact_capacity_formula": "U_N=k^2+4k+5-N, k=floor(sqrt(N))",
        "checked_indices_inclusive": [0, max_index],
        "number_of_capacity_and_block_checks": max_index + 1,
        "next_full_block_count_formula": "2k+3",
        "next_full_block_normalized_contribution": "(2k+3)/2",
        "checked_lower_bound": "U_N >= (2k+3)/2 >= floor(sqrt(N))",
        "strict_denominator_growth_hypothesis_satisfied": False,
        "samples": samples,
        "ordinary_boundary_argument_not_a_finite_test": [
            "The block formula proves U_N tends to infinity although Q_n has repetitions.",
            "With digits in {0,1}, eventual divisibility by 2 forces finite support.",
            "If the cumulative sums must eventually be divisible by every positive integer, their eventual constant is 0.",
            "Nonnegative digits and eventual cumulative sum 0 force every digit to be 0.",
            "Thus growing U_N alone cannot replace strict denominator growth in an interval-filling theorem with these congruences.",
        ],
    }


def main():
    result = {
        "evidence": "Finite exact Fraction computations with ordinary closed-form identities stated separately",
        "starting_revision": "ca5ad952fefb29b50a4e360988fa84f9c7255700",
        "dyadic_safe_continuation": dyadic_experiment(),
        "repeated_denominator_boundary": repeated_denominator_experiment(),
        "limits": [
            "The factorial modulus schedule is frozen at H=128; this finite check does not prove eventual divisibility by every q.",
            "All tested residual bands use the entire exact frozen-schedule tail, not a truncated tail approximation.",
            "Finite successful choices do not prove infinite interval filling or the proposed general equivalence.",
            "The repeated-denominator example violates the strict-chain assumption and is not a counterexample under that assumption.",
            "No Lean theorem, irrationality conclusion, or novelty claim is supplied by this program.",
        ],
    }
    output = Path(__file__).with_name("capacity-results.json")
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({
        "output": str(output),
        "selection_steps_checked": result["dyadic_safe_continuation"]["total_selection_steps_checked"],
        "capacity_and_block_checks": result["repeated_denominator_boundary"]["number_of_capacity_and_block_checks"],
        "all_assertions_passed": True,
        "finite_modulus_schedule_only": True,
    }, indent=2))


if __name__ == "__main__":
    main()
