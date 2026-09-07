#!/usr/bin/env python3
"""Exact audit for the half-row closed-set refutation chain.

Checks, exactly:
  1. parity exclusion: finite Boolean Mersenne sums have odd reduced
     denominator (exhaustive small-range verification);
  2. the truncated mu-Lambert identity approaches 1/2;
  3. integer greedy on target 2^(N-1) against q(N,d) closes with remainder
     exactly zero through --max-n, and reports the midpoint residual V_N
     against the complete-bank bound 2^ceil(N/2);
  4. the formerly claimed exact horizon stability is false, with explicit
     row-5/row-6 and row-51/row-102 counterexamples;
  5. the target convention is T_N = 2^(N-1), not 2^(N-1)-1, with exact
     regression examples for the corrected midpoint identity;
  6. the algebra and elementary inequalities behind the conditional
     two-horizon bypass of an odd midpoint hole.

No finite horizon is promoted to an all-depth statement.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import combinations


def parity_check(max_rank: int) -> None:
    ws = [Fraction(1, (1 << d) - 1) for d in range(2, max_rank + 1)]
    for k in range(len(ws) + 1):
        for combo in combinations(ws, k):
            assert sum(combo).denominator % 2 == 1


def mobius_sieve(limit: int) -> list[int]:
    mu = [0] * (limit + 1)
    mu[1] = 1
    primes: list[int] = []
    composite = bytearray(limit + 1)
    for i in range(2, limit + 1):
        if not composite[i]:
            primes.append(i)
            mu[i] = -1
        for p in primes:
            if i * p > limit:
                break
            composite[i * p] = 1
            if i % p == 0:
                break
            mu[i * p] = -mu[i]
    return mu


def mu_lambert_partial(depth: int) -> Fraction:
    return sum(Fraction(mu[d], (1 << d) - 1) for d in range(1, depth + 1))


def row_closure(max_n: int) -> dict[str, object]:
    failures: list[int] = []
    ratios: list[float] = []
    worst = (0.0, None)
    for n in range(4, max_n + 1):
        half = n // 2
        residual = 1 << (n - 1)
        for d in range(1, half + 1):
            coin = (1 << n) // ((1 << d) - 1)
            if coin <= residual:
                residual -= coin
        v_n = residual
        bank_bound = 1 << (n - half)
        if v_n >= bank_bound:
            failures.append(n)
            continue
        # complete the binary bank exactly
        rest = v_n
        for d in range(half + 1, n + 1):
            coin = (1 << n) // ((1 << d) - 1)
            if coin <= rest:
                rest -= coin
        if rest != 0:
            failures.append(n)
        ratio = v_n / bank_bound
        ratios.append(ratio)
        if ratio > worst[0]:
            worst = (ratio, n)
    return {
        "horizons_checked": max_n - 3,
        "closure_failures": len(failures),
        "first_failures": failures[:5],
        "max_v_over_bank": round(worst[0], 6),
        "max_at_n": worst[1],
    }


def row_support(n: int) -> list[int]:
    residual = 1 << (n - 1)
    support: list[int] = []
    for d in range(1, n + 1):
        coin = (1 << n) // ((1 << d) - 1)
        if coin <= residual:
            support.append(d)
            residual -= coin
    assert residual == 0
    return support


def first_shared_difference(a: int, b: int) -> int | None:
    sa = set(row_support(a))
    sb = set(row_support(b))
    return next((d for d in range(1, min(a, b) + 1)
                 if (d in sa) != (d in sb)), None)


def target_convention_regressions() -> dict[str, object]:
    """Pin the target-0 identities that the earlier note conflated.

    Here "target-0" means T_N = 2^(N-1), while "target-minus-one"
    means 2^(N-1)-1.  The live compactness consumer uses target-0.
    """
    support_6 = row_support(6)
    assert support_6 == [2, 3, 5]
    d = 3
    upper_value = sum(1 << (2 * d - a) for a in support_6 if a > d)
    midpoint_selected = int(d in support_6)
    prefix_quotient = sum(
        (1 << (2 * d)) // ((1 << a) - 1) for a in support_6 if a < d
    )
    z_d = (1 << (2 * d - 1)) - prefix_quotient - (1 << d)
    corrected_rhs = (
        upper_value + midpoint_selected * ((1 << d) + 1) - (1 << d)
    )
    assert (upper_value, z_d, corrected_rhs) == (2, 3, 3)

    support_10 = row_support(10)
    assert support_10 == [2, 3, 6, 7, 10]
    d = 5
    upper_value_5 = sum(
        1 << (2 * d - a) for a in support_10 if a > d
    )
    assert upper_value_5 == 25
    assert upper_value_5 > (1 << (d - 1)) - 1
    assert upper_value_5 <= (1 << d) - 1
    return {
        "target": "2^(N-1)",
        "d3_corrected_midpoint_identity": {
            "upper_value": upper_value,
            "z": z_d,
            "rhs_without_spurious_plus_one": corrected_rhs,
        },
        "d5_upper_value_regression": {
            "upper_value": upper_value_5,
            "false_bound": (1 << (d - 1)) - 1,
            "correct_bank_bound": (1 << d) - 1,
        },
    }


def two_step_midpoint_bypass(max_d: int) -> dict[str, object]:
    """Audit the exact N -> N+2 algebra used by the hole bypass.

    For a lower core D at endpoint 2d, write R_0 for its residual from
    2^(2d-1).  Two quotient transitions give

        R_2 = 4 R_0 - 2 g_1 - g_2,

    where g_i counts selected divisors at the two new endpoints.  If the
    hypothetical hole R_0=2^d occurs, rank d is too large, rank d+1 fits,
    and the remaining demand belongs to the pure binary bank.
    """
    checked = 0
    hypothetical_holes = 0
    for d in range(3, max_d + 1):
        # The actual lower core is enough to audit the transition identity;
        # the implication below is separately checked algebraically even
        # though no actual hole occurs in the audited range.
        support = row_support(2 * d - 1)
        core = [a for a in support if a < d]
        q0 = sum((1 << (2 * d)) // ((1 << a) - 1) for a in core)
        r0 = (1 << (2 * d - 1)) - q0
        g1 = sum((2 * d + 1) % a == 0 for a in core)
        g2 = sum((2 * d + 2) % a == 0 for a in core)
        q2 = sum((1 << (2 * d + 2)) // ((1 << a) - 1) for a in core)
        r2 = (1 << (2 * d + 1)) - q2
        assert r2 == 4 * r0 - 2 * g1 - g2

        pulse = 2 * g1 + g2
        assert pulse <= 3 * len(core) <= 3 * (d - 2)
        assert 3 * (d - 2) < (1 << (d + 1)) - 1
        rank_d_coin = (1 << (2 * d + 2)) // ((1 << d) - 1)
        rank_succ_coin = (1 << (2 * d + 2)) // ((1 << (d + 1)) - 1)
        assert rank_d_coin == (1 << (d + 2)) + 4
        assert rank_succ_coin == (1 << (d + 1)) + 1

        if r0 == 1 << d:
            hypothetical_holes += 1
            assert rank_d_coin > r2
            assert rank_succ_coin <= r2
            bank_remainder = r2 - rank_succ_coin
            assert 0 <= bank_remainder < 1 << (d + 1)
        checked += 1
    return {
        "two_step_transition_identities_checked": checked,
        "actual_midpoint_holes_seen": hypothetical_holes,
        "bypass_status": (
            "conditional exact theorem: any hole is filled two horizons later"
        ),
    }


def one_step_core_transport(max_n: int) -> dict[str, object]:
    supports = {n: row_support(n) for n in range(4, max_n + 1)}
    failures: list[tuple[int, str, int]] = []
    nearest_midpoint: tuple[int, int, int] | None = None
    minimum_financing: tuple[int, int] | None = None
    for n in range(4, max_n):
        cutoff = n // 2
        support = supports[n]
        low = [d for d in support if d <= cutoff]
        upper_value = sum(1 << (n - d) for d in support if d > cutoff)
        divisor_pulse = sum(1 for d in low if (n + 1) % d == 0)
        demand = 2 * upper_value - divisor_pulse
        if minimum_financing is None or demand < minimum_financing[0]:
            minimum_financing = (demand, n)
        if demand < 0:
            failures.append((n, "negative_financing", demand))

        if n % 2 == 1:
            midpoint = 1 << (cutoff + 1)
            distance = demand - midpoint
            candidate = (abs(distance), n, distance)
            if nearest_midpoint is None or candidate < nearest_midpoint:
                nearest_midpoint = candidate
            if distance == 0:
                failures.append((n, "midpoint_hole", demand))

        next_low = {d for d in supports[n + 1] if d <= cutoff}
        if next_low != set(low):
            first = next(
                d for d in range(2, cutoff + 1)
                if ((d in next_low) != (d in low))
            )
            failures.append((n, "core_instability", first))

        residual = (1 << n) - sum(
            (1 << (n + 1)) // ((1 << d) - 1) for d in low
        )
        assert residual == demand

    return {
        "transitions_checked": max(0, max_n - 4),
        "core_transport_failures": len(failures),
        "first_core_transport_failures": failures[:5],
        "minimum_financing": minimum_financing,
        "nearest_odd_midpoint": nearest_midpoint,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n", type=int, default=2500)
    parser.add_argument("--parity-rank", type=int, default=12)
    parser.add_argument("--mu-depth", type=int, default=60)
    args = parser.parse_args()

    global mu
    mu = mobius_sieve(args.mu_depth)

    parity_check(args.parity_rank)
    gap = Fraction(1, 2) - mu_lambert_partial(args.mu_depth)
    closure = row_closure(args.max_n)
    transport = one_step_core_transport(args.max_n)
    target_regressions = target_convention_regressions()
    bypass = two_step_midpoint_bypass(max(3, args.max_n // 2))
    stability_counterexamples = {
        "row_5_vs_6_first_difference": first_shared_difference(5, 6),
        "row_51_vs_102_first_difference": first_shared_difference(51, 102),
    }
    assert stability_counterexamples == {
        "row_5_vs_6_first_difference": 4,
        "row_51_vs_102_first_difference": 43,
    }

    print(
        {
            "parity_exclusion": "verified: finite Boolean Mersenne sums have "
            "odd reduced denominator; 1/2 excluded",
            "mu_lambert_gap_at_depth": {
                "depth": args.mu_depth,
                "abs_gap": float(abs(gap)),
            },
            **closure,
            **transport,
            "target_convention_regressions": target_regressions,
            **bypass,
            "horizon_stability_counterexamples": stability_counterexamples,
            "status": "exact finite verification, not an all-depth theorem",
        }
    )
    if closure["closure_failures"]:
        raise SystemExit("row closure failures detected")
    if transport["core_transport_failures"]:
        raise SystemExit("one-step core transport failures detected")


if __name__ == "__main__":
    main()
