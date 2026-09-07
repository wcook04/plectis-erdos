#!/usr/bin/env python3
"""Exact audit for the 1/465 fixed-horizon corridor reduction."""

from __future__ import annotations

import argparse
from fractions import Fraction
from math import isqrt


def source_digits(horizon: int) -> list[int]:
    remainder = 1
    digits: list[int] = []
    for _ in range(horizon):
        remainder *= 2
        digits.append(remainder // 465)
        remainder %= 465
    return digits


def r45(n: int, digits: list[int]) -> int:
    k, residue = divmod(n, 20)
    if residue == 0:
        return k - 1
    return k + digits[residue - 1]


def divisor_counts(horizon: int) -> list[int]:
    tau = [0] * (horizon + 1)
    for d in range(1, horizon + 1):
        for n in range(d, horizon + 1, d):
            tau[n] += 1
    return tau


def quotient_weights(horizon: int) -> list[int]:
    power = 1 << horizon
    return [power // ((1 << d) - 1) for d in range(1, horizon + 1)]


def greedy_word(horizon: int, target: int) -> tuple[list[int], int]:
    remainder = target
    bits: list[int] = []
    for weight in quotient_weights(horizon):
        bit = int(remainder >= weight)
        bits.append(bit)
        if bit:
            remainder -= weight
    return bits, remainder


def terminal_defects(bits: list[int], digits: list[int]) -> list[int]:
    defects = [0]
    for n in range(1, len(bits) + 1):
        divisor_load = sum(bits[d - 1] for d in range(1, n + 1) if n % d == 0)
        defects.append(2 * defects[-1] + digits[n - 1] - divisor_load)
    return defects


def audit_tau_threshold(cutoff: int) -> None:
    digits = source_digits(20)
    tau = divisor_counts(cutoff - 1)
    direct_r45 = [0] * cutoff
    for i in range(1, cutoff // 4 + 1):
        for j in range(1, (cutoff - 4 * i - 1) // 5 + 1):
            direct_r45[4 * i + 5 * j] += 1
    for n in range(1, cutoff):
        assert r45(n, digits) == direct_r45[n]
    failures = [n for n in range(1, cutoff) if tau[n] > r45(n, digits)]
    assert failures[-1] == 480
    assert tau[480] == 24 and r45(480, digits) == 23
    for n in range(481, cutoff):
        assert tau[n] <= r45(n, digits)
    assert cutoff // 20 - 1 >= 2 * isqrt(cutoff)
    print(
        "tau threshold PASS: last failure n=480; exact finite interval "
        f"481..{cutoff - 1}; analytic bound starts at {cutoff}"
    )


def audit_superincrease_and_base(base: int) -> None:
    weights = quotient_weights(base)
    tail = 0
    for weight in reversed(weights):
        assert weight > tail
        tail += weight

    digits = source_digits(base)
    target = (1 << base) // 465
    for endpoint in range(base // 20 + 1):
        bits, remainder = greedy_word(base, target - endpoint)
        assert remainder == 0
        defects = terminal_defects(bits, digits)
        assert defects[-1] == endpoint
        assert all(0 <= defects[n] <= n // 20 for n in range(1, base + 1))
    print(
        f"base PASS: all {base // 20 + 1} terminal endpoints at rank {base} "
        "exist uniquely and their words satisfy every earlier corridor"
    )


def lower_greedy_excess(horizon: int) -> int:
    midpoint = horizon // 2
    power = 1 << horizon
    remainder = power // 465
    for d in range(1, midpoint + 1):
        weight = power // ((1 << d) - 1)
        if remainder >= weight:
            remainder -= weight
    upper_capacity = (1 << (horizon - midpoint)) - 1
    return max(0, remainder - upper_capacity)


def audit_lower_greedy(horizon: int) -> None:
    maximum = (-1, -1)
    for n in range(1, horizon + 1):
        excess = lower_greedy_excess(n)
        if excess > maximum[0]:
            maximum = (excess, n)
        if n >= 120:
            assert excess <= n // 20
    print(
        f"finite lower-greedy audit PASS through {horizon}: "
        f"maximum endpoint excess {maximum[0]} at rank {maximum[1]}"
    )


def audit_terminal_family(horizon: int) -> None:
    target = (1 << horizon) // 465
    weights = quotient_weights(horizon)
    words: list[list[int]] = []
    for endpoint in range(horizon // 20 + 1):
        remainder = target - endpoint
        bits: list[int] = []
        for weight in weights:
            bit = int(remainder >= weight)
            bits.append(bit)
            if bit:
                remainder -= weight
        assert remainder == 0
        words.append(bits)
    common = 0
    while common < horizon and all(word[common] == words[0][common] for word in words):
        common += 1
    print(
        f"terminal family PASS at rank {horizon}: {len(words)} endpoints, "
        f"common prefix length {common}"
    )


def audit_generic_greedy_warning() -> None:
    horizon = 40
    midpoint = horizon // 2
    weights = quotient_weights(horizon)[:midpoint]
    upper_capacity = (1 << (horizon - midpoint)) - 1
    target = 2 * weights[1] + 1
    remainder = target
    for weight in weights:
        if remainder >= weight:
            remainder -= weight
    assert remainder > upper_capacity + horizon // 20
    print(
        "generic-target warning PASS: quotient-coin arithmetic alone does not "
        "bound the lower-greedy remainder"
    )


def audit_diagonal_recurrence(depth: int) -> None:
    digits = source_digits(20)

    def target_bit(n: int) -> int:
        return digits[(n - 1) % 20]

    loads = [0] * (2 * depth + 1)
    bits: list[int] = []
    margins: list[int] = []
    remainder = 0
    diagonal_remainders = [0]
    real_remainder = Fraction(1, 465)
    real_remainders = [real_remainder]
    selected_denominators: list[tuple[int, int]] = []
    prefix_product = 1
    prefix_numerator = 1
    previous_phase_numerator = 1
    pulse_accumulator = 0
    decision_load_pulses: list[int] = []
    selected_count = 0
    small_selected_margins: list[tuple[int, int, int]] = []
    small_selected_ranks: set[int] = set()
    last_selected_rank: int | None = None
    first_negative_rank: int | None = None
    boundary_hits: list[int] = []

    def backward_carry_accepts(pulses: list[int], rank: int) -> bool:
        carry = 0
        half = rank // 2
        for offset in range(half):
            total = carry + pulses[rank - offset - 1]
            if total % 4:
                return False
            carry = total // 4
            assert -1 <= carry <= rank - 1
        terminal = carry + pulses[rank - half - 1]
        if rank % 2 == 0:
            return terminal % 2 == 1
        return terminal % 4 == 2

    for d in range(1, depth + 1):
        previous_remainder = remainder
        odd_load = loads[2 * d - 1]
        even_load = loads[2 * d]
        source_pair = 2 * target_bit(2 * d - 1) + target_bit(2 * d)
        divisor_pulse = source_pair - 2 * odd_load - even_load
        pre_remainder = (
            4 * previous_remainder
            + divisor_pulse
        )
        midpoint_weight = (1 << (2 * d)) // ((1 << d) - 1)
        margin = pre_remainder - midpoint_weight
        bit = int(margin >= 0)
        if bit and margin < selected_count + 1:
            small_selected_margins.append((d, margin, selected_count))
            small_selected_ranks.add(d)
        remainder = pre_remainder - bit * midpoint_weight
        if 0 <= previous_remainder < (1 << (d - 1)):
            assert remainder <= (1 << d)
            if remainder == (1 << d):
                assert not bit
                assert margin == -1
                assert (odd_load * 2 + even_load - source_pair) % 4 == 0
                boundary_hits.append(d)
        previous_prefix_product = prefix_product
        if bit:
            denominator = (1 << d) - 1
            real_remainder -= Fraction(1, denominator)
            prefix_numerator = (
                prefix_numerator * denominator - 465 * prefix_product
            )
            prefix_product *= denominator
            selected_denominators.append((d, denominator))
        assert real_remainder == Fraction(
            prefix_numerator, 465 * prefix_product
        )
        source_phase_remainder = pow(4, d, 465)
        phase_numerator = source_phase_remainder * prefix_product
        for selected_rank, denominator in selected_denominators:
            phase_numerator -= (
                465
                * pow(4, d, denominator)
                * (prefix_product // denominator)
            )
        denominator_factor = ((1 << d) - 1) if bit else 1
        assert phase_numerator == (
            4 * denominator_factor * previous_phase_numerator
            - 465
            * previous_prefix_product
            * (denominator_factor * divisor_pulse + bit)
        )
        previous_phase_numerator = phase_numerator
        assert (
            465 * prefix_product * remainder
            == (1 << (2 * d)) * prefix_numerator - phase_numerator
        )
        if remainder == (1 << d):
            assert phase_numerator == (
                (1 << d)
                * ((1 << d) * prefix_numerator - 465 * prefix_product)
            )
            odd_part = phase_numerator >> d
            assert odd_part & 1
        decision_load_pulse = bit - divisor_pulse
        assert decision_load_pulse == (
            4 * previous_remainder - remainder - bit * (1 << d)
        )
        decision_load_pulses.append(decision_load_pulse)
        pulse_accumulator = 4 * pulse_accumulator + decision_load_pulse
        modulus_d = 1 << d
        normalized_phase = (
            phase_numerator * pow(prefix_product, -1, 1 << (d + 1))
        ) % (1 << (d + 1))
        assert normalized_phase % modulus_d == (
            465 * pulse_accumulator
        ) % modulus_d
        if not bit:
            assert normalized_phase == (
                465 * pulse_accumulator
            ) % (1 << (d + 1))
            exact_valuation_d = (
                phase_numerator != 0
                and phase_numerator % (1 << d) == 0
                and phase_numerator % (1 << (d + 1)) != 0
            )
            assert exact_valuation_d == (
                pulse_accumulator % (1 << (d + 1)) == (1 << d)
            )
            assert backward_carry_accepts(decision_load_pulses, d) == (
                pulse_accumulator % (1 << (d + 1)) == (1 << d)
            )
        selected_after = selected_count + bit
        rounding_discrepancy = (1 << (2 * d)) * real_remainder - remainder
        assert abs(rounding_discrepancy) <= selected_after + 1
        if bit:
            assert remainder == margin
            if d >= 2:
                assert (
                    margin - (source_pair - 2 * odd_load - even_load - 1)
                ) % 4 == 0
        bits.append(bit)
        margins.append(margin)
        diagonal_remainders.append(remainder)
        real_remainders.append(real_remainder)
        if bit:
            last_selected_rank = d
            selected_count += 1
            for multiple in range(2 * d, 2 * depth + 1, d):
                loads[multiple] += 1
        elif remainder < 0 and first_negative_rank is None:
            first_negative_rank = d
            assert last_selected_rank is not None
            assert last_selected_rank in small_selected_ranks

    # Focused direct check of the diagonal recurrence and its stability
    # certificate.  This is deliberately bounded; it is not horizon evidence.
    for n in range(1, 2 * depth + 1):
        direct_bits, _ = greedy_word(n, (1 << n) // 465)
        midpoint = n // 2
        assert direct_bits[:midpoint] == bits[:midpoint]
    assert not small_selected_margins, small_selected_margins[0]

    phase_bounds = {
        4: Fraction(101, 465),
        6: Fraction(221, 465),
        8: Fraction(281, 465),
        9: Fraction(194, 465),
    }
    for d in range(1, depth + 1):
        midpoint = (d + 1) // 2
        pulse_window = sum(
            (1 << (2 * (d - j))) * decision_load_pulses[j - 1]
            for j in range(midpoint, d + 1)
        )
        telescoped = (
            (1 << (2 * (d - midpoint + 1)))
            * diagonal_remainders[midpoint - 1]
            - diagonal_remainders[d]
            - sum(
                bits[j - 1] * (1 << (2 * d - j))
                for j in range(midpoint, d + 1)
            )
        )
        assert pulse_window == telescoped

        alpha = Fraction(pow(4, d, 465), 465)
        if alpha > Fraction(1, 3):
            assert d % 10 in phase_bounds
            assert alpha - Fraction(1, 3) == phase_bounds[d % 10]
        else:
            assert d % 10 not in phase_bounds

        resolvent = sum(
            (
                Fraction(pow(4, d, (1 << rank) - 1), (1 << rank) - 1)
                for rank in range(1, d + 1)
                if bits[rank - 1]
            ),
            Fraction(),
        )
        assert Fraction(diagonal_remainders[d]) == (
            (1 << (2 * d)) * real_remainders[d] - alpha + resolvent
        )

        if d < depth:
            nu_one = loads[2 * d + 1]
            nu_two = loads[2 * d + 2] - bits[d]
            next_load = (
                2 * loads[2 * d + 1]
                + loads[2 * d + 2]
                - bits[d]
            )
            assert next_load == 2 * nu_one + nu_two

    # The phase and the two divisor loads alone cannot exclude a small event.
    # With three selected nondivisor ranks, both loads may be zero; every
    # source-pair value admits exactly one margin z in {0,1,2,3}.
    synthetic_rank = 64
    synthetic_weight = (1 << synthetic_rank) + 1
    for source_pair in range(4):
        margin = (source_pair - 1) % 4
        prior_remainder = (
            (1 << synthetic_rank) + 1 + margin - source_pair
        ) // 4
        assert 0 <= margin <= 3
        assert 4 * prior_remainder + source_pair - synthetic_weight == margin

    # The strict threshold is sharp.  With the worst skipped-run pulse
    # -3s, equality rho=s remains exactly s and never crosses below zero.
    synthetic_selected_count = 7
    synthetic_remainder = synthetic_selected_count
    for _ in range(20):
        synthetic_remainder = (
            4 * synthetic_remainder - 3 * synthetic_selected_count
        )
        assert synthetic_remainder == synthetic_selected_count

    # A first exit from rho < 2^d must hit rho = 2^d at a skipped
    # comparison of margin -1.  From a final such gate, the next rank enters
    # the upper strip exactly when its fixed-source/load pulse is at least 2.
    for d in range(3, 10):
        midpoint_weight = (1 << d) + 1
        for previous_remainder in range(1 << (d - 1)):
            for source_pair in range(4):
                for divisor_load in range(3 * d + 1):
                    pre_remainder = (
                        4 * previous_remainder + source_pair - divisor_load
                    )
                    bit = int(pre_remainder >= midpoint_weight)
                    new_remainder = pre_remainder - bit * midpoint_weight
                    assert new_remainder <= (1 << d)
                    if new_remainder == (1 << d):
                        assert not bit
                        assert pre_remainder - midpoint_weight == -1
                        assert (divisor_load - source_pair) % 4 == 0

        for next_source_pair in range(4):
            for next_divisor_load in range(3 * d + 1):
                pre_remainder = (
                    4 * (1 << d) + next_source_pair - next_divisor_load
                )
                next_weight = (1 << (d + 1)) + 1
                assert pre_remainder >= next_weight
                new_remainder = pre_remainder - next_weight
                assert new_remainder == (
                    (1 << (d + 1))
                    + next_source_pair
                    - next_divisor_load
                    - 1
                )
                assert (new_remainder > (1 << (d + 1))) == (
                    next_source_pair - next_divisor_load >= 2
                )

    expected_source_pairs = {
        0: 3,
        1: 0,
        2: 0,
        3: 0,
        4: 0,
        5: 2,
        6: 0,
        7: 3,
        8: 0,
        9: 3,
    }
    for n in range(1, 181):
        source_pair = 2 * target_bit(2 * n - 1) + target_bit(2 * n)
        assert source_pair == expected_source_pairs[n % 10]
        anchor_nine_load = 2 * int(n % 9 == 5) + int(n % 9 == 0)
        if n % 10 in {0, 5, 7, 9} and n % 9 == 5:
            assert source_pair - anchor_nine_load < 2
        if n % 10 == 5 and n % 9 == 0:
            assert source_pair - anchor_nine_load < 2
        if n % 10 in {0, 7, 9} and n % 9 == 0:
            assert source_pair - anchor_nine_load == 2

    # Fixed-phase countermodel: the actual selected support through 23 gives
    # zero loads at 24 and 25, so a synthetic globally-unverified predecessor
    # can traverse the exact margin -1 gate and escape on the next pulse.
    if depth >= 25:
        selected_through_23 = {
            rank for rank, selected in enumerate(bits[:23], 1) if selected
        }
        assert selected_through_23 == {9, 13, 14, 17, 19, 21, 22, 23}

        def prefix_load(n: int) -> int:
            return sum(rank in selected_through_23 for rank in range(1, n) if n % rank == 0)

        synthetic_load_24 = 2 * prefix_load(47) + prefix_load(48)
        synthetic_load_25 = 2 * prefix_load(49) + prefix_load(50)
        synthetic_source_24 = 2 * target_bit(47) + target_bit(48)
        synthetic_source_25 = 2 * target_bit(49) + target_bit(50)
        assert (synthetic_source_24, synthetic_load_24) == (0, 0)
        assert (synthetic_source_25, synthetic_load_25) == (2, 0)
        synthetic_remainder_23 = 1 << 22
        synthetic_pre_24 = (
            4 * synthetic_remainder_23
            + synthetic_source_24
            - synthetic_load_24
        )
        assert synthetic_pre_24 == (1 << 24)
        assert synthetic_pre_24 - ((1 << 24) + 1) == -1
        synthetic_remainder_24 = synthetic_pre_24
        synthetic_pre_25 = (
            4 * synthetic_remainder_24
            + synthetic_source_25
            - synthetic_load_25
        )
        synthetic_remainder_25 = synthetic_pre_25 - ((1 << 25) + 1)
        assert synthetic_remainder_25 == (1 << 25) + 1
        synthetic_pulses = decision_load_pulses[:23] + [0]
        assert synthetic_pulses[22] == 3
        assert not backward_carry_accepts(synthetic_pulses, 24)

    lower_remainder = 0
    previous_excess = 0
    for n in range(1, 2 * depth + 1):
        target_digit = target_bit(n)
        if n % 2:
            lower_load = loads[n]
            lower_remainder = 2 * lower_remainder + target_digit - lower_load
        else:
            midpoint = n // 2
            midpoint_bit = bits[midpoint - 1]
            strict_lower_load = loads[n] - midpoint_bit
            midpoint_weight = (1 << n) // ((1 << midpoint) - 1)
            pre_remainder = (
                2 * lower_remainder + target_digit - strict_lower_load
            )
            assert midpoint_bit == int(pre_remainder >= midpoint_weight)
            lower_remainder = pre_remainder - midpoint_bit * midpoint_weight

        capacity = (1 << (n - n // 2)) - 1
        excess = lower_remainder - capacity - n // 20
        lower_load = loads[n] if n % 2 else loads[n] - bits[n // 2 - 1]
        if n % 2:
            expected = 2 * previous_excess + r45(n, digits) - lower_load - 1
        elif n >= 4 and bits[n // 2 - 1]:
            expected = 2 * previous_excess + r45(n, digits) - lower_load - 2
        elif n >= 4:
            expected = (
                2 * previous_excess + capacity + r45(n, digits) - lower_load
            )
            assert excess <= 1 - n // 20
        else:
            expected = excess
        assert excess == expected
        previous_excess = excess

    print(
        f"focused diagonal recurrence PASS through rank {2 * depth}: "
        "all selected margins satisfy the permanence certificate; local "
        "phase/load insufficiency witness PASS; fatal-gateway arithmetic "
        f"PASS (bounded boundary hits: {len(boundary_hits)})"
    )


def audit_resolvent_local_countermodel() -> None:
    """Refute scalar/local resolvent closure at the exact rank 3056 row."""

    gate_rank = 3056
    synthetic_end = gate_rank + 9
    digits = source_digits(20)

    def target_bit(n: int) -> int:
        return digits[(n - 1) % 20]

    loads = [0] * (2 * synthetic_end + 1)
    bits = [0] * (gate_rank + 1)
    remainder = 0
    selected_count = 0
    for d in range(1, gate_rank + 1):
        source_pair = 2 * target_bit(2 * d - 1) + target_bit(2 * d)
        divisor_load = 2 * loads[2 * d - 1] + loads[2 * d]
        pre_remainder = 4 * remainder + source_pair - divisor_load
        midpoint_weight = 5 if d == 1 else (1 << d) + 1
        bit = int(pre_remainder >= midpoint_weight)
        remainder = pre_remainder - bit * midpoint_weight
        bits[d] = bit
        selected_count += bit
        if bit:
            for multiple in range(2 * d, len(loads), d):
                loads[multiple] += 1

    source_at_gate = (
        2 * target_bit(2 * gate_rank - 1) + target_bit(2 * gate_rank)
    )
    load_at_gate = 2 * loads[2 * gate_rank - 1] + loads[2 * gate_rank]
    source_after_gate = (
        2 * target_bit(2 * gate_rank + 1) + target_bit(2 * gate_rank + 2)
    )
    load_after_gate = 2 * loads[2 * gate_rank + 1] + loads[2 * gate_rank + 2]
    assert gate_rank % 10 == 6
    assert bits[gate_rank] == 0
    assert selected_count == 1515
    assert (source_at_gate, load_at_gate) == (0, 16)
    assert (source_after_gate, load_after_gate) == (3, 0)
    assert (31 << (gate_rank - 5)) < remainder < (63 << (gate_rank - 6))

    def arrival_count(offset: int) -> int:
        n = 2 * gate_rank + offset
        return sum(
            bits[rank]
            for rank in range(1, gate_rank + 1)
            if n % rank == 0
        )

    arrivals = [arrival_count(offset) for offset in range(1, 17)]
    assert arrivals == [0, 0, 0, 3, 1, 6, 2, 18, 0, 0, 4, 0, 5, 0, 0, 2]
    arrival_prefix = sum(
        (Fraction(count, 1 << offset)
         for offset, count in enumerate(arrivals, 1)),
        Fraction(),
    )
    assert arrival_prefix == Fraction(13141, 32768)
    resolvent_upper_bound = arrival_prefix + Fraction(selected_count, 1 << 16)
    assert resolvent_upper_bound == Fraction(27797, 65536)
    assert resolvent_upper_bound < Fraction(221, 465)

    # Keep the genuine selected support and loads, but replace the one
    # predecessor remainder by its exact gate value.  This is deliberately
    # not asserted reachable from rho_0=0: it is a forward-consistent local
    # countermodel to any closure using only the scalar resolvent data.
    synthetic_remainder = (1 << (gate_rank - 2)) + 4
    synthetic_remainder = (
        4 * synthetic_remainder + source_at_gate - load_at_gate
    )
    assert synthetic_remainder == (1 << gate_rank)
    assert synthetic_remainder - ((1 << gate_rank) + 1) == -1

    expected_excesses = [2, 4, 10, 20, 79, 307, 1217, 4865, 19456]
    observed_excesses: list[int] = []
    for d in range(gate_rank + 1, synthetic_end + 1):
        source_pair = 2 * target_bit(2 * d - 1) + target_bit(2 * d)
        divisor_load = 2 * loads[2 * d - 1] + loads[2 * d]
        pre_remainder = 4 * synthetic_remainder + source_pair - divisor_load
        midpoint_weight = (1 << d) + 1
        bit = int(pre_remainder >= midpoint_weight)
        assert bit == 1
        synthetic_remainder = pre_remainder - midpoint_weight
        observed_excesses.append(synthetic_remainder - (1 << d))
        for multiple in range(2 * d, len(loads), d):
            loads[multiple] += 1
    assert observed_excesses == expected_excesses
    assert observed_excesses[-1] >= synthetic_end + 1

    print(
        "resolvent local no-go PASS: actual rank-3056 support satisfies the "
        "phase-6 budget, while an exact substituted predecessor creates a "
        "saturated gate and permanently selected forward orbit"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--base", type=int, default=480)
    parser.add_argument("--analytic-cutoff", type=int, default=1620)
    parser.add_argument("--horizon", type=int, default=2000)
    parser.add_argument("--focused-diagonal-depth", type=int, default=120)
    args = parser.parse_args()

    assert args.base == 480, "the durable certificate is specifically rank 480"
    assert args.analytic_cutoff == 1620
    audit_tau_threshold(args.analytic_cutoff)
    audit_superincrease_and_base(args.base)
    audit_lower_greedy(args.horizon)
    audit_terminal_family(args.horizon)
    audit_generic_greedy_warning()
    audit_diagonal_recurrence(args.focused_diagonal_depth)
    audit_resolvent_local_countermodel()


if __name__ == "__main__":
    main()
