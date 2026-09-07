#!/usr/bin/env python3
"""Fast exact replay of #257 low-bit landing-window certificates.

The adjacent-row update is exact and is optionally checked against the direct
greedy construction for an initial range.  The optional incidence audit
recovers the exact carried-digit plateau behind each zero run and tests the
canonical ``2*b`` width candidate; a fixed noncanonical orbit guards against
silently treating local affine ancestry as sufficient.  This script is
evidence only: no finite replay proves an all-depth certificate bound.
"""

from __future__ import annotations

import argparse
import json
from math import isqrt
import time


def sieve_smallest_prime_factor(limit: int) -> list[int]:
    spf = list(range(limit + 1))
    if limit >= 1:
        spf[1] = 1
    for prime in range(2, isqrt(limit) + 1):
        if spf[prime] != prime:
            continue
        for multiple in range(prime * prime, limit + 1, prime):
            if spf[multiple] == multiple:
                spf[multiple] = prime
    return spf


def factorization(n: int, spf: list[int]) -> list[list[int]]:
    factors: list[list[int]] = []
    while n > 1:
        prime = spf[n]
        exponent = 0
        while n % prime == 0:
            n //= prime
            exponent += 1
        factors.append([prime, exponent])
    return factors


def divisors(n: int, spf: list[int]) -> list[int]:
    result = [1]
    for prime, exponent in factorization(n, spf):
        old = result[:]
        power = 1
        for _ in range(exponent):
            power *= prime
            result += [value * power for value in old]
    return result


def weight(row: int, exponent: int) -> int:
    return (1 << (2 * row)) // ((1 << exponent) - 1)


def exact_row(row: int) -> tuple[set[int], int]:
    remainder = (1 << (2 * row - 1)) - (1 << row)
    support: set[int] = set()
    for exponent in range(2, row):
        coin = weight(row, exponent)
        if coin <= remainder:
            support.add(exponent)
            remainder -= coin
    return support, remainder


def row_at_capacity(row: int, capacity: int) -> tuple[set[int], int]:
    """Run the same descending quotient greedy rule at an arbitrary capacity."""
    remainder = capacity
    support: set[int] = set()
    for exponent in range(2, row):
        coin = weight(row, exponent)
        if coin <= remainder:
            support.add(exponent)
            remainder -= coin
    return support, remainder


def pulse(row: int, support: set[int], spf: list[int]) -> int:
    odd = sum(
        1
        for exponent in divisors(2 * row + 1, spf)
        if 2 <= exponent < row and exponent in support
    )
    even = sum(
        1
        for exponent in divisors(2 * row + 2, spf)
        if 2 <= exponent < row and exponent in support
    )
    return 2 * odd + even


def advance(
    row: int, support: set[int], remainder: int, spf: list[int]
) -> tuple[set[int], int, str, int | None]:
    """Advance one row using the exact quotient-weight affine recurrence."""
    middle_remainder = (
        4 * remainder + (1 << (row + 1)) - pulse(row, support, spf)
    )
    largest_false = row - 1
    while largest_false >= 2 and largest_false in support:
        largest_false -= 1
    if largest_false >= 2:
        removed_tail = [e for e in support if e > largest_false]
        upper_remainder = (
            middle_remainder
            + sum(weight(row + 1, e) for e in removed_tail)
            - weight(row + 1, largest_false)
        )
        if upper_remainder >= 0:
            new_support = {e for e in support if e < largest_false}
            return new_support | {largest_false}, upper_remainder, "upper", largest_false
    terminal = weight(row + 1, row)
    if middle_remainder >= terminal:
        return support | {row}, middle_remainder - terminal, "right", None
    assert middle_remainder >= 0
    return set(support), middle_remainder, "middle", None


def certificate(remainder: int, target: int) -> tuple[int, int, int]:
    """Return certificate width, extra width, and the certified residue."""
    base_bits = (target - 1).bit_length()
    base_residue = remainder & ((1 << base_bits) - 1)
    if base_residue >= target:
        return base_bits, 0, base_residue
    zero_run = 0
    quotient = remainder >> base_bits
    while quotient and quotient & 1 == 0:
        zero_run += 1
        quotient >>= 1
    assert quotient
    width = base_bits + zero_run + 1
    return width, zero_run + 1, remainder & ((1 << width) - 1)


def sign_target(row: int, support_card: int) -> int:
    card_target = (4 * support_card) // 7 + 1
    sqrt_target = 2 * isqrt(2 * row) + 4
    return min(card_target, sqrt_target)


def two_adic_valuation(value: int) -> int:
    """Return ``v_2(value)`` for a positive integer."""
    assert value > 0
    return (value & -value).bit_length() - 1


def incidence_plateau_record(
    row: int,
    support: set[int],
    remainder: int,
    target: int,
    spf: list[int],
) -> dict[str, object]:
    """Expose the exact carried-incidence word behind a failed base window.

    Write the full backward incidence numerator as ``L=A+2^b H``, where
    ``b=ceil(log2(target))`` and ``0<=A<2^b``.  Only a prefix through the
    first successful remainder bit is needed to recover ``v_2(H+1)`` (when
    ``A>0``) or ``v_2(H)`` (when ``A=0``), because all omitted terms are
    divisible by the next power of two.
    """
    b = (target - 1).bit_length()
    width, extra, _ = certificate(remainder, target)
    assert b > 0
    prefix_width = max(width + 1, 3 * b + 1)
    assert prefix_width <= row

    coefficients: list[int] = []
    carried_digits: list[int] = []
    carry = 0
    low_numerator = 0
    for r in range(prefix_width):
        coefficient = sum(
            1 for exponent in divisors(2 * row - r, spf)
            if exponent in support
        )
        coefficients.append(coefficient)
        low_numerator += coefficient << r
        total = coefficient + carry
        carried_digits.append(total & 1)
        carry = total >> 1

    modulus = 1 << b
    A = low_numerator % modulus
    H_prefix = low_numerator >> b
    assert remainder % modulus == (-A) % modulus

    if extra == 0:
        zero_run = 0
        valuation_kind = "base_window_already_certifies"
        valuation = None
        expected_plateau: list[int] = []
    elif A > 0:
        zero_run = extra - 1
        valuation_kind = "v2(H+1)"
        valuation = two_adic_valuation(H_prefix + 1)
        expected_plateau = [1] * zero_run + [0]
        assert valuation == zero_run
        assert carried_digits[b:b + zero_run + 1] == expected_plateau
    else:
        zero_run = extra - 1
        valuation_kind = "v2(H)"
        valuation = two_adic_valuation(H_prefix)
        expected_plateau = [0] * zero_run + [1]
        assert valuation == zero_run
        assert carried_digits[b:b + zero_run + 1] == expected_plateau

    return {
        "base_bits": b,
        "A": A,
        "H_mod_2_pow_2b_plus_one": H_prefix % (1 << (2 * b + 1)),
        "extra_bits": extra,
        "zero_run": zero_run,
        "valuation_kind": valuation_kind,
        "valuation": valuation,
        "candidate_extra_le_two_b": extra <= 2 * b,
        "coefficients_from_b": coefficients[b:min(prefix_width, b + 2 * b + 2)],
        "carried_digits_from_b": carried_digits[b:min(prefix_width, b + 2 * b + 2)],
    }


def noncanonical_plateau_countermodel() -> dict[str, object]:
    """Exact no-go to deriving ``2*b`` from a bounded noncanonical ancestry.

    The orbit uses the canonical affine update after row five but starts from
    capacity 506 instead of the distinguished canonical capacity 480.
    """
    spf = sieve_smallest_prime_factor(40)
    support, remainder = row_at_capacity(5, 506)
    landing_support: set[int] | None = None
    landing_remainder: int | None = None
    landing_largest_false: int | None = None
    outgoing_branch: str | None = None
    for row in range(5, 15):
        next_support, next_remainder, branch, largest_false = advance(
            row, support, remainder, spf
        )
        if row == 13:
            assert branch == "upper" and largest_false == 10
            landing_support = set(next_support)
            landing_remainder = next_remainder
            landing_largest_false = largest_false
        if row == 14:
            outgoing_branch = branch
        support, remainder = next_support, next_remainder

    assert landing_support is not None
    assert landing_remainder is not None
    assert landing_largest_false == 10
    assert outgoing_branch == "middle"
    target = sign_target(14, len(landing_support))
    width, extra, residue = certificate(landing_remainder, target)
    b = (target - 1).bit_length()
    assert (len(landing_support), target, b) == (5, 3, 2)
    assert (landing_remainder, width, extra, residue) == (8193, 14, 12, 8193)
    return {
        "status": "exact_noncanonical_falsifier",
        "row_five_capacity": 506,
        "row_five_canonical_capacity": 480,
        "beta": "269/512",
        "canonical_beta": "1/2",
        "affine_generations_before_source": 8,
        "source_row": 13,
        "largest_false": 10,
        "landing_row": 14,
        "landing_support_card": len(landing_support),
        "landing_remainder": landing_remainder,
        "target": target,
        "base_bits": b,
        "certificate_bits": width,
        "extra_bits": extra,
        "candidate_extra_le_two_b": extra <= 2 * b,
        "meaning": (
            "these eight affine transitions and the local upper-to-middle "
            "geometry do not imply the 2*b plateau bound without the "
            "canonical beta=1/2 initial condition"
        ),
    }


def noncanonical_return_delay_countermodel() -> dict[str, object]:
    """Exact no-go to closing return delay with the existing late-gap socket."""
    spf = sieve_smallest_prime_factor(60)
    support, remainder = row_at_capacity(11, 1_805_057)
    assert support == {2, 4, 6, 7, 8, 9}
    assert remainder == 3078
    transitions: list[dict[str, object]] = []
    for row in range(11, 24):
        support, remainder, branch, largest_false = advance(
            row, support, remainder, spf
        )
        transitions.append({
            "source": row,
            "target": row + 1,
            "branch": branch,
            "largest_false": largest_false,
            "remainder": remainder,
        })

    assert transitions[0] == {
        "source": 11,
        "target": 12,
        "branch": "upper",
        "largest_false": 10,
        "remainder": 4,
    }
    assert transitions[1]["branch"] == "middle"
    assert [item["branch"] for item in transitions[2:11]] == ["right"] * 9
    assert transitions[11]["branch"] == "upper"
    assert transitions[11]["largest_false"] == 12
    assert transitions[12]["branch"] == "middle"
    source_row = 12
    base_bits = 3
    right_length = 9
    terminal_source = 22
    assert right_length >= source_row - base_bits - 1
    assert terminal_source < 2 * source_row
    assert 2 * terminal_source >= 3 * source_row
    return {
        "status": "exact_noncanonical_return_delay_no_go",
        "row_eleven_capacity": 1_805_057,
        "small_middle_row": source_row,
        "small_middle_remainder": 4,
        "target": 5,
        "base_bits": base_bits,
        "right_length": right_length,
        "return_delay_lower_bound": source_row - base_bits - 1,
        "terminal_upper_source": terminal_source,
        "before_full_shell": terminal_source < 2 * source_row,
        "late_gap_hypothesis": 2 * terminal_source < 3 * source_row,
        "transitions": transitions,
        "meaning": (
            "local small-middle, return-delay, and pre-full-shell timing can "
            "coexist while the terminal largest skip is non-late; canonical "
            "ancestry or a quotient-three/four gap input is still required"
        ),
    }


def event_record(
    source: int,
    largest_false: int,
    support: set[int],
    remainder: int,
    target: int,
    spf: list[int],
) -> dict[str, object]:
    width, extra, residue = certificate(remainder, target)
    base_bits = (target - 1).bit_length()
    return {
        "d": source,
        "ell": largest_false,
        "height": source - largest_false,
        "landing_row": source + 1,
        "support_card": len(support),
        "target": target,
        "base_bits": base_bits,
        "certificate_bits": width,
        "extra_bits": extra,
        "base_residue": remainder & ((1 << base_bits) - 1),
        "certificate_residue": residue,
        "zero_run_after_base": max(0, extra - 1),
        "remainder_bit_length": remainder.bit_length(),
        "remainder_low_64": remainder & ((1 << 64) - 1),
        "d_factorization": factorization(source, spf),
        "ell_factorization": factorization(largest_false, spf),
        "landing_factorization": factorization(source + 1, spf),
    }


def finite_anchor_programming_record() -> dict[str, object]:
    """Exact digit-level no-go for any fixed-anchor parity argument.

    This programs abstract fresh incidence positions after freezing the
    canonical row-4267 support through rank 512.  It does not claim that the
    enlarged abstract support is itself a canonical greedy row.
    """
    row = 4267
    anchor_limit = 512
    support, _ = exact_row(row)
    anchors = {exponent for exponent in support if exponent <= anchor_limit}
    chosen_positions = {
        2, 4, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 20, 23
    }
    coefficient_word: list[int] = []
    carried_word: list[int] = []
    carry = 0
    low_numerator = 0
    for r in range(25):
        anchor_coefficient = sum(
            1 for exponent in anchors if (2 * row - r) % exponent == 0
        )
        coefficient = anchor_coefficient + int(r in chosen_positions)
        coefficient_word.append(coefficient)
        low_numerator += coefficient << r
        total = coefficient + carry
        carried_word.append(total & 1)
        carry = total >> 1

    support_card = len(anchors) + len(chosen_positions)
    target = (4 * support_card) // 7 + 1
    b = (target - 1).bit_length()
    low_residue = low_numerator % (1 << b)
    negative_residue = (-low_numerator) % (1 << b)
    zero_run = 0
    for bit in carried_word[b:]:
        if bit != 1:
            break
        zero_run += 1

    assert (len(anchors), support_card, target, b) == (235, 250, 143, 8)
    assert coefficient_word == [
        4, 3, 8, 1, 2, 1, 6, 1, 15, 3, 2, 2, 1,
        0, 11, 2, 2, 5, 2, 1, 10, 0, 9, 2, 5,
    ]
    assert carried_word == [
        0, 1, 0, 0, 1, 1, 1, 0,
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0,
    ]
    assert (low_residue, negative_residue, zero_run) == (114, 142, 16)
    return {
        "status": "exact_fixed_anchor_parity_no_go",
        "canonical_anchor_row": row,
        "anchor_limit": anchor_limit,
        "anchor_count": len(anchors),
        "fresh_incidence_positions": sorted(chosen_positions),
        "abstract_support_card": support_card,
        "target": target,
        "base_bits": b,
        "coefficient_word": coefficient_word,
        "carried_word": carried_word,
        "low_numerator_mod_2_pow_b": low_residue,
        "negative_residue_mod_2_pow_b": negative_residue,
        "zero_run": zero_run,
        "extra_bits": zero_run + 1,
        "candidate_extra_le_two_b": zero_run + 1 <= 2 * b,
        "scope": (
            "rules out fixed-anchor plus parity/capacity-only proofs; does not "
            "construct a canonical descending-greedy support at the CRT row"
        ),
    }


def main(
    horizon: int,
    validate: int,
    incidence_plateau: bool,
    anchor_programming: bool,
) -> None:
    started = time.time()
    spf = sieve_smallest_prime_factor(2 * horizon + 8)
    support, remainder = exact_row(3)
    pending: tuple[int, int, set[int], int] | None = None
    kinds = ("direct", "amplified", "hybrid_sign")
    histograms: dict[str, dict[int, int]] = {kind: {} for kind in kinds}
    maxima: dict[str, dict[str, object] | None] = {kind: None for kind in kinds}
    record_breakers: dict[str, list[dict[str, object]]] = {
        kind: [] for kind in kinds
    }
    events = 0
    strict_events = 0
    checkpoints = {5000, 10000, 20000, 50000, 100000, 200000, horizon}
    snapshots: list[dict[str, object]] = []
    plateau_event_count = 0
    plateau_candidate_failures: list[dict[str, object]] = []
    maximum_plateau_event: dict[str, object] | None = None

    for row in range(3, horizon + 2):
        next_support, next_remainder, branch, largest_false = advance(
            row, support, remainder, spf
        )
        if row <= validate:
            expected_support, expected_remainder = exact_row(row + 1)
            assert next_support == expected_support
            assert next_remainder == expected_remainder
        if pending is not None:
            if branch == "middle":
                events += 1
                source, ell, landing_support, landing_remainder = pending
                if 2 * (source + 1) < 3 * ell:
                    strict_events += 1
                    targets = {
                        "direct": len(landing_support),
                        "amplified": (1 << (source - ell)) * len(landing_support),
                        "hybrid_sign": sign_target(
                            source + 1, len(landing_support)
                        ),
                    }
                    for kind, target in targets.items():
                        record = event_record(
                            source,
                            ell,
                            landing_support,
                            landing_remainder,
                            target,
                            spf,
                        )
                        extra = int(record["extra_bits"])
                        histograms[kind][extra] = histograms[kind].get(extra, 0) + 1
                        maximum = maxima[kind]
                        if maximum is None or extra > int(maximum["extra_bits"]):
                            maxima[kind] = record
                            record_breakers[kind].append(record)
                        if kind == "hybrid_sign" and incidence_plateau:
                            plateau = incidence_plateau_record(
                                source + 1,
                                landing_support,
                                landing_remainder,
                                target,
                                spf,
                            )
                            assert plateau["extra_bits"] == extra
                            plateau_event_count += 1
                            plateau_record = {**record, **plateau}
                            if not plateau["candidate_extra_le_two_b"]:
                                plateau_candidate_failures.append(plateau_record)
                            if (
                                maximum_plateau_event is None
                                or int(plateau["zero_run"])
                                    > int(maximum_plateau_event["zero_run"])
                            ):
                                maximum_plateau_event = plateau_record
            pending = None
        if branch == "upper":
            assert largest_false is not None
            pending = (row, largest_false, next_support, next_remainder)
        support, remainder = next_support, next_remainder
        if row in checkpoints:
            snapshots.append({
                "source_horizon": row,
                "strict_events": strict_events,
                "max_extra_bits": {
                    kind: None if maxima[kind] is None else maxima[kind]["extra_bits"]
                    for kind in kinds
                },
            })

    output = {
        "schema": "erdos257_extended_low_bit_window_probe_v0",
        "horizon": horizon,
        "validated_exact_rows_through": validate,
        "elapsed_seconds": time.time() - started,
        "upper_to_middle_events": events,
        "strict_next_late_events": strict_events,
        "histograms": {
            kind: {str(extra): count for extra, count in sorted(histogram.items())}
            for kind, histogram in histograms.items()
        },
        "maxima": maxima,
        "record_breakers": record_breakers,
        "checkpoints": snapshots,
        "exact_width_law": (
            "extra=0 if R mod 2^b >= M; otherwise extra=1 plus the zero-run "
            "length of floor(R/2^b), where b=ceil(log2 M)"
        ),
        "incidence_plateau": {
            "enabled": incidence_plateau,
            "event_count": plateau_event_count,
            "identity": (
                "for L=A+2^b H and a failed base window, zero_run=v2(H+1) "
                "when A>0 and zero_run=v2(H) when A=0; equivalently the "
                "carried incidence digits from b are 1^z0 or 0^z1"
            ),
            "candidate": "extra_bits <= 2*b, hence certificate_bits <= 3*b",
            "candidate_failure_count": len(plateau_candidate_failures),
            "first_candidate_failure": plateau_candidate_failures[:1],
            "maximum_zero_run_event": maximum_plateau_event,
            "claim_ceiling": (
                "the valuation/plateau identity is exact; the 2*b bound is "
                "a canonical-orbit conjecture tested only on this finite replay"
            ),
        },
        "noncanonical_plateau_countermodel": noncanonical_plateau_countermodel(),
        "noncanonical_return_delay_countermodel": (
            noncanonical_return_delay_countermodel()
        ),
        "finite_anchor_programming": (
            finite_anchor_programming_record() if anchor_programming else {
                "enabled": False,
            }
        ),
        "claim_ceiling": (
            "exact finite replay only; no all-depth width bound or landing-sign "
            "theorem follows from these data"
        ),
    }
    print(json.dumps(output))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("horizon", type=int)
    parser.add_argument("--validate", type=int, default=500)
    parser.add_argument(
        "--incidence-plateau",
        action="store_true",
        help="audit the exact carried-incidence plateau behind hybrid windows",
    )
    parser.add_argument(
        "--anchor-programming",
        action="store_true",
        help="emit the exact fixed-anchor parity-programming no-go record",
    )
    arguments = parser.parse_args()
    main(
        arguments.horizon,
        arguments.validate,
        arguments.incidence_plateau,
        arguments.anchor_programming,
    )
