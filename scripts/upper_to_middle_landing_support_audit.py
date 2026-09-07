"""Exact audit of the support geometry at upper-to-middle seam landings.

The integer seam greedy at row ``s`` uses the weights

    floor(4^s / (2^e - 1)),  2 <= e < s,

and target ``2^(2s-1) - 2^s``.  This script replays that greedy algorithm
with Python integers, classifies support changes, and tests the candidate

    2^(d-ell) * |S_(d+1)| <= R_(d+1)

at every upper-to-middle event.  Here ``d`` is the upper source row and
``ell`` its largest false rank.  A failure is the exact falsifier for the
support-amplified route to ``|S_(d+1)| <= R_(d+1)``.

On strictly next-late events it also checks the exact same-largest-false
block identity, its equivalent initial-middle-excess threshold, the coarse
pulse-free linear sufficient condition, and the number of selected prefix
ranks invisible to every pulse in the block.  Two exact noncanonical
countermodels delimit what those identities can prove without the distinguished
canonical capacity: the original one-step example and an eight-generation
affine-ancestry example which still violates both E-MID and E-LIN.

The audit also checks the exact conserved capacity coordinate

    beta_s = C_s / 4^s + 2^(-s).

The canonical orbit is beta=1/2.  After substituting the exact floor error,
an amplified-support failure is equivalent to the actual selected reciprocal
sum entering a corridor of width ``2^h * m / 4^s``.  Fraction arithmetic
checks that equivalence on the bounded diagnostic rows.

No floating-point arithmetic is used.  Floor errors are accumulated as
``Fraction`` values only for diagnostic comparison with the landing
remainder.
"""

from __future__ import annotations

from fractions import Fraction
import json
from math import isqrt
import sys


def ceil_div(num: int, den: int) -> int:
    assert num >= 0 and den > 0
    return (num + den - 1) // den


def row_pulse(s: int, e: int) -> int:
    return 2 * int((2 * s + 1) % e == 0) + int((2 * s + 2) % e == 0)


def seam_row(s: int) -> tuple[frozenset[int], int]:
    scale = 1 << (2 * s)
    remainder = (1 << (2 * s - 1)) - (1 << s)
    support: set[int] = set()
    for e in range(2, s):
        weight = scale // ((1 << e) - 1)
        if weight <= remainder:
            support.add(e)
            remainder -= weight
    return frozenset(support), remainder


def greedy_row_with_capacity(s: int, capacity: int) -> tuple[frozenset[int], int]:
    """Run the same exact Mersenne-weight greedy at an arbitrary capacity."""
    scale = 1 << (2 * s)
    remainder = capacity
    support: set[int] = set()
    for e in range(2, s):
        weight = scale // ((1 << e) - 1)
        if weight <= remainder:
            support.add(e)
            remainder -= weight
    return frozenset(support), remainder


def capacity_beta(s: int, capacity: int) -> Fraction:
    """The exact conserved coordinate for the affine capacity recurrence."""
    return Fraction(capacity, 4 ** s) + Fraction(1, 1 << s)


def canonical_capacity(s: int) -> int:
    return (1 << (2 * s - 1)) - (1 << s)


def canonical_origin_invariant_receipt() -> dict[str, object]:
    """Replay the canonical and eight-generation noncanonical beta values."""
    canonical_beta = Fraction(1, 2)
    for s in range(5, 16):
        assert capacity_beta(s, canonical_capacity(s)) == canonical_beta

    capacities = {5: 370}
    for s in range(6, 16):
        capacities[s] = 4 * capacities[s - 1] + (1 << s)
    noncanonical_beta = Fraction(201, 512)
    for s, capacity in capacities.items():
        assert capacity_beta(s, capacity) == noncanonical_beta
    assert canonical_beta - noncanonical_beta == Fraction(55, 512)
    return {
        "status": "exact_affine_invariant",
        "coordinate": "beta_s = C_s/4^s + 2^(-s)",
        "canonical_beta": "1/2",
        "eight_generation_countermodel_beta": "201/512",
        "permanent_beta_deficit": "55/512",
        "meaning": (
            "bounded affine ancestry preserves rather than repairs a "
            "noncanonical origin; canonical closure requires an actual "
            "anti-concentration input at beta=1/2"
        ),
    }


def noncanonical_capacity_countermodel() -> dict[str, object]:
    """Exact no-go for proofs that forget the canonical seam capacity."""
    capacities = {5: 565, 6: 2324, 7: 9424, 8: 37952}
    rows = {
        s: greedy_row_with_capacity(s, capacity)
        for s, capacity in capacities.items()
    }
    assert capacities[6] == 4 * capacities[5] + (1 << 6)
    assert capacities[7] == 4 * capacities[6] + (1 << 7)
    assert capacities[8] == 4 * capacities[7] + (1 << 8)
    assert rows[5] == (frozenset({2, 3, 4}), 10)
    assert rows[6] == (frozenset({2, 3, 4}), 101)
    assert rows[7] == (frozenset({2, 3, 4, 5}), 3)
    assert rows[8] == (frozenset({2, 3, 4, 5}), 262)
    largest_false = 5
    height = 6 - largest_false
    landing_card = len(rows[7][0])
    landing_remainder = rows[7][1]
    assert 2 * (6 + 1) < 3 * largest_false
    assert row_pulse(6, largest_false) == 0
    assert branch(rows[6][0], rows[7][0], 6) == "upper"
    assert branch(rows[7][0], rows[8][0], 7) == "middle"
    assert branch(rows[5][0], rows[6][0], 5) == "middle"
    previous_pulse = sum(row_pulse(5, e) for e in rows[5][0])
    initial_middle_excess = rows[6][1] - (1 << 6)
    assert previous_pulse == 3
    assert initial_middle_excess == 4 * rows[5][1] - previous_pulse == 37
    assert rows[5][1] >= len(rows[5][0]) + 2
    assert landing_remainder < landing_card
    assert landing_remainder < (1 << height) * landing_card
    return {
        "status": "exact_countermodel",
        "scope": "noncanonical affine capacities with exact Mersenne quotient weights",
        "capacities": capacities,
        "supports": {str(s): sorted(support) for s, (support, _) in rows.items()},
        "remainders": {str(s): remainder for s, (_, remainder) in rows.items()},
        "largest_false": largest_false,
        "height": height,
        "boundary_pulse": row_pulse(6, largest_false),
        "previous_middle_pulse": previous_pulse,
        "initial_middle_excess": initial_middle_excess,
        "previous_card_gap": rows[5][1] - len(rows[5][0]) - 2,
        "branches": ["upper", "middle"],
        "landing_card": landing_card,
        "landing_remainder": landing_remainder,
        "amplified_lhs": (1 << height) * landing_card,
        "meaning": "the fixed canonical seam capacity or its global ancestry is indispensable",
    }


def eight_generation_affine_ancestry_countermodel() -> dict[str, object]:
    """Exact E-MID no-go after eight affine capacity generations.

    The orbit starts from a deliberately noncanonical row-five capacity but
    thereafter obeys the same affine capacity update and exact quotient greedy
    rule as the canonical seam.  The source event is eight updates later.  This
    refutes bounded recent-ancestry arguments which do not also use the
    distinguished canonical origin; it is not a counterexample on that origin.
    """
    capacities = {5: 370}
    for s in range(6, 16):
        capacities[s] = 4 * capacities[s - 1] + (1 << s)
    assert capacities == {
        5: 370,
        6: 1544,
        7: 6304,
        8: 25472,
        9: 102400,
        10: 410624,
        11: 1644544,
        12: 6582272,
        13: 26337280,
        14: 105365504,
        15: 421494784,
    }
    rows = {
        s: greedy_row_with_capacity(s, capacity)
        for s, capacity in capacities.items()
    }
    expected_rows = {
        5: (frozenset({2}), 29),
        6: (frozenset({2, 5}), 47),
        7: (frozenset({2, 5, 6}), 55),
        8: (frozenset({2, 5, 6}), 473),
        9: (frozenset({2, 5, 6, 7}), 338),
        10: (frozenset({2, 5, 6, 7, 9}), 322),
        11: (frozenset({2, 5, 6, 7, 9}), 3333),
        12: (frozenset({2, 5, 6, 7, 9, 10}), 1026),
        13: (frozenset({2, 5, 6, 7, 9, 10}), 12293),
        14: (frozenset({2, 5, 6, 7, 9, 10, 12}), 0),
        15: (frozenset({2, 5, 6, 7, 9, 10, 12}), 32764),
    }
    assert rows == expected_rows

    d = 13
    ell = 12
    height = d - ell
    prefix = rows[ell + 1][0]
    landing_support = prefix | {ell}
    assert d - 5 == 8
    assert branch(rows[ell][0], rows[ell + 1][0], ell) == "middle"
    assert branch(rows[d][0], rows[d + 1][0], d) == "upper"
    assert branch(rows[d + 1][0], rows[d + 2][0], d + 1) == "middle"
    assert 2 * (d + 1) < 3 * ell
    assert rows[d + 1][0] == landing_support

    landing_card = len(landing_support)
    landing_remainder = rows[d + 1][1]
    initial_middle_excess = rows[ell + 1][1] - (1 << (ell + 1))
    block_charge = 0
    landing_prefix_pulse = sum(row_pulse(d, e) for e in prefix)
    middle_threshold = (
        (1 << (ell - height + 1))
        + 4
        + ceil_div(
            4 * block_charge
            + landing_prefix_pulse
            + (1 << height) * landing_card,
            4 ** height,
        )
    )
    linear_buffer = (
        (1 << (ell - height + 1))
        + 4
        + ceil_div(5 * landing_card + 2 * height, 3)
    )
    block_expected = (
        (4 ** height) * initial_middle_excess
        - (1 << (d + 1))
        - 4 ** (height + 1)
        - 4 * block_charge
        - landing_prefix_pulse
    )
    assert landing_card == 7
    assert landing_prefix_pulse == 4
    assert initial_middle_excess == 4101
    assert middle_threshold == 4105
    assert linear_buffer == 4113
    assert block_expected == landing_remainder == 0
    assert initial_middle_excess < middle_threshold < linear_buffer
    assert landing_remainder < (1 << height) * landing_card

    return {
        "status": "exact_countermodel",
        "scope": (
            "eight recent affine-capacity generations with exact Mersenne "
            "quotient weights and greedy supports, but noncanonical row-five origin"
        ),
        "initial_row": 5,
        "initial_capacity": capacities[5],
        "canonical_row_five_capacity": (1 << 9) - (1 << 5),
        "ancestry_generations_before_source": d - 5,
        "capacities": capacities,
        "source": d,
        "largest_false": ell,
        "height": height,
        "prefix_support": sorted(prefix),
        "landing_support": sorted(landing_support),
        "landing_card": landing_card,
        "landing_prefix_pulse": landing_prefix_pulse,
        "block_charge": block_charge,
        "initial_middle_excess": initial_middle_excess,
        "middle_threshold": middle_threshold,
        "linear_buffer": linear_buffer,
        "middle_threshold_deficit": middle_threshold - initial_middle_excess,
        "linear_buffer_deficit": linear_buffer - initial_middle_excess,
        "block_identity_lhs": block_expected,
        "landing_remainder": landing_remainder,
        "amplified_support_target": (1 << height) * landing_card,
        "meaning": (
            "E-MID and E-LIN are not consequences of any argument retaining "
            "only this eight-generation affine window; the canonical origin "
            "or information reaching beyond the window is indispensable"
        ),
    }


def floor_error(s: int, support: frozenset[int]) -> Fraction:
    scale = 1 << (2 * s)
    return sum(
        (Fraction(scale % ((1 << e) - 1), (1 << e) - 1) for e in support),
        Fraction(0),
    )


def low_bit_divisor_incidence_sum(
    s: int, support: frozenset[int], t: int
) -> int:
    """Return the low ``t`` bits of the selected quotient-weight sum.

    The exact finite geometric expansion

        floor(2^(2s)/(2^e-1)) = sum_{q e <= 2s} 2^(2s-qe)

    shows that only exponents below ``t`` survive modulo ``2^t``.  Computing
    those terms directly avoids repeated division of very large integers
    while retaining an exact divisor-incidence interpretation.
    """
    assert 0 <= t <= s
    modulus = 1 << t
    total = 0
    for e in support:
        q_first = max(1, (2 * s - t) // e + 1)
        q_last = (2 * s) // e
        for q in range(q_first, q_last + 1):
            exponent = 2 * s - q * e
            assert 0 <= exponent < t
            total = (total + (1 << exponent)) % modulus
    return total


def low_bit_window_certificate(
    s: int, support: frozenset[int], remainder: int, target: int
) -> dict[str, int] | None:
    """Find the first exact low-bit certificate ``remainder >= target``.

    The canonical capacity is divisible by ``2^s``.  Hence, for ``t <= s``,
    ``remainder`` is congruent to the negative selected low-bit incidence
    sum.  A residue at least ``target`` is therefore an unconditional lower
    bound for the nonnegative integer remainder.
    """
    assert target > 0
    base_bits = (target - 1).bit_length()
    base_low_sum = low_bit_divisor_incidence_sum(s, support, base_bits)
    base_residue = (-base_low_sum) % (1 << base_bits)
    for t in range(base_bits, s + 1):
        modulus = 1 << t
        low_sum = low_bit_divisor_incidence_sum(s, support, t)
        residue = (-low_sum) % modulus
        assert remainder % modulus == residue
        assert (1 <= low_sum <= modulus - target) == (residue >= target)
        if residue >= target:
            scale = 1 << (2 * s)
            direct_low_sum = sum(
                scale // ((1 << e) - 1) for e in support
            ) % modulus
            assert direct_low_sum == low_sum
            return {
                "base_bits": base_bits,
                "base_low_incidence_sum": base_low_sum,
                "base_negative_residue": base_residue,
                "certificate_bits": t,
                "extra_bits": t - base_bits,
                "modulus": modulus,
                "low_incidence_sum": low_sum,
                "negative_residue": residue,
            }
    return None


def floor_error_sign_target(s: int, support_card: int) -> int:
    """A Lean-backed integer threshold strictly above the floor error.

    ``seamRankFloorError_le_four_sevenths`` gives the cardinal branch, while
    ``evenTruncationFloorErrorEnvelope_lt_two_sqrt_add_four`` and
    ``seamWordFloorError_le_evenTruncationEnvelope`` give the square-root
    branch.  Either strict majorant is enough for positive real orientation.
    """
    assert s >= 5 and support_card >= 0
    card_target = (4 * support_card) // 7 + 1
    sqrt_target = 2 * isqrt(2 * s) + 4
    return min(card_target, sqrt_target)


def _is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    divisor = 3
    while divisor * divisor <= n:
        if n % divisor == 0:
            return False
        divisor += 2
    return True


def _primes_above(bound: int, count: int) -> list[int]:
    primes: list[int] = []
    candidate = max(bound + 1, 5)
    if candidate % 2 == 0:
        candidate += 1
    while len(primes) < count:
        if _is_prime(candidate):
            primes.append(candidate)
        candidate += 2
    return primes


def _crt_extend(
    residue: int, modulus: int, target: int, prime: int
) -> tuple[int, int]:
    """Add ``x = target (mod prime)`` to a coprime CRT system."""
    multiplier = ((target - residue) * pow(modulus, -1, prime)) % prime
    new_modulus = modulus * prime
    return (residue + modulus * multiplier) % new_modulus, new_modulus


def finite_pattern_crt_carry_example(t: int, s_mod_six: int) -> dict[str, object]:
    """Realize an arbitrary-width zero low-bit word in strict landing geometry.

    This deliberately does *not* impose canonical greedy reachability.  Its role
    is to test exactly how much the finite divisor window and the upper/middle
    support shape can prove without the distinguished canonical ancestry.
    """
    assert 1 <= t and 0 <= s_mod_six < 6
    base: list[int] = []
    extras: list[int] = []
    carries = [0]
    for r in range(t):
        b_r = int(r % 2 == 0) + int((2 * s_mod_six - r) % 3 == 0)
        x_r = (b_r + carries[-1]) % 2
        next_carry = (b_r + x_r + carries[-1]) // 2
        assert 0 <= next_carry <= 2
        base.append(b_r)
        extras.append(x_r)
        carries.append(next_carry)
    coefficients = [b + x for b, x in zip(base, extras, strict=True)]
    weighted_sum = sum(value << r for r, value in enumerate(coefficients))
    assert weighted_sum == carries[-1] << t

    used_primes = _primes_above(max(t, 5), sum(extras))
    prime_iter = iter(used_primes)
    residue = s_mod_six
    modulus = 6
    for r, x_r in enumerate(extras):
        if x_r == 0:
            continue
        prime = next(prime_iter)
        target = (r * pow(2, -1, prime)) % prime
        residue, modulus = _crt_extend(residue, modulus, target, prime)

    lower_bound = max(3 * t + 4, max(used_primes, default=3) + t + 3)
    if residue <= lower_bound:
        residue += ((lower_bound - residue) // modulus + 1) * modulus
    s = residue
    d = s - 1
    ell = s - 1 - t
    landing_support = {2, 3, ell, *used_primes}
    assert s % 6 == s_mod_six
    assert 2 * (d + 1) < 3 * ell
    assert all(prime < ell for prime in used_primes)
    assert ell not in {2, 3, *used_primes}

    realized_coefficients = [
        sum(int((2 * s - r) % e == 0) for e in landing_support)
        for r in range(t)
    ]
    assert realized_coefficients == coefficients
    assert max(realized_coefficients) <= 3
    realized_sum = sum(
        value << r for r, value in enumerate(realized_coefficients)
    )
    assert realized_sum % (1 << t) == 0
    return {
        "width": t,
        "s_mod_six": s_mod_six,
        "landing_row_bit_length": s.bit_length(),
        "largest_false_gap": t,
        "added_prime_count": len(used_primes),
        "maximum_coefficient": max(realized_coefficients),
        "terminal_carry": carries[-1],
        "weighted_sum_div_modulus": realized_sum >> t,
        "strict_next_late": True,
        "low_bit_residue": 0,
    }


def finite_pattern_crt_carry_no_go(max_width: int = 128) -> dict[str, object]:
    """Replay the exact CRT/carry obstruction through a bounded width."""
    examples = [
        finite_pattern_crt_carry_example(t, phase)
        for t in range(1, max_width + 1)
        for phase in range(6)
    ]
    return {
        "status": "exact_finite_pattern_no_go",
        "widths_checked": [1, max_width],
        "s_mod_six_phases_checked": 6,
        "example_count": len(examples),
        "maximum_coefficient": max(
            int(example["maximum_coefficient"]) for example in examples
        ),
        "maximum_width_examples": [
            example for example in examples if example["width"] == max_width
        ],
        "meaning": (
            "strict next-late upper-to-middle support shape, forced ranks 2 and 3, "
            "omitted ranks 4 and 5, and coefficient ceiling 3 do not force any "
            "finite low-bit clearance; canonical greedy ancestry is indispensable"
        ),
        "claim_ceiling": (
            "these supports have the exact local shape but are not asserted to be "
            "reachable from the canonical greedy capacity"
        ),
    }


def branch(previous: frozenset[int], current: frozenset[int], terminal: int) -> str:
    if current == previous | {terminal}:
        return "right"
    if current == previous:
        return "middle"
    return "upper"


def main(limit: int, floor_error_limit: int) -> None:
    supports: dict[int, frozenset[int]] = {}
    remainders: dict[int, int] = {}
    entering: dict[int, str] = {}
    for s in range(3, limit + 3):
        supports[s], remainders[s] = seam_row(s)
        if s > 3:
            entering[s] = branch(supports[s - 1], supports[s], s - 1)

    events: list[dict[str, object]] = []
    residue_moduli = (2, 3, 4, 5, 7, 8, 16)
    residues = {m: set() for m in residue_moduli}
    first_falsifier: dict[str, object] | None = None
    nonlate: list[dict[str, int]] = []
    boundary_pulse_nonzero: list[dict[str, int]] = []
    block_identity_failures: list[dict[str, int]] = []
    middle_threshold_failures: list[dict[str, int]] = []
    linear_buffer_failures: list[dict[str, int]] = []
    strict_next_late_events = 0
    max_pulse_silent_event: dict[str, int] | None = None
    pulse_silent_1993_event: dict[str, int] | None = None
    canonical_identity_checks = 0
    canonical_identity_failures: list[dict[str, int]] = []
    canonical_corridor_equivalence_failures: list[dict[str, int]] = []
    canonical_corridor_hits = 0
    low_bit_certificate_failures: list[dict[str, int]] = []
    low_bit_extra_histogram: dict[int, int] = {}
    maximum_low_bit_extra_event: dict[str, int] | None = None
    first_natural_scale_failure: dict[str, int] | None = None
    direct_low_bit_certificate_failures: list[dict[str, int]] = []
    direct_low_bit_extra_histogram: dict[int, int] = {}
    maximum_direct_low_bit_extra_event: dict[str, int] | None = None
    first_direct_natural_scale_failure: dict[str, int] | None = None
    hybrid_low_bit_certificate_failures: list[dict[str, int]] = []
    hybrid_low_bit_extra_histogram: dict[int, int] = {}
    maximum_hybrid_low_bit_extra_event: dict[str, int] | None = None
    first_hybrid_natural_scale_failure: dict[str, int] | None = None

    for d in range(5, limit + 1):
        if entering.get(d + 1) != "upper" or entering.get(d + 2) != "middle":
            continue
        missing = [e for e in range(2, d) if e not in supports[d]]
        if not missing:
            continue
        ell = max(missing)
        landing = d + 1
        landing_remainder = remainders[landing]
        landing_card = len(supports[landing])
        height = d - ell
        factor = 1 << height
        lhs = factor * landing_card
        slack = landing_remainder - lhs
        phi = (
            floor_error(landing, supports[landing])
            if landing <= floor_error_limit
            else None
        )
        pulse = row_pulse(d, ell)
        next_late = 2 * (d + 1) < 3 * ell
        if not next_late:
            nonlate.append({"d": d, "ell": ell})
        if pulse != 0:
            boundary_pulse_nonzero.append({"d": d, "ell": ell, "pulse": pulse})
        for modulus in residue_moduli:
            residues[modulus].add(landing_remainder % modulus)
        event = {
            "d": d,
            "ell": ell,
            "height": height,
            "landing_row": landing,
            "landing_remainder": landing_remainder,
            "landing_card": landing_card,
            "support_amplified_lhs": lhs,
            "support_amplified_slack": slack,
            "next_late": next_late,
            "boundary_pulse": pulse,
            "floor_error_num": None if phi is None else phi.numerator,
            "floor_error_den": None if phi is None else phi.denominator,
            "remainder_minus_floor_error_num": None
                if phi is None else (Fraction(landing_remainder) - phi).numerator,
            "remainder_minus_floor_error_den": None
                if phi is None else (Fraction(landing_remainder) - phi).denominator,
        }
        if phi is not None:
            reciprocal_sum = sum(
                (Fraction(1, (1 << e) - 1) for e in supports[landing]),
                Fraction(0),
            )
            canonical_center = Fraction(1, 2) - Fraction(1, 1 << landing)
            reconstructed_remainder = (
                (4 ** landing) * (canonical_center - reciprocal_sum) + phi
            )
            canonical_identity_checks += 1
            if reconstructed_remainder != landing_remainder:
                canonical_identity_failures.append({"d": d, "landing": landing})
            corridor_lower = canonical_center - Fraction(lhs, 4 ** landing) + Fraction(
                phi, 4 ** landing
            )
            corridor_upper = canonical_center + Fraction(phi, 4 ** landing)
            in_corridor = corridor_lower < reciprocal_sum <= corridor_upper
            amplified_failure = landing_remainder < lhs
            if in_corridor:
                canonical_corridor_hits += 1
            if in_corridor != amplified_failure:
                canonical_corridor_equivalence_failures.append(
                    {"d": d, "landing": landing}
                )
            assert corridor_upper - corridor_lower == Fraction(lhs, 4 ** landing)
        if next_late:
            strict_next_late_events += 1
            prefix = frozenset(e for e in supports[d] if e < ell)
            landing_support = prefix | {ell}
            assert supports[ell + 1] == prefix
            assert supports[d + 1] == landing_support
            for j in range(ell + 1, d + 1):
                assert supports[j] == prefix | set(range(ell + 1, j))

            block_charge = 0
            for j in range(ell + 1, d):
                pulse_j = sum(row_pulse(j, e) for e in supports[j])
                block_charge = 4 * block_charge + pulse_j
            landing_prefix_pulse = sum(row_pulse(d, e) for e in prefix)
            initial_middle_excess = remainders[ell + 1] - (1 << (ell + 1))
            landing_card_from_prefix = len(prefix) + 1
            block_expected = (
                (4 ** height) * initial_middle_excess
                - (1 << (d + 1))
                - 4 ** (height + 1)
                - 4 * block_charge
                - landing_prefix_pulse
            )
            threshold_numerator = (
                (1 << (d + 1))
                + 4 ** (height + 1)
                + 4 * block_charge
                + landing_prefix_pulse
                + (1 << height) * landing_card_from_prefix
            )
            middle_threshold = ceil_div(threshold_numerator, 4 ** height)
            linear_buffer = (
                (1 << (ell - height + 1))
                + 4
                + ceil_div(5 * landing_card_from_prefix + 2 * height, 3)
            )
            active_prefix = {
                e for e in prefix
                if any(row_pulse(j, e) != 0 for j in range(ell, d + 1))
            }
            prefix_block_pulse = sum(
                row_pulse(j, e)
                for j in range(ell, d + 1)
                for e in prefix
            )
            block_record = {
                "d": d,
                "ell": ell,
                "height": height,
                "prefix_card": len(prefix),
                "landing_card": landing_card_from_prefix,
                "active_prefix_card": len(active_prefix),
                "pulse_silent_prefix_card": len(prefix) - len(active_prefix),
                "prefix_block_pulse": prefix_block_pulse,
                "landing_prefix_pulse": landing_prefix_pulse,
                "block_charge": block_charge,
                "initial_middle_excess_bit_length": initial_middle_excess.bit_length(),
                "landing_remainder_bit_length": landing_remainder.bit_length(),
            }
            low_bit_certificate = low_bit_window_certificate(
                landing,
                supports[landing],
                landing_remainder,
                lhs,
            )
            if low_bit_certificate is None:
                low_bit_certificate_failures.append(block_record)
            else:
                extra_bits = low_bit_certificate["extra_bits"]
                low_bit_extra_histogram[extra_bits] = (
                    low_bit_extra_histogram.get(extra_bits, 0) + 1
                )
                low_bit_record = {
                    **block_record,
                    **low_bit_certificate,
                    "target": lhs,
                }
                if extra_bits > 0 and first_natural_scale_failure is None:
                    first_natural_scale_failure = low_bit_record
                if (
                    maximum_low_bit_extra_event is None
                    or extra_bits > maximum_low_bit_extra_event["extra_bits"]
                ):
                    maximum_low_bit_extra_event = low_bit_record
            direct_low_bit_certificate = low_bit_window_certificate(
                landing,
                supports[landing],
                landing_remainder,
                landing_card_from_prefix,
            )
            if direct_low_bit_certificate is None:
                direct_low_bit_certificate_failures.append(block_record)
            else:
                direct_extra_bits = direct_low_bit_certificate["extra_bits"]
                direct_low_bit_extra_histogram[direct_extra_bits] = (
                    direct_low_bit_extra_histogram.get(direct_extra_bits, 0) + 1
                )
                direct_low_bit_record = {
                    **block_record,
                    **direct_low_bit_certificate,
                    "target": landing_card_from_prefix,
                }
                if (
                    direct_extra_bits > 0
                    and first_direct_natural_scale_failure is None
                ):
                    first_direct_natural_scale_failure = direct_low_bit_record
                if (
                    maximum_direct_low_bit_extra_event is None
                    or direct_extra_bits
                        > maximum_direct_low_bit_extra_event["extra_bits"]
                ):
                    maximum_direct_low_bit_extra_event = direct_low_bit_record
            hybrid_target = floor_error_sign_target(
                landing, landing_card_from_prefix
            )
            hybrid_low_bit_certificate = low_bit_window_certificate(
                landing,
                supports[landing],
                landing_remainder,
                hybrid_target,
            )
            if hybrid_low_bit_certificate is None:
                hybrid_low_bit_certificate_failures.append(block_record)
            else:
                hybrid_extra_bits = hybrid_low_bit_certificate["extra_bits"]
                hybrid_low_bit_extra_histogram[hybrid_extra_bits] = (
                    hybrid_low_bit_extra_histogram.get(hybrid_extra_bits, 0) + 1
                )
                hybrid_low_bit_record = {
                    **block_record,
                    **hybrid_low_bit_certificate,
                    "target": hybrid_target,
                    "card_target": (4 * landing_card_from_prefix) // 7 + 1,
                    "sqrt_target": 2 * isqrt(2 * landing) + 4,
                }
                if (
                    hybrid_extra_bits > 0
                    and first_hybrid_natural_scale_failure is None
                ):
                    first_hybrid_natural_scale_failure = hybrid_low_bit_record
                if (
                    maximum_hybrid_low_bit_extra_event is None
                    or hybrid_extra_bits
                        > maximum_hybrid_low_bit_extra_event["extra_bits"]
                ):
                    maximum_hybrid_low_bit_extra_event = hybrid_low_bit_record
            event.update({
                "block_identity_holds": block_expected == landing_remainder,
                "middle_threshold_holds": initial_middle_excess >= middle_threshold,
                "linear_buffer_holds": initial_middle_excess >= linear_buffer,
                **block_record,
            })
            if block_expected != landing_remainder:
                block_identity_failures.append(block_record)
            if initial_middle_excess < middle_threshold:
                middle_threshold_failures.append(block_record)
            if initial_middle_excess < linear_buffer:
                linear_buffer_failures.append(block_record)
            if (
                max_pulse_silent_event is None
                or block_record["pulse_silent_prefix_card"]
                    > max_pulse_silent_event["pulse_silent_prefix_card"]
            ):
                max_pulse_silent_event = block_record
            if d == 1993:
                pulse_silent_1993_event = block_record
        events.append(event)
        if slack < 0 and first_falsifier is None:
            reset_charge = (1 << (d + 1)) - landing_remainder
            first_falsifier = {
                **event,
                "reset_charge": reset_charge,
                "falsifier_threshold": (1 << (d + 1)) - lhs,
            }

    minimum = min(events, key=lambda event: int(event["support_amplified_slack"]))
    output = {
        "schema": "erdos257_upper_to_middle_landing_support_audit_v0",
        "rows_checked_through_source": limit,
        "floor_error_checked_through_landing": floor_error_limit,
        "event_count": len(events),
        "candidate": "2^(d-ell) * card(S_(d+1)) <= R_(d+1)",
        "minimum_slack_event": minimum,
        "first_falsifier": first_falsifier,
        "nonlate_events": nonlate,
        "nonzero_boundary_pulse_events": boundary_pulse_nonzero,
        "strict_next_late_block_replay": {
            "event_count": strict_next_late_events,
            "block_identity_failure_count": len(block_identity_failures),
            "first_block_identity_failure": block_identity_failures[:1],
            "middle_threshold_failure_count": len(middle_threshold_failures),
            "first_middle_threshold_failure": middle_threshold_failures[:1],
            "linear_buffer_failure_count": len(linear_buffer_failures),
            "first_linear_buffer_failure": linear_buffer_failures[:1],
            "maximum_pulse_silent_event": max_pulse_silent_event,
            "pulse_silent_1993_event": pulse_silent_1993_event,
            "low_bit_window": {
                "identity": (
                    "R_s = -L_t(S_s) (mod 2^t), where L_t is the low-t-bit "
                    "divisor-incidence expansion of the selected quotient weights, "
                    "equivalently finiteCoeffWindowNumerator(S_s,2s-t,t) mod 2^t"
                ),
                "certificate": (
                    "1 <= L_t <= 2^t-target, equivalently "
                    "(-L_t mod 2^t) >= target"
                ),
                "target": "2^height * landing_card",
                "certificate_failure_count": len(low_bit_certificate_failures),
                "first_certificate_failure": low_bit_certificate_failures[:1],
                "extra_bit_histogram": {
                    str(extra): count
                    for extra, count in sorted(low_bit_extra_histogram.items())
                },
                "maximum_extra_bit_event": maximum_low_bit_extra_event,
                "first_natural_scale_failure": first_natural_scale_failure,
                "claim_ceiling": (
                    "bounded exact replay only; no uniform extra-bit bound or "
                    "all-depth divisor-incidence window theorem is proved"
                ),
            },
            "direct_card_low_bit_window": {
                "identity": "R_s = -L_t(S_s) (mod 2^t)",
                "target": "landing_card",
                "mathematical_role": (
                    "the smallest sufficient landing-sign target, since the "
                    "exact floor error is strictly below landing_card"
                ),
                "certificate_failure_count": len(
                    direct_low_bit_certificate_failures
                ),
                "first_certificate_failure": direct_low_bit_certificate_failures[:1],
                "extra_bit_histogram": {
                    str(extra): count
                    for extra, count in sorted(
                        direct_low_bit_extra_histogram.items()
                    )
                },
                "maximum_extra_bit_event": maximum_direct_low_bit_extra_event,
                "first_natural_scale_failure": first_direct_natural_scale_failure,
                "claim_ceiling": (
                    "bounded exact replay only; no all-depth direct-card "
                    "window theorem is proved"
                ),
            },
            "hybrid_floor_error_low_bit_window": {
                "identity": "R_s = -L_t(S_s) (mod 2^t)",
                "target": (
                    "min(floor(4*landing_card/7)+1, "
                    "2*floor(sqrt(2*landing_row))+4)"
                ),
                "mathematical_role": (
                    "a source-current sufficient sign threshold from the "
                    "Lean-checked per-rank 4/7 floor-error bound and the "
                    "Lean-checked square-root envelope"
                ),
                "certificate_failure_count": len(
                    hybrid_low_bit_certificate_failures
                ),
                "first_certificate_failure": hybrid_low_bit_certificate_failures[:1],
                "extra_bit_histogram": {
                    str(extra): count
                    for extra, count in sorted(
                        hybrid_low_bit_extra_histogram.items()
                    )
                },
                "maximum_extra_bit_event": maximum_hybrid_low_bit_extra_event,
                "first_natural_scale_failure": first_hybrid_natural_scale_failure,
                "claim_ceiling": (
                    "the threshold reduction is proved by existing Lean theorems; "
                    "the low-bit clearance is bounded exact replay only"
                ),
            },
        },
        "canonical_origin_anti_concentration": {
            **canonical_origin_invariant_receipt(),
            "remainder_identity_check_count": canonical_identity_checks,
            "remainder_identity_failure_count": len(canonical_identity_failures),
            "first_remainder_identity_failure": canonical_identity_failures[:1],
            "corridor_equivalence_failure_count": len(
                canonical_corridor_equivalence_failures
            ),
            "first_corridor_equivalence_failure": (
                canonical_corridor_equivalence_failures[:1]
            ),
            "actual_amplified_failure_corridor_hit_count": canonical_corridor_hits,
            "corridor_width": "2^height * landing_card / 4^landing_row",
            "claim_ceiling": (
                "exact identity and bounded replay only; the all-depth "
                "canonical anti-concentration theorem remains open"
            ),
        },
        "landing_remainder_residues": {
            str(modulus): sorted(values) for modulus, values in residues.items()
        },
        "first_events": events[:12],
        "noncanonical_capacity_countermodel":
            noncanonical_capacity_countermodel(),
        "eight_generation_affine_ancestry_countermodel":
            eight_generation_affine_ancestry_countermodel(),
        "finite_pattern_crt_carry_no_go": finite_pattern_crt_carry_no_go(),
    }
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main(
        int(sys.argv[1]) if len(sys.argv) > 1 else 1600,
        int(sys.argv[2]) if len(sys.argv) > 2 else 200,
    )
