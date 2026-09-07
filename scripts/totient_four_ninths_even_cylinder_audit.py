#!/usr/bin/env python3
"""Exact audit for the 4/9 totient Booleanisation candidate.

This script has two independent parts.

* A full-prefix dynamic program checks every corridor word through a small
  horizon.
* A compressed cylinder recurrence checks the same family at much larger
  even horizons, stopping if the common prefix no longer contains every
  proper divisor needed by the following two rows.

All arithmetic is integral.  A successful finite run is evidence, not an
all-depth proof.
"""

from __future__ import annotations

import argparse
from array import array


def target_bit(n: int) -> int:
    """The n-th binary digit of 4/9: the period-6 word 011100."""

    return int(n % 6 in (2, 3, 4))


def raw_coefficient(n: int) -> int:
    """Coefficient of 2^-n in sum phi(k)/(2^(2k)-1)."""

    return n // 2 if n % 2 == 0 else 0


def raw_carry(n: int) -> int:
    """Closed form for K_n = 2 K_(n-1) + t_n - c_n."""

    q, r = divmod(n, 6)
    return (q, 2 * q, q, 2 * q + 1, q + 1, 2 * q + 2)[r]


def full_prefix_dp(horizon: int) -> dict[int, tuple[int, dict[int, int]]]:
    """Return exact even-level endpoint families through ``horizon``."""

    states: dict[int, int] = {0: 0}
    carry = 0
    snapshots: dict[int, tuple[int, dict[int, int]]] = {}
    for n in range(1, horizon + 1):
        carry = 2 * carry + target_bit(n) - raw_coefficient(n)
        assert carry == raw_carry(n)
        children: dict[int, int] = {}
        for defect, word in states.items():
            load = sum(
                (word >> (d - 1)) & 1
                for d in range(1, n)
                if n % d == 0
            )
            pre = 2 * defect + target_bit(n) - load
            for bit in (0, 1):
                child = pre - bit
                if 0 <= child <= carry:
                    child_word = word | (bit << (n - 1))
                    old = children.get(child)
                    assert old is None or old == child_word
                    children[child] = child_word
        states = children
        assert states
        if n % 2 == 0:
            assert set(states) == set(range(carry + 1))
            snapshots[n] = (carry, dict(states))
    return snapshots


def initialize_cylinder(
    snapshots: dict[int, tuple[int, dict[int, int]]], n: int = 6
) -> tuple[int, int, int, int]:
    """Return (common-prefix word, prefix length, suffix length, suffix top)."""

    carry, states = snapshots[n]
    top_word = states[0]
    xor = 0
    for word in states.values():
        xor |= word ^ top_word
    first_variable = (xor & -xor).bit_length() if xor else n + 1
    prefix_length = first_variable - 1
    suffix_length = n - prefix_length
    prefix_word = top_word & ((1 << prefix_length) - 1)
    suffix_top = 0
    for d in range(prefix_length + 1, n + 1):
        suffix_top = 2 * suffix_top + ((top_word >> (d - 1)) & 1)
    assert carry == raw_carry(n)
    return prefix_word, prefix_length, suffix_length, suffix_top


def compressed_audit(horizon: int, crosscheck: int) -> tuple[int, int, int]:
    """Run the exact even-cylinder recurrence.

    Returns ``(final_suffix_width, maximum_suffix_width, rank_of_maximum)``.
    """

    assert horizon >= 6 and horizon % 2 == 0
    snapshots = full_prefix_dp(crosscheck)
    prefix_word, prefix_length, suffix_length, suffix_top = initialize_cylinder(
        snapshots
    )

    fixed = bytearray(horizon + 3)
    divisor_load = array("H", [0]) * (horizon + 3)

    def fix_rank(d: int, bit: int) -> None:
        fixed[d] = bit
        if bit:
            for multiple in range(2 * d, horizon + 3, d):
                divisor_load[multiple] += 1

    for d in range(1, prefix_length + 1):
        fix_rank(d, (prefix_word >> (d - 1)) & 1)

    maximum = (suffix_length, 6)
    n = 6
    while n < horizon:
        carry = raw_carry(n)
        t1, t2 = target_bit(n + 1), target_bit(n + 2)
        g1, g2 = divisor_load[n + 1], divisor_load[n + 2]
        c1, c2 = t1 - g1, t2 - g2
        shift = 2 * c1 + c2

        odd_carry = 2 * carry + t1
        next_carry = 2 * odd_carry + t2 - (n + 2) // 2
        assert next_carry == raw_carry(n + 2)

        # The unique parent/base-4 digit producing new endpoint zero.
        parent = max(0, (-shift + 3) // 4)
        digit = 4 * parent + shift
        assert 0 <= digit <= 3
        odd_defect = 2 * parent + c1 - digit // 2
        assert 0 <= odd_defect <= odd_carry

        next_top = 4 * suffix_top + shift
        next_width = suffix_length + 2
        assert 0 <= next_top - next_carry <= next_top < 1 << next_width

        # Every endpoint q is encoded by the binary interval
        # [next_top-next_carry, next_top].  Strip its common leading word.
        difference = next_top ^ (next_top - next_carry)
        common = next_width - (difference.bit_length() if difference else 0)
        for i in range(common):
            bit = (next_top >> (next_width - 1 - i)) & 1
            prefix_length += 1
            fix_rank(prefix_length, bit)
        next_width -= common
        suffix_length = next_width
        suffix_top = next_top & ((1 << suffix_length) - 1 if suffix_length else 0)
        n += 2

        # These fixed bits make the loads at n+1 and n+2 state-independent.
        # Failure is the precise first midpoint-seam obstruction.
        assert prefix_length >= n // 2 + 1, (
            "first midpoint seam",
            n,
            prefix_length,
            suffix_length,
        )

        if suffix_length > maximum[0]:
            maximum = (suffix_length, n)

        if n <= crosscheck:
            expected_carry, expected = snapshots[n]
            assert expected_carry == next_carry
            assert set(expected) == set(range(next_carry + 1))
            for defect, word in expected.items():
                for d in range(1, prefix_length + 1):
                    assert ((word >> (d - 1)) & 1) == fixed[d]
                encoded = 0
                for d in range(prefix_length + 1, n + 1):
                    encoded = 2 * encoded + ((word >> (d - 1)) & 1)
                assert encoded == suffix_top - defect

    return suffix_length, maximum[0], maximum[1]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--horizon", type=int, default=200_000)
    parser.add_argument("--crosscheck", type=int, default=300)
    args = parser.parse_args()
    final_width, maximum_width, maximum_rank = compressed_audit(
        args.horizon, args.crosscheck
    )
    print(
        "PASS: exact 4/9 even-cylinder audit; "
        f"horizon={args.horizon}, final_suffix_width={final_width}, "
        f"max_suffix_width={maximum_width} at rank {maximum_rank}, "
        f"full-prefix crosscheck={args.crosscheck}"
    )


if __name__ == "__main__":
    main()
