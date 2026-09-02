"""Exact {2,3,5} running-LCM engine for Erdos #269 (standalone, integer-only).

Rebuilt independently of the flat 257-era scripts so the general probe layer has
one importable, problem-owned source engine.  Every quantity here is an exact
integer; no floating point enters the certificate path.

Objects
-------
block a (a >= 1) covers the dyadic shell [2^a, 2^(a+1)).
  b_a  : radix  = H(2^(a+1)) / H(2^a)  in {2, 6, 10, 30}
  d_a  : ordered source digit of the shell
  J_a  : ending jump index (count of prime powers below 2^(a+1))

window (a, L): base B = prod b, forcing F = sum d * suffix-radix-product,
  residue r(q) = least positive residue of (-q F) mod B,
  cap C(q)    = q * (J^2 + 10 J + 27) / 9,
  escape      = r(q) > C(q)   (and B > C(q) for the consumer to fire).
"""

from __future__ import annotations

from bisect import bisect_left, bisect_right

PRIMES = (2, 3, 5)
OTHERS = {2: (3, 5), 3: (2, 5), 5: (2, 3)}


def pair_count_lt(target: int, xs: list[int], ys: list[int]) -> int:
    """Count pairs (x, y) from increasing power lists with x*y < target."""
    j = len(ys) - 1
    while j >= 0 and ys[j] >= target:
        j -= 1
    answer = 0
    for x in xs:
        if x >= target or j < 0:
            break
        while j >= 0 and x * ys[j] >= target:
            j -= 1
        if j < 0:
            break
        answer += j + 1
    return answer


def build_dyadic_blocks(max_a: int) -> list[tuple[int, int, int]]:
    """Return (block_base, block_digit, ending_jump_index) for 1 <= a <= max_a."""
    if max_a < 1:
        raise ValueError("max_a must be positive")
    limit = 1 << (max_a + 1)
    powers: dict[int, list[int]] = {}
    for prime in PRIMES:
        values = [1]
        while values[-1] * prime <= limit:
            values.append(values[-1] * prime)
        powers[prime] = values

    block_counts: dict[int, list[int]] = {}
    cumulative_counts: dict[int, list[int]] = {}
    for prime in PRIMES:
        other_left, other_right = OTHERS[prime]
        widths = [0] * len(powers[prime])
        cumulative = [0] * len(powers[prime])
        for exponent in range(1, len(powers[prime])):
            widths[exponent] = pair_count_lt(
                powers[prime][exponent], powers[other_left], powers[other_right]
            )
            cumulative[exponent] = cumulative[exponent - 1] + widths[exponent]
        block_counts[prime] = widths
        cumulative_counts[prime] = cumulative

    jumps: list[tuple[int, int, int]] = []
    for prime in PRIMES:
        for exponent, value in enumerate(powers[prime][1:], start=1):
            if value < limit:
                jumps.append((value, prime, exponent))
    jumps.sort()
    jump_values = [value for value, _, _ in jumps]

    blocks: list[tuple[int, int, int]] = []
    for a in range(1, max_a + 1):
        lower = 1 << a
        upper = 1 << (a + 1)
        left = bisect_right(jump_values, lower)
        right = bisect_left(jump_values, upper)
        internal = jumps[left:right]
        channels = [prime for _, prime, _ in internal]
        if len(channels) > 2 or len(set(channels)) != len(channels):
            raise AssertionError(("dyadic internal-channel uniqueness", a, internal))
        block_base = 2
        for _, prime, _ in internal:
            block_base *= prime
        if block_base not in (2, 6, 10, 30):
            raise AssertionError(("unexpected block base", a, block_base))
        block_digit = block_counts[2][a + 1]
        suffix_base = 1
        for _, prime, exponent in reversed(internal):
            strip = cumulative_counts[prime][exponent] - cumulative_counts[2][a]
            block_digit += (prime - 1) * suffix_base * strip
            suffix_base *= prime
        blocks.append((block_base, block_digit, right))
    return blocks


def short_bound(denominator: int, jump_index: int) -> int:
    return denominator * (jump_index * jump_index + 10 * jump_index + 27) // 9


def least_positive_residue(value: int, modulus: int) -> int:
    residue = value % modulus
    return modulus if residue == 0 else residue


def escape_depth(
    blocks: list[tuple[int, int, int]],
    denominator: int,
    start: int,
    max_length: int,
) -> dict[str, int | bool | None]:
    """Smallest window length whose canonical residue escapes the analytic cap.

    Returns the exact certificate.  `depth is None` means no escape was found
    inside `max_length`; that is a search limit, never a proof of trapping.
    """
    base, forcing = 1, 0
    index = start - 1
    for length in range(1, max_length + 1):
        if index >= len(blocks):
            return {"depth": None, "reason": "block_range_exhausted", "length": length}
        block_base, block_digit, ending = blocks[index]
        base = base * block_base
        forcing = block_base * forcing + block_digit
        index += 1
        cap = short_bound(denominator, ending)
        residue = least_positive_residue(-denominator * forcing, base)
        if base > cap and residue > cap:
            return {
                "depth": length,
                "ending_jump_index": ending,
                "window_base_bits": base.bit_length(),
                "cap": cap,
                "residue": residue,
                "escaped": True,
            }
    return {"depth": None, "reason": "max_length_reached", "escaped": False}
