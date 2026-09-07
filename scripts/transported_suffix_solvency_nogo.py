#!/usr/bin/env python3
"""Exact counterexample to hereditary solvency of a transported -3 suffix."""

from fractions import Fraction


def weight(rank: int) -> Fraction:
    return Fraction(1, (1 << rank) - 1)


def anchored_unit(height: int) -> Fraction:
    return Fraction(1, 3 * ((1 << height) - 1))


def check_counterexample() -> dict[str, object]:
    height = 15
    window = 4
    suffix_coefficient = (1 << window) - 3
    assert suffix_coefficient == 13
    assert suffix_coefficient == (1 << 0) + (1 << 2) + (1 << 3)

    # Bits 2 and 3 form the top adjacent pair.  Bit 0 is its forced external
    # complement in the transported -3 suffix.
    pair = 12 * anchored_unit(height)
    external = anchored_unit(height)
    extracted_ranks = [17, 19, 21, 23, 25]
    extracted = sum((weight(rank) for rank in extracted_ranks), Fraction())
    external_remainder = external - extracted
    assert external_remainder > 0

    residual = pair + external_remainder
    lower = 2 * weight(14)
    upper = weight(13)
    assert lower < residual < upper

    return {
        "transported_suffix": "2^4-3 = 13 = binary 1101",
        "anchored_height": height,
        "top_adjacent_pair_exponents": [2, 3],
        "pair_front_ranks": [14, 15],
        "forced_external_exponent": 0,
        "future_boolean_extraction": extracted_ranks,
        "external_remainder": str(external_remainder),
        "dangerous_residual": str(residual),
        "margin_above_2w14": str(residual - lower),
        "margin_below_w13": str(upper - residual),
        "hereditary_suffix_solvency": False,
    }


def main() -> None:
    print(check_counterexample())


if __name__ == "__main__":
    main()
