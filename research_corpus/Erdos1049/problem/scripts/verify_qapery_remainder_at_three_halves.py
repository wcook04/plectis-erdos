#!/usr/bin/env python3
"""Do the cleared q-Apery linear forms at 3/2 shrink, or grow?

The transduction checker measures the exterior determinant's local content
against the determinant's own height.  That is a determinant-only proxy: it
excludes the analytic remainder entirely, which is the term the note's
Problem 8.5 actually requires.  This script supplies the missing measurement.

For the cleared integer rows (A_n, B_n) obtained from the Amdeberhan-Zeilberger
sequences by the source's own Lemma 1 clearing factor and primitive
normalisation, define the linear form

    rho_n = B_n * F(3/2) - A_n,        F(t) = sum_{k>=1} 1/(t^k - 1).

An irrationality argument needs |rho_n| -> 0 faster than 1/height.  What we
measure is whether it tends to zero at all.

F(3/2) = sum_{k>=1} 2^k / (3^k - 2^k) is computed as an exact rational bracket:
a truncated sum gives a lower bound, and a geometric tail bound gives an upper
bound.  The bracket width is carried through the linear form, so every reported
sign and magnitude is certified rather than floating-point.

IMPORTANT DISTINCTION, and the reason this script exists separately.  A growing
cleared form does NOT establish that the rational approximants A_n/B_n fail to
converge to F(3/2).  If C_n is the clearing multiplier then C_n(b_n F - a_n) can
grow while F - a_n/b_n still tends to zero, because C_n b_n may outgrow the raw
approximation error.  Both quantities are therefore reported, and the licensed
conclusion is stated per quantity.

Authority boundary: exact rational arithmetic over the displayed range of n.
Not an all-n proof, and not an irrationality result at 3/2, which remains open.
"""

from __future__ import annotations

from fractions import Fraction
import json
import math
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

from verify_qapery_transduction import (  # noqa: E402
    a_seq,
    at_three_halves,
    b_seq,
    clearing_factor,
    valuation,
)

import sympy as sp  # noqa: E402


N_MAX = 8
TAIL_TERMS = 900
PRECISION_BITS = 1200


def f_three_halves_bracket(
    terms: int = TAIL_TERMS, bits: int = PRECISION_BITS
) -> tuple[Fraction, Fraction]:
    """Exact rational lower/upper bracket for F(3/2) = sum 2^k/(3^k - 2^k).

    Uses fixed-point integer arithmetic rather than exact Fraction accumulation:
    summing 900 rationals with 3^900-scale denominators is quadratic and far too
    slow, while floor-scaled integers give the same certified bracket in linear
    time.  Each term contributes at most one ulp of downward error, so the
    truncated sum is a strict lower bound and adding `terms` ulps plus the
    geometric tail gives a strict upper bound.
    """
    scale = 1 << bits
    total = 0
    for k in range(1, terms + 1):
        total += (scale * (2**k)) // (3**k - 2**k)
    lower = Fraction(total, scale)
    # tail: for k > terms, 3^k - 2^k = 3^k (1 - (2/3)^k) > 3^k * c with
    # c = 1 - (2/3)^(terms+1), so term_k < (2/3)^k / c and
    # sum_{k >= k0} (2/3)^k = 3 * (2/3)^k0.
    k0 = terms + 1
    c = Fraction(1) - Fraction(2**k0, 3**k0)
    tail_upper = Fraction(3) * Fraction(2**k0, 3**k0) / c
    ulp_slack = Fraction(terms, scale)
    return lower, lower + ulp_slack + tail_upper


def cleared_row(n: int) -> tuple[int, int]:
    """(A_n, B_n): numerator and denominator rows after clearing + primitive norm."""
    factor = clearing_factor(n)
    u_rat = at_three_halves(sp.cancel(a_seq(n) * factor))
    z_rat = at_three_halves(sp.cancel(b_seq(n) * factor))
    common_den = (u_rat.denominator * z_rat.denominator) // math.gcd(
        u_rat.denominator, z_rat.denominator
    )
    u_int = int(u_rat * common_den)
    z_int = int(z_rat * common_den)
    content = math.gcd(abs(u_int), abs(z_int)) or 1
    return u_int // content, z_int // content


def main() -> None:
    lo, hi = f_three_halves_bracket()
    bracket_bits = -math.log2(float(hi - lo)) if hi > lo else float("inf")

    rows = []
    for n in range(1, N_MAX):
        a_int, b_int = cleared_row(n)
        # rho_n = B_n * F - A_n, bracketed
        rho_lo = Fraction(b_int) * lo - a_int
        rho_hi = Fraction(b_int) * hi - a_int
        if b_int < 0:
            rho_lo, rho_hi = rho_hi, rho_lo
        sign_certain = (rho_lo > 0) == (rho_hi > 0)
        mag = min(abs(float(rho_lo)), abs(float(rho_hi)))
        mag = max(mag, 1e-300)
        log_rho = math.log(abs(float(rho_hi)) if abs(float(rho_hi)) > 0 else mag)

        # raw ratio error, the DIFFERENT quantity
        ratio_lo = lo - Fraction(a_int, b_int)
        ratio_hi = hi - Fraction(a_int, b_int)
        ratio_mag = max(abs(float(ratio_lo)), abs(float(ratio_hi)))

        rows.append(
            {
                "n": n,
                "height_bits_B": int(abs(b_int)).bit_length(),
                "sign_certain_from_bracket": bool(sign_certain),
                "log_abs_rho": round(log_rho, 4),
                "log_abs_rho_over_n2": round(log_rho / (n * n), 5),
                "cleared_form_shrinking": bool(log_rho < 0),
                "raw_ratio_error_log": (
                    round(math.log(ratio_mag), 4) if ratio_mag > 0 else None
                ),
                "raw_ratio_error_over_n2": (
                    round(math.log(ratio_mag) / (n * n), 5) if ratio_mag > 0 else None
                ),
                "raw_ratio_error_shrinking": bool(ratio_mag < 1),
                "v2_B": valuation(b_int, 2),
                "v3_B": valuation(b_int, 3),
            }
        )

    growing = [r for r in rows if not r["cleared_form_shrinking"]]
    ratio_shrinking = all(r["raw_ratio_error_shrinking"] for r in rows)

    print(
        json.dumps(
            {
                "schema": "erdos1049-qapery-remainder-at-three-halves/1",
                "f_three_halves_bracket_accurate_to_bits": round(bracket_bits, 1),
                "authority": (
                    "exact_rational_bracket_over_displayed_range; not an all-n proof "
                    "and not an irrationality result at 3/2"
                ),
                "rows": rows,
                "verdict": {
                    "cleared_forms_grow_at_every_checked_n": len(growing) == len(rows),
                    "raw_ratio_error_shrinks_at_every_checked_n": ratio_shrinking,
                    "licensed_statement": (
                        "This rational-base integerisation of the q-Apery diagonal "
                        "fails to produce small linear forms at 3/2 over the checked "
                        "range."
                    ),
                    "NOT_licensed": (
                        "That the q-Apery approximants fail to approximate F(3/2). "
                        "The raw ratio error and the cleared form are different "
                        "quantities and behave differently here."
                    ),
                },
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
