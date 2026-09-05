# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact finite parameter certificate for RationalBaseRegion.md (stdlib only)."""
from fractions import Fraction as Q
import json

INTERVALS = [
    (Q(1, 14), Q(1, 12)), (Q(1, 7), Q(1, 6)),
    (Q(3, 14), Q(1, 4)), (Q(2, 7), Q(1, 3)),
    (Q(5, 14), Q(2, 5)), (Q(3, 7), Q(7, 15)),
    (Q(1, 2), Q(8, 15)), (Q(4, 7), Q(3, 5)),
    (Q(9, 14), Q(2, 3)), (Q(5, 7), Q(11, 15)),
    (Q(11, 14), Q(4, 5)), (Q(6, 7), Q(13, 15)),
    (Q(13, 14), Q(14, 15)),
]


def floor(x):
    return x.numerator // x.denominator


def omega(x):
    return max(0, floor(14*x)+floor(13*x)-floor(12*x)-floor(15*x),
               2*floor(14*x)-floor(13*x)-floor(15*x))


def atan_bounds(x, terms=20):
    # Even alternating truncation is a lower bound, next term an upper bound.
    assert 0 < x < 1 and terms % 2 == 0
    lower = sum((-1)**j * x**(2*j+1) / (2*j+1) for j in range(terms))
    return lower, lower + x**(2*terms+1)/(2*terms+1)


def main():
    cuts = sorted({Q(j, k) for k in (12, 13, 14, 15) for j in range(k+1)})
    # All floors and the claimed indicator are right-continuous and constant
    # on these half-open cells. Checking their left endpoints proves equality.
    for x in cuts[:-1]:
        assert omega(x) == sum(u <= x < v for u, v in INTERVALS)
    assert omega(Q(1)) == omega(Q(0))
    lo5, _ = atan_bounds(Q(1, 5))
    _, hi239 = atan_bounds(Q(1, 239))
    pi_lower = 16*lo5 - 4*hi239  # Machin's identity.
    assert pi_lower > Q(157, 50)
    j_lower = sum(1/u**2 - 1/v**2 for u, v in INTERVALS)
    assert j_lower < 225
    c0_lower = 266 - 3*(225-j_lower)/Q(157, 50)**2
    margin = c0_lower - Q(81, 200)*Q(1091, 2)
    assert margin > 0
    assert 4**200 < 31**81
    # 31/4 is outside the earlier 1/2-1/pi^2 region: log4/log31>2/5,
    # while pi^2<10 makes the earlier cutoff <2/5.
    _, hi5 = atan_bounds(Q(1, 5))
    lo239, _ = atan_bounds(Q(1, 239))
    pi_upper = 16*hi5 - 4*lo239
    assert pi_upper**2 < 10 and 31**2 < 4**5
    print(json.dumps({
        "status": "pass", "evidence_class": "exact_finite_parameter_certificate",
        "floor_cells": len(cuts)-1, "J_lower": str(j_lower),
        "C0_lower": str(c0_lower), "C0_minus_81_200_C1_lower": str(margin),
        "region_membership": "log(4)/log(31) < 81/200 < C0/C1",
        "earlier_region": "31/4 excluded",
        "boundary": "Does not check polynomial integrality or the analytic irrationality proof."
    }, indent=2))


if __name__ == "__main__":
    main()
