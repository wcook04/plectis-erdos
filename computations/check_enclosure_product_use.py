#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact arithmetic for docs/reading-edition/enclosure-product-use.md.

This checks ordinary algebra, not a Lean replay. The tail double sum and
polynomial convolution are independent checks of the recursive budget.
"""
from fractions import Fraction as Q
from itertools import product
import json

T = Q(3, 10)


def require(condition, message):
    """Keep checks active under python -O, too."""
    if not condition:
        raise AssertionError(message)


def bsum(bounds):
    return sum((Q(b) * T**i for i, b in enumerate(bounds)), Q(0))


def hb(beta, gamma, n):
    """The source's tail recurrence, evaluated with exact rationals."""
    if not beta:
        return Q(0)
    if n == 0:
        return bsum(beta) * bsum(gamma)
    return Q(beta[0]) * bsum(gamma[n:]) + hb(beta[1:], gamma, n - 1)


def tail_pairs(beta, gamma, n):
    return sum((Q(b) * Q(c) * T**(i + j - n)
                for i, b in enumerate(beta) for j, c in enumerate(gamma)
                if i + j >= n), Q(0))


def multiply(p, q):
    result = [Q(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            result[i + j] += a * b
    return result


def check():
    beta, gamma = [Q(0), Q(0), Q(5, 4)], [Q(0), Q(0), Q(0), Q(2)]
    r1, r2 = Q(1, 20), Q(1, 10)
    n1, n2, v1, v2, n = 4, 1, 2, 3, 3
    require(v1 <= n1 and n <= v1 + n2 and n <= v2 + n1, "order premises")
    b1, b2 = bsum(beta[v1:]), bsum(gamma[v2:])
    tail = hb(beta, gamma, n)
    first_error = (b1 + r1 * T**(n1-v1)) * r2 * T**(v1+n2-n)
    second_error = b2 * r1 * T**(v2+n1-n)
    remainder = tail + first_error + second_error
    require((tail, first_error, second_error) ==
            (Q(9, 40), Q(2509, 20000), Q(81, 100000)), "budget terms")
    require(remainder == Q(17563, 50000), "sufficient remainder")

    # Both supplied error bounds are attained for every positive t.
    f, g = beta + [Q(0), r1], [Q(0), r2, Q(0), Q(2)]
    fg = multiply(f, g)
    require(fg[:n] == [0, 0, 0], "zero truncated product")
    quotient = fg[n:]
    require(quotient == [Q(1, 8), 0, Q(501, 200), 0, Q(1, 10)], "witness product")
    # Nonnegative coefficients imply monotonicity throughout 0 < t <= T.
    require(all(c >= 0 for c in quotient), "endpoint maximum argument")
    maximum = sum((c * T**i for i, c in enumerate(quotient)), Q(0))
    require(maximum == remainder > Q(7, 20), "compatible counterexample")
    exact_pair = multiply(beta, gamma)
    require(exact_pair[:n] == [0, 0, 0], "exact pair truncated product")
    exact_maximum = sum((c * T**i for i, c in enumerate(exact_pair[n:])), Q(0))
    require(exact_maximum == Q(9, 40) < Q(7, 20), "compatible successful pair")

    # Exhaustive finite cross-check of the recurrence against a separate sum.
    # Signed inputs test the algebraic identity, not enclosure hypotheses.
    lists = [[]] + [list(x) for length in range(1, 4)
                    for x in product([Q(-1), Q(0), Q(3, 2)], repeat=length)]
    cases = 0
    for b, c in product(lists, repeat=2):
        for order in range(7):
            require(hb(b, c, order) == tail_pairs(b, c, order) == hb(c, b, order),
                    f"tail recurrence mismatch: {b}, {c}, {order}")
            cases += 1
    return {
        "status": "PASS",
        "sufficient_remainder": str(remainder),
        "requested_remainder": "7/20",
        "compatible_witness_excess": str(remainder - Q(7, 20)),
        "exact_polynomial_pair_remainder": str(exact_maximum),
        "recurrence_oracle_cases": cases,
        "interval_argument": "nonnegative quotient coefficients; maximum at t=3/10",
        "evidence": "exact rational arithmetic and ordinary algebra; no Lean replay",
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
