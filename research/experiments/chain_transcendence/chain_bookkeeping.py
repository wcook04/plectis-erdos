#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact bookkeeping for the Subspace Theorem proof on divisibility chains.

For coprime integers a > b >= 1 put rho = b/a and, for an infinite chain
n_1 | n_2 | ... of distinct positive integers,

    X = sum_j 1/((a/b)^(n_j) - 1) = sum_j rho^(n_j) / (1 - rho^(n_j)).

The synthesis paper proves that X is transcendental.  Fix an index j, write
N = n_j, M = n_(j+1) = r N, and choose K >= 1.  The proof applies the p-adic
Subspace Theorem to the integer vector

    Y = (a^(N+(K-1)M), a^((K-1)M) b^N, a^((K-1)M) P_j, u_1, v_1, ..., u_(K-1), v_(K-1)),
    u_k = a^(N+(K-1-k)M) b^(kM),   v_k = a^((K-1-k)M) b^(N+kM),

where P_j = (a^N - b^N) S_j and S_j is the j-th partial sum, together with the
linear form

    L(Y) = x Y_1 - x Y_2 - Y_3 - sum_k c_k (u_k - v_k),   c_k = #{l > j : n_l | kM}.

This script checks the finite bookkeeping of that argument in exact rational
arithmetic:

  * P_j is a positive integer, equal to sum_{m <= N} #{i <= j : n_i | m} a^(N-m) b^m;
  * every coordinate except Y_3 is an S-unit for the primes dividing ab;
  * with x replaced by a truncation of X whose omitted terms cannot divide
    (K-1)M, the identity L(Y) = a^(N+(K-1)M) (1 - rho^N) E_j holds exactly,
    where E_j is the part of the tail with exponents >= KM;
  * 0 < E_j <= (K/(1-rho) + rho/(1-rho)^2) rho^(KM), and c_k <= 1 + log2 k;
  * the S-adic product |L(Y)| * prod_{p | ab} |Y_3|_p, measured against
    ||Y|| = max |Y_i|, has the logarithmic exponent predicted in the paper,
    ((1 - K r) + K r theta) / (1 + (K - 1) r) with theta = log b / log a.

It also records the one-term Liouville exponent log(D_j T_j) / N, which is
positive at base 4/3 with ratio 2, and the rational Millin-type identity
sum_j z^(2^j) / (1 - z^(2^(j+1))) = z / (1 - z), where the first tail
exponent equals the denominator exponent and the argument does not apply.

None of this is a proof.  The theorem rests on the Subspace Theorem and the
argument in the paper; these are finite checks of its formulas.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
from fractions import Fraction
from typing import Iterable

# Chains and exact partial sums


def chain_from_ratios(first: int, ratios: Iterable[int]) -> list[int]:
    """Return first, first*r_1, first*r_1*r_2, ... (every ratio must be >= 2)."""
    ns = [first]
    for r in ratios:
        if r < 2:
            raise ValueError("a strictly increasing divisibility chain has ratios >= 2")
        ns.append(ns[-1] * r)
    return ns


def ratio_word(kind: str, length: int) -> list[int]:
    """Deterministic words over {2, 3} used as ratio sequences."""
    if kind == "doubling":
        return [2] * length
    if kind == "squares":
        # ratio 3 at the square indices 1, 4, 9, ... and 2 elsewhere
        return [3 if math.isqrt(i) ** 2 == i else 2 for i in range(1, length + 1)]
    if kind == "fibonacci":
        u, v = "2", "23"
        while len(v) < length:
            u, v = v, v + u
        return [int(ch) for ch in v[:length]]
    if kind == "thue_morse":
        return [2 + bin(i).count("1") % 2 for i in range(length)]
    if kind == "factorial":
        return list(range(2, length + 2))
    raise ValueError(f"unknown ratio word {kind!r}")


def term(a: int, b: int, n: int) -> Fraction:
    """1/((a/b)^n - 1) = b^n / (a^n - b^n)."""
    return Fraction(b ** n, a ** n - b ** n)


def partial_sum(a: int, b: int, ns: list[int], count: int) -> Fraction:
    return sum((term(a, b, n) for n in ns[:count]), Fraction(0))


def cleared_partial_sum(a: int, b: int, ns: list[int], j: int) -> int:
    """P_j = (a^N - b^N) S_j with N = n_j (j is 1-based); asserts integrality."""
    n_j = ns[j - 1]
    value = (a ** n_j - b ** n_j) * partial_sum(a, b, ns, j)
    if value.denominator != 1:
        raise AssertionError(f"P_{j} is not an integer")
    return value.numerator


def divisor_count_form(a: int, b: int, ns: list[int], j: int) -> int:
    """sum_{m <= N} #{i <= j : n_i | m} a^(N-m) b^m, the expanded form of P_j."""
    n_j = ns[j - 1]
    head = ns[:j]
    return sum(
        sum(1 for n in head if m % n == 0) * a ** (n_j - m) * b ** m
        for m in range(1, n_j + 1)
    )


# The Subspace vector, the form L and the tail


def prime_factors(n: int) -> list[int]:
    out, d = [], 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def valuation(n: int, p: int) -> int:
    n, v = abs(n), 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def is_s_unit(n: int, primes: list[int]) -> bool:
    n = abs(n)
    for p in primes:
        while n % p == 0:
            n //= p
    return n == 1


def minimal_k(a: int, b: int, r: int) -> int:
    """Least K >= 1 with K r log(a/b) > log a (exact integer comparison)."""
    k = 1
    # K r log(a/b) > log a  <=>  (a/b)^(K r) > a  <=>  a^(K r) > a b^(K r)
    while not a ** (k * r) > a * b ** (k * r):
        k += 1
    return k


def truncation_index(ns: list[int], j: int, k: int) -> int:
    """Least J >= j+1 (1-based) such that n_(J+1) > (K-1) M, where M = n_(j+1).

    Chain terms beyond J cannot divide any kM with k < K, so the coefficients
    c_k computed from the truncated chain are the coefficients of the full chain.
    """
    m = ns[j]
    big = j + 1
    while big < len(ns) and ns[big] <= max(k - 1, 1) * m:
        big += 1
    if big >= len(ns):
        raise ValueError("chain too short for the requested truncation")
    return big


def tail_coefficients(ns: list[int], j: int, k: int, big: int) -> list[int]:
    """c_k = #{l : j < l <= J, n_l | k M} for k = 1, ..., K-1 (1-based j, J)."""
    m = ns[j]
    return [sum(1 for n in ns[j:big] if (kk * m) % n == 0) for kk in range(1, k)]


def subspace_vector(a: int, b: int, ns: list[int], j: int, k: int) -> list[int]:
    n_j, m = ns[j - 1], ns[j]
    y1 = a ** (n_j + (k - 1) * m)
    y2 = a ** ((k - 1) * m) * b ** n_j
    y3 = a ** ((k - 1) * m) * cleared_partial_sum(a, b, ns, j)
    coords = [y1, y2, y3]
    for kk in range(1, k):
        coords.append(a ** (n_j + (k - 1 - kk) * m) * b ** (kk * m))   # u_k
        coords.append(a ** ((k - 1 - kk) * m) * b ** (n_j + kk * m))   # v_k
    return coords


def tail_remainder(a: int, b: int, ns: list[int], j: int, big: int, coeffs: list[int]) -> Fraction:
    """E_j: the truncated tail minus the K-1 monomials c_k rho^(kM) moved into Y."""
    rho = Fraction(b, a)
    m = ns[j]
    tail = partial_sum(a, b, ns, big) - partial_sum(a, b, ns, j)
    return tail - sum((c * rho ** ((kk + 1) * m) for kk, c in enumerate(coeffs)), Fraction(0))


def tail_upper_bound(a: int, b: int, m: int, k: int) -> Fraction:
    """(K/(1-rho) + rho/(1-rho)^2) rho^(KM), from c(kM) <= 1 + log2 k <= k."""
    rho = Fraction(b, a)
    return (Fraction(k) / (1 - rho) + rho / (1 - rho) ** 2) * rho ** (k * m)


def log_abs(value: Fraction) -> float:
    """Natural logarithm of |value|, or -inf at zero."""
    if value == 0:
        return float("-inf")
    return math.log(abs(value.numerator)) - math.log(value.denominator)


def linear_form(x: Fraction, coords: list[int], coeffs: list[int]) -> Fraction:
    y1, y2, y3 = coords[:3]
    value = x * y1 - x * y2 - y3
    for idx, c in enumerate(coeffs):
        u, v = coords[3 + 2 * idx], coords[4 + 2 * idx]
        value -= c * (u - v)
    return value


def analyse_row(a: int, b: int, ns: list[int], j: int, k: int) -> dict:
    """Check every finite formula at index j (1-based) with parameter K."""
    rho = Fraction(b, a)
    n_j, m = ns[j - 1], ns[j]
    r = m // n_j
    big = truncation_index(ns, j, k)
    coeffs = tail_coefficients(ns, j, k, big)
    primes = sorted(set(prime_factors(a) + prime_factors(b)))

    p_j = cleared_partial_sum(a, b, ns, j)
    coords = subspace_vector(a, b, ns, j, k)
    x_trunc = partial_sum(a, b, ns, big)
    s_j = partial_sum(a, b, ns, j)
    e_j = tail_remainder(a, b, ns, j, big, coeffs)
    h0 = coords[0]
    lhs = linear_form(x_trunc, coords, coeffs)
    rhs = h0 * (1 - rho ** n_j) * e_j
    tail_bound = tail_upper_bound(a, b, m, k)

    log_l = log_abs(lhs)
    log_p_adic = -sum(valuation(coords[2], p) * math.log(p) for p in primes)
    log_height = math.log(max(abs(c) for c in coords))
    theta = math.log(b) / math.log(a) if b > 1 else 0.0
    predicted = ((1 - k * r) + k * r * theta) / (1 + (k - 1) * r)
    liouville = (math.log(a ** n_j - b ** n_j) + log_abs(x_trunc - s_j)) / n_j
    exponents = [0, 1] + [kk * r for kk in range(1, k)] + [1 + kk * r for kk in range(1, k)]
    return {
        "j": j,
        "N": n_j,
        "ratio": r,
        "K": k,
        "truncation_J": big,
        "coefficients": coeffs,
        "coefficient_bound_holds": all(c <= 1 + math.log2(kk) for kk, c in enumerate(coeffs, start=1)),
        "P_j_integer_matches_divisor_form": p_j == divisor_count_form(a, b, ns, j),
        "identity_exact": lhs == rhs,
        "tail_positive_and_bounded": 0 < e_j <= tail_bound,
        "s_unit_coordinates": all(is_s_unit(c, primes) for i, c in enumerate(coords) if i != 2),
        "exponent_condition": a ** (k * r) > a * b ** (k * r),
        "monomials_distinct_below_Kr": len(set(exponents)) == len(exponents) and max(exponents) < k * r,
        "log_product_over_log_height": round((log_l + log_p_adic) / log_height, 5),
        "predicted_limit": round(predicted, 5),
        "liouville_exponent_per_N": round(liouville, 4),
    }


def analyse_chain(a: int, b: int, word: str, rows: int, k: int | None = None) -> dict:
    ratios = ratio_word(word, rows + 40)
    ns = chain_from_ratios(1, ratios)
    out = []
    for j in range(1, rows + 1):
        r = ns[j] // ns[j - 1]
        kk = k if k is not None else minimal_k(a, b, r)
        out.append(analyse_row(a, b, ns, j, kk))
    return {"a": a, "b": b, "word": word, "rows": out}


# The rational boundary example


def millin_boundary(a: int, b: int, depth: int, k: int = 3) -> dict:
    """sum_{j <= J} z^(2^j)/(1 - z^(2^(j+1))) = z/(1-z) - z^(2^(J+1))/(1 - z^(2^(J+1))).

    Here the partial-sum denominator exponent N = 2^(J+1) equals the first
    tail exponent M, so the would-be coordinates a^((K-1)M) b^N and
    a^(N+(K-2)M) b^M coincide and every vector lies in a fixed hyperplane.
    """
    z = Fraction(b, a)
    ok = True
    coincide = True
    for big in range(depth):
        finite = sum((z ** (2 ** i) / (1 - z ** (2 ** (i + 1))) for i in range(big + 1)), Fraction(0))
        w = z ** (2 ** (big + 1))
        ok &= finite == z / (1 - z) - w / (1 - w)
        n_exp = m_exp = 2 ** (big + 1)
        coincide &= a ** ((k - 1) * m_exp) * b ** n_exp == a ** (n_exp + (k - 2) * m_exp) * b ** m_exp
    return {"a": a, "b": b, "depth": depth, "telescoping_identity_exact": ok,
            "second_and_fourth_coordinates_coincide": coincide,
            "value": str(z / (1 - z))}


# Command line

DEFAULT_CASES = (
    (4, 3, "squares", 9),
    (4, 3, "fibonacci", 8),
    (4, 3, "thue_morse", 8),
    (4, 3, "doubling", 9),
    (5, 4, "fibonacci", 7),
    (3, 2, "squares", 8),
    (9, 7, "thue_morse", 6),
    (2, 1, "squares", 8),
    (4, 3, "factorial", 5),
)


def run_default() -> dict:
    cases = [analyse_chain(a, b, word, rows) for a, b, word, rows in DEFAULT_CASES]
    boundary = millin_boundary(4, 3, 8)
    checks = [
        key for key in (
            "coefficient_bound_holds", "P_j_integer_matches_divisor_form",
            "identity_exact", "tail_positive_and_bounded", "s_unit_coordinates",
            "exponent_condition", "monomials_distinct_below_Kr")
    ]
    all_ok = all(row[key] for case in cases for row in case["rows"] for key in checks)
    all_ok &= boundary["telescoping_identity_exact"] and boundary["second_and_fourth_coordinates_coincide"]
    return {
        "schema": "plectis-chain-transcendence-bookkeeping/1",
        "boundary": "Finite exact checks of the formulas in the proof; the theorem rests on the Subspace Theorem and the written proof.",
        "all_exact_checks_pass": all_ok,
        "cases": cases,
        "millin_boundary": boundary,
    }


def print_table(result: dict) -> None:
    for case in result["cases"]:
        print(f"base {case['a']}/{case['b']}, ratio word {case['word']}")
        print("   j      N  r  K  c_1..c_(K-1)   exact  observed  predicted  Liouville/N")
        for row in case["rows"]:
            exact = all(row[key] for key in (
                "coefficient_bound_holds", "P_j_integer_matches_divisor_form", "identity_exact",
                "tail_positive_and_bounded", "s_unit_coordinates", "exponent_condition",
                "monomials_distinct_below_Kr"))
            print(f"  {row['j']:2d} {row['N']:6d} {row['ratio']:2d} {row['K']:2d}  "
                  f"{str(row['coefficients']):13s} {str(exact):6s} "
                  f"{row['log_product_over_log_height']:+.5f}  {row['predicted_limit']:+.5f}   "
                  f"{row['liouville_exponent_per_N']:+.4f}")
    boundary = result["millin_boundary"]
    print("Millin-type identity at z = 3/4: exact", boundary["telescoping_identity_exact"],
          "; coordinates coincide", boundary["second_and_fourth_coordinates_coincide"])
    print("all exact checks pass:", result["all_exact_checks_pass"])


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--json", metavar="PATH", help="write the full result as JSON")
    args = parser.parse_args(argv)
    result = run_default()
    print_table(result)
    if args.json:
        with open(args.json, "w", encoding="utf-8") as handle:
            json.dump(result, handle, indent=1)
            handle.write("\n")
    return 0 if result["all_exact_checks_pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
