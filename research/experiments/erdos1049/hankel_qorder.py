#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Compute the first nonzero term of Zudilin's normalised Hankel determinant.

The long Erdos 1049 paper (subsection 'The sharp q-order of the normalised
Hankel determinant') studies, at x = z = 1 and with q a formal variable,

    v_m^* = sum_{t>=0} q^((m+1)t) (q;q)_m^3 (q^(t+1);q)_m / (q^(m+t+1);q)_(m+1),
    V_N^* = det(v_(i+j)^*)_{0 <= i,j < N},

and proves ord_q V_N^* = N(N-1)(2N-1)/6 with leading coefficient
(N!)^2 (N+1)! / 2^N at every rank.  Independently of that proof, the paper
reports an exact computation for 1 <= N <= 7.  This program repeats it with
exact integer power-series arithmetic truncated beyond q^(91+8):

  1. v_m^* for 0 <= m <= 12 is expanded from the displayed hypergeometric sum,
     and separately as alpha_m F(p) - beta_m with p = 1/q, using the
     coefficient normalisation alpha_m = p [p (p-1)^3]^m ([m]_p!)^3 R_m(p),
     beta_m = [alpha_m F(p)]_+ - 1 and F(p) = sum tau(j) p^-j of the paper's
     coefficient section.  The two expansions must agree.
  2. V_N^* is computed twice: by expansion over column subsets of the
     truncated series (the Leibniz sum grouped by the columns already used),
     and by fraction-free elimination of the truncated polynomial matrix with
     every division checked exact.  The two must agree through the cutoff.
  3. The order and leading coefficient at each rank are compared with the
     closed forms and with the values printed in the paper.
  4. The row identity: applying D_j = prod_{r<j} (I - q^r S), S the backward
     shift in m, directly to the sequence (v_m^*), the entry D_j v_(j+l)^*
     has order j(j+1)/2 + j l and leading coefficient (-1)^j (j+1)^2 (j+2)/2
     for 0 <= j, l <= 6 (row 1: order l+1, coefficient -6).  Each hypergeometric
     summand t <= j contributes (-1)^j h^(t)_(j-t) at that degree, with
     h^(0)_r = (r+1)(r+2)(2r+3)/6 and h^(t)_r = binom(r+2, 2) for t > 0.
  5. For each rank the reversal is the unique permutation minimising the
     total entry order, by enumeration of all N! permutations.

It proves the order and leading coefficient only for these seven ranks; the
all-rank statement is the paper's proof.  It says nothing about the value of
V_N^* at a fixed q or about denominators.  No floating point and no Lean kernel.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import sys
from pathlib import Path

SCHEMA = "erdos1049-public-computation/1"
PROGRAM = "hankel_qorder.py"
MAX_RANK = 7
MARGIN = 8
PRINTED_ORDERS = [0, 1, 5, 14, 30, 55, 91]
PRINTED_LEADING = [1, 6, 108, 4320, 324000, 40824000, 8001504000]
SHOWN_COEFFICIENTS = 8

Series = list  # integer coefficients of q^0, ..., q^cutoff


# ------------------------------------------------------------ series helpers
def times_one_minus(series: Series, power: int) -> Series:
    out = list(series)
    for d in range(power, len(series)):
        out[d] -= series[d - power]
    return out


def over_one_minus(series: Series, power: int) -> Series:
    out = list(series)
    for d in range(power, len(out)):
        out[d] += out[d - power]
    return out


def shifted(series: Series, amount: int) -> Series:
    n = len(series)
    if amount >= n:
        return [0] * n
    return [0] * amount + series[: n - amount]


def mul(a: Series, b: Series) -> Series:
    n = len(a)
    out = [0] * n
    for i, x in enumerate(a):
        if x:
            for j in range(n - i):
                y = b[j]
                if y:
                    out[i + j] += x * y
    return out


def add(a: Series, b: Series, sign: int = 1) -> Series:
    return [x + sign * y for x, y in zip(a, b)]


def first_nonzero(series: Series) -> tuple[int, int] | tuple[None, None]:
    for degree, c in enumerate(series):
        if c:
            return degree, c
    return None, None


def digest(values: list[int]) -> str:
    return hashlib.sha256(json.dumps([str(v) for v in values], separators=(",", ":")).encode()).hexdigest()


# ------------------------------------------------------------ the moments
def hypergeometric_summand(m: int, t: int, cutoff: int) -> Series:
    """T_(m,t) = q^((m+1)t) (q;q)_m^3 (q^(t+1);q)_m / (q^(m+t+1);q)_(m+1)."""

    s = [0] * (cutoff + 1)
    s[0] = 1
    for power in range(1, m + 1):
        for _ in range(3):
            s = times_one_minus(s, power)
    for power in range(t + 1, t + m + 1):
        s = times_one_minus(s, power)
    for power in range(m + t + 1, 2 * m + t + 2):
        s = over_one_minus(s, power)
    return shifted(s, (m + 1) * t)


def moment_hypergeometric(m: int, cutoff: int) -> Series:
    total = [0] * (cutoff + 1)
    for t in range(cutoff // (m + 1) + 1):
        total = add(total, hypergeometric_summand(m, t, cutoff))
    return total


def poly_mul(a: list[int], b: list[int]) -> list[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return out


def moment_from_coefficients(m: int, cutoff: int) -> Series:
    """alpha_m F(p) - beta_m as a series in q = 1/p (coefficient normalisation)."""

    # Gaussian binomials in p by q-Pascal: [n,k] = [n-1,k] + p^(n-k) [n-1,k-1].
    gauss: dict[tuple[int, int], list[int]] = {}
    for n in range(2 * m + 1):
        for k in range(n + 1):
            if k in (0, n):
                gauss[n, k] = [1]
            else:
                left, right = gauss[n - 1, k], [0] * (n - k) + gauss[n - 1, k - 1]
                size = max(len(left), len(right))
                gauss[n, k] = [(left[i] if i < len(left) else 0) + (right[i] if i < len(right) else 0)
                               for i in range(size)]
    R = [0]
    for k in range(m + 1):
        term = [0] * (k * (k + 1) // 2) + poly_mul(gauss[m, k], gauss[m + k, k])
        R = [(R[i] if i < len(R) else 0) + (-1) ** (m + k) * (term[i] if i < len(term) else 0)
             for i in range(max(len(R), len(term)))]
    factorial = [1]
    for j in range(1, m + 1):
        factorial = poly_mul(factorial, [1] * j)
    s = poly_mul(poly_mul(poly_mul(factorial, factorial), factorial), R)
    alpha = [0] * (m + 1) + s
    for _ in range(3 * m):
        alpha = poly_mul(alpha, [-1, 1])
    while alpha and alpha[-1] == 0:
        alpha.pop()
    degree = len(alpha) - 1
    tau = [0] * (degree + cutoff + 1)
    for d in range(1, len(tau)):
        for k in range(d, len(tau), d):
            tau[k] += 1
    # alpha F - beta = 1 + sum_{k >= 1} q^k sum_i alpha_i tau(i + k).
    return [1] + [sum(alpha[i] * tau[i + k] for i in range(degree + 1)) for k in range(1, cutoff + 1)]


# ------------------------------------------------------------ determinants
def determinant_by_subsets(entries: list[list[Series]], cutoff: int) -> Series:
    """Leibniz sum grouped by the set of columns used by the first rows."""

    n = len(entries)
    one = [0] * (cutoff + 1)
    one[0] = 1
    table = {0: one}
    for row in range(n):
        following: dict[int, Series] = {}
        for used, value in table.items():
            for column in range(n):
                if used & (1 << column):
                    continue
                sign = -1 if bin(used >> (column + 1)).count("1") % 2 else 1
                term = mul(value, entries[row][column])
                key = used | (1 << column)
                following[key] = add(following[key], term, sign) if key in following else (
                    term if sign == 1 else [-x for x in term])
        table = following
    return table[(1 << n) - 1]


def _bias(count: int, width: int) -> int:
    return int.from_bytes((b"\x00" * (width - 1) + b"\x80") * count, "little")


def determinant_by_elimination(entries: list[list[Series]], cutoff: int) -> Series:
    """Fraction-free elimination of the truncated polynomial matrix.

    Each entry is the polynomial of degree at most `cutoff` given by its
    truncation, evaluated at q = 2^(8*width); an exact division of integers then
    mirrors an exact division in Z[q].  The determinant of the truncated
    matrix agrees with V_N^* through q^cutoff.
    """

    n = len(entries)
    bound = math.factorial(n)
    for row in entries:
        bound *= max(sum(abs(c) for c in entry) for entry in row)
    width = (bound.bit_length() + 2) // 8 + 1
    half = 1 << (8 * width - 1)

    def pack(poly: Series) -> int:
        data = b"".join((c + half).to_bytes(width, "little") for c in poly)
        return int.from_bytes(data, "little") - _bias(len(poly), width)

    m = [[pack(entry) for entry in row] for row in entries]
    sign, previous = 1, 1
    for k in range(n - 1):
        if m[k][k] == 0:
            swap = next((i for i in range(k + 1, n) if m[i][k]), None)
            if swap is None:
                return [0] * (cutoff + 1)
            m[k], m[swap] = m[swap], m[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                quotient, remainder = divmod(m[k][k] * m[i][j] - m[i][k] * m[k][j], previous)
                if remainder:
                    raise ArithmeticError("fraction-free elimination left a remainder")
                m[i][j] = quotient
        previous = m[k][k]
    count = n * cutoff + 1
    data = (sign * m[n - 1][n - 1] + _bias(count, width)).to_bytes(count * width, "little")
    coefficients = [int.from_bytes(data[i * width:(i + 1) * width], "little") - half for i in range(count)]
    return coefficients[: cutoff + 1]


# ------------------------------------------------------------ the computation
def compute() -> dict:
    lower_bound = MAX_RANK * (MAX_RANK - 1) * (2 * MAX_RANK - 1) // 6
    cutoff = lower_bound + MARGIN
    count = 2 * MAX_RANK - 1
    moments = [moment_hypergeometric(m, cutoff) for m in range(count)]
    moments_agree = all(moments[m] == moment_from_coefficients(m, cutoff) for m in range(count))

    ranks = []
    for n in range(1, MAX_RANK + 1):
        entries = [[moments[i + j] for j in range(n)] for i in range(n)]
        by_subsets = determinant_by_subsets(entries, cutoff)
        by_elimination = determinant_by_elimination(entries, cutoff)
        order, leading = first_nonzero(by_subsets)
        closed_order = n * (n - 1) * (2 * n - 1) // 6
        closed_leading = math.factorial(n) ** 2 * math.factorial(n + 1) // 2**n
        orders = [[j * (j + 1) // 2 + j * l for l in range(n)] for j in range(n)]
        weights = {perm: sum(orders[j][perm[j]] for j in range(n)) for perm in itertools.permutations(range(n))}
        least = min(weights.values())
        minimisers = [perm for perm, w in weights.items() if w == least]
        ranks.append({
            "rank": n,
            "q_order": order,
            "leading_coefficient": leading,
            "closed_form_order": closed_order,
            "closed_form_leading_coefficient": closed_leading,
            "coefficients_from_order": [str(c) for c in by_subsets[order: order + SHOWN_COEFFICIENTS]],
            "truncated_series_sha256": digest(by_subsets),
            "two_determinant_methods_agree": by_subsets == by_elimination,
            "reversal_is_unique_minimiser": minimisers == [tuple(range(n - 1, -1, -1))],
            "minimum_entry_order_weight": least,
        })

    # Row identity: apply D_j = prod_{r<j} (I - q^r S) to the whole sequence.
    grid = []
    sequence = [list(v) for v in moments]
    transformed = {0: sequence}
    for j in range(1, MAX_RANK):
        previous = transformed[j - 1]
        r = j - 1
        # D_j v is defined at indices m >= j.
        transformed[j] = [add(previous[m], shifted(previous[m - 1], r), -1) if m >= j else None
                          for m in range(count)]
    for j in range(MAX_RANK):
        expected_coefficient = (-1) ** j * (j + 1) ** 2 * (j + 2) // 2
        for l in range(MAX_RANK):
            order, coefficient = first_nonzero(transformed[j][j + l])
            grid.append({
                "row": j, "column": l, "q_order": order, "leading_coefficient": coefficient,
                "matches_row_identity": order == j * (j + 1) // 2 + j * l and coefficient == expected_coefficient,
            })

    # Per-summand contributions at the leading degree.
    tails = []
    for j in range(MAX_RANK):
        for l in range(MAX_RANK):
            m, degree = j + l, j * (j + 1) // 2 + j * l
            contributions = []
            for t in range(j + 1):
                # D_j applied to the sequence (T_(k,t))_k, evaluated at k = m.
                seq = {k: hypergeometric_summand(k, t, cutoff) for k in range(m - j, m + 1)}
                for r in range(j):
                    seq = {k: add(seq[k], shifted(seq[k - 1], r), -1) for k in seq if k - 1 in seq}
                value = seq[m]
                expected = (-1) ** j * ((j + 1) * (j + 2) * (2 * j + 3) // 6 if t == 0 else math.comb(j - t + 2, 2))
                contributions.append({"t": t, "coefficient": value[degree], "expected": expected,
                                      "vanishes_below": all(c == 0 for c in value[:degree])})
            tails.append({
                "row": j, "column": l,
                "contributions": contributions,
                "all_match": all(c["coefficient"] == c["expected"] and c["vanishes_below"] for c in contributions),
                "sum_is_row_coefficient": sum(c["coefficient"] for c in contributions)
                == (-1) ** j * (j + 1) ** 2 * (j + 2) // 2,
            })

    checks = {
        "two expansions of v_m^* agree for 0 <= m <= 12": moments_agree,
        "two determinant methods agree through the cutoff at every rank": all(
            r["two_determinant_methods_agree"] for r in ranks),
        "orders equal the printed list 0,1,5,14,30,55,91": [r["q_order"] for r in ranks] == PRINTED_ORDERS,
        "leading coefficients equal the printed list": [r["leading_coefficient"] for r in ranks] == PRINTED_LEADING,
        "orders equal N(N-1)(2N-1)/6": all(r["q_order"] == r["closed_form_order"] for r in ranks),
        "leading coefficients equal (N!)^2 (N+1)!/2^N": all(
            r["leading_coefficient"] == r["closed_form_leading_coefficient"] for r in ranks),
        "rank 2 starts 6q": ranks[1]["q_order"] == 1 and ranks[1]["leading_coefficient"] == 6,
        "reversal is the unique minimising permutation at every rank": all(
            r["reversal_is_unique_minimiser"] for r in ranks),
        "row identity holds for 0 <= j, l <= 6": all(g["matches_row_identity"] for g in grid),
        "row 1 has order l+1 and coefficient -6 in every column": all(
            g["q_order"] == g["column"] + 1 and g["leading_coefficient"] == -6 for g in grid if g["row"] == 1),
        "N = 2 entry orders are (0 0; 1 2)": [[g["q_order"] for g in grid if g["row"] == j and g["column"] < 2]
                                                for j in range(2)] == [[0, 0], [1, 2]],
        "per-summand contributions match h^(t)_(j-t)": all(t["all_match"] and t["sum_is_row_coefficient"]
                                                           for t in tails),
    }
    return {
        "q_degree_cutoff": cutoff,
        "moment_indices": [0, count - 1],
        "moment_sha256": [digest(v) for v in moments],
        "ranks": ranks,
        "transformed_rows": grid,
        "per_summand_contributions": tails,
        "checks": checks,
        "all_printed_claims_verified": all(checks.values()),
    }


def canonical(obj: object) -> str:
    return json.dumps(obj, indent=2, sort_keys=True) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--receipt", type=Path, help="write a receipt JSON to this path")
    args = parser.parse_args()
    result = compute()
    if args.receipt:
        receipt = {
            "schema": SCHEMA,
            "program": PROGRAM,
            "program_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "arguments": [],
            "verification_scope": "finite_computation_only",
            "claim_boundary": (
                "Exact order and leading coefficient of V_N^* for 1 <= N <= 7 and the "
                "transformed-row leading terms for 0 <= j, l <= 6. The all-rank theorem is the "
                "paper's proof. No floating point and no Lean kernel."
            ),
            "paper_passage": "Subsection 'The sharp q-order of the normalised Hankel determinant', paragraph 'Formal verification and computations'",
            "result": result,
        }
        args.receipt.write_text(canonical(receipt), encoding="utf-8")
    sys.stdout.write(canonical(result))
    return 0 if result["all_printed_claims_verified"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
