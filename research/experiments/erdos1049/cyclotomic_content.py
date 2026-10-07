#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Cyclotomic content of the coefficient pencil det(alpha_{i+j} Y - beta_{i+j}).

The long Erdos 1049 paper (subsection 'Coefficient moments and cyclotomic
content', paragraph 'Testing for additional cyclotomic factors') fixes,
for Zudilin's 2016 construction at x = z = 1,

    R_m = sum_{k=0}^m (-1)^(m+k) p^(k(k+1)/2) [m, k]_p [m+k, k]_p,
    s_m = ([m]_p!)^3 R_m,            [m]_p! = prod_{j<=m} (1 + p + ... + p^(j-1)),
    alpha_m = p [p (p-1)^3]^m s_m,   beta_m = [alpha_m sum_{j>=1} tau(j) p^-j]_+ - 1,

and studies H_N(Y; p) = det(alpha_{i+j} Y - beta_{i+j})_{i,j<N}.  With
t_{m,d} = min(v_d(alpha_m), v_d(beta_m)), v_d the multiplicity of the
cyclotomic polynomial Phi_d, the assignment bound is
e_{N,d} = min over permutations sigma of sum_i t_{i+sigma(i),d}.

This program, using exact integer polynomial arithmetic only:

  1. builds alpha_m, beta_m for m <= 14 and checks R_m against Van Assche's
     positive expansion, alpha_0 = p, beta_0 = 0 and
     beta_1 = p^3 (p-1)^2 (p+2);
  2. for every pair 1 <= N <= 8, 1 <= d <= max(8, 2N-2) (76 pairs) computes
     e_{N,d} by a subset recurrence and by all N! permutations, an optimal
     assignment, integer row and column potentials u, v with
     u_i + v_j <= t_{i+j,d} and sum u + sum v = e_{N,d} (shortest paths, as in
     the paper), and the first Y0 in {0, ..., N} with a nonzero residue
     Gamma_{N,d}(Y0) in Z[p]/(Phi_d);
  3. computes that residue three ways: the signed minimum-cost subset
     recurrence; the determinant of the reduced matrix obtained by dividing
     row i by Phi_d^u_i and column j by Phi_d^v_j; and the full polynomial
     H_N(Y0; p) by fraction-free elimination, divided exactly by Phi_d^e_{N,d};
  4. for N <= 5 computes H_N(Y0; p) for Y0 = 0, ..., N and their monic gcd in
     Q[p], certifying that no further factor exists by a gcd computation modulo
     a prime that does not divide a leading coefficient.

It certifies equality with the assignment bound only at these 76 pairs and
the complete contents only through rank five.  It proves nothing about larger
ranks, about cyclotomic indices outside the stated window at ranks six to
eight, or about moment representations.  No floating point and no Lean kernel.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import sys
from pathlib import Path

sys.set_int_max_str_digits(0)

SCHEMA = "erdos1049-public-computation/1"
PROGRAM = "cyclotomic_content.py"
MAX_RANK = 8
CONTENT_MAX_RANK = 5
PRINTED_CONTENTS = {
    1: {"p": 1},
    2: {"p": 5, "1": 4},
    3: {"p": 14, "1": 15, "2": 4},
    4: {"p": 30, "1": 32, "2": 8, "3": 4},
    5: {"p": 55, "1": 55, "2": 19, "4": 4, "3": 8},
}

Poly = list  # integer coefficients, lowest degree first


# ------------------------------------------------------------- polynomials
def trim(a: Poly) -> Poly:
    while a and a[-1] == 0:
        a.pop()
    return a


def padd(a: Poly, b: Poly) -> Poly:
    out = list(a) + [0] * max(0, len(b) - len(a))
    for i, c in enumerate(b):
        out[i] += c
    return trim(out)


def pscale(a: Poly, c: int) -> Poly:
    return trim([c * x for x in a])


def pshift(a: Poly, k: int) -> Poly:
    return [0] * k + list(a) if a else []


def pmul_school(a: Poly, b: Poly) -> Poly:
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return trim(out)


def _bias(count: int, width: int) -> int:
    return int.from_bytes((b"\x00" * (width - 1) + b"\x80") * count, "little")


def pack(a: Poly, width: int) -> int:
    half = 1 << (8 * width - 1)
    data = b"".join((c + half).to_bytes(width, "little") for c in a)
    return int.from_bytes(data, "little") - _bias(len(a), width)


def unpack(value: int, count: int, width: int) -> Poly:
    half = 1 << (8 * width - 1)
    data = (value + _bias(count, width)).to_bytes(count * width, "little")
    return trim([int.from_bytes(data[i * width:(i + 1) * width], "little") - half for i in range(count)])


def pmul(a: Poly, b: Poly) -> Poly:
    if not a or not b:
        return []
    if min(len(a), len(b)) < 40:
        return pmul_school(a, b)
    bound = min(len(a), len(b)) * max(map(abs, a)) * max(map(abs, b))
    width = (bound.bit_length() + 2) // 8 + 1
    return unpack(pack(a, width) * pack(b, width), len(a) + len(b) - 1, width)


def pdivmod_monic(a: Poly, q: Poly) -> tuple[Poly, Poly]:
    if q[-1] != 1:
        raise ValueError("monic divisor required")
    r = list(a)
    dq = len(q) - 1
    if len(r) - 1 < dq:
        return [], trim(r)
    quotient = [0] * (len(r) - dq)
    nonzero = [(j, c) for j, c in enumerate(q[:-1]) if c]
    for i in range(len(r) - 1, dq - 1, -1):
        c = r[i]
        if c:
            quotient[i - dq] = c
            for j, qc in nonzero:
                r[i - dq + j] -= c * qc
            r[i] = 0
    return trim(quotient), trim(r[:dq])


def pdiv_exact_integer(a: Poly, b: Poly) -> Poly:
    """Exact division in Z[p] by a nonzero (not necessarily monic) polynomial."""

    r = list(a)
    db = len(b) - 1
    if not r:
        return []
    quotient = [0] * max(1, len(r) - db)
    for i in range(len(r) - 1, db - 1, -1):
        c = r[i]
        if c:
            if c % b[-1]:
                raise ArithmeticError("inexact polynomial division")
            k = c // b[-1]
            quotient[i - db] = k
            for j, y in enumerate(b):
                r[i - db + j] -= k * y
    if any(r):
        raise ArithmeticError("inexact polynomial division")
    return trim(quotient)


_CYCLO: dict[int, Poly] = {}


def cyclotomic(d: int) -> Poly:
    if d not in _CYCLO:
        a = [-1] + [0] * (d - 1) + [1]
        for e in range(1, d):
            if d % e == 0:
                a, r = pdivmod_monic(a, cyclotomic(e))
                if r:
                    raise ArithmeticError("cyclotomic division failed")
        _CYCLO[d] = a
    return _CYCLO[d]


def valuation(a: Poly, d: int) -> int:
    if not a:
        raise ArithmeticError("valuation of the zero polynomial")
    count = 0
    while True:
        quotient, remainder = pdivmod_monic(a, cyclotomic(d))
        if remainder:
            return count
        a, count = quotient, count + 1


def divide_power(a: Poly, d: int, e: int) -> Poly:
    for _ in range(e):
        a, remainder = pdivmod_monic(a, cyclotomic(d))
        if remainder:
            raise ArithmeticError("nonzero remainder dividing by a cyclotomic power")
    return a


def reduce_mod(a: Poly, d: int) -> Poly:
    return pdivmod_monic(a, cyclotomic(d))[1]


def digest(a: Poly) -> str:
    return hashlib.sha256(json.dumps([str(c) for c in a], separators=(",", ":")).encode()).hexdigest()


# ---------------------------------------------------------- source sequence
def gaussian_table(limit: int) -> dict[tuple[int, int], Poly]:
    table: dict[tuple[int, int], Poly] = {}
    for n in range(limit + 1):
        for k in range(n + 1):
            if k in (0, n):
                table[n, k] = [1]
            else:  # q-Pascal: [n,k] = [n-1,k] + p^(n-k) [n-1,k-1]
                table[n, k] = padd(table[n - 1, k], pshift(table[n - 1, k - 1], n - k))
    return table


def source_sequences(max_index: int) -> tuple[list[Poly], list[Poly]]:
    gauss = gaussian_table(2 * max_index)
    alphas, betas = [], []
    for m in range(max_index + 1):
        R: Poly = []
        for k in range(m + 1):
            term = pshift(pmul(gauss[m, k], gauss[m + k, k]), k * (k + 1) // 2)
            R = padd(R, pscale(term, (-1) ** (m + k)))
        positive: Poly = []
        for k in range(m + 1):
            term = pshift(pmul(gauss[m, k], gauss[m + k, k]), (m - k) * (m - k + 1) // 2)
            for j in range(m - k + 1, m + 1):
                term = pmul(term, [-1] + [0] * (j - 1) + [1])
            positive = padd(positive, term)
        if R != positive:
            raise ArithmeticError("R_m differs from Van Assche's positive expansion")
        factorial = [1]
        for j in range(1, m + 1):
            factorial = pmul(factorial, [1] * j)
        s = pmul(pmul(pmul(factorial, factorial), factorial), R)
        if len(s) - 1 != 3 * m * m - m or s[-1] != 1:
            raise ArithmeticError("s_m is not monic of degree 3m^2 - m")
        p_minus_1_cubed_m = [1]
        for _ in range(3 * m):
            p_minus_1_cubed_m = pmul(p_minus_1_cubed_m, [-1, 1])
        alpha = pshift(pmul(p_minus_1_cubed_m, s), m + 1)
        degree = len(alpha) - 1
        tau = [0] * (degree + 1)
        for j in range(1, degree + 1):
            for multiple in range(j, degree + 1, j):
                tau[multiple] += 1
        beta = [sum(alpha[i] * tau[i - r] for i in range(r + 1, degree + 1)) for r in range(degree)]
        beta[0] -= 1
        alphas.append(alpha)
        betas.append(trim(beta))
    return alphas, betas


# -------------------------------------------------------------- determinants
def full_determinant(matrix: list[list[Poly]]) -> Poly:
    """det of a polynomial matrix by fraction-free elimination at p = 2^(8*width)."""

    n = len(matrix)
    if any(not any(row) for row in matrix):
        return []
    rows_norm = [max(sum(map(abs, entry)) for entry in row) for row in matrix]
    bound = 1
    for k in range(2, n + 1):
        bound *= k
    for value in rows_norm:
        bound *= value
    degree = sum(max(len(entry) - 1 for entry in row if entry) for row in matrix)
    width = (bound.bit_length() + 2) // 8 + 1
    m = [[pack(entry, width) if entry else 0 for entry in row] for row in matrix]
    sign, previous = 1, 1
    for k in range(n - 1):
        if m[k][k] == 0:
            swap = next((i for i in range(k + 1, n) if m[i][k] != 0), None)
            if swap is None:
                return []
            m[k], m[swap] = m[swap], m[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                q, r = divmod(m[k][k] * m[i][j] - m[i][k] * m[k][j], previous)
                if r:
                    raise ArithmeticError("fraction-free elimination left a remainder")
                m[i][j] = q
        previous = m[k][k]
    return unpack(sign * m[n - 1][n - 1], degree + 1, width)


def small_determinant(matrix: list[list[Poly]]) -> Poly:
    """det over Z[p] by fraction-free elimination with exact polynomial division."""

    m = [[list(entry) for entry in row] for row in matrix]
    n = len(m)
    sign, previous = 1, [1]
    for k in range(n - 1):
        if not m[k][k]:
            swap = next((i for i in range(k + 1, n) if m[i][k]), None)
            if swap is None:
                return []
            m[k], m[swap] = m[swap], m[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = padd(pmul(m[k][k], m[i][j]), pscale(pmul(m[i][k], m[k][j]), -1))
                m[i][j] = pdiv_exact_integer(numerator, previous)
        previous = m[k][k]
    return pscale(m[n - 1][n - 1], sign)


def pencil_matrix(alphas: list[Poly], betas: list[Poly], n: int, y: int) -> list[list[Poly]]:
    return [[padd(pscale(alphas[i + j], y), pscale(betas[i + j], -1)) for j in range(n)] for i in range(n)]


# ------------------------------------------------------------- assignments
def assignment_by_subsets(cost: list[list[int]]) -> tuple[int, list[int]]:
    n = len(cost)
    best = {0: (0, [])}
    for mask in range(1 << n):
        if mask not in best:
            continue
        i = bin(mask).count("1")
        if i == n:
            continue
        value, columns = best[mask]
        for j in range(n):
            if not mask & (1 << j):
                new = mask | (1 << j)
                candidate = (value + cost[i][j], columns + [j])
                if new not in best or candidate[0] < best[new][0]:
                    best[new] = candidate
    return best[(1 << n) - 1]


def potentials(cost: list[list[int]], sigma: list[int]) -> tuple[list[int], list[int]]:
    """Shortest-path potentials on columns, as described in the paper."""

    n = len(cost)
    edges = [(sigma[i], j, cost[i][j] - cost[i][sigma[i]]) for i in range(n) for j in range(n)]
    dist = [0] * n  # a new source vertex with a zero-length edge to every column
    for _ in range(n + 1):
        changed = False
        for a, b, w in edges:
            if dist[a] + w < dist[b]:
                dist[b] = dist[a] + w
                changed = True
        if not changed:
            break
    else:
        raise ArithmeticError("negative cycle: the assignment is not optimal")
    v = dist
    u = [cost[i][sigma[i]] - v[sigma[i]] for i in range(n)]
    return u, v


def residue_by_subsets(n: int, d: int, y: int, t, entry_residues) -> tuple[int, Poly]:
    """Signed minimum-cost subset recurrence for Gamma_{N,d}(Y0) modulo Phi_d."""

    table = {0: (0, [1])}
    for mask in range(1 << n):
        if mask not in table:
            continue
        i = bin(mask).count("1")
        if i == n:
            continue
        cost, value = table[mask]
        for j in range(n):
            if mask & (1 << j):
                continue
            a_res, b_res = entry_residues[i + j]
            entry = padd(pscale(a_res, y), pscale(b_res, -1))
            sign = -1 if bin(mask >> (j + 1)).count("1") % 2 else 1
            term = reduce_mod(pscale(pmul(value, entry), sign), d)
            new_cost, new = cost + t[i + j], mask | (1 << j)
            if new not in table or new_cost < table[new][0]:
                table[new] = (new_cost, term)
            elif new_cost == table[new][0]:
                table[new] = (new_cost, reduce_mod(padd(table[new][1], term), d))
    return table[(1 << n) - 1]


# -------------------------------------------------------------- polynomial gcd
def gcd_mod_prime(a: list[int], b: list[int], prime: int) -> list[int]:
    a = trim([x % prime for x in a])
    b = trim([x % prime for x in b])
    while b:
        inverse = pow(b[-1], -1, prime)
        while len(a) >= len(b) and a:
            factor = a[-1] * inverse % prime
            shift = len(a) - len(b)
            for j, y in enumerate(b):
                a[shift + j] = (a[shift + j] - factor * y) % prime
            trim(a)
        a, b = b, a
    return a


def certify_content(values: list[Poly]) -> dict:
    """Monic gcd in Q[p] of the given integer polynomials (zero ones are skipped)."""

    values = [v for v in values if v]
    exponents: dict[str, int] = {}
    power_of_p = min(next(i for i, c in enumerate(v) if c) for v in values)
    cofactors = [v[power_of_p:] for v in values]
    if power_of_p:
        exponents["p"] = power_of_p
    for d in range(1, 61):
        e = min(valuation(v, d) for v in cofactors)
        if e:
            exponents[str(d)] = e
            cofactors = [divide_power(v, d, e) for v in cofactors]
    lead = cofactors[0][-1]
    for prime in (1_000_003, 1_000_033, 1_000_037, 1_000_039):
        if lead % prime == 0:
            continue
        g = cofactors[0]
        for other in cofactors[1:]:
            g = gcd_mod_prime(g, other, prime)
        if len(g) == 1:
            return {"exponents": exponents, "coprime_cofactors_certified_mod": prime}
    raise ArithmeticError("could not certify that the cofactors are coprime")


# ------------------------------------------------------------------ driver
def compute() -> dict:
    max_index = 2 * MAX_RANK - 2
    alphas, betas = source_sequences(max_index)
    source_checks = {
        "alpha_0 = p": alphas[0] == [0, 1],
        "beta_0 = 0": betas[0] == [],
        "beta_1 = p^3 (p-1)^2 (p+2)": betas[1] == pshift(pmul(pmul([-1, 1], [-1, 1]), [2, 1]), 3),
        "every alpha_m nonzero": all(alphas),
    }
    window = {n: list(range(1, max(8, 2 * n - 2) + 1)) for n in range(1, MAX_RANK + 1)}
    max_d = max(max(ds) for ds in window.values())
    t_table = {d: [min(valuation(alphas[m], d), valuation(betas[m], d) if betas[m] else 10**9)
                   for m in range(max_index + 1)] for d in range(1, max_d + 1)}

    # Full determinant polynomials, cached by (N, Y0).
    determinants: dict[tuple[int, int], Poly] = {}

    def determinant(n: int, y: int) -> Poly:
        if (n, y) not in determinants:
            determinants[n, y] = full_determinant(pencil_matrix(alphas, betas, n, y))
        return determinants[n, y]

    witnesses = []
    for n in range(1, MAX_RANK + 1):
        for d in window[n]:
            t = t_table[d]
            cost = [[t[i + j] for j in range(n)] for i in range(n)]
            e, sigma = assignment_by_subsets(cost)
            brute = min(sum(cost[i][s[i]] for i in range(n)) for s in itertools.permutations(range(n)))
            if brute != e:
                raise ArithmeticError("assignment minimum disagrees with brute force")
            u, v = potentials(cost, sigma)
            if any(u[i] + v[j] > cost[i][j] for i in range(n) for j in range(n)) or sum(u) + sum(v) != e:
                raise ArithmeticError("potentials fail the dual conditions")
            entry_residues = {}
            for m in range(2 * n - 1):
                a_res = reduce_mod(divide_power(alphas[m], d, t[m]), d)
                b_res = reduce_mod(divide_power(betas[m], d, t[m]), d) if betas[m] else []
                entry_residues[m] = (a_res, b_res)
            chosen = None
            for y in range(n + 1):
                cost_found, residue = residue_by_subsets(n, d, y, t, entry_residues)
                if cost_found != e:
                    raise ArithmeticError("subset recurrence minimum differs from e_{N,d}")
                if residue:
                    chosen = (y, residue)
                    break
            if chosen is None:
                raise ArithmeticError(f"no nonzero residue at N={n}, d={d}")
            y, residue = chosen
            # Reduced matrix: divide row i by Phi_d^u_i and column j by Phi_d^v_j, reduce mod Phi_d.
            reduced = []
            for i in range(n):
                row = []
                for j in range(n):
                    if u[i] + v[j] == t[i + j]:
                        a_res, b_res = entry_residues[i + j]
                        row.append(reduce_mod(padd(pscale(a_res, y), pscale(b_res, -1)), d))
                    else:
                        row.append([])
                reduced.append(row)
            reduced_det = reduce_mod(small_determinant(reduced), d)
            # Direct check on the full polynomial H_N(Y0; p).
            full = determinant(n, y)
            quotient = divide_power(full, d, e)
            direct = reduce_mod(quotient, d)
            if not (residue == reduced_det == direct):
                raise ArithmeticError(f"residue methods disagree at N={n}, d={d}")
            witnesses.append({
                "rank": n,
                "cyclotomic_index": d,
                "assignment_bound": e,
                "optimal_assignment": sigma,
                "row_potentials": u,
                "column_potentials": v,
                "Y0": y,
                "residue_coefficients_low_to_high": [str(c) for c in residue],
                "three_methods_agree": True,
            })

    example = next(w for w in witnesses if w["rank"] == 2 and w["cyclotomic_index"] == 1)
    example_matrix = [[t_table[1][i + j] for j in range(2)] for i in range(2)]

    contents = []
    content_checks = {}
    for n in range(1, CONTENT_MAX_RANK + 1):
        values = [determinant(n, y) for y in range(n + 1)]
        certificate = certify_content(values)
        contents.append({"rank": n, **certificate})
        content_checks[f"content N={n} matches the printed factorisation"] = (
            certificate["exponents"] == PRINTED_CONTENTS[n])
        for d in window[n]:
            wit = next(w for w in witnesses if w["rank"] == n and w["cyclotomic_index"] == d)
            content_checks[f"content N={n}: exponent of Phi_{d} equals e_(N,d)"] = (
                certificate["exponents"].get(str(d), 0) == wit["assignment_bound"])
        content_checks[f"content N={n}: no Phi_d beyond the witness window"] = all(
            int(k) in window[n] for k in certificate["exponents"] if k != "p")

    checks = dict(source_checks)
    checks["76 witness pairs"] = len(witnesses) == 76
    checks["every witness residue nonzero and three methods agree"] = all(
        w["three_methods_agree"] and w["residue_coefficients_low_to_high"] for w in witnesses)
    checks["example N=2, d=1: entry valuations (0 2; 2 5)"] = example_matrix == [[0, 2], [2, 5]]
    checks["example N=2, d=1: e = 4"] = example["assignment_bound"] == 4
    checks["example N=2, d=1: Gamma(0) = -9"] = (example["Y0"], example["residue_coefficients_low_to_high"]) == (0, ["-9"])
    checks.update(content_checks)

    return {
        "source_sequences": {
            "indices": f"0..{max_index}",
            "alpha_degrees": [len(a) - 1 for a in alphas],
            "beta_degrees": [len(b) - 1 for b in betas],
            "alpha_sha256": [digest(a) for a in alphas],
            "beta_sha256": [digest(b) for b in betas],
        },
        "entry_valuations_t_m_d": {str(d): t_table[d] for d in sorted(t_table)},
        "determinant_value_polynomials": [
            {"rank": n, "Y0": y, "degree": len(poly) - 1, "sha256": digest(poly)}
            for (n, y), poly in sorted(determinants.items())
        ],
        "complete_contents_through_rank_5": contents,
        "residue_witnesses": witnesses,
        "digest_rule": "sha256 of the compact JSON list of decimal coefficient strings, lowest degree first",
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
                "Exact contents of H_N through rank five and nonzero minimum-valuation residues "
                "at the 76 pairs 1 <= N <= 8, 1 <= d <= max(8, 2N-2). Nothing about larger ranks "
                "or other cyclotomic indices at ranks six to eight. No floating point and no "
                "Lean kernel."
            ),
            "paper_passage": "Subsection 'Coefficient moments and cyclotomic content', paragraph 'Testing for additional cyclotomic factors'",
            "result": result,
        }
        args.receipt.write_text(canonical(receipt), encoding="utf-8")
    sys.stdout.write(canonical(result))
    return 0 if result["all_printed_claims_verified"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
