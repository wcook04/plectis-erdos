#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Independently check computations/finite_coefficients.json against D_{N,h}.

RECONSTRUCTION NOTE
-------------------
This file is a NEW artefact, written on 2026-09-20.  It was reconstructed from
the mathematical definitions in the #1049 reasoning paper
(paper/reasoning-parts/erdos1049/core.tex, "Coefficient moments and cyclotomic
content", lines 1790-1896) and from the Lean declarations in
lean/ErdosProblems/Erdos1049/PaperR20/CoefficientPencil.lean
(coefficientRPoly, coefficientQFactorialPoly, coefficientMomentPoly,
coefficientHankelDetPoly).  It is not a recovered copy of an earlier script.

The paper cites computations/finite_coefficients.json and
computations/check_finite_coefficients.py.  Neither path existed in the working
tree, and `git log --all` over both paths is empty; an earlier pass reported
the same absence across every checkout.  The same sixteen coefficient lists
were nevertheless present, split across
computations/certificates/s_hankel_rank<N>_shift<h>.json; what was missing was
the two cited filenames, not the computation.

What this checker does, and why it is independent
-------------------------------------------------
It never imports finite_coefficients_generate.py, and it shares no code with
it.  Every step takes a different route to the same object:

  * Gaussian binomials come from the product formula
        [n choose k]_p = prod_{i=1}^{k} (p^{n-k+i} - 1) / (p^i - 1),
    carried out as exact polynomial division by a monic divisor over Z.  The
    generator (and Lean's `gaussBinom`) use the q-Pascal recursion instead.
  * The q-factorial comes from [m]_p! = prod_{j=1}^{m} (p^j - 1)/(p - 1),
    again by exact division, not as prod (1 + p + ... + p^{j-1}).
  * R_m is then formed by the paper's *defining* signed sum, and separately by
    Van Assche's positive expansion; the two are required to agree.
  * s_m(1) = (m!)^3 is checked against factorials directly.
  * The determinant is never computed symbolically.  At each of many exact
    integer bases p0 the integer Hankel matrix (s_{i+j+h}(p0)) is reduced by
    Bareiss fraction-free elimination, whose successive pivots are exactly the
    leading principal minors D_{1,h}(p0), ..., D_{N,h}(p0).

The connection to D_{N,h} is a proof, not a sample.  For each (N, h) let

    dmax(N, h) = max over permutations sigma of sum_i deg s_{i + sigma(i) + h},

computed here by brute-force enumeration of all N! permutations from the
*computed* degrees of s_m.  Then deg D_{N,h} <= dmax(N, h), and the stored
polynomial has degree <= dmax(N, h) as well.  Two polynomials of degree at most
dmax that agree at more than dmax distinct integers are equal in Z[p].  This
checker evaluates the stored list at dmax + 1 + margin distinct integer bases
and compares each value with the Bareiss determinant, so agreement certifies
the polynomial identity

    stored_{N,h}(p - 1) = D_{N,h}(p)   in  Z[p],

after which integrality, strict positivity, the degree and the coefficient
count are read off the stored list.

Run
---
    python3 computations/check_finite_coefficients.py

`--help` lists the options.  Exact integer arithmetic only; no floating point,
no external package, no network, no Lean, no subprocess.  Nothing is written.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import permutations
from math import factorial
from pathlib import Path
import argparse
import json
import re
import sys
import time

RECONSTRUCTED_ON = "2026-09-20"
INTEGER_TEXT = re.compile(r"^-?(0|[1-9][0-9]*)$")


class CheckFailure(Exception):
    """A checked property did not hold."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CheckFailure(message)


# --------------------------------------------------------------------------
# Minimal exact polynomial arithmetic over Z (lists of int, low term first).
# Deliberately plain: these are small polynomials, degree at most 660.
# --------------------------------------------------------------------------

def trim(a):
    while a and a[-1] == 0:
        a.pop()
    return a


def add(a, b):
    r = list(a) + [0] * max(0, len(b) - len(a))
    for i, x in enumerate(b):
        r[i] += x
    return trim(r)


def sub(a, b):
    r = list(a) + [0] * max(0, len(b) - len(a))
    for i, x in enumerate(b):
        r[i] -= x
    return trim(r)


def mul(a, b):
    if not a or not b:
        return []
    r = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                if bj:
                    r[i + j] += ai * bj
    return trim(r)


def exact_quotient(num, den):
    """num / den where den is monic and the division is exact over Z."""
    require(bool(den) and den[-1] == 1, "divisor must be monic")
    d = len(den) - 1
    if len(num) - 1 < d:
        require(not trim(list(num)), "inexact division: degree too small")
        return []
    q = [0] * (len(num) - d)
    rest = list(num)
    for i in range(len(num) - 1, d - 1, -1):
        c = rest[i]
        if c:
            q[i - d] = c
            for j in range(d):
                if den[j]:
                    rest[i - d + j] -= c * den[j]
        rest[i] = 0
    require(not trim(rest[:d]), "inexact division: nonzero remainder")
    return trim(q)


def pow_minus_one(j):
    """The polynomial p^j - 1."""
    f = [0] * (j + 1)
    f[j] = 1
    f[0] = -1
    return f


def evaluate(coefficients, x):
    acc = 0
    for c in reversed(coefficients):
        acc = acc * x + c
    return acc


# --------------------------------------------------------------------------
# The paper's moment polynomials, by a route the generator does not use
# --------------------------------------------------------------------------

def gaussian_by_product(n, k):
    """[n choose k]_p = prod_{i=1}^{k} (p^{n-k+i} - 1) / (p^i - 1), exactly."""
    if k < 0 or k > n:
        return []
    numerator = [1]
    denominator = [1]
    for i in range(1, k + 1):
        numerator = mul(numerator, pow_minus_one(n - k + i))
        denominator = mul(denominator, pow_minus_one(i))
    # prod (p^i - 1) is monic, so the quotient stays in Z[p].
    return exact_quotient(numerator, denominator)


def q_factorial_by_product(m):
    """[m]_p! = prod_{j=1}^{m} (p^j - 1) / (p - 1), exactly."""
    numerator = [1]
    denominator = [1]
    for j in range(1, m + 1):
        numerator = mul(numerator, pow_minus_one(j))
        denominator = mul(denominator, pow_minus_one(1))
    return exact_quotient(numerator, denominator)


def moment_polynomials(mmax, verbose=False):
    """s_0(p), ..., s_mmax(p), with the paper's internal identities checked."""
    binom = {}
    for n in range(2 * mmax + 1):
        for k in range(min(n, mmax) + 1):
            binom[(n, k)] = gaussian_by_product(n, k)
    out = []
    for m in range(mmax + 1):
        signed = []
        for k in range(m + 1):
            term = [0] * (k * (k + 1) // 2) + mul(binom[(m, k)], binom[(m + k, k)])
            signed = sub(signed, term) if (m + k) % 2 else add(signed, term)
        # Van Assche's positive expansion, core.tex:1822-1826.
        positive = []
        for k in range(m + 1):
            tail = [1]
            for j in range(m - k + 1, m + 1):
                tail = mul(tail, pow_minus_one(j))
            term = mul(mul(binom[(m, k)], binom[(m + k, k)]), tail)
            positive = add(positive, [0] * ((m - k) * (m - k + 1) // 2) + term)
        require(signed == positive,
                f"R_{m}: the defining signed sum and Van Assche's positive "
                f"expansion disagree")
        require(evaluate(signed, 1) == 1, f"R_{m}(1) is not 1")
        f = q_factorial_by_product(m)
        require(evaluate(f, 1) == factorial(m), f"[{m}]_1! is not {m}!")
        s = mul(mul(f, f), mul(f, signed))
        require(len(s) - 1 == 3 * m * m - m,
                f"deg s_{m} = {len(s) - 1}, expected 3m^2 - m = {3 * m * m - m}")
        require(s[-1] == 1, f"s_{m} is not monic")
        require(evaluate(s, 1) == factorial(m) ** 3, f"s_{m}(1) is not ({m}!)^3")
        out.append(s)
        if verbose:
            print(f"  s_{m}: degree {len(s) - 1}, monic, s({1}) = ({m}!)^3", flush=True)
    return out


# --------------------------------------------------------------------------
# Determinants at integer bases
# --------------------------------------------------------------------------

def bareiss_leading_minors(matrix, n):
    """Fraction-free elimination; pivot k is the (k+1)x(k+1) leading minor.

    Returns None if a pivot vanishes (the elimination cannot continue without
    a row swap, which would destroy the leading-minor readout).
    """
    a = [row[:] for row in matrix]
    previous = 1
    minors = []
    for k in range(n):
        pivot = a[k][k]
        if pivot == 0:
            return None
        minors.append(pivot)
        for i in range(k + 1, n):
            aik = a[i][k]
            row_i = a[i]
            row_k = a[k]
            for j in range(k + 1, n):
                row_i[j] = (row_i[j] * pivot - aik * row_k[j]) // previous
        previous = pivot
    return minors


def fraction_determinant(matrix, n):
    """Fallback for a vanishing pivot: rational elimination with row swaps."""
    a = [[Fraction(x) for x in row] for row in matrix]
    result = Fraction(1)
    for j in range(n):
        pivot = next((i for i in range(j, n) if a[i][j]), None)
        if pivot is None:
            return 0
        if pivot != j:
            a[pivot], a[j] = a[j], a[pivot]
            result = -result
        value = a[j][j]
        result *= value
        for i in range(j + 1, n):
            factor = a[i][j] / value
            for k in range(j + 1, n):
                a[i][k] -= factor * a[j][k]
    require(result.denominator == 1, "integer matrix produced a non-integer determinant")
    return result.numerator


def hankel_leading_minors(values, n, h):
    matrix = [[values[i + j + h] for j in range(n)] for i in range(n)]
    minors = bareiss_leading_minors(matrix, n)
    if minors is not None:
        return minors
    return [fraction_determinant([[values[i + j + h] for j in range(k)]
                                 for i in range(k)], k) for k in range(1, n + 1)]


def max_permutation_degree(degrees, n, h):
    """max over permutations sigma of sum_i deg s_{i + sigma(i) + h}.

    A rigorous upper bound for deg D_{N,h}, computed from the measured degrees
    rather than from the paper's closed form.
    """
    best = None
    for sigma in permutations(range(n)):
        total = sum(degrees[i + sigma[i] + h] for i in range(n))
        if best is None or total > best:
            best = total
    return 0 if best is None else best


def paper_degree(n, h):
    """The paper's closed form, core.tex:1887."""
    return sum(3 * (2 * i + h) ** 2 - (2 * i + h) for i in range(n))


# --------------------------------------------------------------------------
# Reading the stored certificate
# --------------------------------------------------------------------------

def load_certificates(path):
    payload = json.loads(Path(path).read_text())
    if isinstance(payload, dict) and "certificates" in payload:
        rows = payload["certificates"]
        stored = {}
        for row in rows:
            texts = row["coefficients_low_to_high"]
            for text in texts:
                require(bool(INTEGER_TEXT.match(text)),
                        f"coefficient {text!r} is not a plain decimal integer")
            stored[(int(row["rank"]), int(row["shift"]))] = [int(x) for x in texts]
        return stored, payload
    raise CheckFailure(f"{path}: not a finite-coefficient certificate file")


def load_split_certificates(directory, max_rank):
    """The sixteen per-rank files, for the optional cross-comparison."""
    stored = {}
    for h in (0, 1):
        for n in range(1, max_rank + 1):
            path = Path(directory) / f"s_hankel_rank{n}_shift{h}.json"
            if not path.exists():
                return None
            texts = json.loads(path.read_text())["coefficients_low_to_high"]
            stored[(n, h)] = [int(x) for x in texts]
    return stored


# --------------------------------------------------------------------------
# Driver
# --------------------------------------------------------------------------

def run(path, max_rank, margin, compare_split, verbose=True):
    started = time.time()
    stored, payload = load_certificates(path)
    ranks = sorted({n for (n, _) in stored})
    max_rank = min(max_rank, max(ranks))

    if verbose:
        print(f"Moment polynomials s_0 .. s_{2 * max_rank - 1} "
              f"(product-formula Gaussian binomials)", flush=True)
    s = moment_polynomials(2 * max_rank - 1)
    degrees = [len(x) - 1 for x in s]
    if verbose:
        print(f"  degrees {degrees}", flush=True)

    bounds = {}
    for h in (0, 1):
        for n in range(1, max_rank + 1):
            bound = max_permutation_degree(degrees, n, h)
            require(bound == paper_degree(n, h),
                    f"permutation degree bound for D_{{{n},{h}}} is {bound}, "
                    f"the paper's closed form gives {paper_degree(n, h)}")
            bounds[(n, h)] = bound
    if verbose:
        print("  permutation degree bounds agree with the paper's closed form",
              flush=True)

    needed = max(bounds.values()) + 1 + margin
    bases = list(range(1, needed + 1))
    if verbose:
        print(f"Evaluating at {len(bases)} exact integer bases "
              f"p = 1 .. {bases[-1]}", flush=True)

    # Bareiss at every base gives all leading principal minors, both shifts.
    computed = {(n, h): [] for h in (0, 1) for n in range(1, max_rank + 1)}
    fallbacks = 0
    for index, base in enumerate(bases):
        values = [evaluate(x, base) for x in s]
        for h in (0, 1):
            matrix = [[values[i + j + h] for j in range(max_rank)]
                      for i in range(max_rank)]
            minors = bareiss_leading_minors(matrix, max_rank)
            if minors is None:
                fallbacks += 1
                minors = hankel_leading_minors(values, max_rank, h)
            for n in range(1, max_rank + 1):
                computed[(n, h)].append(minors[n - 1])
        if verbose and (index + 1) % 250 == 0:
            print(f"  {index + 1}/{len(bases)} bases, "
                  f"{round(time.time() - started, 1)}s", flush=True)

    split = load_split_certificates(Path(path).resolve().parent / "certificates",
                                    max_rank) if compare_split else None

    rows = []
    total = 0
    for h in (0, 1):
        for n in range(1, max_rank + 1):
            require((n, h) in stored, f"no stored certificate for N={n}, h={h}")
            poly = stored[(n, h)]
            bound = bounds[(n, h)]
            require(bool(poly), f"D_{{{n},{h}}}: empty coefficient list")
            require(len(poly) - 1 <= bound,
                    f"D_{{{n},{h}}}: stored degree {len(poly) - 1} exceeds the "
                    f"permutation bound {bound}")
            points = bound + 1 + margin
            mismatch = None
            for base, value in zip(bases[:points], computed[(n, h)][:points]):
                if evaluate(poly, base - 1) != value:
                    mismatch = base
                    break
            require(mismatch is None,
                    f"D_{{{n},{h}}}: stored polynomial and the Bareiss "
                    f"determinant differ at p = {mismatch}")
            # Both sides have degree <= bound and agree at points > bound
            # distinct integers, so they are equal in Z[p].
            low = min(poly)
            require(len(poly) - 1 == bound,
                    f"D_{{{n},{h}}}: degree {len(poly) - 1}, expected {bound}")
            require(poly[-1] == 1, f"D_{{{n},{h}}}: leading coefficient "
                                   f"{poly[-1]}, expected 1")
            require(low > 0, f"D_{{{n},{h}}}: minimum coefficient {low} is not "
                             f"strictly positive")
            total += len(poly)
            row = {
                "rank": n,
                "shift": h,
                "degree": len(poly) - 1,
                "degree_bound_from_permutations": bound,
                "coefficient_count": len(poly),
                "minimum_coefficient": str(low),
                "leading_coefficient": str(poly[-1]),
                "value_at_p_equals_one": str(poly[0]),
                "integer_bases_compared": points,
                "identity_certified_in_Z_p": True,
            }
            if split is not None:
                row["matches_split_certificate_files"] = (split[(n, h)] == poly)
                require(row["matches_split_certificate_files"],
                        f"D_{{{n},{h}}}: disagrees with "
                        f"certificates/s_hankel_rank{n}_shift{h}.json")
            rows.append(row)
            if verbose:
                print(f"  D_{{{n},{h}}}: degree {len(poly) - 1}, "
                      f"{len(poly)} coefficients, min {low}, "
                      f"{points} bases compared", flush=True)

    # Independent value at the polynomial endpoint: D_{N,h}(1) = det(((i+j+h)!)^3).
    for h in (0, 1):
        for n in range(1, max_rank + 1):
            direct = fraction_determinant(
                [[factorial(i + j + h) ** 3 for j in range(n)] for i in range(n)], n)
            require(direct == stored[(n, h)][0],
                    f"D_{{{n},{h}}}(1) = {stored[(n, h)][0]} does not match "
                    f"det(((i+j+h)!)^3) = {direct}")
    if verbose:
        print("  endpoint values match det(((i+j+h)!)^3) at p = 1", flush=True)

    return {
        "schema": "finite_coefficient_independent_check_v1",
        "reconstructed_on": RECONSTRUCTED_ON,
        "input": str(Path(path).resolve()),
        "max_rank": max_rank,
        "shifts": [0, 1],
        "certificate_count": len(rows),
        "total_coefficients": total,
        "total_coefficients_expected_by_paper": 8824 if max_rank == 8 else None,
        "all_coefficients_strictly_positive": True,
        "all_leading_coefficients_one": True,
        "degrees_match_paper_closed_form": True,
        "polynomial_identity_method": (
            "exact integer evaluation at more distinct bases than the "
            "permutation degree bound, against Bareiss fraction-free "
            "elimination of the integer Hankel matrix"
        ),
        "bareiss_pivot_fallbacks": fallbacks,
        "compared_against_split_certificate_files": split is not None,
        "floating_point_used_for_mathematics": False,
        "lean_run": False,
        "python": sys.version,
        "seconds": round(time.time() - started, 3),
        "certificates": rows,
        "scope": (
            "This certifies the sixteen finite determinant identities and the "
            "strict coefficient positivity they assert. It is a finite "
            "computer-algebra certificate, not a Lean theorem and not an "
            "all-rank positivity result."
        ),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--input", type=Path,
                        default=Path(__file__).resolve().parent / "finite_coefficients.json",
                        help="certificate JSON to check (default: the path the paper cites)")
    parser.add_argument("--max-rank", type=int, default=8,
                        help="largest Hankel rank to check (default 8)")
    parser.add_argument("--margin", type=int, default=8,
                        help="extra evaluation bases beyond the degree bound (default 8)")
    parser.add_argument("--no-split-comparison", action="store_true",
                        help="skip the comparison with certificates/s_hankel_rank*.json")
    parser.add_argument("--json", action="store_true",
                        help="print the machine-readable summary instead of a table")
    parser.add_argument("--quiet", action="store_true", help="suppress progress lines")
    args = parser.parse_args()

    if not 1 <= args.max_rank <= 10:
        parser.error("rank must be in 1,...,10")
    if args.margin < 0:
        parser.error("margin must be non-negative")

    try:
        summary = run(args.input, args.max_rank, args.margin,
                      not args.no_split_comparison,
                      verbose=not (args.quiet or args.json))
    except CheckFailure as failure:
        print(f"CHECK FAILED: {failure}", file=sys.stderr)
        return 1

    if args.json:
        print(json.dumps(summary, indent=2))
    else:
        print(f"{summary['certificate_count']} certificates checked, "
              f"{summary['total_coefficients']} coefficients, all strictly positive.")
        print(f"Every stored polynomial is proved equal to D_"
              f"{{N,h}}(1+t) in Z[t] by exact integer evaluation.")
        print(f"{summary['seconds']}s")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
