#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Generate the sixteen finite coefficient-moment determinant certificates.

RECONSTRUCTION NOTE
-------------------
This file is a NEW artefact, written on 2026-09-20.  It was reconstructed from
the mathematical definitions in the #1049 reasoning paper
(paper/reasoning-parts/erdos1049/core.tex, "Coefficient moments and cyclotomic
content", lines 1790-1896) and from the Lean declarations in
lean/ErdosProblems/Erdos1049/PaperR20/CoefficientPencil.lean
(coefficientRPoly, coefficientQFactorialPoly, coefficientMomentPoly,
coefficientHankelDetPoly).  It is not a recovered copy of an earlier script.

The paper cites two paths that do not exist:

    computations/finite_coefficients.json
    computations/check_finite_coefficients.py

Verified here by `git log --all` over both paths, which is empty, and by a
pickaxe search whose only hits are the commits that introduced the citing
prose.  An earlier pass reported the same absence across every checkout.

The *data* those paths describe is nevertheless present in this tree, split
across sixteen files computations/certificates/s_hankel_rank<N>_shift<h>.json
written by computations/reproduce.py.  So what was missing is the two cited
filenames, not the computation.  This script regenerates the coefficient lists
from scratch by two independent division-free / division-checked routes and
writes them to the single aggregated path the paper actually cites.

Definitions used (paper display at core.tex:1795-1802, 1848)
------------------------------------------------------------
    [m]_p!   = prod_{j=1}^{m} (1 + p + ... + p^{j-1})
    R_m(p)   = sum_{k=0}^{m} (-1)^{m+k} p^{k(k+1)/2} [m choose k]_p [m+k choose k]_p
    s_m(p)   = ([m]_p!)^3 R_m(p)
    D_{N,h}(p) = det( s_{i+j+h}(p) )_{0 <= i,j < N},      D_{0,h} = 1

with [n choose k]_p the Gaussian binomial polynomial, here by the q-Pascal
recursion [n choose k]_p = [n-1 choose k]_p + p^{n-k} [n-1 choose k-1]_p,
which is Lean's `gaussBinom` (QBinomialUnitIdentity.lean:70-76) verbatim.
The certificate variable is t = p - 1, matching the Lean certificate consumer
`coefficientHankelDet_pos_of_certificate`, whose hypotheses are about the
coefficients of `(coefficientHankelDetPoly N h).comp (X + 1)`.

Arithmetic
----------
Exact integers only.  No floating point anywhere, no rationals, no external
package: polynomials are Python lists of `int`, low coefficient first.  Large
polynomial products use Kronecker substitution (pack the coefficients into one
big integer at a base 2^B wide enough that no block can overflow or borrow,
multiply once, unpack), which is exact by construction.

Two independent determinant routes are run and required to agree:

  laplace       division-free Laplace expansion over column subsets.  One
                dynamic programme per shift computes every leading principal
                minor D_{1,h}, ..., D_{N,h} at once, using only polynomial
                multiplication and addition.  No division is performed, so no
                exactness assumption is needed anywhere.

  condensation  the paper's own route: Desnanot-Jacobi (Dodgson) condensation
                D_{N,h} = (D_{N-1,h} D_{N-1,h+2} - D_{N-1,h+1}^2) / D_{N-2,h+2},
                with every division carried out as an exact division by a monic
                divisor and the remainder asserted to be zero, as the paper
                states ("The computation checks that every division has zero
                remainder").

Run
---
    python3 computations/finite_coefficients_generate.py \
        --output computations/finite_coefficients.json

`--help` lists the options.  The script refuses to overwrite an existing output
file unless --force is given.  No network, no Lean, no subprocess.
"""

from __future__ import annotations

from pathlib import Path
import argparse
import json
import sys
import time

RECONSTRUCTED_ON = "2026-09-20"


def require(condition: bool, message: str) -> None:
    """Contract check that stays active under `python -O`."""
    if not condition:
        raise ArithmeticError(message)


# --------------------------------------------------------------------------
# Exact polynomial arithmetic over Z.  A polynomial is a list of ints, low
# coefficient first, with no trailing zeros.  The zero polynomial is [].
# --------------------------------------------------------------------------

def trim(a: list[int]) -> list[int]:
    while a and a[-1] == 0:
        a.pop()
    return a


def maxbits(a: list[int]) -> int:
    best = 0
    for x in a:
        b = x.bit_length()
        if b > best:
            best = b
    return best


def padd(a: list[int], b: list[int]) -> list[int]:
    if len(a) < len(b):
        a, b = b, a
    r = list(a)
    for i, x in enumerate(b):
        r[i] += x
    return trim(r)


def psub(a: list[int], b: list[int]) -> list[int]:
    r = list(a) + [0] * max(0, len(b) - len(a))
    for i, x in enumerate(b):
        r[i] -= x
    return trim(r)


def pneg(a: list[int]) -> list[int]:
    return [-x for x in a]


def _pack(a: list[int], width: int, half: int) -> int:
    """Kronecker pack: return sum_i a_i * 2^(8*width), via a balanced offset.

    Every coefficient is stored as a_i + half in its own `width`-byte block,
    which is a value in [0, 2^(8*width)) exactly when |a_i| < half.  The whole
    offset is then subtracted back off in one big-integer operation.
    """
    buf = bytearray(width * len(a))
    for i, c in enumerate(a):
        buf[i * width:(i + 1) * width] = (c + half).to_bytes(width, "little")
    offset = int.from_bytes((b"\x00" * (width - 1) + b"\x80") * len(a), "little")
    return int.from_bytes(bytes(buf), "little") - offset


def _unpack(value: int, width: int, half: int, length: int) -> list[int]:
    offset = int.from_bytes((b"\x00" * (width - 1) + b"\x80") * length, "little")
    shifted = value + offset
    require(0 <= shifted < 1 << (8 * width * length), "Kronecker block overflow")
    raw = shifted.to_bytes(width * length, "little")
    return [
        int.from_bytes(raw[i * width:(i + 1) * width], "little") - half
        for i in range(length)
    ]


SCHOOLBOOK_CUTOFF = 24


def pmul(a: list[int], b: list[int]) -> list[int]:
    """Exact product.  Schoolbook for short inputs, Kronecker otherwise."""
    if not a or not b:
        return []
    n, m = len(a), len(b)
    if min(n, m) <= SCHOOLBOOK_CUTOFF:
        res = [0] * (n + m - 1)
        for i, ai in enumerate(a):
            if ai:
                for j, bj in enumerate(b):
                    if bj:
                        res[i + j] += ai * bj
        return trim(res)
    # |product coefficient| < min(n, m) * max|a| * max|b|, so this block width
    # cannot overflow; the +2 covers the sign bit and the strictness.
    bits = maxbits(a) + maxbits(b) + min(n, m).bit_length() + 2
    width = (bits + 7) // 8
    half = 1 << (8 * width - 1)
    product = _pack(a, width, half) * _pack(b, width, half)
    return trim(_unpack(product, width, half, n + m - 1))


def pdivmod_monic(num: list[int], den: list[int]) -> tuple[list[int], list[int]]:
    """Divide by a monic divisor.  Exact over Z; returns (quotient, remainder)."""
    require(bool(den), "division by the zero polynomial")
    d = len(den) - 1
    require(den[d] == 1, "divisor is not monic; exactness over Z is not assured")
    if len(num) - 1 < d:
        return [], trim(list(num))
    quotient = [0] * (len(num) - d)
    rest = list(num)
    tail = [(j, den[j]) for j in range(d) if den[j]]
    for i in range(len(num) - 1, d - 1, -1):
        c = rest[i]
        if c:
            quotient[i - d] = c
            base = i - d
            for j, dj in tail:
                rest[base + j] -= c * dj
        rest[i] = 0
    return trim(quotient), trim(rest)


def taylor_shift_one(a: list[int]) -> list[int]:
    """Return the coefficients of a(1 + t) given the coefficients of a(p)."""
    n = len(a)
    c = list(a)
    for i in range(n - 1):
        for j in range(n - 2, i - 1, -1):
            c[j] += c[j + 1]
    return trim(c)


def peval(a: list[int], x: int) -> int:
    acc = 0
    for c in reversed(a):
        acc = acc * x + c
    return acc


# --------------------------------------------------------------------------
# The paper's polynomials
# --------------------------------------------------------------------------

def gaussian_table(nmax: int, kmax: int) -> list[list[list[int]]]:
    """[n choose k]_p for 0 <= n <= nmax, 0 <= k <= kmax, by q-Pascal."""
    table: list[list[list[int]]] = [[[] for _ in range(kmax + 1)] for _ in range(nmax + 1)]
    for n in range(nmax + 1):
        for k in range(kmax + 1):
            if k > n:
                table[n][k] = []
            elif k == 0 or k == n:
                table[n][k] = [1]
            else:
                table[n][k] = padd(table[n - 1][k], [0] * (n - k) + table[n - 1][k - 1])
    return table


def signed_diagonal(m: int, table) -> list[int]:
    """R_m(p), the paper's signed Gaussian-binomial sum (Lean coefficientRPoly)."""
    total: list[int] = []
    for k in range(m + 1):
        term = [0] * (k * (k + 1) // 2) + pmul(table[m][k], table[m + k][k])
        total = padd(total, pneg(term) if (m + k) % 2 else term)
    return total


def positive_diagonal(m: int, table) -> list[int]:
    """Van Assche's positive expansion of R_m (core.tex:1822-1826).

    R_m = sum_k [m,k]_p [m+k,k]_p p^{(m-k)(m-k+1)/2} prod_{j=m-k+1}^{m} (p^j - 1).
    Used only as a cross-check of `signed_diagonal`; it is not the definition.
    """
    total: list[int] = []
    for k in range(m + 1):
        tail = [1]
        for j in range(m - k + 1, m + 1):
            factor = [0] * (j + 1)
            factor[j] = 1
            factor[0] = -1
            tail = pmul(tail, factor)
        term = pmul(pmul(table[m][k], table[m + k][k]), tail)
        total = padd(total, [0] * ((m - k) * (m - k + 1) // 2) + term)
    return total


def q_factorial(m: int) -> list[int]:
    """[m]_p! = prod_{j=1}^{m} (1 + p + ... + p^{j-1}) (Lean coefficientQFactorialPoly)."""
    f = [1]
    for j in range(1, m + 1):
        f = pmul(f, [1] * j)
    return f


def moment_polynomials(mmax: int, verbose: bool = False) -> list[list[int]]:
    """s_0(p), ..., s_mmax(p) as exact integer polynomials in p."""
    table = gaussian_table(2 * mmax, mmax)
    out = []
    for m in range(mmax + 1):
        r = signed_diagonal(m, table)
        require(r == positive_diagonal(m, table),
                f"signed and positive expansions of R_{m} disagree")
        f = q_factorial(m)
        s = pmul(pmul(f, pmul(f, f)), r)
        require(len(s) - 1 == 3 * m * m - m, f"deg s_{m} is not 3m^2 - m")
        require(s[-1] == 1, f"s_{m} is not monic")
        out.append(s)
        if verbose:
            print(f"  s_{m}: degree {len(s) - 1}", flush=True)
    return out


# --------------------------------------------------------------------------
# Determinants
# --------------------------------------------------------------------------

def laplace_leading_minors(s: list[list[int]], n: int, h: int) -> list[list[int]]:
    """All leading principal minors D_{1,h}, ..., D_{n,h}, division-free.

    f[S] is the determinant of the submatrix on rows 0..|S|-1 and the columns
    in S (ascending).  Expanding along the last row gives
        f[S] = sum_{j in S} (-1)^{(|S|-1)+rank_S(j)} s_{(|S|-1)+j+h} f[S \\ {j}],
    and f[{0,...,N-1}] is exactly D_{N,h}.
    """
    level = {0: [1]}
    minors = []
    for k in range(1, n + 1):
        nxt: dict[int, list[int]] = {}
        for subset, value in level.items():
            for j in range(n):
                bit = 1 << j
                if subset & bit:
                    continue
                term = pmul(s[(k - 1) + j + h], value)
                if ((k - 1) + bin(subset & (bit - 1)).count("1")) % 2:
                    term = pneg(term)
                key = subset | bit
                nxt[key] = padd(nxt.get(key, []), term)
        level = nxt
        minors.append(level[(1 << k) - 1])
    return minors


def condensation_minors(s: list[list[int]], n: int, verbose: bool = False):
    """The paper's Desnanot-Jacobi route; every division is checked exact."""
    # D_{N,h} at shift h needs D_{N-1,h+2} and D_{N-2,h+2}, so the base row
    # reaches shift 2n - 1, which is exactly the last available moment.
    hmax = 2 * n - 1
    d: dict[tuple[int, int], list[int]] = {}
    for h in range(hmax + 1):
        d[(0, h)] = [1]
        d[(1, h)] = s[h]
    divisions = 0
    for rank in range(2, n + 1):
        for h in range(0, 2 + 2 * (n - rank)):
            numerator = psub(
                pmul(d[(rank - 1, h)], d[(rank - 1, h + 2)]),
                pmul(d[(rank - 1, h + 1)], d[(rank - 1, h + 1)]),
            )
            quotient, remainder = pdivmod_monic(numerator, d[(rank - 2, h + 2)])
            require(remainder == [],
                    f"Desnanot-Jacobi division left a remainder at N={rank}, h={h}")
            divisions += 1
            d[(rank, h)] = quotient
        if verbose:
            print(f"  condensation level {rank} complete", flush=True)
    return d, divisions


# --------------------------------------------------------------------------
# Driver
# --------------------------------------------------------------------------

def expected_degree(n: int, h: int) -> int:
    """The paper's all-rank degree formula (core.tex:1887)."""
    return sum(3 * (2 * i + h) ** 2 - (2 * i + h) for i in range(n))


def build(max_rank: int, method: str, verbose: bool = True) -> dict:
    started = time.time()
    if verbose:
        print(f"Coefficient moments s_0 .. s_{2 * max_rank - 1}", flush=True)
    s_p = moment_polynomials(2 * max_rank - 1)
    s_t = [taylor_shift_one(x) for x in s_p]
    if verbose:
        print(f"  moments ready, {round(time.time() - started, 2)}s", flush=True)

    results: dict[tuple[int, int], list[int]] = {}
    timings: dict[str, float] = {}
    divisions = 0

    if method in ("laplace", "both"):
        mark = time.time()
        for h in (0, 1):
            for n, poly in enumerate(laplace_leading_minors(s_t, max_rank, h), start=1):
                results[(n, h)] = poly
            if verbose:
                print(f"  Laplace expansion, shift {h}, "
                      f"{round(time.time() - mark, 2)}s", flush=True)
        timings["laplace_seconds"] = time.time() - mark

    if method in ("condensation", "both"):
        mark = time.time()
        table, divisions = condensation_minors(s_t, max_rank, verbose=verbose)
        timings["condensation_seconds"] = time.time() - mark
        for h in (0, 1):
            for n in range(1, max_rank + 1):
                got = table[(n, h)]
                if method == "both":
                    require(results[(n, h)] == got,
                            f"the two determinant routes disagree at N={n}, h={h}")
                else:
                    results[(n, h)] = got

    certificates = []
    total = 0
    for h in (0, 1):
        for n in range(1, max_rank + 1):
            poly = results[(n, h)]
            degree = len(poly) - 1
            require(degree == expected_degree(n, h),
                    f"degree of D_{{{n},{h}}} is {degree}, "
                    f"the paper's formula gives {expected_degree(n, h)}")
            require(poly[-1] == 1, f"D_{{{n},{h}}} is not monic")
            low = min(poly)
            total += len(poly)
            certificates.append({
                "rank": n,
                "shift": h,
                "degree": degree,
                "coefficient_count": len(poly),
                "leading_coefficient": str(poly[-1]),
                "minimum_coefficient": str(low),
                "value_at_p_equals_one": str(poly[0]),
                "all_coefficients_strictly_positive": low > 0,
                "coefficients_low_to_high": [str(c) for c in poly],
            })

    # Normalisation spot check, the paper's own (core.tex:1872-1874): direct
    # integer Hankel determinants at small integer bases, by a third route
    # (plain cofactor expansion over Z), against evaluations of the polynomials.
    def integer_det(matrix):
        size = len(matrix)
        if size == 0:
            return 1
        if size == 1:
            return matrix[0][0]
        acc = 0
        for j in range(size):
            minor = [row[:j] + row[j + 1:] for row in matrix[1:]]
            acc += (-1) ** j * matrix[0][j] * integer_det(minor)
        return acc

    spot = []
    for base in (1, 2, 3, 5, 11):
        values = [peval(x, base) for x in s_p]
        for h in (0, 1):
            for n in range(1, min(max_rank, 6) + 1):
                direct = integer_det([[values[i + j + h] for j in range(n)]
                                      for i in range(n)])
                require(direct == peval(results[(n, h)], base - 1),
                        f"evaluation mismatch at p={base}, N={n}, h={h}")
        spot.append(base)
    if verbose:
        print(f"  normalisation spot checks at p in {spot}", flush=True)

    payload = {
        "schema": "finite_coefficient_moment_certificates_v1",
        "reconstruction": {
            "reconstructed_on": RECONSTRUCTED_ON,
            "status": "newly reconstructed artefact, not a recovered original",
            "reason": (
                "The paper cites computations/finite_coefficients.json and "
                "computations/check_finite_coefficients.py. Neither path exists "
                "in the working tree, and git log --all over both paths is "
                "empty. This file was regenerated from the definitions in "
                "paper/reasoning-parts/erdos1049/core.tex and in "
                "lean/ErdosProblems/Erdos1049/PaperR20/CoefficientPencil.lean."
            ),
            "existing_equivalent_data": (
                "computations/certificates/s_hankel_rank<N>_shift<h>.json hold "
                "the same sixteen coefficient lists, written by "
                "computations/reproduce.py through SymPy. The missing thing was "
                "the two cited filenames, not the computation."
            ),
            "generator": "computations/finite_coefficients_generate.py",
            "checker": "computations/check_finite_coefficients.py",
        },
        "variable": "t = p - 1",
        "definition": {
            "gaussian_binomial": "q-Pascal recursion in the base p",
            "q_factorial": "[m]_p! = prod_{j=1}^{m} (1 + p + ... + p^{j-1})",
            "R_m": ("sum_{k=0}^{m} (-1)^{m+k} p^{k(k+1)/2} "
                    "[m choose k]_p [m+k choose k]_p"),
            "s_m": "([m]_p!)^3 R_m(p)",
            "D_N_h": "det( s_{i+j+h}(p) )_{0 <= i,j < N}, with D_{0,h} = 1",
            "lean_declarations": [
                "ErdosProblems.Erdos1049.PaperR20.coefficientRPoly",
                "ErdosProblems.Erdos1049.PaperR20.coefficientQFactorialPoly",
                "ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly",
                "ErdosProblems.Erdos1049.PaperR20.coefficientHankelDetPoly",
            ],
        },
        "max_rank": max_rank,
        "shifts": [0, 1],
        "method": method,
        "methods_run": sorted(timings),
        "exact_divisions_checked_zero_remainder": divisions,
        "normalisation_spot_check_bases": spot,
        "total_coefficients": total,
        "all_coefficients_strictly_positive":
            all(c["all_coefficients_strictly_positive"] for c in certificates),
        "floating_point_used_for_mathematics": False,
        "lean_run": False,
        "python": sys.version,
        "seconds": round(time.time() - started, 3),
        "certificates": certificates,
    }
    payload.update({k: round(v, 3) for k, v in timings.items()})
    return payload


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parent / "finite_coefficients.json",
                        help="destination JSON (default: the path the paper cites)")
    parser.add_argument("--max-rank", type=int, default=8,
                        help="largest Hankel rank N to certify (default 8)")
    parser.add_argument("--method", choices=("laplace", "condensation", "both"),
                        default="both",
                        help="determinant route; 'both' requires the two to agree")
    parser.add_argument("--force", action="store_true",
                        help="overwrite an existing output file")
    parser.add_argument("--quiet", action="store_true", help="suppress progress lines")
    args = parser.parse_args()

    if not 1 <= args.max_rank <= 10:
        parser.error("rank must be in 1,...,10")
    out = args.output.resolve()
    if out.exists() and not args.force:
        parser.error(f"refusing to overwrite {out}; pass --force")

    payload = build(args.max_rank, args.method, verbose=not args.quiet)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2) + "\n")

    print(f"Wrote {out}")
    print(f"  {len(payload['certificates'])} certificates, "
          f"{payload['total_coefficients']} coefficients, "
          f"all strictly positive: {payload['all_coefficients_strictly_positive']}")
    print(f"  {payload['seconds']}s total")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
