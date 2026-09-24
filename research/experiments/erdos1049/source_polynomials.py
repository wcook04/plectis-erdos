#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Reconstruct Zudilin's cancelled polynomials U_n, V_n in Z[X] for n = 1..4.

For the direction (14,12,14;27) the long Erdos 1049 paper (subsection 'The
polynomial forms and their common factors') displays

    a0 = 14n+1, a1 = 12n+1, a2 = 14n+1, beta = 27n+2, N = 15n,
    M = 266n^2 + 34n + 1,
    c_k(X) = (-1)^(a1+a2+k+1) X^(e_k) [k-1, a1-1]_X [beta-a2-1, beta-k-1]_X,
    e_k = a1(a1-1)/2 - (beta-a2)(beta-a2-1)/2 + (beta-k)(beta-k-1)/2,
    A_n = sum_{k=a2}^{beta-1} c_k X^(a0 k),
    B_n = sum_k c_k X^(a0 k) ( sum_{l=1}^{k-a1} 1/(X^l - 1)
                               + sum_{j=1}^{a0-1} X^(-j(k-a1)) / (X^j - 1) ),
    D_N = prod_{l<=N} Phi_l,   Omega_n = prod_{2<=l<=N} Phi_l^omega(n/l),
    U_n = X^-M (D_N/Omega_n) A_n,   V_n = X^-M (D_N/Omega_n) B_n.

This program builds A_n and D_N B_n as exact integer Laurent polynomials
(each D_N/(X^l - 1) is a polynomial because l <= N), divides D_N A_n and
D_N B_n by Omega_n and then by X^M, and requires zero remainder at every step.
It then checks:

  * the exact degrees K_n = deg A_n, W_n = deg U_n, deg D_N, deg Omega_n
    against the printed table, deg V_n = W_n - 1, and leading coefficients
    (-1)^n for both U_n and V_n;
  * with F(1/q) = sum_{j>=1} tau(j) q^j expanded independently from the divisor
    function, that U_n(1/q) F(1/q) - V_n(1/q) has no coefficient below q^(K_n-W_n)
    and that its next twelve coefficients agree with the positive source
    expression q^M (D_N/Omega_n)(1/q) H_n(1/q), H_n being Zudilin's series;
  * exact rational evaluation at 31/4, 3 and 7/2: b^W_n U_n(a/b) and
    b^W_n V_n(a/b) are integers, U_n(a/b) has reduced denominator exactly b^W_n,
    V_n(a/b) has reduced denominator exactly b^(W_n - 1), so b^(W_n - 1) does
    not clear U_n(a/b) at the two noninteger bases.

All arithmetic is on Python integers and fractions; no floating point and no
Lean kernel.  The Gaussian binomials are built from their cyclotomic
factorisation and cross-checked against the product definition at X = 1, 2, 3.
The computation covers n = 1, 2, 3, 4 only and proves no statement for other
indices.  The historical high-precision real evaluations of the remainder are
not part of this program.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from fractions import Fraction
from math import comb, gcd
from pathlib import Path

sys.set_int_max_str_digits(0)

SCHEMA = "erdos1049-public-computation/1"
PROGRAM = "source_polynomials.py"
PRINTED_TABLE = {
    1: {"K": 587, "W": 333, "deg_D": 72, "deg_Omega": 25},
    2: {"K": 2264, "W": 1315, "deg_D": 278, "deg_Omega": 94},
    3: {"K": 5032, "W": 2944, "deg_D": 628, "deg_Omega": 219},
    4: {"K": 8891, "W": 5220, "deg_D": 1102, "deg_Omega": 380},
}
SERIES_CHECK_TERMS = 12
BASES = [(31, 4), (3, 1), (7, 2)]
# Coefficient lists are stored in the result when their JSON is at most this size
# (all four indices fit; the n = 4 lists take about 0.4 MB).
STORE_LIMIT_BYTES = 1_000_000

Poly = list  # integer coefficients, lowest degree first


# ------------------------------------------------------- integer polynomials
def trim(p: Poly) -> Poly:
    while p and p[-1] == 0:
        p.pop()
    return p


def padd_into(acc: Poly, p: Poly, shift: int = 0) -> None:
    if len(acc) < len(p) + shift:
        acc.extend([0] * (len(p) + shift - len(acc)))
    for i, c in enumerate(p):
        if c:
            acc[i + shift] += c


def _bias(count: int, width: int) -> int:
    return int.from_bytes((b"\x00" * (width - 1) + b"\x80") * count, "little")


def pmul(p: Poly, q: Poly) -> Poly:
    """Exact product by Kronecker substitution with balanced base-2^(8*width) digits."""

    if not p or not q:
        return []
    bound = min(len(p), len(q)) * max(abs(c) for c in p) * max(abs(c) for c in q)
    width = (bound.bit_length() + 2) // 8 + 1
    half = 1 << (8 * width - 1)

    def pack(r: Poly) -> int:
        data = b"".join((c + half).to_bytes(width, "little") for c in r)
        return int.from_bytes(data, "little") - _bias(len(r), width)

    n = len(p) + len(q) - 1
    value = pack(p) * pack(q) + _bias(n, width)
    data = value.to_bytes(n * width, "little")
    return trim([int.from_bytes(data[i * width:(i + 1) * width], "little") - half for i in range(n)])


def pprod(polys: list[Poly]) -> Poly:
    if not polys:
        return [1]
    while len(polys) > 1:
        polys = [pmul(polys[i], polys[i + 1]) if i + 1 < len(polys) else polys[i]
                 for i in range(0, len(polys), 2)]
    return polys[0]


def pdivmod_monic(p: Poly, q: Poly) -> tuple[Poly, Poly]:
    """Divide by a monic polynomial; return quotient and remainder."""

    if q[-1] != 1:
        raise ValueError("divisor must be monic")
    r = list(p)
    dq = len(q) - 1
    if len(r) - 1 < dq:
        return [], trim(r)
    quotient = [0] * (len(r) - dq)
    nonzero = [(j, c) for j, c in enumerate(q[:-1]) if c]
    for i in range(len(r) - 1, dq - 1, -1):
        c = r[i]
        if c:
            quotient[i - dq] = c
            base = i - dq
            for j, qc in nonzero:
                r[base + j] -= c * qc
            r[i] = 0
    return trim(quotient), trim(r[:dq])


def pexact_div(p: Poly, q: Poly, what: str) -> Poly:
    quotient, remainder = pdivmod_monic(p, q)
    if remainder:
        raise ArithmeticError(f"nonzero remainder in {what}")
    return quotient


def peval_hom(p: Poly, a: int, b: int) -> int:
    """Return b^deg(p) p(a/b) as an integer (homogenised Horner scheme)."""

    value = 0
    for i, c in enumerate(reversed(p)):
        value = value * a + c * b**i
    return value


# ---------------------------------------------------------- building blocks
_CYCLO: dict[int, Poly] = {}


def cyclotomic(l: int) -> Poly:
    if l not in _CYCLO:
        p = [-1] + [0] * (l - 1) + [1]
        for d in range(1, l):
            if l % d == 0:
                p = pexact_div(p, cyclotomic(d), f"X^{l}-1 by Phi_{d}")
        _CYCLO[l] = p
    return _CYCLO[l]


def phi_count(l: int) -> int:
    return len(cyclotomic(l)) - 1


_GAUSS: dict[tuple[int, int], Poly] = {}


def gaussian(m: int, r: int) -> Poly:
    """[m, r]_X via its factorisation into Phi_l, l | exponent pattern."""

    if not 0 <= r <= m:
        raise ValueError("Gaussian binomial needs 0 <= r <= m")
    key = (m, r)
    if key not in _GAUSS:
        factors = [cyclotomic(l) for l in range(2, m + 1) if m // l - r // l - (m - r) // l == 1]
        g = pprod(factors)
        if len(g) - 1 != r * (m - r) or sum(g) != comb(m, r):
            raise ArithmeticError("Gaussian binomial degree or value at 1 is wrong")
        for x in (2, 3):
            num = den = 1
            for j in range(1, r + 1):
                num *= 1 - x ** (m - r + j)
                den *= 1 - x**j
            if num % den or peval_hom(g, x, 1) != num // den:
                raise ArithmeticError("Gaussian binomial disagrees with its product formula")
        _GAUSS[key] = g
    return _GAUSS[key]


def omega(num: int, den: int) -> int:
    """Zudilin's weight at num/den for the direction (14,12,14;27)."""

    def fl(c: int) -> int:
        return (c * num) // den

    return max(0, fl(14) + fl(13) - fl(12) - fl(15), 2 * fl(14) - fl(13) - fl(15))


def divisor_counts(limit: int) -> list[int]:
    tau = [0] * (limit + 1)
    for d in range(1, limit + 1):
        for multiple in range(d, limit + 1, d):
            tau[multiple] += 1
    return tau


def series_mul(p: list[Fraction], q: list[Fraction], terms: int) -> list[Fraction]:
    out = [Fraction(0)] * terms
    for i, a in enumerate(p[:terms]):
        if a:
            for j, b in enumerate(q[: terms - i]):
                out[i + j] += a * b
    return out


def series_inv(p: list[Fraction], terms: int) -> list[Fraction]:
    if p[0] == 0:
        raise ArithmeticError("series not invertible")
    out = [Fraction(0)] * terms
    out[0] = 1 / p[0]
    for k in range(1, terms):
        out[k] = -sum((p[i] * out[k - i] for i in range(1, min(k, len(p) - 1) + 1)), Fraction(0)) / p[0]
    return out


def pochhammer_series(start: int, length: int, terms: int) -> list[Fraction]:
    """(q^start; q)_length = prod_{i<length} (1 - q^(start+i)) as a truncated series."""

    out = [Fraction(1)] + [Fraction(0)] * (terms - 1)
    for i in range(length):
        e = start + i
        if e < terms:
            factor = [Fraction(1)] + [Fraction(0)] * (terms - 1)
            factor[e] -= 1
            out = series_mul(out, factor, terms)
    return out


def source_series(a0: int, a1: int, a2: int, beta: int, terms: int) -> list[Fraction]:
    """First coefficients of H_n(1/q) = sum_t R(q^t) q^(a0 t) as a power series in q."""

    total = [Fraction(0)] * terms
    t = 0
    while a0 * t < terms:
        ratio1 = series_mul(pochhammer_series(t + 1, a1 - 1, terms),
                            series_inv(pochhammer_series(1, a1 - 1, terms), terms), terms)
        ratio2 = series_mul(pochhammer_series(1, beta - a2 - 1, terms),
                            series_inv(pochhammer_series(a2 + t, beta - a2, terms), terms), terms)
        term = series_mul(ratio1, ratio2, terms)
        shift = a0 * t
        for i in range(terms - shift):
            total[i + shift] += term[i]
        t += 1
    return total


# ------------------------------------------------------------- construction
def build(n: int) -> dict:
    a0, a1, a2, beta = 14 * n + 1, 12 * n + 1, 14 * n + 1, 27 * n + 2
    N = 15 * n
    M = 266 * n * n + 34 * n + 1
    if M != a1 * (a1 - 1) // 2 + a0 * a1 + (beta - a2) * (a2 - a1):
        raise ArithmeticError("M_n differs from Zudilin's formula (16)")
    nu = {l: omega(n, l) for l in range(2, N + 1)}
    if any(v not in (0, 1) for v in nu.values()):
        raise ArithmeticError("a cyclotomic exponent is not 0 or 1")
    omega_support = [l for l in range(2, N + 1) if nu[l]]
    D = pprod([cyclotomic(l) for l in range(1, N + 1)])
    Omega = pprod([cyclotomic(l) for l in omega_support])
    deg_D, deg_Omega = len(D) - 1, len(Omega) - 1
    if deg_D != sum(phi_count(l) for l in range(1, N + 1)):
        raise ArithmeticError("deg D_N differs from the totient sum")

    # c_k X^(a0 k) as (offset, polynomial)
    terms = {}
    for k in range(a2, beta):
        e = a1 * (a1 - 1) // 2 - (beta - a2) * (beta - a2 - 1) // 2 + (beta - k) * (beta - k - 1) // 2
        sign = (-1) ** (a1 + a2 + k + 1)
        core = pmul(gaussian(k - 1, a1 - 1), gaussian(beta - a2 - 1, beta - k - 1))
        terms[k] = (e + a0 * k, [sign * c for c in core])

    # A_n as a Laurent polynomial
    offset_A = min(o for o, _ in terms.values())
    A: Poly = []
    for o, p in terms.values():
        padd_into(A, p, o - offset_A)
    trim(A)
    K = offset_A + len(A) - 1
    order_A = offset_A + next(i for i, c in enumerate(A) if c)

    # D_N/(X^l - 1) for l = 1..N
    D_over = {l: pexact_div(D, [-1] + [0] * (l - 1) + [1], f"D_N by X^{l}-1") for l in range(1, N + 1)}
    prefix: dict[int, Poly] = {0: []}
    running: Poly = []
    for l in range(1, N + 1):
        padd_into(running, D_over[l])
        prefix[l] = list(running)

    # D_N B_n = sum_k c_k X^(a0 k) G_k,
    # G_k = sum_{l<=k-a1} D/(X^l-1) + sum_{j<a0} X^(-j(k-a1)) D/(X^j-1)
    pieces = []
    for k, (o, p) in terms.items():
        m = k - a1
        low = -(a0 - 1) * m
        G: Poly = []
        padd_into(G, prefix[m], -low)
        for j in range(1, a0):
            padd_into(G, D_over[j], -j * m - low)
        trim(G)
        pieces.append((o + low, pmul(p, G)))
    offset_DB = min(o for o, _ in pieces)
    DB: Poly = []
    for o, p in pieces:
        padd_into(DB, p, o - offset_DB)
    trim(DB)
    while DB and DB[0] == 0:
        DB.pop(0)
        offset_DB += 1

    # Divide by Omega_n, then by X^M; both remainders must vanish.
    DA = pmul(D, A)
    UA = pexact_div(DA, Omega, "D_N A_n by Omega_n")
    VB = pexact_div(DB, Omega, "D_N B_n by Omega_n")
    U = shift_down(offset_A, UA, M, "U_n")
    V = shift_down(offset_DB, VB, M, "V_n")
    W = len(U) - 1
    if W != K - M + deg_D - deg_Omega:
        raise ArithmeticError("deg U_n differs from the degree formula")

    # Series check with the divisor function.
    E = K - W
    tau = divisor_counts(K + SERIES_CHECK_TERMS + 1)
    Urev = list(reversed(U))                     # q^W U(1/q)
    Vrev = [0] + list(reversed(V))               # q^W V(1/q), since deg V = W - 1
    if len(V) - 1 != W - 1:
        raise ArithmeticError("deg V_n is not W_n - 1")
    top = W + E + SERIES_CHECK_TERMS              # highest q-exponent needed, shifted by W
    product = pmul(Urev, tau[: top + 1])
    product += [0] * (top + 1 - len(product))
    coefficients = [product[i] - (Vrev[i] if i < len(Vrev) else 0) for i in range(top)]
    vanishing_below = all(c == 0 for c in coefficients[: W + E])
    observed = coefficients[W + E: W + E + SERIES_CHECK_TERMS]
    P = pexact_div(D, Omega, "D_N by Omega_n")
    source = series_mul([Fraction(c) for c in reversed(P)],
                        source_series(a0, a1, a2, beta, SERIES_CHECK_TERMS), SERIES_CHECK_TERMS)
    if any(x.denominator != 1 for x in source):
        raise ArithmeticError("source series has a non-integer coefficient")
    expected = [int(x) for x in source]

    evaluations = []
    for a, b in BASES:
        hat_U = peval_hom(U, a, b)          # b^W U(a/b)
        hat_V = peval_hom(V, a, b) * b      # b^W V(a/b), since deg V = W - 1
        den_U = Fraction(hat_U, b**W).denominator
        den_V = Fraction(hat_V, b**W).denominator
        evaluations.append({
            "base": f"{a}/{b}",
            "reduced_denominator_of_U_is_b^W": den_U == b**W,
            "reduced_denominator_of_V_is_b^(W-1)": den_V == b ** (W - 1),
            "b^(W-1)_clears_U": (hat_U % b == 0),
            "gcd_hatV_b^W_is_b": gcd(hat_V, b**W) == b,
            "hatU_decimal_digits": len(str(abs(hat_U))),
            "hatV_decimal_digits": len(str(abs(hat_V))),
            "gcd_hatU_hatV": str(gcd(hat_U, hat_V)),
        })

    return {
        "n": n,
        "parameters": {"a0": a0, "a1": a1, "a2": a2, "beta": beta, "N": N, "M": M},
        "omega_support_l": omega_support,
        "K": K, "W": W, "deg_D": deg_D, "deg_Omega": deg_Omega,
        "deg_V": len(V) - 1,
        "lead_U": U[-1], "lead_V": V[-1],
        "order_of_A_at_zero": order_A,
        "division_by_Omega_and_X^M_exact": True,
        "series_check": {
            "coefficients_below_q^(K-W)_vanish": vanishing_below,
            "next_twelve_coefficients": [str(c) for c in observed],
            "source_expression_coefficients": [str(c) for c in expected],
            "agree": observed == expected,
        },
        "evaluations": evaluations,
        "_U": U, "_V": V,
    }


def shift_down(offset: int, p: Poly, M: int, name: str) -> Poly:
    """Divide the Laurent polynomial X^offset p by X^M; the result must be a polynomial."""

    lowest = offset + next(i for i, c in enumerate(p) if c)
    if lowest < M:
        raise ArithmeticError(f"{name}: division by X^M leaves a nonzero remainder")
    return [0] * (offset - M) + p if offset >= M else p[M - offset:]


def digest(p: Poly) -> str:
    return hashlib.sha256(json.dumps([str(c) for c in p], separators=(",", ":")).encode()).hexdigest()


def compute(max_n: int) -> dict:
    rows = []
    checks = {}
    for n in range(1, max_n + 1):
        row = build(n)
        U, V = row.pop("_U"), row.pop("_V")
        row["U_coefficients_sha256"] = digest(U)
        row["V_coefficients_sha256"] = digest(V)
        row["max_coefficient_bits"] = {"U": max(abs(c) for c in U).bit_length(),
                                       "V": max(abs(c) for c in V).bit_length()}
        size = len(json.dumps([[str(c) for c in U], [str(c) for c in V]]))
        if size <= STORE_LIMIT_BYTES:
            row["U_coefficients_low_to_high"] = [str(c) for c in U]
            row["V_coefficients_low_to_high"] = [str(c) for c in V]
        else:
            row["coefficients_stored"] = False
            row["coefficient_json_bytes"] = size
        rows.append(row)
        printed = PRINTED_TABLE[n]
        checks[f"n={n}: degree table"] = all(row[key] == printed[key] for key in printed)
        checks[f"n={n}: deg V = W - 1"] = row["deg_V"] == row["W"] - 1
        checks[f"n={n}: leading coefficients (-1)^n"] = row["lead_U"] == row["lead_V"] == (-1) ** n
        checks[f"n={n}: coefficients below q^(K-W) vanish"] = row["series_check"]["coefficients_below_q^(K-W)_vanish"]
        checks[f"n={n}: next twelve coefficients match the source expression"] = row["series_check"]["agree"]
        for ev in row["evaluations"]:
            base = ev["base"]
            ok = ev["reduced_denominator_of_U_is_b^W"] and ev["reduced_denominator_of_V_is_b^(W-1)"]
            if base != "3/1":
                ok = ok and not ev["b^(W-1)_clears_U"] and ev["gcd_hatV_b^W_is_b"]
            checks[f"n={n}: exact evaluation at {base}"] = ok
    return {
        "indices": list(range(1, max_n + 1)),
        "coefficient_digest_rule": "sha256 of the compact JSON list of decimal coefficient strings, lowest degree first",
        "rows": rows,
        "checks": checks,
        "all_printed_claims_verified": all(checks.values()),
    }


def canonical(obj: object) -> str:
    return json.dumps(obj, indent=2, sort_keys=True) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--max-n", type=int, default=4, choices=[1, 2, 3, 4],
                        help="largest index to reconstruct (paper: 4)")
    parser.add_argument("--receipt", type=Path, help="write a receipt JSON to this path")
    args = parser.parse_args()
    result = compute(args.max_n)
    if args.receipt:
        receipt = {
            "schema": SCHEMA,
            "program": PROGRAM,
            "program_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "arguments": [] if args.max_n == 4 else ["--max-n", str(args.max_n)],
            "verification_scope": "finite_computation_only",
            "claim_boundary": (
                "Exact reconstruction of U_n and V_n in Z[X] for n = 1..4 only, with exact "
                "divisibility, degree, series and rational-evaluation checks. No statement for "
                "other indices; the historical high-precision real evaluations are not reproduced. "
                "No floating point and no Lean kernel."
            ),
            "paper_passage": "Subsection 'Finite calculations', paragraph beginning 'A computer-algebra calculation reconstructs the forms'",
            "result": result,
        }
        args.receipt.write_text(canonical(receipt), encoding="utf-8")
    sys.stdout.write(canonical(result))
    return 0 if result["all_printed_claims_verified"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
