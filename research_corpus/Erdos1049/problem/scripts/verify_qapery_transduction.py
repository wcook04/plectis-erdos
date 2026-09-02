#!/usr/bin/env python3
"""Exact transduction of the Amdeberhan-Zeilberger q-Apery module to base 3/2.

Source: T. Amdeberhan and D. Zeilberger, "q-Apery Irrationality Proofs by q-WZ
pairs", arXiv:math/9804122, sections 1.1-1.7.  Archived at
annexes/arxiv-math9804122-amdeberhan-zeilberger-q-apery/.  That paper constructs rational sequences a_n, b_n
converging to h_q(1) = sum_{k>=1} 1/(q^k - 1), which is exactly the function of
Erdos #1049, and proves irrationality for INTEGER |q| > 1.

This checker replays the source algebra symbolically, then specialises the
module at the rational base q = 3/2 and measures precisely what arithmetic the
family supplies there.  It is exact finite computation over a displayed range,
not an all-n proof and not an irrationality result at 3/2.

Checks performed
----------------
A. source_recurrence   Both a_n and b_n satisfy L u = y_2 u_{n+2} + y_1 u_{n+1}
                       + y_0 u_n = 0 with the source coefficients.  This also
                       validates the reading of the potential c(n, k).
B. casoratian          The adjacent Casoratian W_n = a_{n+1} b_n - a_n b_{n+1}
                       equals the closed form -q^{n+1}(q^{n+1}+2)/(q^{n+1}-1).
C. denominator_endpoints  deg b_n = n(3n+1)/2, constant coefficient 1, leading
                       coefficient (-1)^n.
D. three_halves_shear  At q = 3/2 the reduced Casoratian has v_3 = n+1 and
                       v_2 = -(n+1) exactly.
E. homogeneous_units   The homogeneous evaluation of b_n at (3, 2) is a unit
                       modulo 2 and modulo 3, so the denominator channel is
                       coprime to 6 and falls under the note's endpoint
                       obstruction.
F. cleared_rows        Apply the source's own Lemma 1 clearing factor, specialise
                       at (3, 2), take primitive integer rows, and report the
                       row contents, endpoint jets and the exterior determinant
                       valuations that survive.  This is the measurement that
                       decides whether the cleared q-Apery module supplies any
                       simultaneous 2-adic and 3-adic gain at 3/2.

Authority boundary: exact symbolic and integer arithmetic over the displayed
range of n.  Nothing here proves an all-n statement, and nothing here decides
the irrationality of h_{3/2}(1).  Erdos #1049 remains open.
"""

from __future__ import annotations

from fractions import Fraction
import json
import math

import sympy as sp


Q = sp.symbols("q")
# Symbolic replay is the expensive layer (a_seq builds rational functions in q);
# n <= 4 is enough to close the recurrence and the Casoratian.  The integer layer
# is cheap enough to carry the closed-form fits further.  Raising N_MAX_INTEGER
# past 8 costs minutes, not seconds; do it deliberately, not by default.
N_MAX_SYMBOLIC = 5
N_MAX_INTEGER = 8


# ---------------------------------------------------------------- source layer


def q_pochhammer(n: int):
    """(q)_n = prod_{i=1}^{n} (1 - q^i); (q)_0 = 1."""
    value = sp.Integer(1)
    for i in range(1, n + 1):
        value *= 1 - Q**i
    return sp.expand(value)


def q_binomial(n: int, k: int):
    """Gaussian binomial [n choose k]_q as a polynomial in q."""
    if k < 0 or k > n:
        return sp.Integer(0)
    return sp.cancel(q_pochhammer(n) / (q_pochhammer(k) * q_pochhammer(n - k)))


def mollifier(n: int, k: int):
    """Source 1.3: b(n,k) = (-1)^k q^{k(k+1)/2} [n+k, k]_q [n, k]_q."""
    return (
        sp.Integer(-1) ** k
        * Q ** sp.Rational(k * (k + 1), 2)
        * q_binomial(n + k, k)
        * q_binomial(n, k)
    )


def potential(n: int, k: int):
    """Source 1.2: the potential c(n,k).

    c(n,k) = sum_{m=1}^{n} q^m / ((1 - q^m) (q)_m)
           + sum_{m=1}^{k} 1 / ((q^m - 1) [n+m, m]_q (q)_n)

    The archived arXiv source is amstex whose \\frac braces are lost in text
    extraction, so this reading is validated downstream by check A (the source
    recurrence) rather than assumed.
    """
    total = sp.Integer(0)
    for m in range(1, n + 1):
        total += Q**m / ((1 - Q**m) * q_pochhammer(m))
    for m in range(1, k + 1):
        total += 1 / ((Q**m - 1) * q_binomial(n + m, m) * q_pochhammer(n))
    return total


def a_seq(n: int):
    """Source 1.4: a(n) = sum_{k=0}^{n} c(n,k) b(n,k)."""
    return sp.cancel(
        sp.together(sum(potential(n, k) * mollifier(n, k) for k in range(n + 1)))
    )


def b_seq(n: int):
    """Source 1.4: b(n) = sum_{k=0}^{n} b(n,k)."""
    return sp.expand(sum(mollifier(n, k) for k in range(n + 1)))


def alpha(n: int):
    return Q ** (n + 1)


def y0(n: int):
    """Source 1.5: y_0(n) = q (alpha_n - 1)(q alpha_n + 2)."""
    a = alpha(n)
    return sp.expand(Q * (a - 1) * (Q * a + 2))


def y2(n: int):
    """Source 1.5: y_2(n) = (q alpha_n - 1)(alpha_n + 2)."""
    a = alpha(n)
    return sp.expand((Q * a - 1) * (a + 2))


def y1(n: int):
    """Source 1.5: the middle coefficient, quoted verbatim from the annex."""
    a = alpha(n)
    return sp.expand(
        Q**3 * a**5
        + 2 * Q**2 * (Q + 1) * a**4
        + Q**2 * a**3
        - 4 * Q * (Q + 1) * a**2
        + (Q**2 - 4 * Q + 1) * a
        + 2 * (Q + 1)
    )


# ------------------------------------------------------------ rational base


def valuation(value: Fraction | int, prime: int) -> int | float:
    """Exact p-adic valuation of a rational, negative on denominators."""
    if value == 0:
        return math.inf
    frac = Fraction(value)
    result = 0
    num, den = abs(frac.numerator), frac.denominator
    while num % prime == 0:
        num //= prime
        result += 1
    while den % prime == 0:
        den //= prime
        result -= 1
    return result


def at_three_halves(expr) -> Fraction:
    value = sp.nsimplify(sp.cancel(expr.subs(Q, sp.Rational(3, 2))))
    return Fraction(int(sp.numer(value)), int(sp.denom(value)))


def homogeneous_evaluation(poly, width: int) -> int:
    """H_W(P) = 3^? 2^? weighting: sum_i p_i 3^i 2^{W-i}, the note's H_W."""
    p = sp.Poly(sp.expand(poly), Q)
    coeffs = {n: int(c) for (n,), c in p.terms()}
    return sum(c * 3**i * 2 ** (width - i) for i, c in coeffs.items())


def clearing_factor(n: int):
    """Source Lemma 1: (q)_{n+1} * prod_{s=[n/2]}^{n} (1 - q^s).

    The archived text renders this as `(q)_n+1\\prod_s=[n/2]^n(1-q^s)`; the
    degree bookkeeping below confirms the (q)_{n+1} reading, since
    deg b_n + deg(clearing) = 3n^2/2 + 7n^2/8 = 19n^2/8, matching the source's
    own estimate z_n = O(q^{19 n^2 / 8}) in Lemma 1.
    """
    value = q_pochhammer(n + 1)
    for s in range(n // 2, n + 1):
        if s >= 1:
            value *= 1 - Q**s
    return sp.expand(value)


# ------------------------------------------------------------------- checks


def check_source_recurrence() -> list[dict]:
    rows = []
    for n in range(0, N_MAX_SYMBOLIC):
        for name, seq in (("a", a_seq), ("b", b_seq)):
            residual = sp.simplify(
                sp.cancel(
                    y2(n) * seq(n + 2) + y1(n) * seq(n + 1) + y0(n) * seq(n)
                )
            )
            ok = residual == 0
            rows.append({"n": n, "sequence": name, "residual_is_zero": bool(ok)})
            assert ok, f"source recurrence failed for {name} at n={n}: {residual}"
    return rows


def check_casoratian() -> list[dict]:
    rows = []
    for n in range(0, N_MAX_SYMBOLIC):
        actual = sp.cancel(
            a_seq(n + 1) * b_seq(n) - a_seq(n) * b_seq(n + 1)
        )
        closed = sp.cancel(
            -Q ** (n + 1) * (Q ** (n + 1) + 2) / (Q ** (n + 1) - 1)
        )
        ok = sp.simplify(actual - closed) == 0
        rows.append({"n": n, "matches_closed_form": bool(ok)})
        assert ok, f"Casoratian closed form failed at n={n}"
    return rows


def check_denominator_endpoints() -> list[dict]:
    rows = []
    for n in range(0, N_MAX_INTEGER):
        poly = sp.Poly(b_seq(n), Q)
        degree = poly.degree()
        coeffs = {e: int(c) for (e,), c in poly.terms()}
        expected_degree = n * (3 * n + 1) // 2
        row = {
            "n": n,
            "degree": int(degree),
            "expected_degree": expected_degree,
            "constant_coefficient": coeffs.get(0, 0),
            "leading_coefficient": coeffs.get(int(degree), 0),
        }
        assert row["degree"] == expected_degree, row
        assert row["constant_coefficient"] == 1, row
        assert row["leading_coefficient"] == (-1) ** n, row
        rows.append(row)
    return rows


def check_three_halves_shear() -> list[dict]:
    rows = []
    for n in range(0, N_MAX_INTEGER):
        w = at_three_halves(
            -Q ** (n + 1) * (Q ** (n + 1) + 2) / (Q ** (n + 1) - 1)
        )
        row = {
            "n": n,
            "casoratian_numerator": w.numerator,
            "casoratian_denominator": w.denominator,
            "v3": valuation(w, 3),
            "v2": valuation(w, 2),
        }
        assert row["v3"] == n + 1, row
        assert row["v2"] == -(n + 1), row
        rows.append(row)
    return rows


def check_homogeneous_units() -> list[dict]:
    rows = []
    for n in range(0, N_MAX_INTEGER):
        poly = b_seq(n)
        width = n * (3 * n + 1) // 2
        value = homogeneous_evaluation(poly, width)
        row = {
            "n": n,
            "width": width,
            "homogeneous_value_mod_2": value % 2,
            "homogeneous_value_mod_3": value % 3,
            "coprime_to_6": value % 2 != 0 and value % 3 != 0,
        }
        assert row["coprime_to_6"], row
        rows.append(row)
    return rows


def check_cleared_rows() -> tuple[list[dict], list[dict]]:
    """Apply the source clearing factor, specialise at 3/2, measure the gain."""
    rows: list[dict] = []
    integer_rows: dict[int, tuple[int, int]] = {}
    for n in range(0, N_MAX_INTEGER):
        factor = clearing_factor(n)
        u_rat = at_three_halves(sp.cancel(a_seq(n) * factor))
        z_rat = at_three_halves(sp.cancel(b_seq(n) * factor))

        # Clear the common power of 2 that the rational base introduces, so the
        # row is a genuine integer pair, then primitively normalise it.
        scale = max(1, u_rat.denominator, z_rat.denominator)
        common_den = (u_rat.denominator * z_rat.denominator) // math.gcd(
            u_rat.denominator, z_rat.denominator
        )
        u_int = int(u_rat * common_den)
        z_int = int(z_rat * common_den)
        content = math.gcd(abs(u_int), abs(z_int)) or 1
        u_prim, z_prim = u_int // content, z_int // content
        integer_rows[n] = (u_prim, z_prim)
        rows.append(
            {
                "n": n,
                "clearing_denominator_v2": valuation(Fraction(1, common_den), 2),
                "clearing_denominator_v3": valuation(Fraction(1, common_den), 3),
                "row_content": content,
                "row_content_v2": valuation(content, 2),
                "row_content_v3": valuation(content, 3),
                "primitive_v2_U": valuation(u_prim, 2) if u_prim else None,
                "primitive_v3_U": valuation(u_prim, 3) if u_prim else None,
                "primitive_v2_V": valuation(z_prim, 2),
                "primitive_v3_V": valuation(z_prim, 3),
            }
        )

    exteriors: list[dict] = []
    for n in range(0, N_MAX_INTEGER - 1):
        u_n, v_n = integer_rows[n]
        u_m, v_m = integer_rows[n + 1]
        delta = u_n * v_m - u_m * v_n
        if delta == 0:
            exteriors.append({"n": n, "m": n + 1, "delta_is_zero": True})
            continue
        v2 = valuation(delta, 2)
        v3 = valuation(delta, 3)
        # Local-to-Archimedean balance in natural logarithm, as
        # local gain minus Archimedean cost.  SIGN CONVENTION: this field is
        # gain - cost, so a POSITIVE value is the direction an irrationality
        # argument needs (the certified local divisor outgrows the height).
        # That is the negation of the quantity in the note's Problem 8.5, which
        # is written cost - gain and asks for it to be negative.
        #
        # This is a determinant-only proxy for Problem 8.5, not Problem 8.5
        # itself: it compares the determinant's own local content against the
        # determinant's own height and does NOT include the analytic remainder
        # term log|L_n|.  A separate measurement of the remainder is required
        # before any statement about the full margin.
        local_gain = v2 * math.log(2) + v3 * math.log(3)
        archimedean_cost = math.log(abs(delta))
        exteriors.append(
            {
                "n": n,
                "m": n + 1,
                "delta_is_zero": False,
                "v2_delta": v2,
                "v3_delta": v3,
                # closed forms conjectured from the displayed range only
                "v2_matches_3nn_plus_3n_plus_1": v2 == 3 * n * n + 3 * n + 1,
                "v3_matches_n_plus_1": v3 == n + 1,
                "abs_delta_bits": int(delta).bit_length(),
                "local_gain_nats": round(local_gain, 4),
                "archimedean_cost_nats": round(archimedean_cost, 4),
                "margin_nats": round(local_gain - archimedean_cost, 4),
                "margin_over_n_squared": (
                    round((local_gain - archimedean_cost) / (n * n), 5)
                    if n
                    else None
                ),
                # True means the local divisor beats the determinant height,
                # i.e. the direction an irrationality argument needs.  Over the
                # checked range this is False at every n.
                "local_gain_beats_height": local_gain - archimedean_cost > 0,
            }
        )
    return rows, exteriors


def main() -> None:
    recurrence = check_source_recurrence()
    casoratian = check_casoratian()
    endpoints = check_denominator_endpoints()
    shear = check_three_halves_shear()
    units = check_homogeneous_units()
    cleared, exteriors = check_cleared_rows()

    print(
        json.dumps(
            {
                "schema": "erdos1049-qapery-transduction/1",
                "source": {
                    "citation": (
                        "T. Amdeberhan and D. Zeilberger, q-Apery Irrationality "
                        "Proofs by q-WZ pairs, arXiv:math/9804122, sections "
                        "1.1-1.7"
                    ),
                    "annex_slug": "arxiv-math9804122-amdeberhan-zeilberger-q-apery",
                    "source_scope": "integer |q| > 1",
                    "specialisation_scope": "q = 3/2, outside the source theorem",
                },
                "authority": (
                    "exact_symbolic_and_integer_computation_over_displayed_range_"
                    "not_an_all_n_proof_and_not_an_irrationality_result_at_3_2"
                ),
                "A_source_recurrence": recurrence,
                "B_casoratian": casoratian,
                "C_denominator_endpoints": endpoints,
                "D_three_halves_shear": shear,
                "E_homogeneous_units": units,
                "F_cleared_rows": cleared,
                "F_cleared_exteriors": exteriors,
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
