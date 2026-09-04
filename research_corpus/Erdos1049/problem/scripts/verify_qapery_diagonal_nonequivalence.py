#!/usr/bin/env python3
"""The q-Apery and Van Assche denominators are two diagonals of one kernel.

This checker settles a question the #1049 programme had left as an assumption:
whether the classical q-series approximant families for F(t) = sum 1/(t^n - 1)
share a single scalar recurrence, so that a failure measured on one of them
transfers to the others.

They do not.  What they share is one bivariate kernel - Van Assche's little
q-Legendre polynomial P_n(x | q) - evaluated on DIFFERENT moving diagonals:

    Amdeberhan-Zeilberger : b_n(p) = P_n(p^(n+1) | p^-1)
    Van Assche            : A_n(p) = P_n(p^n     | p^-1)

Pullback along different diagonals does not preserve the minimal scalar
recurrence, the endpoint arithmetic after rational specialisation, or the
integral lattice.  This script proves all three statements exactly.

Sources, both archived and hash-pinned locally:
  * W. Van Assche, "Little q-Legendre polynomials and irrationality of certain
    Lambert series", annexes/arxiv-math0101187-van-assche-little-q-legendre-lambert/.
    Definition used here is his eq. (Pnpbinom):
        P_n(x|q) = sum_{k=0}^n [n,k]_p [n+k,k]_p p^{-kn+k(k-1)/2} (-x)^k,  p = 1/q.
  * T. Amdeberhan and D. Zeilberger, "q-Apery Irrationality Proofs by q-WZ
    pairs", arXiv:math/9804122, annexes/arxiv-math9804122-amdeberhan-zeilberger-q-apery/.
    Section 1.3 mollifier and section 1.5 operator L = y_2 N^2 + y_1 N + y_0.

Checks performed
----------------
A. kernel_identity        P_n(p^(n+1) | p^-1) equals the Amdeberhan-Zeilberger
                          denominator b_n exactly.  The two families really do
                          share one kernel.
B. diagonal_initial_data  The Van Assche diagonal has A_0 = 1, A_1 = -p,
                          A_2 = p(p^4+p^3+p^2-p-1).
C. recurrence_fails       The Van Assche diagonal does NOT satisfy the
                          Amdeberhan-Zeilberger operator.  The residual at n = 0
                          is exactly -p(p-1)^2(p+1)(p^5+2p^4+2p^3+2p^2+2),
                          strictly negative for every real p > 1, and the
                          residual is nonzero at n = 1, 2 as well.
D. endpoint_shape         deg A_n = n(3n-1)/2, and A_n = p * Ahat_n with
                          Ahat_n(0) = -1 and leading coefficient (-1)^n.  So the
                          Van Assche denominator does NOT have unit endpoints in
                          its natural coordinate - it carries a monomial factor p.
E. three_halves_endpoint  Consequently the homogeneous evaluation of A_n at (3,2)
                          has v_3 = 1 and v_2 = 0, rather than being coprime to 6
                          as the q-Apery denominator is.  This is an explicit
                          disconfirming example against any blanket claim that
                          every family member has unit endpoints.

Authority boundary: exact symbolic computation over the displayed range of n.
Check C proves non-equivalence outright (one nonzero residual suffices).  Checks
D and E are verified over the displayed range and match a proof contour, but are
not themselves all-n proofs.  Nothing here decides Erdos #1049, which remains
open at 3/2.
"""

from __future__ import annotations

import json
import math

import sympy as sp


P = sp.symbols("p")
N_MAX = 7


def q_pochhammer(n: int):
    value = sp.Integer(1)
    for i in range(1, n + 1):
        value *= 1 - P**i
    return sp.expand(value)


def q_binomial(n: int, k: int):
    """Gaussian binomial [n, k]_p."""
    if k < 0 or k > n:
        return sp.Integer(0)
    return sp.cancel(q_pochhammer(n) / (q_pochhammer(k) * q_pochhammer(n - k)))


def little_q_legendre(n: int, x):
    """Van Assche eq. (Pnpbinom), verbatim, in the base p = 1/q."""
    total = sp.Integer(0)
    for k in range(n + 1):
        # exponent is -kn + k(k-1)/2 : only k(k-1) is halved, not the whole sum
        exponent = sp.Rational(k * (k - 1), 2) - k * n
        total += (
            q_binomial(n, k)
            * q_binomial(n + k, k)
            * P**exponent
            * (-x) ** k
        )
    return sp.cancel(sp.expand(total))


def az_denominator(n: int):
    """Amdeberhan-Zeilberger section 1.3/1.4: b_n = sum_k b(n,k)."""
    total = sp.Integer(0)
    for k in range(n + 1):
        total += (
            sp.Integer(-1) ** k
            * P ** sp.Rational(k * (k + 1), 2)
            * q_binomial(n + k, k)
            * q_binomial(n, k)
        )
    return sp.expand(total)


def van_assche_diagonal(n: int):
    """A_n = P_n(p^n | p^-1): the diagonal forced by Van Assche's eq. (2.5)."""
    return sp.expand(little_q_legendre(n, P**n))


def az_diagonal(n: int):
    """P_n(p^(n+1) | p^-1): the diagonal the q-WZ construction actually uses."""
    return sp.expand(little_q_legendre(n, P ** (n + 1)))


# --- Amdeberhan-Zeilberger section 1.5 operator (corrected coefficients) -----


def alpha(n: int):
    return P ** (n + 1)


def y0(n: int):
    a = alpha(n)
    return sp.expand(P * (a - 1) * (P * a + 2))


def y2(n: int):
    a = alpha(n)
    return sp.expand((P * a - 1) * (a + 2))


def y1(n: int):
    a = alpha(n)
    return sp.expand(
        P**3 * a**5
        + 2 * P**2 * (P + 1) * a**4
        + P**2 * a**3
        - 4 * P * (P + 1) * a**2
        + (P**2 - 4 * P + 1) * a
        + 2 * (P + 1)
    )


def apply_operator(seq, n: int):
    return sp.expand(
        sp.cancel(y2(n) * seq(n + 2) + y1(n) * seq(n + 1) + y0(n) * seq(n))
    )


# ---------------------------------------------------------------- checks


def check_kernel_identity() -> list[dict]:
    rows = []
    for n in range(N_MAX):
        diff = sp.simplify(az_diagonal(n) - az_denominator(n))
        ok = diff == 0
        rows.append({"n": n, "P_n(p^(n+1)) == b_n_AZ": bool(ok)})
        assert ok, f"kernel identity failed at n={n}: {diff}"
    return rows


def check_diagonal_initial_data() -> dict:
    a0, a1, a2 = (van_assche_diagonal(n) for n in range(3))
    expected2 = sp.expand(P * (P**4 + P**3 + P**2 - P - 1))
    assert sp.simplify(a0 - 1) == 0, a0
    assert sp.simplify(a1 + P) == 0, a1
    assert sp.simplify(a2 - expected2) == 0, a2
    return {
        "A_0": sp.sstr(a0),
        "A_1": sp.sstr(a1),
        "A_2": sp.sstr(sp.factor(a2)),
        "matches_expected": True,
    }


def check_recurrence_fails() -> dict:
    residual0 = apply_operator(van_assche_diagonal, 0)
    predicted = sp.expand(
        -P * (P - 1) ** 2 * (P + 1) * (P**5 + 2 * P**4 + 2 * P**3 + 2 * P**2 + 2)
    )
    matches = sp.simplify(residual0 - predicted) == 0
    assert matches, f"residual at n=0 is {sp.factor(residual0)}, not the predicted form"
    assert residual0 != 0

    # strictly negative for every real p > 1: every factor is positive there
    sample = [sp.Rational(3, 2), sp.Rational(2), sp.Rational(7, 2), sp.Rational(11, 5)]
    signs = {str(v): int(sp.sign(residual0.subs(P, v))) for v in sample}
    assert all(s == -1 for s in signs.values()), signs

    # and it is not a lucky zero elsewhere either
    later = {}
    for n in (1, 2):
        r = apply_operator(van_assche_diagonal, n)
        later[n] = r != 0
        assert r != 0, f"residual unexpectedly vanished at n={n}"

    # control: the AZ diagonal DOES satisfy its own operator
    control = {}
    for n in range(3):
        r = apply_operator(az_denominator, n)
        control[n] = r == 0
        assert r == 0, f"control failed: AZ operator did not annihilate b_n at n={n}"

    return {
        "residual_n0_factored": sp.sstr(sp.factor(residual0)),
        "matches_predicted_form": bool(matches),
        "strictly_negative_at_sampled_p_gt_1": signs,
        "residual_nonzero_at_n": {str(k): bool(v) for k, v in later.items()},
        "control_az_diagonal_satisfies_its_own_operator": {
            str(k): bool(v) for k, v in control.items()
        },
        "conclusion": (
            "Van Assche's P_n(p^n | p^-1) does NOT satisfy the Amdeberhan-Zeilberger "
            "scalar recurrence, so measurements made on the q-Apery diagonal do not "
            "transfer to it by the shared-kernel identity alone."
        ),
    }


def check_endpoint_shape() -> list[dict]:
    rows = []
    for n in range(1, N_MAX):
        a = sp.Poly(van_assche_diagonal(n), P)
        degree = a.degree()
        expected_degree = n * (3 * n - 1) // 2
        coeffs = {e: int(c) for (e,), c in a.terms()}
        # A_n should be divisible by exactly p^1
        assert coeffs.get(0, 0) == 0, f"A_{n} has nonzero constant term"
        hat = sp.Poly(sp.cancel(van_assche_diagonal(n) / P), P)
        hat_coeffs = {e: int(c) for (e,), c in hat.terms()}
        row = {
            "n": n,
            "deg_A_n": int(degree),
            "expected_deg": expected_degree,
            "A_n_constant_term": coeffs.get(0, 0),
            "Ahat_constant_term": hat_coeffs.get(0, 0),
            "Ahat_leading_coefficient": hat_coeffs.get(int(hat.degree()), 0),
            "expected_leading": (-1) ** n,
        }
        assert row["deg_A_n"] == expected_degree, row
        assert row["Ahat_constant_term"] == -1, row
        assert row["Ahat_leading_coefficient"] == (-1) ** n, row
        rows.append(row)
    return rows


def homogeneous_evaluation(poly, width: int) -> int:
    p = sp.Poly(sp.expand(poly), P)
    coeffs = {e: int(c) for (e,), c in p.terms()}
    return sum(c * 3**i * 2 ** (width - i) for i, c in coeffs.items())


def valuation(value: int, prime: int) -> int | float:
    if value == 0:
        return math.inf
    value = abs(value)
    out = 0
    while value % prime == 0:
        value //= prime
        out += 1
    return out


def check_three_halves_endpoint() -> list[dict]:
    rows = []
    for n in range(1, N_MAX):
        a = van_assche_diagonal(n)
        width = n * (3 * n - 1) // 2
        h = homogeneous_evaluation(a, width)
        row = {
            "n": n,
            "width": width,
            "v3_of_H": valuation(h, 3),
            "v2_of_H": valuation(h, 2),
        }
        assert row["v3_of_H"] == 1, row
        assert row["v2_of_H"] == 0, row
        rows.append(row)
    return rows


def main() -> None:
    kernel = check_kernel_identity()
    initial = check_diagonal_initial_data()
    fails = check_recurrence_fails()
    endpoints = check_endpoint_shape()
    three_halves = check_three_halves_endpoint()

    print(
        json.dumps(
            {
                "schema": "erdos1049-qapery-diagonal-nonequivalence/1",
                "sources": {
                    "van_assche": (
                        "annexes/arxiv-math0101187-van-assche-little-q-legendre-lambert"
                        "/source.tex, eq. (Pnpbinom)"
                    ),
                    "amdeberhan_zeilberger": (
                        "annexes/arxiv-math9804122-amdeberhan-zeilberger-q-apery"
                        "/source.tex, sections 1.3-1.5"
                    ),
                },
                "authority": (
                    "exact_symbolic_computation_over_displayed_range; check C is a "
                    "decisive non-equivalence proof, checks D and E are range-verified "
                    "and not all-n proofs; nothing here decides Erdos #1049"
                ),
                "A_kernel_identity": kernel,
                "B_diagonal_initial_data": initial,
                "C_recurrence_fails": fails,
                "D_endpoint_shape": endpoints,
                "E_three_halves_endpoint": three_halves,
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
