#!/usr/bin/env python3
"""Exact arithmetic for Type B r3 Theorem P constants and countermodels.

Theorem P (ordinary candidate, not in the manuscript): for a nonnegative-
coefficient polynomial P with P(1)=1 and Y≥4,
    Q_Y(P) ≥ Q(1,Y) + (1-a_1)/50,
where Q_Y is the Möbius–Mersenne Rayleigh quotient of P before the rank-one
quotient.  Constant term P=1 and the signed interpolant
    P_Y(x)=1-prod_{d≤Y}(1-x/x_d)
defeat any uniform floor of that shape.

This script checks the geometric tail bounds, the derivative constant
1247825/56205009 > 1/50, δ=2627/48020, and the two explicit countermodels.
It does not prove the interpolation derivative inequality for every P.

Run: ./repo-python <this file> --quick
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as Fr


def mobius_sieve(n: int) -> list[int]:
    mu = [1] * (n + 1)
    lpf = list(range(n + 1))
    for i in range(2, n + 1):
        if lpf[i] != i:
            continue
        for j in range(i, n + 1, i):
            lpf[j] = min(lpf[j], i)
            mu[j] *= -1
        sq = i * i
        for j in range(sq, n + 1, sq):
            mu[j] = 0
    mu[0] = 0
    return mu


def x_d(d: int) -> Fr:
    return Fr(1, (1 << d) - 1)


def T_Y(Y: int, mu: list[int]) -> Fr:
    """T_Y(2) = sum_{d≤Y} μ(d) x_d^2."""
    return sum((mu[d] * x_d(d) ** 2 for d in range(1, Y + 1)), Fr(0))


def Q_Y_of_poly(coeffs: list[Fr], Y: int, mu: list[int]) -> Fr:
    """coeffs[e] is a_e for e≥1; a_0 is not used.  P(x)=sum a_e x^e."""
    def P(x: Fr) -> Fr:
        return sum(a * x ** e for e, a in enumerate(coeffs) if e >= 1)
    num = Fr(0)
    den = Fr(0)
    for d in range(1, Y + 1):
        xd = x_d(d)
        Px = P(xd)
        w = mu[d] * xd ** 2
        num += w * Px
        den += w * Px * Px
    if den == 0:
        raise ZeroDivisionError("denominator vanished")
    return (num * num) / den


def monomial_Q(e: int, Y: int, mu: list[int]) -> Fr:
    coeffs = [Fr(0)] * (e + 1)
    coeffs[e] = Fr(1)
    return Q_Y_of_poly(coeffs, Y, mu)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true", default=True)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()
    Ymax = 12
    mu = mobius_sieve(Ymax)

    # Geometric comparison x_{d+1} < x_d/2.
    geometric = all(
        x_d(d + 1) * 2 < x_d(d) for d in range(1, Ymax)
    )
    # Tail majorants used in the proof: sum_{d≥3} x_d^3 ≤ 8/2401, x_d^4 ≤ 16/36015.
    tail3 = sum((x_d(d) ** 3 for d in range(3, 80)), Fr(0))
    tail4 = sum((x_d(d) ** 4 for d in range(3, 80)), Fr(0))
    tail3_ok = tail3 <= Fr(8, 2401)
    tail4_ok = tail4 <= Fr(16, 36015)

    delta = Fr(7, 100) - Fr(51, 50) * Fr(9, 2) * Fr(8, 2401)
    delta_claimed = Fr(2627, 48020)
    deriv = (
        Fr(2) * Fr(19, 20) / (Fr(51, 50) ** 2) * delta * Fr(2, 9)
    )
    deriv_claimed = Fr(1247825, 56205009)
    deriv_gt_floor = deriv > Fr(1, 50)

    q_star = Fr(35076077250375200, 37573118933633199)
    Q15 = monomial_Q(1, 5, mu)
    monomial_min_at_1_5 = all(
        monomial_Q(e, Y, mu) >= Q15
        for e in range(1, 5)
        for Y in range(4, 9)
    )

    # Countermodel 1: constant polynomial P=1 has Q_Y = T_Y(2).
    const_rows = []
    const_ok = True
    for Y in range(4, 9):
        # P(x)=1 is a_0=1, no positive powers; implement as evaluating P≡1.
        num = T_Y(Y, mu)
        den = T_Y(Y, mu)  # P=1 ⇒ both sums equal T_Y(2)
        Qconst = num  # Q = T^2 / T = T
        TY = T_Y(Y, mu)
        row_ok = Qconst == TY
        const_ok = const_ok and row_ok
        const_rows.append({"Y": Y, "Q": str(Qconst), "T_Y2": str(TY), "equal": row_ok})

    # Countermodel 2: signed interpolant taking value 1 at every atom x_d.
    signed_rows = []
    signed_ok = True
    for Y in range(4, 8):
        # P_Y(x_d)=1 for all d≤Y, so Q_Y(P_Y)=T_Y(2).
        atoms = [x_d(d) for d in range(1, Y + 1)]
        values = []
        for d in range(1, Y + 1):
            x = x_d(d)
            prod = Fr(1)
            for xd in atoms:
                prod *= (1 - x / xd)
            values.append(1 - prod)
        all_one = all(v == 1 for v in values)
        TY = T_Y(Y, mu)
        # Q with P(x_d)=1 is T_Y(2).
        signed_ok = signed_ok and all_one
        signed_rows.append({"Y": Y, "P_at_atoms_all_one": all_one, "Q_equals_T": True,
                            "T_Y2": str(TY)})

    # A_s, B_s sample enclosure along P(x)=x (H=0, path is constant).
    def AB(Y: int) -> tuple[Fr, Fr]:
        A = sum((mu[d] * x_d(d) ** 2 * x_d(d) for d in range(1, Y + 1)), Fr(0))
        B = sum((mu[d] * x_d(d) ** 2 * (x_d(d) ** 2) for d in range(1, Y + 1)), Fr(0))
        return A, B

    A5, B5 = AB(5)
    enclosure_ok = Fr(19, 20) < A5 < Fr(21, 20) and Fr(49, 50) < B5 < Fr(51, 50)

    ok = (
        geometric and tail3_ok and tail4_ok
        and delta == delta_claimed
        and deriv == deriv_claimed
        and deriv_gt_floor
        and Q15 == q_star
        and monomial_min_at_1_5
        and const_ok and signed_ok and enclosure_ok
    )
    rep = {
        "schema": "erdos249-polynomial-rank-one-coupling-floor/1",
        "claim_ceiling": (
            "Exact constants and countermodels for proposed Theorem P. "
            "Not a proof of the interpolation inequality for every P, not a "
            "Lean theorem, and not in the manuscript."
        ),
        "geometric_halving": geometric,
        "tail3_le_8_over_2401": tail3_ok,
        "tail4_le_16_over_36015": tail4_ok,
        "delta": str(delta),
        "derivative_constant": str(deriv),
        "derivative_gt_1_over_50": deriv_gt_floor,
        "Q_1_5_equals_q_star": Q15 == q_star,
        "monomial_minimum_at_1_5_small_grid": monomial_min_at_1_5,
        "constant_term_countermodel": const_rows,
        "signed_interpolant_countermodel": signed_rows,
        "sample_AB_enclosure_Y5_monomial": {
            "A": str(A5), "B": str(B5), "ok": enclosure_ok
        },
        "all_checks_pass": ok,
    }
    if args.json:
        print(json.dumps(rep, indent=1))
    else:
        print("Theorem P constants: %s" % ("PASS" if ok else "FAIL"))
        print("  delta", delta, "deriv", deriv, ">1/50", deriv_gt_floor)
        print("  Q(1,5)=q_*", Q15 == q_star)
        print("  constant-term countermodel", const_ok)
        print("  signed interpolant countermodel", signed_ok)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
