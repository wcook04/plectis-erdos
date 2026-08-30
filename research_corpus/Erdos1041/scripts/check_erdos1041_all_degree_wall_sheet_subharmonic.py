#!/usr/bin/env python3
"""Exact algebra checks for the all-degree tight-gap wall normalization."""

from __future__ import annotations

import sympy as sp


def report(name: str, ok: bool, detail: str = "") -> None:
    print(("PASS " if ok else "FAIL ") + name + ((" :: " + detail) if detail else ""))
    if not ok:
        raise AssertionError(name)


def degree_gap_check(n: int) -> bool:
    y, c, alpha = sp.symbols(f"y c alpha_{n}", nonzero=True)
    # Independent exact coefficients are enough: the critical equations only
    # select the parameter manifold and are not used in the terminal identity.
    coeffs = [sp.Symbol(f"r_{n}_{k}") for k in range(n - 1)]
    z = sp.Symbol(f"z_{n}")
    R = sum(coeffs[k] * z**k for k in range(n - 1))
    H = z**n + R
    lam = alpha**n
    P = sp.expand((H.subs(z, c + alpha * y) - H.subs(z, c)) / lam)
    C = c / alpha
    Q = sp.Poly(sp.cancel(P - (y + C) ** n), y)
    return Q.degree() <= n - 2 and sp.expand(P).coeff(y, n) == 1 and sp.expand(P).coeff(y, n - 1) == n * C


def ray_freeze_check(epsilon: int) -> bool:
    # lambda=3+4i has exact modulus five.  The physical ray direction is
    # epsilon*i*lambda/|lambda| and s=|lambda|*tau.
    tau = sp.symbols("tau", positive=True)
    lam = sp.Integer(3) + sp.Integer(4) * sp.I
    modulus = sp.Integer(5)
    d = epsilon * sp.I * lam / modulus
    s = modulus * tau
    return sp.simplify(d * s / lam - epsilon * sp.I * tau) == 0


def terminal_order_check(n: int) -> bool:
    # If w=T*eta+a/T, the first correction to w^n is order T^(n-2),
    # exactly matching the largest allowed lower term.  Differentiating
    # T^(-1), T=tau^(1/n), gives tau^(-1-1/n).
    T, eta, a = sp.symbols(f"T eta a_{n}", nonzero=True)
    w = eta * T + a / T
    expanded = sp.Add.make_args(sp.expand(w**n))
    powers = [int(term.as_powers_dict().get(T, 0)) for term in expanded]
    second_degree = max(power for power in powers if power < n)
    tau = sp.symbols(f"tau_{n}", positive=True)
    derivative = sp.diff(tau ** (-sp.Rational(1, n)), tau)
    expected = -sp.Rational(1, n) * tau ** (-1 - sp.Rational(1, n))
    return second_degree == n - 2 and sp.simplify(derivative - expected) == 0


def main() -> int:
    report("W1 exact ray freezing, epsilon=+1", ray_freeze_check(+1))
    report("W2 exact ray freezing, epsilon=-1", ray_freeze_check(-1))
    degrees = range(2, 13)
    gap = {n: degree_gap_check(n) for n in degrees}
    report("W3 centred terminal degree gap n=2..12", all(gap.values()), str(gap))
    orders = {n: terminal_order_check(n) for n in degrees}
    report("W4 inverse terminal correction orders n=2..12", all(orders.values()), str(orders))
    print("ALL PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
