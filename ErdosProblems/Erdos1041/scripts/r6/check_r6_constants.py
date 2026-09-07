#!/usr/bin/env python3
"""Exact scalar checks for the round-six ordinary proof.

Python 3.10+, standard library only. This is not an analytic path checker.
The universal complex-analytic and topological arguments are in the report.
"""
from __future__ import annotations
from fractions import Fraction as Q
from math import comb
import json

if not __debug__:
    raise RuntimeError("Run without -O: exact assertions must remain enabled")


def atan_bounds(x: Q, terms: int = 60) -> tuple[Q, Q]:
    if not 0 < x < 1 or terms < 2:
        raise ValueError("Require 0 < x < 1 and at least two terms")
    s = sum(((-1) ** k * x ** (2*k+1) / (2*k+1)
             for k in range(terms)), Q(0))
    other = s + (-1) ** terms * x ** (2*terms+1) / (2*terms+1)
    return min(s, other), max(s, other)


def exp_upper(x: Q, terms: int = 70) -> Q:
    if not 0 <= x < 1:
        raise ValueError("This bound is implemented only for 0 <= x < 1")
    term = Q(1)
    s = term
    for k in range(1, terms+1):
        term *= x / k
        s += term
    next_term = term*x/(terms+1)
    return s + next_term / (1-x/(terms+2))


def main() -> None:
    lo5, hi5 = atan_bounds(Q(1, 5))
    lo239, hi239 = atan_bounds(Q(1, 239))
    pi_lo, pi_hi = 16*lo5-4*hi239, 16*hi5-4*lo239
    assert 3 < pi_lo < pi_hi < Q(22, 7)
    assert Q(25, 13) < Q(5, 4)**3
    assert Q(25, 3**5) < 1  # the maximum of 25/N^(2N-1), N >= 3
    assert Q(49, 50)-Q(1, 10) == Q(22, 25)
    assert Q(11, 25)-Q(2, 5) == Q(1, 25)
    derivative_weight = 1+Q(100, 99)
    assert derivative_weight < 3
    error = (1+Q(22, 21))/10 + 3*Q(1, 100)*(2+Q(22, 21))
    assert error == Q(311, 1050)
    saving = 2-Q(22, 21)-error
    assert saving == Q(689, 1050) > Q(3, 5)
    assert Q(2, 1)/(1-Q(1, 10)) == Q(20, 9)

    lower_t, b, angle = Q(13, 15), Q(1, 120), Q(11, 42)
    assert lower_t**23 < Q(1, 25)
    length = (2-(2-angle)*lower_t
              + b*(1-(1-angle)*lower_t**2)
              +3*b*b*(2*(1/lower_t-1)+angle/lower_t))
    assert length == Q(58672129, 117936000) < Q(1, 2)
    collar_x = Q(1, 10)*lower_t/25
    assert collar_x == Q(13, 3750)
    collar = 1/(1+collar_x)
    assert collar == Q(3750, 3763) < 1

    # Polynomial coefficient cancellation, exact finite regressions only.
    regressions = []
    for N in range(3, 17):
        bN = Q(1, 10*N)
        coeff = [Q(0)]*(2*N+1)
        for k in range(N+1):
            coeff[2*N-k] += comb(N, k)*bN**k
            coeff[k] -= comb(N, k)*bN**k
        delta = sum(abs(coeff[k]) for k in range(1, 2*N))
        assert coeff[0] == -1 and coeff[-1] == 1
        assert coeff[N] == 0
        assert delta == 2*((1+bN)**N-1-bN**N)
        assert 2*N*bN <= delta <= Q(20, 9)*N*bN
        regressions.append(N)

    X = Q(635762889599, 10**12)
    terminal = Q(13, 25)*exp_upper(X)
    assert terminal < 1
    output = {
        'status': 'pass',
        'evidence': 'exact rational constants; finite coefficient regressions; not full analytic formalisation',
        'pi_upper_less_than': '22/7',
        'scale_base_comparison': '25/13 < (5/4)^3',
        'uniform_length_saving': str(saving),
        'degree24_t_lower': str(lower_t),
        'degree24_length_upper': str(length),
        'degree24_level_upper': str(collar),
        'coefficient_regression_N': regressions,
        'terminal_exponential_pass': True,
        'angular_certificate_X_assumed_for_this_terminal_check': str(X),
        'analytic_proof': 'report/research_report.tex, Sections 2--5',
    }
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
