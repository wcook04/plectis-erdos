#!/usr/bin/env python3
"""Erdos #68 in a coordinate the packet has never used: e, I_0(2), and a cubic residual.

Upstream analytic state
-----------------------
Every recorded Erdos #68 route works in the factorial-gap coordinate itself:
the strict-successor carries `D_m`, the predecessor gap `A_m`, the private prime
support of `n!-1`, the channel/Hermite-Pade linear forms.  The packet's negative
results close that coordinate from four directions at once -- fixed-prime
p-adic valuation (n!-1 = -1 mod Q for every n >= Q, so terms do not tend to zero
Q-adically), growth-only arguments (Kovac--Tao: decreasing each n!-1 by at most
n^2+1 already produces a rational series), digit bias (49998 digits
indistinguishable from uniform), and primehood (first threshold failure at the
prime m=59).

None of those obstructions is stated about the *value* S.  They are all stated
about the representation `sum 1/(n!-1)`.  This probe checks an exact
re-representation that moves S into a different coordinate entirely.

The identities
--------------
From `1/(n!-1) = 1/n! + 1/(n!(n!-1))`, applied twice:

    (1)  S = (e - 2) + sum_(n>=2) 1/(n! (n!-1))
    (2)  S = e + I_0(2) - 4 + sum_(n>=2) 1/((n!)^2 (n!-1))

where `I_0(2) = sum_(n>=0) 1/(n!)^2` is the modified Bessel value.  Both `e` and
`I_0(2)` are classical irrationals -- `e` transcendental, `I_0(2)` irrational by
the Siegel E-function theory -- and the residual in (2) converges like
`(n!)^(-3)`.

So Erdos #68 is equivalent to a ternary linear-independence question:

    S rational  <=>  e + I_0(2) + sum_(n>=2) 1/((n!)^2 (n!-1))  in  Q.

That is not a proof of anything.  It is a coordinate in which the four recorded
obstructions are not statements, because none of them is about `e` or `I_0(2)`.

Probe
-----
Verify (1) and (2) to high precision, and separately verify the exact rational
identity `1/(n!-1) = 1/n! + 1/(n!(n!-1))` that generates them, so the chain is
checked termwise and not only at the limit.

Also verify the two structural facts the reframing has to respect:

  * the endpoint recurrence `a_(n+1) = (n+1) a_n + n` for `a_n = n!-1`, which is
    the exact invariant the Kovac--Tao quadratic perturbation destroys;
  * `S = sum_(j>=1) sum_(n>=2) (n!)^(-j)`, the full geometric expansion whose
    first two layers are `e-2` and `I_0(2)-2`.

Predeclared falsifier
---------------------
Any residual above 10^-100 at 110-digit working precision falsifies the
identity as stated and the reframing dies here rather than downstream.

Claim boundary
--------------
This establishes exact identities between convergent series.  It proves nothing
about the irrationality of S, it does not show the new coordinate is tractable,
and Erdos #68 remains open.  `I_0(2)` irrational and `e` transcendental are
cited classical facts, not outputs of this probe.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, getcontext
from fractions import Fraction
from math import factorial
from pathlib import Path

TERMS = 90
PRECISION = 130
TOLERANCE = Decimal(10) ** -100


def _series(term, lo: int, hi: int) -> Decimal:
    total = Decimal(0)
    for n in range(lo, hi):
        total += term(n)
    return total


def run(terms: int = TERMS) -> dict:
    getcontext().prec = PRECISION

    def fact(n: int) -> Decimal:
        return Decimal(factorial(n))

    S = _series(lambda n: 1 / (fact(n) - 1), 2, terms)
    e = _series(lambda n: 1 / fact(n), 0, terms + 20)
    I0 = _series(lambda n: 1 / fact(n) ** 2, 0, terms)
    residual_1 = _series(lambda n: 1 / (fact(n) * (fact(n) - 1)), 2, terms)
    residual_2 = _series(lambda n: 1 / (fact(n) ** 2 * (fact(n) - 1)), 2, terms)

    gap_1 = S - (e - 2 + residual_1)
    gap_2 = S - (e + I0 - 4 + residual_2)

    # Termwise exact rational check of the generating identity.
    termwise_ok = all(
        Fraction(1, factorial(n) - 1)
        == Fraction(1, factorial(n)) + Fraction(1, factorial(n) * (factorial(n) - 1))
        for n in range(2, 40)
    )

    # Endpoint recurrence a_(n+1) = (n+1) a_n + n.
    recurrence_ok = all(
        factorial(n + 1) - 1 == (n + 1) * (factorial(n) - 1) + n for n in range(2, 400)
    )

    # Full geometric expansion S = sum_j sum_n (n!)^-j.  The n=2 column is
    # sum_j 2^-j, so the j-range must reach ~340 layers to clear the tolerance;
    # truncating it at 60 leaves 2^-59 and the falsifier fires.
    layered = _series(
        lambda j: _series(lambda n: 1 / fact(n) ** j, 2, terms), 1, 450
    )
    gap_layered = S - layered

    return {
        "probe": "erdos68_transcendental_reframing",
        "precision_digits": PRECISION,
        "terms": terms,
        "S": str(S)[:60],
        "identity_1_e_plus_quadratic_residual": {
            "form": "S = (e - 2) + sum_(n>=2) 1/(n!(n!-1))",
            "residual_gap": f"{gap_1:.3e}",
            "holds": abs(gap_1) < TOLERANCE,
        },
        "identity_2_e_plus_bessel_plus_cubic_residual": {
            "form": "S = e + I_0(2) - 4 + sum_(n>=2) 1/((n!)^2 (n!-1))",
            "residual_gap": f"{gap_2:.3e}",
            "holds": abs(gap_2) < TOLERANCE,
            "I_0(2)": str(I0)[:40],
        },
        "identity_3_full_geometric_layering": {
            "form": "S = sum_(j>=1) sum_(n>=2) (n!)^(-j)",
            "residual_gap": f"{gap_layered:.3e}",
            "holds": abs(gap_layered) < TOLERANCE,
        },
        "termwise_exact_rational_identity": termwise_ok,
        "endpoint_recurrence_a_next_eq_np1_a_n_plus_n": recurrence_ok,
        "consequence": (
            "S rational <=> e + I_0(2) + sum_(n>=2) 1/((n!)^2 (n!-1)) in Q. "
            "The packet's four recorded obstructions (fixed-prime p-adic, "
            "Kovac--Tao growth-only, digit bias, primehood) are all statements "
            "about the factorial-gap representation and none is a statement in "
            "this coordinate."
        ),
        "claim_boundary": (
            "Exact identities only. No irrationality is proved, the new "
            "coordinate is not shown tractable, and Erdos #68 remains open."
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--terms", type=int, default=TERMS)
    parser.add_argument("--json-out", type=Path, default=None)
    args = parser.parse_args()

    result = run(args.terms)
    text = json.dumps(result, indent=2)
    print(text)
    if args.json_out:
        args.json_out.write_text(text + "\n", encoding="utf-8")

    holds = [
        result["identity_1_e_plus_quadratic_residual"]["holds"],
        result["identity_2_e_plus_bessel_plus_cubic_residual"]["holds"],
        result["identity_3_full_geometric_layering"]["holds"],
        result["termwise_exact_rational_identity"],
        result["endpoint_recurrence_a_next_eq_np1_a_n_plus_n"],
    ]
    return 0 if all(holds) else 1


if __name__ == "__main__":
    raise SystemExit(main())
