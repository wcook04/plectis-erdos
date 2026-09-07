#!/usr/bin/env python3
"""Receipt for the general-degree straight-spoke identity.

Companion to [`../GeneralSpokeIdentity.md`](../GeneralSpokeIdentity.md).

Normalise a critical point of a monic degree-``n`` polynomial to the origin and
scale by ``f(c)^(1/n)``, so the normalised polynomial is

    G(w) = w^n + a_{n-1} w^{n-1} + ... + a_2 w^2 + 1

with no linear term (exactly ``G'(0) = 0``) and ``G(0) = 1``.  For ``w`` a ROOT
of ``G``, set ``c_k = a_k w^k``; then ``sum_{k>=2} c_k = -1`` and

    **(S)**   G(tw) = (1 - t^2) - t^2 (1 - t) Q(t),
              Q(t)  = sum_{k>=3} c_k (1 + t + ... + t^{k-3}),

whence, since ``1 - t^2 >= 0`` on ``[0,1]``,

    **(SC)**  (1 - t) |Q(t)| <= 1 on [0,1]   ==>   |G| <= 1 on the whole spoke.

At ``n = 3`` this is verbatim the identity of ``CubicCriticalHub.md``,
``G(tw) = 1 - t^2 - t^2 (1-t) w^3``, whose condition is ``|w| <= 1``.

This script checks three things and exits non-zero if any fails:

1.  (S) symbolically, with the root relation imposed, at several degrees;
2.  the ``n = 3`` reduction to the recorded cubic identity;
3.  (SC) numerically -- that whenever the criterion holds for a sampled root of
    a sampled normalised polynomial, ``|G|`` really does stay at or below 1 along
    the whole spoke.

It proves nothing about Erdos #1041; (SC) is sufficient, not necessary, and
supplies no length bound on its own.
"""
from __future__ import annotations

import argparse
import json
import sys
from typing import Any

import numpy as np

DEFAULT_DEGREES = (3, 4, 5, 6)
SPOKE_SAMPLES = 4001
NUMERIC_TOLERANCE = 1.0e-9


def symbolic_identity_residuals(degrees) -> dict[str, str]:
    import sympy as sp

    t, w = sp.symbols("t w")
    residuals: dict[str, str] = {}
    for degree in degrees:
        lower = sp.symbols(f"a2:{degree}")            # a_2 .. a_{degree-1}
        coefficients = {2 + i: lower[i] for i in range(len(lower))}
        coefficients[degree] = sp.Integer(1)
        terms = {k: coefficients[k] * w ** k for k in coefficients}
        # impose sum_k c_k = -1 by solving for the lowest free coefficient
        relation = sp.Eq(sum(terms.values()), -1)
        solution = sp.solve(relation, lower[0], dict=True)[0]
        quotient = sum(
            terms[k] * sum(t ** j for j in range(k - 2))
            for k in sorted(terms)
            if k >= 3
        )
        left = (1 + sum(coefficients[k] * (t * w) ** k for k in sorted(coefficients)))
        right = (1 - t ** 2) - t ** 2 * (1 - t) * quotient
        residual = sp.simplify(sp.expand((left - right).subs(solution)))
        residuals[str(degree)] = str(residual)
    return residuals


def cubic_reduction_residual() -> str:
    import sympy as sp

    t, w, a2 = sp.symbols("t w a2")
    solution = sp.solve(sp.Eq(a2 * w ** 2 + w ** 3, -1), a2, dict=True)[0]
    left = sp.expand((1 + a2 * (t * w) ** 2 + (t * w) ** 3).subs(solution))
    right = sp.expand(1 - t ** 2 - t ** 2 * (1 - t) * w ** 3)
    return str(sp.simplify(left - right))


def normalised_polynomial(degree: int, rng: np.random.Generator) -> np.ndarray:
    """Coefficients of ``G`` in numpy order, highest power first."""
    coefficients = np.zeros(degree + 1, dtype=complex)
    coefficients[0] = 1.0
    for index in range(2, degree):                    # a_{degree-1} .. a_2
        coefficients[degree - index] = (
            rng.standard_normal() + 1j * rng.standard_normal()
        )
    coefficients[degree] = 1.0                        # constant term G(0) = 1
    return coefficients


def criterion_and_spoke_max(
    coefficients: np.ndarray, root: complex
) -> tuple[float, float]:
    """Return ``max_t (1-t)|Q(t)|`` and ``max_t |G(tw)|`` on the spoke."""
    degree = len(coefficients) - 1
    powers = {k: coefficients[degree - k] for k in range(degree + 1)}
    terms = {k: powers[k] * root ** k for k in range(2, degree + 1)}
    grid = np.linspace(0.0, 1.0, SPOKE_SAMPLES)
    quotient = np.zeros_like(grid, dtype=complex)
    for k in range(3, degree + 1):
        partial = np.zeros_like(grid, dtype=complex)
        for exponent in range(k - 2):
            partial = partial + grid ** exponent
        quotient = quotient + terms[k] * partial
    criterion = float(np.max((1.0 - grid) * np.abs(quotient)))
    spoke = np.polyval(coefficients, grid * root)
    return criterion, float(np.max(np.abs(spoke)))


def numeric_rows(degrees, trials: int, seed: int) -> dict[str, Any]:
    rng = np.random.default_rng(seed)
    checked = 0
    criterion_holds = 0
    violations = 0
    worst_excess = 0.0
    for degree in degrees:
        for _ in range(trials):
            coefficients = normalised_polynomial(degree, rng)
            for root in np.roots(coefficients):
                checked += 1
                criterion, spoke_max = criterion_and_spoke_max(coefficients, root)
                if criterion <= 1.0:
                    criterion_holds += 1
                    if spoke_max > 1.0 + NUMERIC_TOLERANCE:
                        violations += 1
                        worst_excess = max(worst_excess, spoke_max - 1.0)
    return {
        "roots_checked": checked,
        "criterion_satisfied": criterion_holds,
        "criterion_satisfied_but_spoke_left_unit_level": violations,
        "worst_excess_over_one": worst_excess,
    }


def build_payload(degrees, trials: int, seed: int) -> dict[str, Any]:
    residuals = symbolic_identity_residuals(degrees)
    reduction = cubic_reduction_residual()
    numeric = numeric_rows(degrees, trials, seed)
    return {
        "schema": "erdos1041_general_spoke_identity_v0",
        "boundary": (
            "an identity and a sufficient containment criterion; proves nothing "
            "about Erdos 1041 and supplies no length bound"
        ),
        "degrees": list(degrees),
        "symbolic_identity_residuals": residuals,
        "cubic_reduction_residual": reduction,
        "numeric": numeric,
        "identity_holds": all(value == "0" for value in residuals.values()),
        "cubic_reduction_holds": reduction == "0",
        "criterion_sound": numeric["criterion_satisfied_but_spoke_left_unit_level"] == 0,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trials", type=int, default=120)
    parser.add_argument("--seed", type=int, default=20260823)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    payload = build_payload(DEFAULT_DEGREES, args.trials, args.seed)

    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        for degree, residual in sorted(payload["symbolic_identity_residuals"].items()):
            print(f"  n={degree}: identity residual = {residual}")
        print(f"  n=3 reduction to CubicCriticalHub identity = "
              f"{payload['cubic_reduction_residual']}")
        numeric = payload["numeric"]
        print(f"  roots checked                       : {numeric['roots_checked']}")
        print(f"  criterion (SC) satisfied            : "
              f"{numeric['criterion_satisfied']}")
        print(f"  satisfied but spoke exceeded one    : "
              f"{numeric['criterion_satisfied_but_spoke_left_unit_level']}")

    if not payload["identity_holds"]:
        print("GUARD FAILED: identity (S) no longer simplifies to zero.",
              file=sys.stderr)
        return 1
    if not payload["cubic_reduction_holds"]:
        print("GUARD FAILED: the n=3 case no longer reduces to the recorded "
              "cubic identity.", file=sys.stderr)
        return 1
    if not payload["criterion_sound"]:
        print("GUARD FAILED: criterion (SC) held while the spoke left level one; "
              "the criterion as stated is unsound.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
