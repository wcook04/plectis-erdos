#!/usr/bin/env python3
"""Exact scalar replay for TypeBReturnAssimilation20260831.md.

This checks the rational counterexample to the returned top-two-mass
equivalence, the actual-area strengthening, the sharp radial no-go algebra,
and the finite interval selector formula.  The analytic coarea, Bergman-area,
and lollipop arguments remain ordinary mathematics in the note.
"""

from __future__ import annotations

from fractions import Fraction as Q

import sympy as sp


def report(name: str, condition: bool, detail: str = "") -> None:
    print(("PASS " if condition else "FAIL ") + name + (f" :: {detail}" if detail else ""))
    if not condition:
        raise AssertionError(name)


# Return 05 correction.  Squared reciprocal-vector moduli are proportional to
# 36, 24, 20, hence the normalized weights below.
weights = (Q(9, 20), Q(3, 10), Q(1, 4))
report(
    "top-two mass does not imply the second-weight threshold",
    sum(weights) == 1
    and weights[0] + weights[1] >= Q(2, 3)
    and weights[1] < Q(1, 3),
    f"weights={weights}, top-two={weights[0] + weights[1]}",
)


# Actual area is a genuine strengthening: the admissible right side decreases
# and the left side increases with the scalar area parameter.
alpha, kappa2, K, L2, S = sp.symbols(
    "alpha kappa2 K L2 S", positive=True, real=True
)
capacity_slack = 4 * (L2 - kappa2 * S) - sp.pi * kappa2 * K
area_slack = 4 * (L2 - alpha * S) - sp.pi * alpha * K
report(
    "actual-area slack dominates capacity slack",
    sp.simplify(
        area_slack
        - capacity_slack
        - (kappa2 - alpha) * (sp.pi * K + 4 * S)
    )
    == 0,
)


# The radial no-go substitution.  K_Q > 4 L^2/k and S_Q >= L^2/k force
# (pi+1)kappa^2 < k whenever the returned strict criterion can hold.
k, kap2, ell2 = sp.symbols("k kap2 ell2", positive=True, real=True)
forced_gap = sp.expand(
    4 * (1 - kap2 / k) * ell2 - sp.pi * kap2 * (4 * ell2 / k)
)
report(
    "radial no-go factorization",
    sp.simplify(forced_gap - 4 * ell2 * (k - (sp.pi + 1) * kap2) / k)
    == 0,
)


# Star entrance: K_min=4kq^2/eta.  Factor the exact success slack.
eta, q = sp.symbols("eta q", positive=True, real=True)
star_slack = sp.expand(
    4 * (k**2 * q**2 - kap2 * k * q**2)
    - sp.pi * kap2 * (4 * k * q**2 / eta)
)
star_expected = 4 * k * q**2 * (k * eta - kap2 * (sp.pi + eta)) / eta
report("star-selector threshold factorization", sp.simplify(star_slack - star_expected) == 0)


# The one-interval finite-energy formula reduces to the returned optimum.
r = sp.symbols("r", positive=True, real=True)
finite_one_cell = 4 * k * q**2 / (1 - r**2)
returned_one_cell = 4 * k * q**2 / eta
report(
    "finite selector reproduces the star cell",
    sp.simplify(finite_one_cell.subs(r**2, 1 - eta) - returned_one_cell) == 0,
)


# Exact scalar placement of the source-current quintic two-sheet area bound
# relative to the best possible radial threshold.  Use 333/106 < pi to keep
# the comparison rational and strict: 2/(pi+1) < 212/439 < 0.483.
area_upper_without_tiny_gap = sp.real_root(Q(1, 4), 5) ** 2
report(
    "quintic two-sheet capacity area remains above radial ceiling",
    sp.N(area_upper_without_tiny_gap, 30) > sp.N(2 / (sp.pi + 1), 30),
    f"area<{sp.N(area_upper_without_tiny_gap, 16)}, radial<{sp.N(2/(sp.pi+1), 16)}",
)


# The quadratic family is outside the necessary radial region for every
# 0<r<1: k=2, kappa=1 gives pi+1<2, which is false already from pi>3.
report("quadratic radial obstruction", not (sp.pi + 1 < 2))

print("ALL CHECKS PASSED")
