#!/usr/bin/env python3
"""Falsification probes for the polygonal-shortening and nodal-deficit statements.

Three independent checks, all finite and all falsification-only.  The universal
quantifiers live in the analytic sources named at the bottom of this docstring;
nothing here is a proof oracle.

``polygon_max``   Lemma 4.2 of TraceCurvatureMeasureAndPolygonalShortening.md:
                  for the regular ``d``-gon ``P_s`` with circumradius ``s`` and
                  ``s^d <= b``, ``max_{u in P_s} |b - u^d| = b + s^d
                  cos^d(pi/d)``, attained at an edge midpoint.  Checked for
                  ``d = 3..10`` on random admissible ``(b, s)`` by dense
                  sampling of the polygon boundary, which is where the maximum
                  modulus of the holomorphic function ``b - u^d`` must sit.

``first_variation``  the polygon replaces the corpus lollipop coefficient
                  ``1 - pi/n`` of GroupedCriticalClusterMonodromy.md by
                  ``1 - sin(pi/n)``.  Since ``sin(x) < x`` on ``(0, pi]``, the
                  polygon subtracts strictly more in every degree, and the
                  admissibility constraint gains the factor ``cos^n(pi/n) < 1``.
                  In degree three the sign of the first variation flips:
                  ``L_circle = 2r + 2(pi/3 - 1)s`` grows with ``s`` while
                  ``L_polygon = 2r - (2 - sqrt(3))s`` shrinks.

``beta_calibration``  the exact deficit (13) of
                  NodalCroftonBudgetAndCyclicPullbacks.md for
                  ``Gamma_n = {Re z^n = 1}``,
                  ``D = (n-1) B(1 - 1/(2n), 1/2)``, checked against the
                  renormalised arclength ``lim_S (2 n S - H^1(Gamma_n cap
                  D(0,S)))`` computed by a singularity-removing quadrature,
                  and against the gamma-quotient form
                  ``2 n sqrt(pi) Gamma(1 - 1/(2n)) / Gamma(1/2 - 1/(2n))``.

Authority: TraceCurvatureMeasureAndPolygonalShortening.md sections 4-5 and
NodalCroftonBudgetAndCyclicPullbacks.md section 2.  Neither closes Erdos 1041.
"""

from __future__ import annotations

import cmath
import json
import math
import random

BOUNDARY_SAMPLES = 3000
POLYGON_TOLERANCE = 1e-11
QUADRATURE_NODES = 400000
CALIBRATION_TOLERANCE = 1e-8


def polygon_boundary_max(b: float, s: float, d: int) -> float:
    """Dense boundary maximum of ``|b - u^d|`` over the regular ``d``-gon."""

    best = 0.0
    for j in range(d):
        first = s * cmath.exp(2j * math.pi * j / d)
        second = s * cmath.exp(2j * math.pi * (j + 1) / d)
        for k in range(BOUNDARY_SAMPLES + 1):
            point = first + (second - first) * (k / BOUNDARY_SAMPLES)
            best = max(best, abs(b - point**d))
    return best


def check_polygon_max() -> dict:
    rng = random.Random(20260905)
    worst = 0.0
    instances = 0
    for degree in range(3, 11):
        for _ in range(12):
            s = rng.uniform(0.05, 1.0)
            b = rng.uniform(s**degree, 4.0)
            predicted = b + s**degree * math.cos(math.pi / degree) ** degree
            observed = polygon_boundary_max(b, s, degree)
            worst = max(worst, abs(observed - predicted) / predicted)
            # the midpoint of an edge is the attaining point
            midpoint = s * math.cos(math.pi / degree) * cmath.exp(
                1j * math.pi / degree
            )
            assert abs(abs(b - midpoint**degree) - predicted) < 1e-12 * predicted
            instances += 1
    assert worst < POLYGON_TOLERANCE, worst
    return {
        "degrees": "3..10",
        "instances": instances,
        "max_relative_error": worst,
        "boundary_samples_per_edge": BOUNDARY_SAMPLES,
    }


def check_first_variation() -> dict:
    rows = []
    for n in range(3, 13):
        polygon = 1.0 - math.sin(math.pi / n)
        circle = 1.0 - math.pi / n
        assert polygon > circle, n
        assert math.cos(math.pi / n) ** n < 1.0
        rows.append(
            {
                "n": n,
                "polygon_coefficient": polygon,
                "lollipop_coefficient": circle,
                "gain": polygon - circle,
                "admissibility_factor": math.cos(math.pi / n) ** n,
            }
        )
    # degree three: the circular first variation has the wrong sign
    r, s = 0.9, 0.05
    circle_length = 2 * r + 2 * (math.pi / 3 - 1) * s
    polygon_length = 2 * r - (2 - math.sqrt(3)) * s
    assert circle_length > 2 * r > polygon_length
    assert abs(polygon_length - (2 * r - 2 * s * (1 - math.sin(math.pi / 3)))) < 1e-15
    return {
        "rows": rows,
        "degree_three_circle_length": circle_length,
        "degree_three_polygon_length": polygon_length,
        "degree_three_sign_flip": True,
    }


def nodal_deficit_quadrature(n: int) -> float:
    """``lim_S (2 n S - H^1({Re z^n = 1} cap D(0,S)))`` by quadrature.

    Each of the ``2 n`` ends satisfies ``ds/dr = (1 - r^{-2n})^{-1/2}`` for
    ``r >= 1``, so the truncated length is ``2 n int_1^S (1 - r^{-2n})^{-1/2}
    dr`` and the deficit is ``2 n [1 - int_1^inf ((1-r^{-2n})^{-1/2} - 1) dr]``.
    Substituting ``r^{-2n} = sin^2(phi)`` removes both endpoint singularities.
    """

    excess = 0.0
    step = (math.pi / 2) / QUADRATURE_NODES
    for k in range(QUADRATURE_NODES):
        phi = (k + 0.5) * step
        x = math.sin(phi) ** 2
        dr = (
            (1 / (2 * n))
            * x ** (-1 / (2 * n) - 1)
            * 2
            * math.sin(phi)
            * math.cos(phi)
            * step
        )
        excess += (1 / math.cos(phi) - 1) * dr
    return 2 * n * (1 - excess)


def check_beta_calibration() -> dict:
    rows = []
    for n in (2, 3, 4):
        beta_form = (n - 1) * math.exp(
            math.lgamma(1 - 1 / (2 * n))
            + math.lgamma(0.5)
            - math.lgamma(1.5 - 1 / (2 * n))
        )
        gamma_form = (
            2
            * n
            * math.sqrt(math.pi)
            * math.exp(math.lgamma(1 - 1 / (2 * n)) - math.lgamma(0.5 - 1 / (2 * n)))
        )
        quadrature = nodal_deficit_quadrature(n)
        assert abs(beta_form - gamma_form) < CALIBRATION_TOLERANCE * beta_form
        assert abs(beta_form - quadrature) < 1e-7 * beta_form, (n, beta_form, quadrature)
        # the deficit is strictly positive, so the sharp budget 2 n R is not
        # attained on this family
        assert quadrature > 0
        rows.append(
            {
                "n": n,
                "beta_form": beta_form,
                "gamma_form": gamma_form,
                "renormalised_quadrature": quadrature,
            }
        )
    assert abs(rows[0]["beta_form"] - 2.3962804694711844) < 1e-12
    return {"rows": rows}


def main() -> None:
    print(
        json.dumps(
            {
                "status": "pass",
                "polygon_max": check_polygon_max(),
                "first_variation": check_first_variation(),
                "beta_calibration": check_beta_calibration(),
                "evidence_class": "deterministic_floating_point_falsification_only",
                "universal_authority": [
                    "TraceCurvatureMeasureAndPolygonalShortening.md",
                    "NodalCroftonBudgetAndCyclicPullbacks.md",
                ],
            }
        )
    )


if __name__ == "__main__":
    main()
