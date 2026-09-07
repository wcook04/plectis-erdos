#!/usr/bin/env python3
"""Erdős #1041: evidence on the corpus's STRONG first-merge completion.

This probe does not introduce the reduction it tests.  ``MinimumCriticalNewtonHubLab.md``
already proves, as ordinary mathematics, the first-merge reduction and the
discriminant/Fekete sandwich, and already names the two completions:

    rho = |f(c)|^(1/n)  at a minimum-modulus critical point satisfies rho <= R,
    because  |Disc f| = n^n prod |f(d)| >= n^n |f(c)|^(n-1)  meets the
    Fekete/Hadamard bound  |Disc f| <= n^n R^(n(n-1)),

    strong:  L_1 + L_2 <= 2 rho          (implies the weak one, exact on the
    weak:    L_1 + L_2 <= 2 R             regular family, "but it may be false")

and it records ``critical-scale-normalized-minimum-critical-newton-hub`` as the
dedicated one-way falsifier for the strong statement, whose canonical
degree-five run reached 0.9495242630078684 without crossing one.

What this probe adds to that record is falsification pressure and structure, not
the statement:

* **Multi-seeded adversarial pressure.**  Five independent seedings -- near
  extremal, uniform, clustered, near-collision, and a combined restart -- drive
  the strong ratio to 0.999994283 at degree three, an order of magnitude closer
  to the boundary than the canonical run, and none crosses.  Running several
  seedings is the point: a single basin pinned below a threshold proved nothing
  for the straight completion, which sat at 1.9999... across degrees three to
  twelve and was false.
* **A complete cubic parameter sweep.**  The normalised cubic is
  ``P(u) = u^3 + s u^2 + 1`` with critical points ``0`` and ``-2s/3`` and
  ``P(-2s/3) = 1 + 4 s^3 / 27``, so minimality is exactly
  ``|1 + 4 s^3 / 27| >= 1`` and the whole degree-three case is a sweep over one
  complex parameter -- complete rather than sampled.
* **A second exact equality family.**  Every monic quadratic satisfies the
  strong statement with equality: ``f(c+u) = u^2 - d^2`` gives
  ``L = |z1 - z2| = 2|d|`` and ``|f(c)| = |d|^2``, so ``L = 2|f(c)|^(1/2)``
  exactly.  The lab records ``z^n - r^n``; the quadratics are a second family,
  and both are affine conjugates of ``z^n - 1``.
* **The extremum is a cusp.**  At ``z^n - r^n`` the critical point at the origin
  has multiplicity ``n-1``.  Splitting it drops the ratio by a fractional power
  of the perturbation: at degree five, perturbation 1e-9 gives 0.99648, 1e-6
  gives 0.98012, 1e-3 gives 0.88553.  A second-order variational argument at the
  extremum will not see the right behaviour.
* **A per-hub elimination.**  ``L(c) <= 2 max_k |z_k - c|`` at every critical
  point is tight on both equality families but false, so minimality is
  load-bearing in the strong statement too, not only in the straight one.

Engine limitation recorded here: at a *degenerate* critical point the two-branch
substitution ``f(z(u)) = (1-u^2) f(c)`` is the wrong local model -- all ``n``
preimages are equidistant from the hub and the field is stiff at the start -- so
``descending_pair`` under-reports the length there.  On ``z^n - r^n`` it returns
1.7989 rather than the true ``2r = 1.8`` at degree six.  The under-report is in
the conservative direction for the conjecture, and the equality family is
therefore asserted from its ordinary proof, not from the integrator.

Numerical continuation is candidate evidence.  The strong statement is not
proved here and Erdős #1041 remains open.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any

import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)
from system.lib.formal_math_lemniscate import (  # noqa: E402
    coefficients_from_roots,
    critical_table,
    descending_pair,
    minimal_critical_value_hub,
)

SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/"
    "check_erdos1041_minimal_hub_metric_scale.py"
)
ENGINE_REF = "system/lib/formal_math_lemniscate.py"
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "StraightSpokeHubCriterionLab.md"
)
PACKET_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/research_packet.json"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1041_minimal_hub_metric_scale_receipt.json"
)

TOLERANCES = {"relative_tolerance": 1.0e-11, "absolute_tolerance": 1.0e-13}


def minimal_hub_ratio(roots: np.ndarray) -> float | None:
    """``L(c*) / (2 |f(c*)|^{1/n})`` at the least-critical-value hub."""

    roots = np.asarray(roots, dtype=np.complex128)
    degree = len(roots)
    hub = minimal_critical_value_hub(roots)
    if hub is None:
        return None
    value = hub["critical_value_modulus"]
    if value <= 1.0e-300:
        return None
    pair = descending_pair(roots, hub["critical_point"], **TOLERANCES)
    if pair is None or pair["maximum_endpoint_error"] > 1.0e-8:
        return None
    return float(pair["total_length"] / (2.0 * value ** (1.0 / degree)))


def all_hub_ratios(roots: np.ndarray) -> list[float]:
    roots = np.asarray(roots, dtype=np.complex128)
    degree = len(roots)
    out: list[float] = []
    for row in critical_table(roots):
        value = row["critical_value_modulus"]
        if value <= 1.0e-13:
            continue
        pair = descending_pair(roots, row["critical_point"], **TOLERANCES)
        if pair is None or pair["maximum_endpoint_error"] > 1.0e-8:
            continue
        out.append(float(pair["total_length"] / (2.0 * value ** (1.0 / degree))))
    return out


def quadratic_identity(seed: int = 5, trials: int = 40) -> dict[str, Any]:
    """``L(c) = 2 |f(c)|^{1/2}`` exactly, for every monic quadratic."""

    rng = np.random.default_rng(seed)
    worst = 0.0
    counted = 0
    for _ in range(trials):
        roots = np.asarray(
            [
                complex(rng.standard_normal(), rng.standard_normal()),
                complex(rng.standard_normal(), rng.standard_normal()),
            ],
            dtype=np.complex128,
        )
        if abs(roots[0] - roots[1]) < 1.0e-3:
            continue
        ratio = minimal_hub_ratio(roots)
        if ratio is None:
            continue
        worst = max(worst, abs(ratio - 1.0))
        counted += 1
    return {
        "statement": "L(c) = |z1 - z2| = 2|d| and |f(c)| = |d|^2, so L = 2|f(c)|^{1/2}",
        "quadratics_checked": counted,
        "maximum_deviation_from_equality": worst,
    }


def pure_power_identity() -> list[dict[str, Any]]:
    """``z^n - r^n``: ``L = 2r`` and ``|f(0)| = r^n``, hence equality -- by proof.

    The branches at the origin are two radii, so the identity is ordinary
    mathematics.  What is checked numerically is the exactly-representable half,
    ``|f(0)| = r^n``; the integrator's length is recorded alongside so its
    degenerate-hub deficit stays visible instead of being asserted away.
    """

    rows: list[dict[str, Any]] = []
    for degree in (3, 4, 5, 6, 8):
        for radius in (0.6, 0.9):
            roots = radius * np.exp(2j * np.pi * np.arange(degree) / degree)
            hub = minimal_critical_value_hub(roots)
            if hub is None:
                continue
            value = hub["critical_value_modulus"]
            pair = descending_pair(roots, hub["critical_point"], **TOLERANCES)
            row = {
                "degree": degree,
                "radius": radius,
                "critical_value_modulus": value,
                "radius_to_the_degree": radius**degree,
                "critical_value_identity_error": abs(value - radius**degree),
                "true_branch_pair_length": 2 * radius,
            }
            if pair is not None:
                row["integrated_branch_pair_length"] = pair["total_length"]
                row["integrator_deficit_at_degenerate_hub"] = (
                    2 * radius - pair["total_length"]
                )
                row["ratio_from_integrator"] = pair["total_length"] / (
                    2 * value ** (1.0 / degree)
                )
            # The extremum is a CUSP: splitting the multiplicity-(n-1) critical
            # point drops the ratio by a fractional power of the perturbation.
            if radius == 0.9:
                row["perturbation_response"] = {}
                for scale in (1.0e-9, 1.0e-6, 1.0e-3):
                    perturbed = roots * np.exp(scale * np.arange(degree))
                    got = minimal_hub_ratio(perturbed)
                    if got is not None:
                        row["perturbation_response"][f"{scale:g}"] = got
            rows.append(row)
    return rows


def cusp_exponent_rows(seed: int = 20260825, directions: int = 3) -> list[dict[str, Any]]:
    """The exponent of the cusp at the extremal family.

    HardRegimeIsNearFekete.md adopts the cusp mechanism and states that any
    perturbative attack on the D-near-one side "must handle a fractional-power
    response, which is a materially harder object than a Hessian".  It does not
    give the exponent.  This measures it.

    Perturbing ``z^n - r^n`` and fitting ``log(1 - M)`` against ``log delta``
    returns ``1/(n-1)`` -- the spacing exponent of a multiplicity ``n-1``
    critical point splitting into ``n-1`` simple ones, and the same exponent
    that appears in ``T* <= D^{1/(n-1)}``.
    """

    rng = np.random.default_rng(seed)
    radius = 0.9
    rows: list[dict[str, Any]] = []
    for degree in (3, 4, 5, 6):
        base = radius * np.exp(2j * np.pi * np.arange(degree) / degree)
        scales, deficits = [], []
        for delta in (1e-9, 1e-8, 1e-7, 1e-6, 1e-5, 1e-4, 1e-3, 1e-2):
            got = []
            for _ in range(directions):
                perturbed = (
                    base
                    * (1 + delta * rng.standard_normal(degree))
                    * np.exp(1j * delta * rng.standard_normal(degree))
                )
                ratio = minimal_hub_ratio(perturbed)
                if ratio is not None:
                    got.append(1.0 - ratio)
            if got and np.mean(got) > 0:
                scales.append(delta)
                deficits.append(float(np.mean(got)))
        row: dict[str, Any] = {
            "degree": degree,
            "predicted_exponent": 1.0 / (degree - 1),
            "samples": len(scales),
        }
        if len(scales) >= 5:
            fitted = float(
                np.polyfit(np.log(np.array(scales)), np.log(np.array(deficits)), 1)[0]
            )
            row["fitted_exponent"] = fitted
            row["relative_error"] = abs(fitted - 1.0 / (degree - 1)) * (degree - 1)
            row["deficit_by_scale"] = {
                f"{s:g}": d for s, d in zip(scales, deficits, strict=True)
            }
        rows.append(row)
    return rows


def fekete_rows(seed: int = 909, trials: int = 45) -> list[dict[str, Any]]:
    """(F): the least critical-value modulus never exceeds ``R^n``.

    Checked with the circumcentre at the origin and ``R = 1`` by construction --
    roots are drawn in the closed unit disk with at least two on the circle, so
    ``R = 1`` and (F) reads ``min_j |f(c_j)| <= 1``.
    """

    rng = np.random.default_rng(seed)
    rows: list[dict[str, Any]] = []
    for degree in (3, 4, 5, 6, 8):
        worst = -1.0
        counted = 0
        for _ in range(trials):
            angles = rng.random(degree) * 2 * np.pi
            radii = np.sqrt(rng.random(degree))
            radii[0] = 1.0
            radii[1] = 1.0
            angles[1] = angles[0] + np.pi  # antipodal pair pins R = 1
            roots = radii * np.exp(1j * angles)
            values = [
                row["critical_value_modulus"]
                for row in critical_table(roots)
                if row["critical_value_modulus"] > 1.0e-13
            ]
            if not values:
                continue
            counted += 1
            worst = max(worst, min(values))
        rows.append(
            {
                "degree": degree,
                "configurations": counted,
                "maximum_of_min_critical_value_modulus": worst,
                "fekete_bound_holds": bool(worst <= 1.0 + 1.0e-9),
            }
        )
    return rows


def sweep_rows(seed: int = 20260824, trials: int = 32) -> list[dict[str, Any]]:
    """(M) at the minimal hub, against the same ratio at a general hub."""

    rng = np.random.default_rng(seed)
    rows: list[dict[str, Any]] = []
    for degree in (3, 4, 5, 6, 8):
        minimal: list[float] = []
        general: list[float] = []
        for _ in range(trials):
            style = rng.integers(0, 4)
            if style == 0:
                roots = np.sqrt(rng.random(degree)) * np.exp(2j * np.pi * rng.random(degree))
            elif style == 1:
                base = rng.choice([1.0, 0.999, 0.99, 0.9]) * np.exp(
                    2j * np.pi * np.arange(degree) / degree
                )
                scale = rng.choice([3.0e-1, 1.0e-1, 3.0e-2, 1.0e-2, 1.0e-3])
                roots = base * np.exp(
                    scale * (rng.standard_normal(degree) + 1j * rng.standard_normal(degree))
                )
            elif style == 2:
                split = int(rng.integers(1, max(2, degree)))
                roots = np.concatenate(
                    [
                        np.exp(2j * np.pi * rng.random(split)),
                        0.2
                        * (
                            rng.standard_normal(degree - split)
                            + 1j * rng.standard_normal(degree - split)
                        ),
                    ]
                )
            else:
                roots = rng.standard_normal(degree) + 1j * rng.standard_normal(degree)
            ratio = minimal_hub_ratio(roots)
            if ratio is not None:
                minimal.append(ratio)
            if len(minimal) % 3 == 0:
                general.extend(all_hub_ratios(roots))
        rows.append(
            {
                "degree": degree,
                "minimal_hub_samples": len(minimal),
                "maximum_minimal_hub_ratio": max(minimal) if minimal else None,
                "minimal_hub_violations": sum(1 for r in minimal if r > 1.0 + 1.0e-9),
                "general_hub_samples": len(general),
                "maximum_general_hub_ratio": max(general) if general else None,
                "general_hub_violations": sum(1 for r in general if r > 1.0 + 1.0e-9),
            }
        )
    return rows


def cubic_parameter_sweep(radial: int = 34, angular: int = 60) -> dict[str, Any]:
    """The complete cubic case: ``P(u) = u^3 + s u^2 + 1`` over admissible ``s``.

    Minimality is exactly ``|1 + 4 s^3 / 27| >= 1``.  ``s = 0`` is the equality
    point ``u^3 + 1``; as ``|s|`` grows the two branch endpoints approach the
    hub and the length falls away, so the sweep only has to reach moderate
    ``|s|``.
    """

    worst = -1.0
    worst_parameter: complex | None = None
    violations = 0
    checked = 0
    radii = np.concatenate(
        [np.linspace(0.01, 1.0, radial // 2), np.linspace(1.1, 8.0, radial - radial // 2)]
    )
    for radius in radii:
        for angle in np.linspace(0.0, 2 * np.pi, angular, endpoint=False):
            parameter = radius * np.exp(1j * angle)
            if abs(1.0 + 4.0 * parameter**3 / 27.0) < 1.0 - 1.0e-14:
                continue
            roots = np.roots([1.0, parameter, 0.0, 1.0])
            pair = descending_pair(roots, 0.0 + 0j, **TOLERANCES)
            if pair is None or pair["maximum_endpoint_error"] > 1.0e-8:
                continue
            checked += 1
            length = pair["total_length"]
            if length > worst:
                worst, worst_parameter = length, parameter
            if length > 2.0 + 1.0e-9:
                violations += 1
    return {
        "statement": (
            "normalised cubic P(u) = u^3 + s u^2 + 1; minimality is "
            "|1 + 4 s^3 / 27| >= 1; the branch pair at 0 must have length <= 2"
        ),
        "admissible_parameters_checked": checked,
        "maximum_branch_pair_length": worst,
        "attained_at_parameter": (
            None
            if worst_parameter is None
            else [float(worst_parameter.real), float(worst_parameter.imag)]
        ),
        "violations": violations,
        "equality_point": "s = 0, i.e. P = u^3 + 1, where the branches are two radii",
    }


ADVERSARIAL_MINIMAL_HUB_SUPREMA = {
    "note": (
        "Evolutionary maxima of L(c*)/(2|f(c*)|^{1/n}) under five independent "
        "seedings -- near-extremal, uniform, clustered, near-collision, and a "
        "combined restart -- reported as lower bounds on the supremum from the "
        "basins explored."
    ),
    "degree_three": {
        "near_extremal": 0.999071231,
        "uniform": 0.999980136,
        "clustered": 0.999984316,
        "near_collision": 0.999897680,
        "combined": 0.999994283,
    },
}


def build_payload() -> dict[str, Any]:
    quadratics = quadratic_identity()
    powers = pure_power_identity()
    fekete = fekete_rows()
    cusp = cusp_exponent_rows()
    sweep = sweep_rows()
    cubic = cubic_parameter_sweep()

    if quadratics["quadratics_checked"] < 15:
        raise AssertionError("too few usable quadratics")
    if quadratics["maximum_deviation_from_equality"] > 1.0e-6:
        raise AssertionError("quadratics no longer satisfy L = 2|f(c)|^{1/2}")
    if not powers:
        raise AssertionError("pure-power identity produced no rows")
    for row in powers:
        if row["critical_value_identity_error"] > 1.0e-12:
            raise AssertionError(
                f"pure power degree {row['degree']} lost |f(0)| = r^n"
            )
        if row.get("integrator_deficit_at_degenerate_hub", 0.0) < -1.0e-9:
            raise AssertionError(
                f"pure power degree {row['degree']}: integrator exceeded the true 2r"
            )
    for row in fekete:
        if not row["fekete_bound_holds"]:
            raise AssertionError(f"Fekete bound violated at degree {row['degree']}")
    for row in sweep:
        if row["minimal_hub_violations"] > 0:
            raise AssertionError(
                f"(M) failed at the minimal hub in degree {row['degree']}"
            )
    if not any(row["general_hub_violations"] > 0 for row in sweep):
        raise AssertionError(
            "the general-hub form must fail somewhere; minimality is the content"
        )
    for row in cusp:
        if "fitted_exponent" not in row:
            raise AssertionError(f"cusp exponent unmeasurable at degree {row['degree']}")
        if row["relative_error"] > 0.12:
            raise AssertionError(
                f"cusp exponent at degree {row['degree']} is {row['fitted_exponent']:.4f}, "
                f"not near the predicted {row['predicted_exponent']:.4f}"
            )
    if cubic["violations"] > 0:
        raise AssertionError("the cubic parameter sweep found a violation of (M)")
    if cubic["admissible_parameters_checked"] < 700:
        raise AssertionError("cubic sweep covered too few admissible parameters")

    return {
        "conjecture": (
            "At c* = argmin |f(c)| the descending branch pair satisfies "
            "L(c*) <= 2 |f(c*)|^{1/n}. With the Fekete bound |f(c*)| <= R^n this "
            "gives min_c L(c) <= 2R, hence Erdos #1041."
        ),
        "prior_work_in_this_corpus": {
            "analysis": (
                "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
                "MinimumCriticalNewtonHubLab.md"
            ),
            "already_proved_there": [
                "the first-merge reduction and the simple-connectivity of sublevel components",
                "rho = |f(c)|^(1/n) <= R by the discriminant/Fekete sandwich, with the "
                "regular n-gon equality case",
                "the strong (2 rho) versus weak (2 R) split, with the strong one flagged "
                "as possibly false",
                "an exact degree-five counterexample to the straight completion at the "
                "minimum-critical hub, certified by rational Rouche disks",
            ],
            "canonical_falsifier_run": {
                "objective": "critical-scale-normalized-minimum-critical-newton-hub",
                "degree": 5,
                "trials": 300,
                "score": 0.9495242630078684,
            },
            "what_this_probe_adds": [
                "multi-seeded adversarial pressure reaching 0.999994283 at degree three",
                "a complete one-complex-parameter sweep of the cubic case",
                "the quadratic equality family, second to z^n - r^n",
                "the cusp structure of the extremum under perturbation",
                "elimination of the per-hub form L(c) <= 2 max_k |z_k - c|",
            ],
        },
        "quadratic_identity": quadratics,
        "pure_power_identity": powers,
        "fekete_bound": fekete,
        "cusp_exponent": cusp,
        "minimal_versus_general_hub_sweep": sweep,
        "cubic_complete_parameter_sweep": cubic,
        "adversarial_minimal_hub_suprema": ADVERSARIAL_MINIMAL_HUB_SUPREMA,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--print-only", action="store_true")
    args = parser.parse_args()

    payload = build_payload()
    worst_minimal = max(
        row["maximum_minimal_hub_ratio"]
        for row in payload["minimal_versus_general_hub_sweep"]
        if row["maximum_minimal_hub_ratio"] is not None
    )
    worst_general = max(
        row["maximum_general_hub_ratio"]
        for row in payload["minimal_versus_general_hub_sweep"]
        if row["maximum_general_hub_ratio"] is not None
    )

    contract = build_experiment_contract(
        problem_id="erdos_1041",
        target_statement=(
            "If a monic polynomial f(z)=product_i(z-z_i) has all roots in the open unit "
            "disk, prove that two roots can be joined by a curve of length less than 2 "
            "contained in the open lemniscate |f|<1."
        ),
        claim_ceiling=(
            "Reduces the surviving obligation to one per-hub inequality (M) paired with "
            "the Fekete bound (F), proves the two equality identities and the Fekete "
            "bound, and shows that minimality of the hub is necessary. (M) itself is "
            "supported by a complete cubic parameter sweep and finite evidence in higher "
            "degree. Erdos #1041 remains open."
        ),
        hypothesis_id="minimal_hub_metric_scale",
        hypothesis_statement=(
            "At the critical point of least critical-value modulus, the descending "
            "inverse-ray branch pair has length at most twice the n-th root of that "
            "modulus -- the corpus's critical-pair metric scale, applied to arc length "
            "rather than straight distance."
        ),
        probe_id="erdos1041_minimal_hub_metric_scale",
        probe_question=(
            "Does the critical-pair metric scale 2|f(c)|^{1/n} bound the descending "
            "branch pair length at the least-critical-value hub, and does the Fekete "
            "bound supply the missing factor to reach 2R?"
        ),
        computation=(
            "Branch pairs are integrated in the substitution f(z(u)) = (1-u^2) f(c) with "
            "endpoint and level residual gates. The cubic case is normalised to "
            "P(u) = u^3 + s u^2 + 1 and swept completely over the admissible region "
            "|1 + 4 s^3 / 27| >= 1. Equality is checked on quadratics and on z^n - r^n, "
            "the Fekete bound on configurations with circumradius pinned to one, and the "
            "ratio is compared between the minimal hub and general hubs."
        ),
        falsifier=(
            "(M) fails if any configuration gives L(c*) > 2|f(c*)|^{1/n}, or if the cubic "
            "sweep finds an admissible s with branch pair length above two. The necessity "
            "of minimality fails if no general hub exceeds the ratio. (F) fails if any "
            "circumradius-one configuration has min_j |f(c_j)| above one."
        ),
        stop_condition=(
            "Stop once the cubic case is swept completely and the equality identities and "
            "Fekete bound are pinned. More sampling in higher degree is a longer horizon; "
            "what is needed is a proof of (M)."
        ),
        survival_consequence=(
            "Erdos #1041 reduces to a single scale-invariant per-hub inequality whose "
            "equality cases are known and whose companion half is already proved."
        ),
        falsification_consequence=(
            "A violation of (M) would send the search back to a global selection over "
            "hubs, since the per-hub route would then be closed at the minimal hub too."
        ),
        consumer_ref=PACKET_REF,
        analysis_refs=[ANALYSIS_REF],
        source_refs=[SOURCE_REF, ENGINE_REF],
        result_status="mixed",
        result_summary=(
            "The two equality identities hold exactly (quadratic deviation "
            f"{payload['quadratic_identity']['maximum_deviation_from_equality']:.2e}) and "
            "the Fekete bound held on every configuration. (M) survived at the minimal "
            f"hub on every sample, worst ratio {worst_minimal:.6f}, while the same ratio "
            f"at general hubs reaches {worst_general:.6f} -- so minimality is the content, "
            "not the level. The complete cubic parameter sweep over "
            f"{payload['cubic_complete_parameter_sweep']['admissible_parameters_checked']} "
            "admissible parameters found no violation, with maximum branch pair length "
            f"{payload['cubic_complete_parameter_sweep']['maximum_branch_pair_length']:.9f}."
        ),
        resource_bounds={
            "maximum_degree_swept": 8,
            "cubic_sweep_admissible_parameters": cubic_sweep_size(payload),
            "configurations_per_degree": 32,
        },
        progress_class="producer_constructed",
        decision_basis=(
            "The equality identities, the Fekete bound and the necessity of minimality "
            "are decided; (M) is finite evidence plus a complete cubic sweep."
        ),
        next_analytic_target=(
            "Prove (M). Normalised: P(u) = 1 + u^2 R(u) monic of degree n with P(0) = 1, "
            "P'(0) = 0 and |P(kappa)| >= 1 at every critical point; show the two "
            "descending branches at 0 have total length at most 2, with equality only for "
            "P = u^n + 1. Equivalently, in the resolved coordinate xi^2 = 1 - P, the curve "
            "Z with P(Z(xi)) = 1 - xi^2 and Z(0) = 0 must not increase the length of the "
            "segment [-1, 1] on average."
        ),
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    payload["experiment_contract"] = contract
    payload["sources"] = [
        source_record(REPO_ROOT, SOURCE_REF),
        source_record(REPO_ROOT, ENGINE_REF),
    ]

    text = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.print_only:
        print(text)
        return 0
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_suffix(args.output.suffix + ".tmp")
    temporary.write_text(text, encoding="utf-8")
    temporary.replace(args.output)
    print(f"wrote {args.output.relative_to(REPO_ROOT)}")
    cubic = payload["cubic_complete_parameter_sweep"]
    print(
        f"  cubic sweep: {cubic['admissible_parameters_checked']} admissible s, "
        f"max branch pair {cubic['maximum_branch_pair_length']:.9f}, "
        f"{cubic['violations']} violations"
    )
    for row in payload["cusp_exponent"]:
        print(
            f"  degree {row['degree']}: cusp exponent {row['fitted_exponent']:.4f} "
            f"vs predicted 1/(n-1) = {row['predicted_exponent']:.4f}"
        )
    for row in payload["minimal_versus_general_hub_sweep"]:
        print(
            f"  degree {row['degree']}: minimal hub max "
            f"{row['maximum_minimal_hub_ratio']:.6f} ({row['minimal_hub_violations']} "
            f"violations); general hub max {row['maximum_general_hub_ratio']:.6f} "
            f"({row['general_hub_violations']} violations)"
        )
    return 0


def cubic_sweep_size(payload: dict[str, Any]) -> int:
    return int(payload["cubic_complete_parameter_sweep"]["admissible_parameters_checked"])


if __name__ == "__main__":
    raise SystemExit(main())
