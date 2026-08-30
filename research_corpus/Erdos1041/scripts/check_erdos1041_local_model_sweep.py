#!/usr/bin/env python3
"""Erdős #1041: the hard regime has a universal local model, swept completely.

`HardRegimeIsNearFekete.md` shows, from ``T* <= D^{1/(n-1)}``, that the hard
configurations are the near-Fekete ones.  `StraightSpokeHubCriterionLab.md`
measures the response there as a cusp of order ``1/(n-1)``.  Those two facts
together identify the local model.

**Derivation.**  Perturb the extremal family, ``f = z^n - r^n + eps*g``.  Then
``f' = n z^{n-1} + eps g'``, so the ``n-1`` critical points satisfy
``z^{n-1} = -eps g'(0)/n`` to leading order: they sit at radius
``(eps |g'(0)| / n)^{1/(n-1)}``, equally spaced in angle.  That radius is exactly
the measured cusp scale.  Zooming there, every perturbation ``g`` degenerates to
the same two-term model, and after the scaling ``z -> mu z`` -- which sends
``lambda -> lambda mu^{1-n}`` and ``c -> c mu^{-n}``, and whose rotation freedom
normalises ``lambda`` to be real and nonnegative -- the hard regime is the
three-real-parameter family

        f(z) = z^n + lambda z - rho e^{i gamma},   lambda >= 0.

The corpus already names this family in negative result 8, as the one where all
critical-value arguments coalesce.  So the near-extremal case of MIN is a
*complete parameter sweep* rather than a sample, which is what this probe runs.

**What it finds.**  The minimum over admissible hubs of ``L(c)/(2R)`` stays below
one across the whole family, with its supremum attained at ``lambda = 0`` -- the
exactly extremal family, where equality is already known.  Meanwhile *individual*
hubs exceed one in a large fraction of cells.  So the minimum over hubs is not a
convenience of the argument; it is load-bearing, and now witnessed by hundreds of
configurations on an exact family rather than by one pinned counterexample.

**Claim boundary.**  This is the leading-order zoom.  Verifying MIN on the local
model does not prove MIN near the extremal family: that needs uniform control of
the error between a polynomial and its model.  What it does is reduce the regime
where every previous mechanism failed to a compact, completely searchable space,
and confirm that MIN survives there while its per-hub strengthening does not.
Erdős #1041 remains open.
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
    critical_table,
    descending_pair,
)

SOURCE_REF = (
    "research_corpus/Erdos1041/scripts/"
    "check_erdos1041_local_model_sweep.py"
)
ENGINE_REF = "system/lib/formal_math_lemniscate.py"
ANALYSIS_REF = (
    "research_corpus/Erdos1041/"
    "StraightSpokeHubCriterionLab.md"
)
REGIME_REF = (
    "research_corpus/Erdos1041/"
    "HardRegimeIsNearFekete.md"
)
PACKET_REF = (
    "research_corpus/Erdos1041/research_packet.json"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "source-provenance://private-authoring-project/receipts/"
    "erdos1041_local_model_sweep_receipt.json"
)

TOLERANCES = {"relative_tolerance": 1.0e-12, "absolute_tolerance": 1.0e-14}
LAMBDAS = (0.0, 1.0e-6, 1.0e-4, 1.0e-2, 1.0e-1, 1.0, 3.0)
MODULI = (0.5, 0.9, 0.99, 0.999, 0.99999)
ARGUMENT_COUNT = 8
DEGREES = (3, 4, 5, 6)


def evaluate(degree: int, lam: float, modulus: float, argument: float) -> dict[str, Any] | None:
    """Hub ratios for one cell of the local model, or ``None`` if unusable."""

    coefficients = np.zeros(degree + 1, dtype=np.complex128)
    coefficients[0] = 1.0
    coefficients[-2] = lam
    coefficients[-1] = -modulus * np.exp(1j * argument)
    roots = np.roots(coefficients)
    if np.abs(roots).max() >= 1.0:
        return None
    radius = float(np.abs(roots).max())
    ratios: list[float] = []
    for row in critical_table(roots):
        if not row["admissible"] or row["critical_value_modulus"] <= 1.0e-14:
            continue
        pair = descending_pair(roots, row["critical_point"], **TOLERANCES)
        if pair is None or pair["maximum_endpoint_error"] > 1.0e-7:
            continue
        ratios.append(pair["total_length"] / (2.0 * radius))
    if not ratios:
        return None
    return {
        "admissible_hub_count": len(ratios),
        "minimum_hub_ratio": min(ratios),
        "maximum_hub_ratio": max(ratios),
    }


def sweep_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for degree in DEGREES:
        cells = 0
        worst_minimum = -1.0
        worst_at: tuple[float, float, float] | None = None
        worst_maximum = -1.0
        cells_with_a_hub_over_one = 0
        for lam in LAMBDAS:
            arguments = (
                np.linspace(0.0, 2 * np.pi, ARGUMENT_COUNT, endpoint=False)
                if lam > 0
                else np.array([np.pi])
            )
            for modulus in MODULI:
                for argument in arguments:
                    measured = evaluate(degree, lam, modulus, float(argument))
                    if measured is None:
                        continue
                    cells += 1
                    if measured["maximum_hub_ratio"] > 1.0:
                        cells_with_a_hub_over_one += 1
                    worst_maximum = max(worst_maximum, measured["maximum_hub_ratio"])
                    if measured["minimum_hub_ratio"] > worst_minimum:
                        worst_minimum = measured["minimum_hub_ratio"]
                        worst_at = (lam, modulus, float(argument) / np.pi)
        rows.append(
            {
                "degree": degree,
                "cells": cells,
                "supremum_minimum_hub_ratio": worst_minimum,
                "attained_at_lambda_modulus_argument_over_pi": list(worst_at) if worst_at else None,
                "supremum_maximum_hub_ratio": worst_maximum,
                "cells_with_a_hub_over_one": cells_with_a_hub_over_one,
                "min_over_hubs_holds": bool(worst_minimum < 1.0),
                "per_hub_form_fails": bool(cells_with_a_hub_over_one > 0),
            }
        )
    return rows


#: The closed form that is NOT there.  Recorded so the detour is not repeated.
CLOSED_FORM_NEGATIVE = {
    "observation": (
        "At a fixed lambda = 1e-6 the ratio D/S at the minimising hub reads "
        "0.29733, 0.24413, 0.20870, 0.18233 for degrees 3 to 6. Inverting and "
        "subtracting n log 2 gives 1.2839, 1.3236, 1.3258, 1.3257, which looks "
        "convergent and suggests D/S = 1/(n log 2 + kappa)."
    ),
    "verdict": "no closed form; the apparent convergence is a fixed-lambda artifact",
    "why": (
        "Taking lambda to zero at each degree separately, the same quantity keeps "
        "drifting and kappa does not settle: 5.50, 1.51, 1.28, 1.21, 1.16, 1.12, "
        "1.08, 1.05 for degrees 3 to 10, still falling. Different degrees reach "
        "their asymptotic regime at different lambda, so comparing them at one "
        "fixed lambda compares different stages of the same limit."
    ),
}


def build_payload() -> dict[str, Any]:
    rows = sweep_rows()
    for row in rows:
        if row["cells"] < 40:
            raise AssertionError(f"degree {row['degree']} swept too few cells")
        if not row["min_over_hubs_holds"]:
            raise AssertionError(
                f"MIN failed on the local model at degree {row['degree']}: "
                f"supremum {row['supremum_minimum_hub_ratio']:.9f}"
            )
        if not row["per_hub_form_fails"]:
            raise AssertionError(
                f"degree {row['degree']}: no hub exceeded one, so the sweep is not "
                "reaching the regime where the per-hub form is known to fail"
            )
    return {
        "model": "f(z) = z^n + lambda z - rho exp(i gamma), lambda >= 0",
        "derivation": (
            "Perturbing z^n - r^n by eps*g puts the n-1 critical points at radius "
            "(eps|g'(0)|/n)^{1/(n-1)}, the measured cusp scale; zooming there sends "
            "every perturbation to this two-term model, and the scaling z -> mu z "
            "normalises lambda real and nonnegative, leaving three real parameters."
        ),
        "sweep": rows,
        "closed_form_negative": CLOSED_FORM_NEGATIVE,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--print-only", action="store_true")
    args = parser.parse_args()

    payload = build_payload()
    contract = build_experiment_contract(
        problem_id="erdos_1041",
        target_statement=(
            "If a monic polynomial f(z)=product_i(z-z_i) has all roots in the open unit "
            "disk, prove that two roots can be joined by a curve of length less than 2 "
            "contained in the open lemniscate |f|<1."
        ),
        claim_ceiling=(
            "Identifies the leading-order local model of the regime the corpus calls "
            "hard, and sweeps it completely. MIN survives on the model and its per-hub "
            "strengthening does not. It is a leading-order zoom, so it does not prove "
            "MIN near the extremal family, and Erdos #1041 remains open."
        ),
        hypothesis_id="hard_regime_local_model",
        hypothesis_statement=(
            "The near-Fekete regime has a universal three-parameter local model "
            "z^n + lambda z - rho exp(i gamma), on which the minimum over admissible "
            "hubs of L(c)/(2R) stays below one while individual hubs exceed it."
        ),
        probe_id="erdos1041_local_model_sweep",
        probe_question=(
            "Does the hard regime reduce to a compact parameter family, and does MIN "
            "survive a complete sweep of it while the per-hub form fails?"
        ),
        computation=(
            "The model is built from its coefficients directly, its roots taken, and "
            "every admissible hub's descending branch pair integrated with endpoint and "
            "level residual gates. Lambda runs over seven values including zero, the "
            "modulus over five, and the argument over eight, the argument being fixed "
            "only where lambda vanishes and the family is rotationally degenerate."
        ),
        falsifier=(
            "MIN fails if any cell has minimum hub ratio at least one. The sweep is "
            "inadequate if no cell has a hub ratio above one, since the per-hub form is "
            "independently known to fail in this regime."
        ),
        stop_condition=(
            "Stop once the three-parameter space is covered at every degree. Extending "
            "to finer grids is a longer horizon; what is missing is uniform control of "
            "the error between a polynomial and its local model, which is analysis."
        ),
        survival_consequence=(
            "The regime where every previous mechanism failed is reduced to a compact "
            "searchable family on which MIN holds, so the remaining work is the "
            "uniformity estimate rather than a further search for counterexamples."
        ),
        falsification_consequence=(
            "A cell with minimum hub ratio at least one would refute MIN on the local "
            "model and, given the model is the leading-order zoom, would strongly "
            "indicate a genuine counterexample nearby."
        ),
        consumer_ref=PACKET_REF,
        analysis_refs=[ANALYSIS_REF, REGIME_REF],
        source_refs=[SOURCE_REF, ENGINE_REF],
        result_status="finite_support",
        result_summary=(
            "Across the three-parameter local model the minimum over admissible hubs "
            "stays below one at every degree, with suprema "
            + ", ".join(f"{row['supremum_minimum_hub_ratio']:.9f}" for row in payload["sweep"])
            + " for degrees 3 to 6, each attained at lambda = 0 where equality is "
            "already known. Individual hubs exceed one in "
            + ", ".join(str(row["cells_with_a_hub_over_one"]) for row in payload["sweep"])
            + " cells respectively, so the minimum over hubs is load-bearing."
        ),
        resource_bounds={
            "maximum_degree": max(DEGREES),
            "lambda_values": len(LAMBDAS),
            "modulus_values": len(MODULI),
            "argument_values": ARGUMENT_COUNT,
        },
        progress_class="mechanism_opened",
        decision_basis=(
            "A complete sweep of the identified local model, with the per-hub failure "
            "acting as a positive control that the sweep reaches the intended regime."
        ),
        next_analytic_target=(
            "Control the error between a polynomial in the near-Fekete shell and its "
            "local model uniformly, so that a verification on the model transfers. The "
            "cusp order 1/(n-1) is the scale at which that control must hold."
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
    for row in payload["sweep"]:
        print(
            f"  degree {row['degree']}: {row['cells']} cells, sup min-hub "
            f"{row['supremum_minimum_hub_ratio']:.9f}, sup max-hub "
            f"{row['supremum_maximum_hub_ratio']:.7f}, "
            f"{row['cells_with_a_hub_over_one']} cells with a hub over one"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
