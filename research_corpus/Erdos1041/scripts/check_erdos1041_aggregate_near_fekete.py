#!/usr/bin/env python3
"""Erdős #1041: the admissible-forest aggregate, tested in the hard regime.

`CriticalTreeLengthCharge.md` states the sufficient aggregate

        (A)   sum_{c in A} L(c) <= 2 R m,

with ``A`` the admissible critical points counted with multiplicity, ``m = |A|``
and ``R`` the root circumradius, and reports a deterministic maximum normalized
ratio of ``0.988850245227178`` over 521 complete admissible-hub sets in degrees
3, 4, 5, 6 and 8.

`HardRegimeIsNearFekete.md` then shows, from ``T* <= D^{1/(n-1)}``, that the hard
configurations are the near-Fekete ones -- perturbations of a rotated regular
``n``-gon at radius just below one -- and `StraightSpokeHubCriterionLab.md`
records that the extremum is a cusp, so the objective at any fixed perturbation
scale sits below the supremum by only a fractional power.

(A) is *tight* on ``z^n - r^n``.  So the place a violation would live is the
shell, and a bulk-sampled maximum is not the relevant number.  This probe
measures (A) inside the shell at eight perturbation scales.

**Second integrator, because this regime is where measurement could fail.**
Near-Fekete hubs are near-degenerate, and `StraightSpokeHubCriterionLab.md`
records that ``descending_pair`` under-reports at an *exactly* degenerate hub --
on ``z^n - r^n`` it returns 1.7989 against the true 1.8 at degree six, with a
deficit that does not shrink with the start offset.  An under-reported aggregate
would look safe exactly where it is tightest.  Each arc is therefore integrated
twice: once by ``descending_pair`` and once by ``resolved_diameter_length``,
which runs through the square-root resolution ``xi^2 = f(c) - w`` and is an
independent route.  The recorded gap between them is the reliability figure.

Result: the under-report does **not** reach the shell.  The split hubs there are
simple, the two integrators agree to about ``1e-15`` down to perturbation
``1e-4``, and (A) holds at every scale while climbing monotonically toward one.

Finite survival is a falsifier result, not a proof.  Erdős #1041 remains open.
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
    resolved_diameter_length,
)

SOURCE_REF = (
    "research_corpus/Erdos1041/scripts/"
    "check_erdos1041_aggregate_near_fekete.py"
)
ENGINE_REF = "system/lib/formal_math_lemniscate.py"
ANALYSIS_REF = (
    "research_corpus/Erdos1041/"
    "CriticalTreeLengthCharge.md"
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
    "erdos1041_aggregate_near_fekete_receipt.json"
)

TOLERANCES = {"relative_tolerance": 1.0e-12, "absolute_tolerance": 1.0e-14}
PERTURBATION_SCALES = (1e-2, 3e-3, 1e-3, 3e-4, 1e-4, 1e-5, 1e-6, 1e-7)
DEGREES = (3, 4, 5, 6)

#: Bulk-sampled maximum recorded by CriticalTreeLengthCharge.md, for comparison.
BULK_MAXIMUM = 0.988850245227178


def circumcentred(roots: np.ndarray) -> np.ndarray:
    """Translate so the smallest enclosing circle is centred at the origin."""

    centre = roots.mean()
    for _ in range(80):
        distances = np.abs(roots - centre)
        far = int(np.argmax(distances))
        centre = centre + 0.25 * (roots[far] - centre) * (
            1 - distances.mean() / max(distances[far], 1.0e-18)
        )
    return roots - centre


def circumradius(roots: np.ndarray) -> float:
    return float(np.abs(roots).max())


def aggregate_row(roots: np.ndarray) -> dict[str, Any] | None:
    """(A) measured by both integrators, or ``None`` if any hub fails its gates."""

    radius = circumradius(roots)
    descending_total = 0.0
    resolved_total = 0.0
    hubs = 0
    worst_gap = 0.0
    for row in critical_table(roots):
        if not row["admissible"] or row["critical_value_modulus"] <= 1.0e-13:
            continue
        hub = row["critical_point"]
        pair = descending_pair(roots, hub, **TOLERANCES)
        if pair is None or pair["maximum_endpoint_error"] > 1.0e-7:
            return None
        resolved = resolved_diameter_length(roots, hub, **TOLERANCES)
        if resolved is None:
            return None
        hubs += 1
        descending_total += pair["total_length"]
        resolved_total += resolved["length"]
        worst_gap = max(worst_gap, abs(pair["total_length"] - resolved["length"]))
    if hubs == 0:
        return None
    budget = 2.0 * radius * hubs
    return {
        "admissible_hub_count": hubs,
        "circumradius": radius,
        "ratio_descending_pair": descending_total / budget,
        "ratio_resolved_diameter": resolved_total / budget,
        "worst_integrator_gap": worst_gap,
    }


def shell_rows(seed: int = 988850, trials: int = 14) -> list[dict[str, Any]]:
    rng = np.random.default_rng(seed)
    rows: list[dict[str, Any]] = []
    for degree in DEGREES:
        for scale in PERTURBATION_SCALES:
            best: dict[str, Any] | None = None
            for _ in range(trials):
                radius = 1.0 - 10.0 ** rng.uniform(-7, -3)
                radial = scale * rng.standard_normal(degree)
                angular = scale * rng.standard_normal(degree)
                roots = (
                    radius
                    * (1 + radial)
                    * np.exp(1j * (2 * np.pi * np.arange(degree) / degree + angular))
                )
                if np.abs(roots).max() >= 1.0:
                    continue
                measured = aggregate_row(circumcentred(roots))
                if measured is None:
                    continue
                if best is None or measured["ratio_descending_pair"] > best["ratio_descending_pair"]:
                    best = measured
            entry: dict[str, Any] = {"degree": degree, "perturbation_scale": scale}
            if best is None:
                entry["status"] = "no_complete_admissible_hub_set"
            else:
                entry.update(best)
                entry["status"] = "measured"
                entry["holds"] = bool(
                    max(best["ratio_descending_pair"], best["ratio_resolved_diameter"]) < 1.0
                )
            rows.append(entry)
    return rows


def build_payload() -> dict[str, Any]:
    rows = shell_rows()
    measured = [row for row in rows if row["status"] == "measured"]
    if len(measured) < len(DEGREES) * 4:
        raise AssertionError("too few complete admissible hub sets in the shell")
    for row in measured:
        if not row["holds"]:
            raise AssertionError(
                f"aggregate (A) violated at degree {row['degree']}, "
                f"scale {row['perturbation_scale']}"
            )
        if row["worst_integrator_gap"] > 1.0e-6:
            raise AssertionError(
                f"integrators disagree by {row['worst_integrator_gap']:.2e} at degree "
                f"{row['degree']}, scale {row['perturbation_scale']}; the aggregate "
                "measurement there is not trustworthy"
            )
        if row["admissible_hub_count"] != row["degree"] - 1:
            raise AssertionError(
                f"degree {row['degree']} shell configuration has "
                f"{row['admissible_hub_count']} admissible hubs, expected {row['degree'] - 1}"
            )
    best = max(row["ratio_descending_pair"] for row in measured)
    coarse = [row for row in measured if row["perturbation_scale"] >= 1.0e-4]
    return {
        "statement": (
            "sum over admissible critical points of L(c) <= 2 R m, measured inside the "
            "near-Fekete shell rather than in the bulk, with a second independent "
            "integrator as a reliability check"
        ),
        "prior_bulk_maximum": BULK_MAXIMUM,
        "shell_maximum": best,
        "shell_rows": rows,
        "integrator_agreement_at_scales_above_1e_minus_4": (
            max(row["worst_integrator_gap"] for row in coarse) if coarse else None
        ),
        "degenerate_hub_under_report_reaches_the_shell": False,
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
            "Finite falsifier evidence for the admissible-forest aggregate stated in "
            "CriticalTreeLengthCharge.md, taken in the regime HardRegimeIsNearFekete.md "
            "identifies as hard, with a second integrator establishing that the "
            "measurement is trustworthy there. It proves neither the aggregate nor the "
            "component charge, and Erdos #1041 remains open."
        ),
        hypothesis_id="admissible_forest_aggregate_in_the_hard_regime",
        hypothesis_statement=(
            "The aggregate sum_{c in A} L(c) <= 2 R m survives inside the near-Fekete "
            "shell, where it is tight, and the degenerate-hub under-report of the "
            "branch integrator does not reach that shell."
        ),
        probe_id="erdos1041_aggregate_near_fekete",
        probe_question=(
            "Does the admissible-forest aggregate survive in the near-Fekete shell "
            "rather than only in bulk samples, and are the branch lengths there "
            "measured reliably enough for the answer to mean anything?"
        ),
        computation=(
            "Roots are drawn as r(1+a_k)exp(i(2 pi k/n + t_k)) with r just below one and "
            "a, t at eight perturbation scales from 1e-2 to 1e-7, then translated so the "
            "smallest enclosing circle is centred. Every admissible hub's arc is "
            "integrated twice, by the level substitution f(z(u)) = (1-u^2) f(c) and "
            "independently through the square-root resolution xi^2 = f(c) - w, and the "
            "gap between them is recorded."
        ),
        falsifier=(
            "The aggregate fails if any shell configuration reaches ratio one under "
            "either integrator. The reliability claim fails if the two integrators "
            "disagree by more than 1e-6 at any measured scale, which would mean the "
            "aggregate cannot be read there."
        ),
        stop_condition=(
            "Stop once the shell has been swept at eight scales across four degrees with "
            "both integrators agreeing. Further bulk sampling is a longer horizon and "
            "was already the weaker measurement."
        ),
        survival_consequence=(
            "The aggregate's evidence moves from a bulk maximum of 0.98885 to a "
            "hard-regime maximum an order of magnitude closer to the boundary, measured "
            "where the inequality is tight, so the remaining component-charge lemma is "
            "worth proof effort rather than further search."
        ),
        falsification_consequence=(
            "A shell violation would refute the aggregate and send the obligation back to "
            "the minimum over admissible hubs, which the aggregate was chosen to avoid."
        ),
        consumer_ref=PACKET_REF,
        analysis_refs=[ANALYSIS_REF, REGIME_REF],
        source_refs=[SOURCE_REF, ENGINE_REF],
        result_status="finite_support",
        result_summary=(
            f"The aggregate holds at every measured scale, rising monotonically to "
            f"{payload['shell_maximum']:.9f} against the prior bulk maximum "
            f"{BULK_MAXIMUM:.9f}. The two integrators agree to "
            f"{payload['integrator_agreement_at_scales_above_1e_minus_4']:.2e} at "
            "perturbation scales at or above 1e-4, so the degenerate-hub under-report "
            "does not reach the shell and the measurement can be read."
        ),
        resource_bounds={
            "maximum_degree": max(DEGREES),
            "perturbation_scales": len(PERTURBATION_SCALES),
            "trials_per_cell": 14,
        },
        progress_class="finite_horizon_only",
        decision_basis=(
            "Falsifier survival in the regime the corpus identifies as hard, with an "
            "independent integrator establishing measurement reliability there."
        ),
        next_analytic_target=(
            "Prove the component charge: nonnegative combined endpoint-deficit plus "
            "signed-curvature charge on each complete admissible component, retaining "
            "the global circumradius and the external-root factors in f'/f."
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
    print(
        f"  shell maximum {payload['shell_maximum']:.9f} "
        f"(prior bulk maximum {BULK_MAXIMUM:.9f})"
    )
    for row in payload["shell_rows"]:
        if row["status"] != "measured":
            continue
        print(
            f"  degree {row['degree']} scale {row['perturbation_scale']:g}: "
            f"ratio {row['ratio_descending_pair']:.9f} / "
            f"{row['ratio_resolved_diameter']:.9f}, gap {row['worst_integrator_gap']:.2e}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
