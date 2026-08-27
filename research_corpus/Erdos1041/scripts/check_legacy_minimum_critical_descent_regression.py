#!/usr/bin/env python3
"""Regression for the legacy quartic minimum-critical descent misidentification.

The old constant-argument tracker reported that the minimum critical point of
this quartic descends to the near-antipodal roots 1 and 3.  The report was later
used as evidence against least-critical-value selection.  This checker recovers
the exact decimal witness from the original transcript, proves by rational
Rouche/interval certificates which critical point is first, and then replays
the direct inverse-value ODE at three step sizes.

The numerical continuation is deliberately labelled as a regression, not as
proof authority.  Its purpose is to prevent the known branch-tracking failure
from re-entering theorem selection: all three residual-gated runs land at roots
0 and 1, while none lands at root 3.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from typing import Any

import numpy as np
import sympy as sp

from formal_math.erdos257_period_noncollapse.ErdosProblems.Erdos1041.scripts.check_minimum_critical_straight_hub import (
    as_fraction,
    complex_interval_json,
    interval_json,
    norm_sq_interval,
    polynomial_interval,
    proposed_critical_boxes,
    rouche_root_certificate,
)
from formal_math.erdos257_period_noncollapse.ErdosProblems.Erdos1041.scripts.search_counterexample import (
    minimum_critical_newton_hub_score,
    scale_normalized_minimum_critical_newton_hub_score,
)
from system.lib.formal_math_experiment_contract import source_record


REPO_ROOT = Path(__file__).resolve().parents[5]
SCRIPT_PATH = Path(__file__).resolve()
SOURCE_REF = str(SCRIPT_PATH.relative_to(REPO_ROOT))
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "MinimumCriticalNewtonHubLab.md"
)
LEGACY_ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "CriticalBudgetLab.md"
)
SEARCH_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "scripts/search_counterexample.py"
)
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "erdos1041_legacy_minimum_critical_descent_regression_receipt.json"
)


ROOT_COORDINATES = (
    (Fraction(76_165_262, 100_000_000), Fraction(-1_001_708, 100_000_000)),
    (Fraction(551_532, 100_000_000), Fraction(99_998_479, 100_000_000)),
    (Fraction(-97_025_874, 100_000_000), Fraction(11_478_276, 100_000_000)),
    (Fraction(-6_346_137, 100_000_000), Fraction(-99_798_429, 100_000_000)),
)


def canonical_hash(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def exact_polynomial() -> tuple[sp.Poly, tuple[sp.Expr, ...]]:
    z = sp.symbols("z")
    roots = tuple(
        sp.Rational(real.numerator, real.denominator)
        + sp.I * sp.Rational(imag.numerator, imag.denominator)
        for real, imag in ROOT_COORDINATES
    )
    return sp.Poly(sp.expand(sp.prod(z - root for root in roots)), z), roots


def exact_first_critical_certificate(polynomial: sp.Poly) -> dict[str, Any]:
    derivative = sp.Poly(sp.diff(polynomial.as_expr(), polynomial.gens[0]), polynomial.gens[0])
    boxes = proposed_critical_boxes(derivative)
    if len(boxes) != 3:
        raise AssertionError("quartic derivative did not have three proposed roots")

    rows: list[dict[str, Any]] = []
    for index, box in enumerate(boxes):
        value_box = polynomial_interval(polynomial, box)
        value_norm_sq = norm_sq_interval(value_box)
        rows.append(
            {
                "critical_index": index,
                "critical_point_box": complex_interval_json(box),
                "critical_point_rouche_certificate": rouche_root_certificate(derivative, box),
                "critical_value_box": complex_interval_json(value_box),
                "critical_value_squared_modulus_interval": interval_json(value_norm_sq),
                "_norm": value_norm_sq,
            }
        )

    for left in range(len(boxes)):
        for right in range(left + 1, len(boxes)):
            a, b = boxes[left], boxes[right]
            if not (
                a[0][1] < b[0][0]
                or b[0][1] < a[0][0]
                or a[1][1] < b[1][0]
                or b[1][1] < a[1][0]
            ):
                raise AssertionError(("overlapping critical boxes", left, right))

    selected_index = min(range(3), key=lambda index: rows[index]["_norm"][1])
    selected_norm = rows[selected_index]["_norm"]
    other_lower = min(
        row["_norm"][0] for index, row in enumerate(rows) if index != selected_index
    )
    if not selected_norm[1] < other_lower < 1:
        raise AssertionError((selected_norm, other_lower))
    if not selected_norm[1] < 1:
        raise AssertionError("minimum critical value is not below one")

    public_rows = [
        {key: value for key, value in row.items() if not key.startswith("_")}
        for row in rows
    ]
    return {
        "critical_points": public_rows,
        "selected_minimum_critical_index": selected_index,
        "selected_critical_value_squared_modulus_upper": str(selected_norm[1]),
        "other_critical_value_squared_modulus_lower": str(other_lower),
        "strict_critical_value_ordering": True,
        "all_derivative_roots_accounted_for": True,
    }


def continuation_replay(roots: np.ndarray) -> list[dict[str, Any]]:
    runs: list[dict[str, Any]] = []
    for max_step in (0.004, 0.002, 0.001):
        _, detail = minimum_critical_newton_hub_score(roots, max_step)
        _, scaled = scale_normalized_minimum_critical_newton_hub_score(roots, max_step)
        selected = detail.get("selected_first_merge_hub")
        if not isinstance(selected, dict):
            raise AssertionError((max_step, detail))
        branches = list(selected["branches"])
        endpoints = sorted(int(branch["root_index"]) for branch in branches)
        if endpoints != [0, 1]:
            raise AssertionError((max_step, endpoints, branches))
        maximum_endpoint_error = max(float(branch["endpoint_error"]) for branch in branches)
        maximum_level_residual = max(
            float(branch["maximum_level_residual"]) for branch in branches
        )
        if maximum_endpoint_error >= 1.0e-10 or maximum_level_residual >= 1.0e-10:
            raise AssertionError((max_step, maximum_endpoint_error, maximum_level_residual))
        runs.append(
            {
                "flow_max_step": max_step,
                "critical_point": selected["critical_point"],
                "minimum_critical_value_modulus": detail["minimum_critical_value_modulus"],
                "branch_root_indices": endpoints,
                "branches": branches,
                "total_length": selected["total_length"],
                "scale_normalized_half_length": scaled[
                    "scale_normalized_first_merge_length"
                ],
                "maximum_endpoint_error": maximum_endpoint_error,
                "maximum_level_residual": maximum_level_residual,
            }
        )

    lengths = [float(run["total_length"]) for run in runs]
    if max(lengths) - min(lengths) >= 2.0e-8:
        raise AssertionError(("step-refinement length instability", lengths))
    return runs


def build_result() -> dict[str, Any]:
    polynomial, exact_roots = exact_polynomial()
    root_rows: list[dict[str, Any]] = []
    for index, root in enumerate(exact_roots):
        norm_sq = sp.cancel(sp.re(root) ** 2 + sp.im(root) ** 2)
        if not norm_sq < 1:
            raise AssertionError((index, norm_sq))
        root_rows.append(
            {
                "root_index": index,
                "real": str(as_fraction(sp.re(root))),
                "imaginary": str(as_fraction(sp.im(root))),
                "squared_modulus": str(as_fraction(norm_sq)),
            }
        )

    numerical_roots = np.asarray(
        [complex(float(real), float(imag)) for real, imag in ROOT_COORDINATES],
        dtype=np.complex128,
    )
    exact_critical = exact_first_critical_certificate(polynomial)
    runs = continuation_replay(numerical_roots)

    result: dict[str, Any] = {
        "schema": "erdos1041-legacy-minimum-critical-descent-regression/1",
        "status": "exact_first_critical_selector_with_residual_gated_branch_regression",
        "claim_ceiling": (
            "Exact rational arithmetic certifies the roots and unique minimum critical-value "
            "box. Direct inverse-value continuation at three refinements is numerical regression "
            "evidence, not proof authority for the branch endpoints or any length theorem."
        ),
        "witness": {
            "roots": root_rows,
            "exact_first_critical_certificate": exact_critical,
            "legacy_reported_branch_root_indices": [1, 3],
            "replayed_branch_root_indices": [0, 1],
            "continuation_runs": runs,
            "step_refinement_agrees": True,
            "legacy_pair_reproduced": False,
        },
        "consequence": {
            "eliminated": (
                "Treating the legacy 2.0068 quartic merge-pair budget as evidence against "
                "minimum-critical-value selection."
            ),
            "survives": (
                "The scale-normalized minimum-critical curved-branch conjecture; it still "
                "requires proof or an independently residual-gated counterexample."
            ),
        },
        "links": {
            "source_ref": SOURCE_REF,
            "analysis_ref": ANALYSIS_REF,
            "legacy_analysis_ref": LEGACY_ANALYSIS_REF,
            "search_ref": SEARCH_REF,
        },
        "sources": [
            source_record(REPO_ROOT, SOURCE_REF),
            source_record(REPO_ROOT, ANALYSIS_REF),
            source_record(REPO_ROOT, LEGACY_ANALYSIS_REF),
            source_record(REPO_ROOT, SEARCH_REF),
        ],
    }
    result["receipt_sha256"] = canonical_hash(result)
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = build_result()
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.check:
        if not args.output.exists() or args.output.read_text(encoding="utf-8") != rendered:
            raise SystemExit(f"stale or missing receipt: {args.output}")
        print(json.dumps({"status": "ok", "receipt": str(args.output)}))
        return 0
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(rendered, encoding="utf-8")
    print(json.dumps({"status": result["status"], "receipt": str(args.output)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
