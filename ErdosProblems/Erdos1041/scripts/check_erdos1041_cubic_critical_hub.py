#!/usr/bin/env python3
"""Exact symbolic receipt for the cubic case of Erdős #1041.

The checker verifies the polynomial identities and exact boundary inequality
used by the Rouché/homotopy proof.  The argument-principle step remains an
ordinary complex-analysis proof in ``CubicCriticalHub.md``; the downstream
spoke and length estimates are kernel-checked in ``CubicCriticalHub.lean``.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any

import sympy as sp


REPO_ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/"
    "check_erdos1041_cubic_critical_hub.py"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "CubicCriticalHub.md"
)
LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/"
    "CubicCriticalHub.lean"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos1041_cubic_critical_hub_receipt.json"
)


def exact_identities() -> dict[str, Any]:
    b, w, t, c, lam = sp.symbols("b w t c lam")
    normalized = lambda z: z**3 - sp.Rational(3, 2) * b * z**2 + 1

    spoke_rhs = 1 - t**2 - t**2 * (1 - t) * w**3
    spoke_remainder = sp.factor(normalized(t * w) - spoke_rhs)
    expected_spoke_remainder = sp.factor(t**2 * normalized(w))
    if sp.expand(spoke_remainder - expected_spoke_remainder) != 0:
        raise AssertionError("normalized spoke identity failed")

    boundary_norm_sq = (
        1 + sp.Rational(1024, 729) * c**6 - sp.Rational(64, 27) * c**4
    )
    boundary_defect = sp.factor(boundary_norm_sq - 1)
    expected_boundary_defect = sp.Rational(64, 729) * c**4 * (16 * c**2 - 27)
    if sp.expand(boundary_defect - expected_boundary_defect) != 0:
        raise AssertionError("unit-circle boundary defect identity failed")

    # If |1-z|>1, then |z|^2-2 Re(z)>0.  Under radial scaling z -> lam*z,
    # the new strict defect is lam*(lam*|z|^2-2 Re(z)); this exact two-real-
    # variable polynomial is what makes the homotopy stay in the strict region.
    norm_sq, real_part = sp.symbols("norm_sq real_part", real=True)
    radial_defect = sp.factor(lam**2 * norm_sq - 2 * lam * real_part)
    expected_radial_defect = lam * (lam * norm_sq - 2 * real_part)
    if sp.expand(radial_defect - expected_radial_defect) != 0:
        raise AssertionError("radial strict-region identity failed")

    return {
        "normalized_cubic": "w^3-(3/2)*b*w^2+1",
        "spoke_identity_remainder": str(spoke_remainder),
        "spoke_identity_consequence": (
            "At a normalized root, P_b(tw)=1-t^2-t^2(1-t)w^3."
        ),
        "unit_circle_boundary_defect": str(boundary_defect),
        "boundary_sign_certificate": (
            "For real |c|<=1, 16*c^2-27<=-11, so the defect is nonpositive; "
            "equality forces c=0 and then b=0."
        ),
        "radial_strict_region_defect": str(radial_defect),
        "rouche_large_parameter_threshold": "(3/2)*|b|>2, equivalently |b|>4/3",
    }


def build_payload() -> dict[str, Any]:
    identities = exact_identities()
    contract = build_experiment_contract(
        problem_id="erdos_1041",
        target_statement=(
            "For a monic cubic with all roots in the open unit disk, join two "
            "listed roots inside |f|<1 by a path of length less than two."
        ),
        claim_ceiling=(
            "The exact symbolic checker verifies the algebraic identities in the "
            "ordinary Rouché proof. Lean checks the spoke and metric consumer. "
            "The unrestricted all-degree Erdős problem remains open."
        ),
        hypothesis_id="minimal_critical_value_cubic_hub",
        hypothesis_statement=(
            "For a cubic, the critical point with smaller critical-value modulus "
            "normalizes to P_b(w)=w^3-(3/2)b w^2+1 with at least two unit-disc "
            "zeros, and those zeros give safe short straight spokes."
        ),
        probe_id="exact_normalized_cubic_boundary_and_spoke_identities",
        probe_question=(
            "Do the unit-circle exclusion, radial homotopy, and spoke containment "
            "reduce to the claimed exact identities?"
        ),
        computation=(
            "Expand and factor the normalized spoke remainder, the unit-circle "
            "boundary norm defect, and the radial strict-region defect over Q."
        ),
        falsifier=(
            "Any nonzero symbolic remainder, or a sign factor not forced "
            "nonpositive on |cos(u)|<=1."
        ),
        stop_condition=(
            "Stop after exact identities are checked; do not replace the "
            "Rouché zero count by floating root scans."
        ),
        survival_consequence=(
            "Use the ordinary Rouché/homotopy lemma and the Lean fan-in to land "
            "the cubic theorem, then seek a higher-degree replacement for cubic sparsity."
        ),
        falsification_consequence=(
            "Withdraw the cubic proof and repair the first failed identity."
        ),
        consumer_ref=ANALYSIS_REF,
        analysis_refs=[ANALYSIS_REF],
        source_refs=[SOURCE_REF, LEAN_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "All three rational polynomial identities are exact. The unit-circle "
            "defect factors as (64/729)c^4(16c^2-27), which is nonpositive for "
            "|c|<=1; the spoke remainder is t^2 P_b(w)."
        ),
        progress_class="one_way_theorem",
        decision_basis=(
            "The symbolic receipt supports a complete ordinary proof of the "
            "degree-three case and a kernel-checked downstream consumer."
        ),
        next_analytic_target=(
            "At a minimal-modulus critical value in higher degree, replace the "
            "sparse cubic normalized form by a multiplicity-aware root-sheet bound."
        ),
        resource_bounds={"symbolic_variables": 7},
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos1041-cubic-critical-hub/1",
        "status": "exact_symbolic_and_lean_consumed_cubic_theorem",
        "result": identities,
        "experiment_contract": contract,
        "source_records": [
            source_record(REPO_ROOT, ref) for ref in [SOURCE_REF, ANALYSIS_REF, LEAN_REF]
        ],
    }


def emit(payload: dict[str, Any], output: Path, check: bool) -> int:
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if check:
        if not output.exists() or output.read_text(encoding="utf-8") != rendered:
            print(f"stale receipt: {output}", file=sys.stderr)
            return 1
        print("Erdős 1041 cubic critical-hub receipt is current")
        return 0
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(rendered, encoding="utf-8")
    print(output)
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    return emit(build_payload(), args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
