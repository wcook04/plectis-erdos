#!/usr/bin/env python3
"""Certify the three-ray obstruction to affine Erdős #249 endpoint modes."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import sympy as sp

REPO_ROOT = Path(__file__).resolve().parents[5]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
)

SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/"
    "scripts/check_totient_affine_mode.py"
)
LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/"
    "TotientAffineModeEscape.lean"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/"
    "TotientAffineModeComputationalLab.md"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos249_totient_affine_mode_receipt.json"
)


def build_receipt() -> dict[str, object]:
    p, q = sp.symbols("p q", integer=True, positive=True)
    # Oriented twice-area of (p,p-1), (q,q-1), (2p,p-1).
    determinant = sp.expand(
        (q - p) * ((p - 1) - (p - 1))
        - (2 * p - p) * ((q - 1) - (p - 1))
    )
    expected = -p * (q - p)
    if sp.expand(determinant - expected) != 0:
        raise AssertionError("symbolic affine determinant identity failed")
    examples = []
    for left, right in [(3, 5), (5, 11), (101, 211), (1009, 2027)]:
        value = int(determinant.subs({p: left, q: right}))
        if value >= 0:
            raise AssertionError("prime-ray determinant did not stay negative")
        examples.append({"p": left, "q": right, "determinant": value})
    summary = (
        "For symbolic primes p<q, the totient points at p, q, and 2p have "
        "oriented affine determinant -p(q-p), hence are non-collinear. Lean "
        "uses arbitrarily late such triples to exclude every eventually affine "
        "fixed-quotient endpoint-error tail."
    )
    return {
        "schema": "erdos249-totient-affine-mode/1",
        "problem_id": "erdos_249",
        "symbolic_certificate": {
            "points": ["(p,p-1)", "(q,q-1)", "(2p,p-1)"],
            "totient_inputs": ["phi(p)=p-1", "phi(q)=q-1", "phi(2p)=p-1"],
            "determinant": "-p*(q-p)",
            "nonzero_when": "2 < p < q are prime",
        },
        "numeric_regressions": examples,
        "lean_theorem": (
            "ErdosProblems.Erdos249.PeriodMultipleEscape."
            "not_eventuallyAffine_pureDyadicEndpointError"
        ),
        "result_summary": summary,
        "experiment_contract": build_experiment_contract(
            problem_id="erdos_249",
            target_statement=(
                "Prove irrationality of sum_{n>=1} phi(n)/2^n by forcing "
                "cofinal escape of the exact endpoint cocycle."
            ),
            claim_ceiling=(
                "Eventually affine fixed-quotient endpoint errors are excluded; "
                "general non-affine linear-scale traps and Erdős #249 remain open."
            ),
            hypothesis_id="eventually_affine_fixed_quotient_boundary_mode",
            hypothesis_statement=(
                "A surviving endpoint trap may eventually have error A*H+B."
            ),
            probe_id="prime_prime_double_totient_affine_determinant",
            probe_question=(
                "Can the recurrence-forced affine totient word interpolate its "
                "values at arbitrarily late p, q, and 2p?"
            ),
            computation=(
                "Symbolically evaluate the affine determinant of the exact totient "
                "values phi(p), phi(q), phi(2p) for primes 2<p<q."
            ),
            falsifier="A nonzero symbolic determinant for every 2<p<q.",
            stop_condition=(
                "Once the determinant factors as a manifestly nonzero product, "
                "formalize the cofinal contradiction and stop affine-mode scans."
            ),
            survival_consequence=(
                "A zero determinant would retain affine linear-scale shadowing."
            ),
            falsification_consequence=(
                "Delete every eventually affine fixed-quotient boundary mode; only "
                "genuinely non-affine linear-scale traps can survive."
            ),
            consumer_ref=LEAN_REF,
            consumer_declarations=[
                "not_eventuallyAffine_pureDyadicEndpointError"
            ],
            analysis_refs=[ANALYSIS_REF],
            source_refs=[SOURCE_REF, LEAN_REF],
            result_status="exact_one_way_result",
            result_summary=summary,
            progress_class="mechanism_eliminated",
            decision_basis=(
                "The symbolic determinant is -p(q-p), and the Lean theorem "
                "constructs arbitrarily late prime pairs and consumes the exact "
                "endpoint recurrence."
            ),
            next_analytic_target=(
                "Attack non-affine full-linear-envelope traps by propagating the "
                "cofinal pre-prime bottom locks through composite totient blocks."
            ),
        ),
        "sources": [source_record(REPO_ROOT, ref) for ref in [SOURCE_REF, LEAN_REF]],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = json.dumps(build_receipt(), indent=2, sort_keys=True) + "\n"
    output = args.output.resolve()
    if args.check:
        if not output.exists() or output.read_text(encoding="utf-8") != rendered:
            print(f"stale or missing receipt: {output}", file=sys.stderr)
            return 1
        print(json.dumps({"status": "current", "output": str(output)}))
        return 0
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(rendered, encoding="utf-8")
    print(json.dumps({"status": "written", "output": str(output)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
