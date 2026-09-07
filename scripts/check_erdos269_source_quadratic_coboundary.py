#!/usr/bin/env python3
"""Eliminate phase-conditioned quadratic source coboundaries for Erdős #269."""

from __future__ import annotations

import argparse
from bisect import bisect_right
import json
from pathlib import Path
import sys
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT))

from formal_math.erdos257_period_noncollapse.scripts.check_erdos269_dyadic_windows import (  # noqa: E402
    build_dyadic_blocks,
)
from formal_math.erdos257_period_noncollapse.scripts.check_erdos269_source_linear_coboundary import (  # noqa: E402
    BASE_FEATURE_NAMES,
    PRIMES,
    RADIX_PHASES,
    channel_tables,
)
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)
from system.lib.formal_math_linear_certificates import (  # noqa: E402
    exact_left_null_inconsistency,
)


SOURCE_REF = str(Path(__file__).resolve().relative_to(REPO_ROOT))
LINEAR_CHECKER_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos269_source_linear_coboundary.py"
)
WINDOW_ENGINE_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos269_dyadic_windows.py"
)
CERTIFICATE_REF = "system/lib/formal_math_linear_certificates.py"
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "WeightedPhaseCarry.lean"
)
TAIL_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "DyadicShellSummability.lean"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "SourceQuadraticCoboundaryNoGo.md"
)
PACKET_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "research_packet.json"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos269_source_quadratic_coboundary_receipt.json"
)
DEFAULT_EQUATION_COUNT = 116


def quadratic_feature_names() -> tuple[str, ...]:
    names = list(BASE_FEATURE_NAMES)
    names.extend(
        f"{BASE_FEATURE_NAMES[left]}*{BASE_FEATURE_NAMES[right]}"
        for left in range(1, len(BASE_FEATURE_NAMES))
        for right in range(left, len(BASE_FEATURE_NAMES))
    )
    return tuple(names)


def quadratic_features(base: list[int]) -> list[int]:
    values = list(base)
    values.extend(
        base[left] * base[right]
        for left in range(1, len(base))
        for right in range(left, len(base))
    )
    return values


def compute(equation_count: int) -> dict[str, Any]:
    maximum_scale = equation_count + 1
    powers, boundary, cumulative = channel_tables(maximum_scale + 1)
    blocks = build_dyadic_blocks(maximum_scale + 1)
    names = quadratic_feature_names()

    def base_features(scale: int) -> list[int]:
        exponent_three = bisect_right(powers[3], 1 << scale) - 1
        exponent_five = bisect_right(powers[5], 1 << scale) - 1
        exponents = {2: scale, 3: exponent_three, 5: exponent_five}
        linear = [
            1,
            scale,
            scale * scale,
            *(cumulative[prime][exponents[prime]] for prime in PRIMES),
            *(boundary[prime][exponents[prime]] for prime in PRIMES),
        ]
        return quadratic_features(linear)

    def phase_features(scale: int) -> list[int]:
        radix = blocks[scale - 1][0]
        features = base_features(scale)
        return [
            value if radix == phase else 0
            for phase in RADIX_PHASES
            for value in features
        ]

    rows = []
    digits = []
    radices = []
    for scale in range(1, equation_count + 1):
        radix, digit, _ = blocks[scale - 1]
        current = phase_features(scale)
        following = phase_features(scale + 1)
        rows.append(
            [
                radix * value - next_value
                for value, next_value in zip(current, following)
            ]
        )
        digits.append(digit)
        radices.append(radix)

    certificate = exact_left_null_inconsistency(rows, digits)
    if certificate is None:
        raise AssertionError(
            "configured quadratic source equations remained exactly consistent"
        )
    if any(certificate.column_pairings) or certificate.target_pairing == 0:
        raise AssertionError("quadratic left-null certificate failed exact replay")
    support = [
        index + 1
        for index, value in enumerate(certificate.primitive_left_null)
        if value
    ]
    return {
        "base_linear_feature_names": list(BASE_FEATURE_NAMES),
        "quadratic_feature_names": list(names),
        "base_quadratic_feature_count": len(names),
        "radix_phases": list(RADIX_PHASES),
        "coefficient_count": len(names) * len(RADIX_PHASES),
        "equation_count": equation_count,
        "coefficient_rank": certificate.coefficient_rank,
        "augmented_rank": certificate.augmented_rank,
        "primitive_left_null_certificate": list(
            certificate.primitive_left_null
        ),
        "certificate_support_scales": support,
        "certificate_support_size": len(support),
        "certificate_column_pairings": list(certificate.column_pairings),
        "certificate_digit_pairing": certificate.target_pairing,
        "radix_word": radices,
        "digit_word": digits,
        "potential_class": (
            "C_a is a radix-phase-conditioned polynomial of total degree at "
            "most two in the eight nonconstant direct source coordinates"
        ),
        "coboundary_equation": "d_a=b_a*C_a-C_(a+1)",
        "quadratic_source_class_inconsistent": True,
    }


def build_payload(equation_count: int) -> dict[str, Any]:
    result = compute(equation_count)
    contract = build_experiment_contract(
        problem_id="erdos_269",
        target_statement=(
            "Exclude exact integral states of the genuine normalized {2,3,5} "
            "source tail."
        ),
        claim_ceiling=(
            "The exact certificate eliminates the declared phase-conditioned "
            "degree-two direct-source potential class. It does not exclude higher "
            "degree, nonpolynomial, unbounded-memory, or later-onset carries."
        ),
        hypothesis_id="phase_conditioned_source_quadratic_integral_coboundary",
        hypothesis_statement=(
            "The integral-tail coboundary is a phase-conditioned polynomial of "
            "degree at most two in the eight nonconstant boundary, cumulative, "
            "and scale coordinates used by the exact source digit."
        ),
        probe_id="exact_source_quadratic_coboundary_left_null_test",
        probe_question=(
            "Does the first mathematically specified nonlinear enlargement of the "
            "landed source-linear class solve d_a=b_a C_a-C_(a+1)?"
        ),
        computation=(
            "Materialize every constant, linear, square, and cross term in the "
            "eight nonconstant exact source coordinates, allow independent "
            "coefficients in all four radix phases, and extract an exact primitive "
            "left-null separator from the resulting rational system."
        ),
        falsifier=(
            "A primitive integer left-null vector pairing to zero with every "
            "quadratic coefficient column and nonzero with the actual digit word."
        ),
        stop_condition=(
            "Stop when the whole declared quadratic class is exactly inconsistent; "
            "do not add arbitrary higher monomials to interpolate a longer prefix."
        ),
        survival_consequence=(
            "An exact solution would open an explicit nonlinear integral-tail "
            "potential for all-scale symbolic analysis."
        ),
        falsification_consequence=(
            "Any source-coordinate integral carry must use degree at least three, "
            "nonpolynomial structure, unbounded memory, or a later-onset mechanism."
        ),
        consumer_ref=CONSUMER_REF,
        analysis_refs=[ANALYSIS_REF, PACKET_REF],
        source_refs=[
            SOURCE_REF,
            LINEAR_CHECKER_REF,
            WINDOW_ENGINE_REF,
            CERTIFICATE_REF,
            CONSUMER_REF,
            TAIL_REF,
        ],
        result_status="exact_one_way_result",
        result_summary=(
            f"The {result['coefficient_count']}-parameter phase-conditioned "
            "quadratic source class is exactly inconsistent: coefficient rank "
            f"{result['coefficient_rank']} versus augmented rank "
            f"{result['augmented_rank']}, with a replayed primitive left-null "
            "separator."
        ),
        progress_class="mechanism_eliminated",
        decision_basis=(
            "The certificate eliminates an entire nonlinear functional class, not "
            "a longer finite orbit horizon."
        ),
        next_analytic_target=(
            "Test a source-derived nonlinear recurrence with unbounded memory or "
            "prove that every integral carry would force a finite-degree potential."
        ),
        resource_bounds={
            "equation_count": equation_count,
            "coefficient_count": result["coefficient_count"],
            "polynomial_total_degree": 2,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos269-source-quadratic-coboundary-no-go/1",
        "status": "exact_phase_conditioned_source_quadratic_mechanism_elimination",
        "parameters": {"equation_count": equation_count},
        "result": result,
        "experiment_contract": contract,
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [
                SOURCE_REF,
                LINEAR_CHECKER_REF,
                WINDOW_ENGINE_REF,
                CERTIFICATE_REF,
                CONSUMER_REF,
                TAIL_REF,
                ANALYSIS_REF,
                PACKET_REF,
            ]
        ],
    }


def emit(payload: dict[str, Any], output: Path, check: bool) -> int:
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if check:
        if not output.exists() or output.read_text(encoding="utf-8") != rendered:
            print(f"stale receipt: {output}", file=sys.stderr)
            return 1
        print(json.dumps({"status": "current", "output": str(output)}))
        return 0
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(rendered, encoding="utf-8")
    print(json.dumps({"status": "written", "output": str(output)}))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--equation-count", type=int, default=DEFAULT_EQUATION_COUNT
    )
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.equation_count < 2:
        parser.error("--equation-count must be at least two")
    return emit(build_payload(args.equation_count), args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
