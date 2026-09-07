#!/usr/bin/env python3
"""Exact source-linear coboundary falsifier for Erdős #269.

An integral normalized tail would give an integer coboundary

    d_a = b_a C_a - C_(a+1).

This checker tests a source-native finite-rank realization of C_a.  Its nine
coordinates are the quadratic scale, and the boundary/cumulative pair-count
coordinates from all three prime channels used to construct the actual digit.
The coefficients may depend independently on the current radix phase
2, 6, 10, or 30.  Exact rational row reduction produces a primitive integer
left-null certificate proving that the actual source equations are
inconsistent in this 36-dimensional class.
"""

from __future__ import annotations

import argparse
from bisect import bisect_right
import json
from math import gcd
from pathlib import Path
import sys
from typing import Any

import sympy as sp


REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT))

from formal_math.erdos257_period_noncollapse.scripts.check_erdos269_dyadic_windows import (  # noqa: E402
    build_dyadic_blocks,
    pair_count_lt,
)
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos269_source_linear_coboundary.py"
)
WINDOW_ENGINE_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos269_dyadic_windows.py"
)
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
    "SourceLinearCoboundaryNoGo.md"
)
PACKET_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
    "research_packet.json"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos269_source_linear_coboundary_receipt.json"
)

PRIMES = (2, 3, 5)
OTHER_CHANNELS = {2: (3, 5), 3: (2, 5), 5: (2, 3)}
RADIX_PHASES = (2, 6, 10, 30)
BASE_FEATURE_NAMES = (
    "one",
    "scale",
    "scale_squared",
    "cumulative_pair_count_2",
    "cumulative_pair_count_3",
    "cumulative_pair_count_5",
    "boundary_pair_count_2",
    "boundary_pair_count_3",
    "boundary_pair_count_5",
)


def channel_tables(max_scale: int) -> tuple[dict[int, list[int]], dict[int, list[int]], dict[int, list[int]]]:
    limit = 1 << (max_scale + 2)
    powers: dict[int, list[int]] = {}
    for prime in PRIMES:
        values = [1]
        while values[-1] * prime <= limit:
            values.append(values[-1] * prime)
        powers[prime] = values

    boundary: dict[int, list[int]] = {}
    cumulative: dict[int, list[int]] = {}
    for prime in PRIMES:
        left, right = OTHER_CHANNELS[prime]
        widths = [0] * len(powers[prime])
        totals = [0] * len(powers[prime])
        for exponent in range(1, len(widths)):
            widths[exponent] = pair_count_lt(
                powers[prime][exponent], powers[left], powers[right]
            )
            totals[exponent] = totals[exponent - 1] + widths[exponent]
        boundary[prime] = widths
        cumulative[prime] = totals
    return powers, boundary, cumulative


def primitive_integer_vector(vector: sp.Matrix) -> list[int]:
    denominators = [int(value.q) for value in vector]
    common = 1
    for denominator in denominators:
        common = int(sp.ilcm(common, denominator))
    values = [int(value * common) for value in vector]
    divisor = 0
    for value in values:
        divisor = gcd(divisor, abs(value))
    values = [value // divisor for value in values]
    first = next(value for value in values if value)
    return values if first > 0 else [-value for value in values]


def first_inconsistency(rows: list[list[int]], target: list[int]) -> dict[str, Any]:
    for count in range(1, len(rows) + 1):
        matrix = sp.Matrix(rows[:count])
        rhs = sp.Matrix(target[:count])
        rank = int(matrix.rank())
        augmented_rank = int(matrix.row_join(rhs).rank())
        if augmented_rank == rank:
            continue
        certificate: list[int] | None = None
        pairing = 0
        for vector in matrix.T.nullspace():
            candidate = primitive_integer_vector(vector)
            candidate_pairing = sum(
                coefficient * value
                for coefficient, value in zip(candidate, target[:count])
            )
            if candidate_pairing:
                certificate = candidate
                pairing = candidate_pairing
                break
        if certificate is None:
            raise AssertionError("inconsistent system lacked a separating certificate")
        column_pairings = [
            int(sum(certificate[row] * matrix[row, column] for row in range(count)))
            for column in range(matrix.cols)
        ]
        if any(column_pairings) or pairing == 0:
            raise AssertionError("invalid left-null certificate")
        return {
            "first_inconsistent_equation_count": count,
            "last_consistent_equation_count": count - 1,
            "coefficient_rank": rank,
            "augmented_rank": augmented_rank,
            "primitive_left_null_certificate": certificate,
            "certificate_column_pairings": column_pairings,
            "certificate_digit_pairing": pairing,
        }
    raise AssertionError("configured equations did not falsify the ansatz")


def compute(max_scale: int, shifted_window_max_start: int) -> dict[str, Any]:
    powers, boundary, cumulative = channel_tables(max_scale + 1)
    blocks = build_dyadic_blocks(max_scale + 1)

    def base_features(scale: int) -> list[int]:
        exponent_three = bisect_right(powers[3], 1 << scale) - 1
        exponent_five = bisect_right(powers[5], 1 << scale) - 1
        exponents = {2: scale, 3: exponent_three, 5: exponent_five}
        return [
            1,
            scale,
            scale * scale,
            *(cumulative[prime][exponents[prime]] for prime in PRIMES),
            *(boundary[prime][exponents[prime]] for prime in PRIMES),
        ]

    def phase_features(scale: int) -> list[int]:
        radix = blocks[scale - 1][0]
        features = base_features(scale)
        return [
            value if radix == phase else 0
            for phase in RADIX_PHASES
            for value in features
        ]

    unphased_rows: list[list[int]] = []
    phased_rows: list[list[int]] = []
    digits: list[int] = []
    radices: list[int] = []
    for scale in range(1, max_scale + 1):
        radix, digit, _ = blocks[scale - 1]
        current = base_features(scale)
        following = base_features(scale + 1)
        unphased_rows.append(
            [radix * value - next_value for value, next_value in zip(current, following)]
        )
        phased_current = phase_features(scale)
        phased_following = phase_features(scale + 1)
        phased_rows.append(
            [
                radix * value - next_value
                for value, next_value in zip(phased_current, phased_following)
            ]
        )
        digits.append(digit)
        radices.append(radix)

    unphased = first_inconsistency(unphased_rows, digits)
    phased = first_inconsistency(phased_rows, digits)
    witness_count = phased["first_inconsistent_equation_count"]
    phased["radix_word"] = radices[:witness_count]
    phased["digit_word"] = digits[:witness_count]
    phased["coefficient_count"] = len(RADIX_PHASES) * len(BASE_FEATURE_NAMES)

    shifted_results = []
    window_length = witness_count
    for start in range(1, shifted_window_max_start + 1):
        stop = start - 1 + window_length
        if stop > len(phased_rows):
            break
        matrix = sp.Matrix(phased_rows[start - 1 : stop])
        rhs = sp.Matrix(digits[start - 1 : stop])
        coefficient_rank = int(matrix.rank())
        augmented_rank = int(matrix.row_join(rhs).rank())
        shifted_results.append(
            {
                "start_scale": start,
                "coefficient_rank": coefficient_rank,
                "augmented_rank": augmented_rank,
                "inconsistent": coefficient_rank != augmented_rank,
            }
        )

    return {
        "base_feature_names": list(BASE_FEATURE_NAMES),
        "radix_phases": list(RADIX_PHASES),
        "potential_class": (
            "C_a=sum_s 1[b_a=s] sum_j alpha_(s,j) feature_j(a), "
            "with rational alpha_(s,j)"
        ),
        "coboundary_equation": "d_a=b_a*C_a-C_(a+1)",
        "unphased_source_linear_result": unphased,
        "phase_conditioned_source_linear_result": phased,
        "shifted_window_checks": shifted_results,
        "all_configured_shifted_windows_inconsistent": all(
            row["inconsistent"] for row in shifted_results
        ),
    }


def build_payload(max_scale: int, shifted_window_max_start: int) -> dict[str, Any]:
    result = compute(max_scale, shifted_window_max_start)
    phased = result["phase_conditioned_source_linear_result"]
    contract = build_experiment_contract(
        problem_id="erdos_269",
        target_statement=(
            "Exclude exact integral states of the genuine normalized {2,3,5} "
            "source tail."
        ),
        claim_ceiling=(
            "The exact certificate eliminates one source-native finite-rank "
            "coboundary class from the actual initial state. It does not exclude "
            "nonlinear, unbounded-memory, or later-onset integral carries."
        ),
        hypothesis_id="phase_conditioned_source_linear_integral_coboundary",
        hypothesis_statement=(
            "The normalized source tail is a rational linear combination of the "
            "quadratic scale and all direct boundary/cumulative channel counts, "
            "with coefficients depending on the current radix phase."
        ),
        probe_id="exact_source_coordinate_coboundary_rank_test",
        probe_question=(
            "Can the actual digit equation d_a=b_a C_a-C_(a+1) be solved in the "
            "full phase-conditioned direct source-coordinate span?"
        ),
        computation=(
            "Construct the actual radix/digit word and all nine source coordinates "
            "exactly, form the rational linear system, and extract a primitive "
            "integer left-null inconsistency certificate."
        ),
        falsifier=(
            "A left-null vector of the coefficient matrix with nonzero pairing "
            "against the actual digit vector."
        ),
        stop_condition=(
            "Stop once the phase-conditioned class is exactly inconsistent; do not "
            "add arbitrary coordinates merely to interpolate a longer prefix."
        ),
        survival_consequence=(
            "An exact solution would construct a source-native closed-form integral "
            "coboundary and materially open the rational/counterexample branch."
        ),
        falsification_consequence=(
            "Any integral-tail proof or counterexample must use nonlinear or "
            "unbounded-memory phase information beyond the direct finite source span."
        ),
        consumer_ref=CONSUMER_REF,
        consumer_declarations=[
            "phaseWeightExp_mul_add",
            "weightedPhaseCoeff_mul_add",
            "carry_eq_residue_add_transfer",
        ],
        analysis_refs=[ANALYSIS_REF, PACKET_REF],
        source_refs=[SOURCE_REF, WINDOW_ENGINE_REF, CONSUMER_REF, TAIL_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "The 36-parameter phase-conditioned span is inconsistent on the actual "
            f"first {phased['first_inconsistent_equation_count']} source equations: "
            f"coefficient rank {phased['coefficient_rank']} versus augmented rank "
            f"{phased['augmented_rank']}. A primitive integer left-null certificate "
            "pairs nontrivially with the digit vector."
        ),
        progress_class="mechanism_eliminated",
        decision_basis=(
            "This is an exact algebraic obstruction to the whole declared potential "
            "class, not evidence from extending a numerical horizon."
        ),
        next_analytic_target=(
            "Probe nonlinear source potentials or prove that every integral carry "
            "would force a finite-rank reachable phase collapse already excluded by "
            "the certificate and the existing observer boundary."
        ),
        resource_bounds={
            "maximum_source_equation_scale": max_scale,
            "shifted_window_max_start": shifted_window_max_start,
            "phase_conditioned_coefficient_count": phased["coefficient_count"],
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos269-source-linear-coboundary-no-go/1",
        "status": "exact_phase_conditioned_source_linear_mechanism_elimination",
        "parameters": {
            "max_scale": max_scale,
            "shifted_window_max_start": shifted_window_max_start,
        },
        "result": result,
        "experiment_contract": contract,
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [SOURCE_REF, WINDOW_ENGINE_REF, CONSUMER_REF, TAIL_REF, ANALYSIS_REF, PACKET_REF]
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
    parser.add_argument("--max-scale", type=int, default=80)
    parser.add_argument("--shifted-window-max-start", type=int, default=40)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.max_scale < 40:
        parser.error("--max-scale must be at least 40")
    if args.shifted_window_max_start < 1:
        parser.error("--shifted-window-max-start must be positive")
    return emit(
        build_payload(args.max_scale, args.shifted_window_max_start),
        args.output,
        args.check,
    )


if __name__ == "__main__":
    raise SystemExit(main())
