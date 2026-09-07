#!/usr/bin/env python3
"""Exhaust the split factor-30 and factor-35 #243 boundary cylinders."""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)
from system.lib.formal_math_residue_cylinder import (  # noqa: E402
    centered_successor_signature,
    centered_transport_next_multiplier_mod,
    certify_complete_affine_lift_family,
    exact_quotient_value_mod,
)

from check_erdos243_t0_factor26_activation import (  # noqa: E402
    CURRENT_SOURCE_MODULUS,
    TARGET_SOURCE_MODULUS,
    _load_parent_cache,
)
from check_erdos243_t0_factor27_singleton import (  # noqa: E402
    FACTOR27_SOURCE_MODULUS,
    _multiplier25_modulus,
)
from check_erdos243_t0_factor28_activation import (  # noqa: E402
    FACTOR28_SOURCE_MODULUS,
    _multiplier26_mod756,
    _multiplier27_mod28,
)
from check_erdos243_t0_factor29_activation import (  # noqa: E402
    EXPECTED_FACTOR28_NEGATIVE,
    EXPECTED_FACTOR28_SOURCE_PARENTS,
    FACTOR29_SOURCE_MODULUS,
)


SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_t0_factor30_35_split.py"
)
FACTOR29_SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_t0_factor29_activation.py"
)
FACTOR29_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos243_t0_factor29_activation_receipt.json"
)
LIBRARY_REF = "system/lib/formal_math_residue_cylinder.py"
TEST_REF = "system/server/tests/test_formal_math_residue_cylinder.py"
NOTE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/"
    "CleanRecoveryLengthComputationalLab.md"
)
PACKET_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/"
    "research_packet.json"
)
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "erdos243_t0_factor30_35_split_receipt.json"
)

BRANCHES = {
    -1: {"raw_factor": 30, "multiplicity": 7},
    -6: {"raw_factor": 35, "multiplicity": 8},
}
EXPECTED_SOURCE_FAMILIES = {
    -1: EXPECTED_FACTOR28_SOURCE_PARENTS * 7,
    -6: EXPECTED_FACTOR28_SOURCE_PARENTS * 8,
}
EXPECTED_EXHAUSTIVE_REFINEMENTS = {
    error: EXPECTED_SOURCE_FAMILIES[error] * branch["raw_factor"]
    for error, branch in BRANCHES.items()
}
EXPECTED_LOGICAL_PARENTS = {
    error: EXPECTED_FACTOR28_NEGATIVE * branch["multiplicity"]
    for error, branch in BRANCHES.items()
}


def _factor29_coordinates_mod(
    refined29: int, quotient_modulus: int
) -> tuple[int, int]:
    """Propagate to the factor-29 quotient and height-29 multiplier."""

    multiplier25 = _multiplier25_modulus(
        refined29, FACTOR29_SOURCE_MODULUS * quotient_modulus
    )
    multiplier26 = exact_quotient_value_mod(
        25 * multiplier25 * multiplier25 - 26 * multiplier25 + 27,
        divisor=26,
        quotient_modulus=27 * 28 * 29 * quotient_modulus,
    )
    multiplier27 = exact_quotient_value_mod(
        26 * multiplier26 * multiplier26 - 27 * multiplier26 + 28,
        divisor=27,
        quotient_modulus=28 * 29 * quotient_modulus,
    )
    assert multiplier27 % 28 == 1
    quotient = ((multiplier27 - 1) // 28) % (29 * quotient_modulus)
    multiplier28 = centered_transport_next_multiplier_mod(
        27,
        -1,
        multiplier27,
        payment=1,
        successor_error=-1,
        quotient_modulus=29 * quotient_modulus,
    )
    return quotient, multiplier28


def _next_multiplier_mod(refined29: int, error: int, modulus: int) -> int:
    _, multiplier28 = _factor29_coordinates_mod(refined29, modulus)
    return centered_transport_next_multiplier_mod(
        28,
        -1,
        multiplier28,
        payment=1,
        successor_error=error,
        quotient_modulus=modulus,
    )


def _negative_factor29_sources():
    """Yield every actual negative factor-29 source with its logical weight."""

    cached = _load_parent_cache()
    assert cached is not None
    parent_residues, parent_weights = cached
    assert parent_residues.size == 18

    for p_current, parent_weight in zip(parent_residues, parent_weights, strict=True):
        parity_counts: list[Counter[int]] = []
        for quotient_parity in (0, 1):
            local_counts: Counter[int] = Counter()
            factor26_targets = [
                int(p_current)
                + CURRENT_SOURCE_MODULUS * (quotient_parity + 2 * half)
                for half in range(13)
            ]
            surviving_factor26 = [
                target
                for target in factor26_targets
                if _multiplier25_modulus(target, TARGET_SOURCE_MODULUS) == 1
            ]
            assert len(surviving_factor26) == 4
            for target26 in surviving_factor26:
                for lift27 in range(27):
                    target27 = target26 + TARGET_SOURCE_MODULUS * lift27
                    for lift28 in range(28):
                        target28 = target27 + FACTOR27_SOURCE_MODULUS * lift28
                        multiplier25 = _multiplier25_modulus(
                            target28, FACTOR28_SOURCE_MODULUS
                        )
                        multiplier27 = _multiplier27_mod28(
                            _multiplier26_mod756(multiplier25)
                        )
                        if centered_successor_signature(27, -1, multiplier27) != (
                            1,
                            28,
                            -1,
                        ):
                            continue
                        for lift29 in range(29):
                            refined29 = (
                                target28 + FACTOR28_SOURCE_MODULUS * lift29
                            )
                            _, multiplier28 = _factor29_coordinates_mod(refined29, 1)
                            signature = centered_successor_signature(
                                28, -1, multiplier28
                            )
                            if signature not in ((1, 29, -1), (1, 29, -6)):
                                continue
                            error = signature[2]
                            local_counts[error] += 1
                            logical_weight = (
                                2 * int(parent_weight)
                                if quotient_parity == 0
                                else 0
                            )
                            yield refined29, error, logical_weight
            parity_counts.append(local_counts)
        assert parity_counts[0] == parity_counts[1]


def _profile(signatures: Counter[tuple[int, int, int]]) -> tuple[int, int, int]:
    cofinal = sum(count for (_, height, _), count in signatures.items() if height == 1)
    positive = sum(
        count
        for (_, height, error), count in signatures.items()
        if height > 1 and error > 0
    )
    negative = sum(
        count
        for (_, height, error), count in signatures.items()
        if height > 1 and error < 0
    )
    return cofinal, positive, negative


def complete_factor30_35_split_census() -> dict[str, Any]:
    """Exhaust every actual next lift and certify each affine summary."""

    source_families: Counter[int] = Counter()
    exhaustive_refinements: Counter[int] = Counter()
    affine_families: dict[int, Counter[tuple[int, int]]] = {
        error: Counter() for error in BRANCHES
    }
    quotient_affine_families: dict[int, Counter[tuple[int, int]]] = {
        error: Counter() for error in BRANCHES
    }
    quotient_coordinate_counts: dict[int, Counter[int]] = {
        error: Counter() for error in BRANCHES
    }
    source_profiles: dict[int, Counter[tuple[int, int, int]]] = {
        error: Counter() for error in BRANCHES
    }
    weighted_profiles: dict[int, Counter[tuple[int, int, int]]] = {
        error: Counter() for error in BRANCHES
    }
    weighted_modes: dict[int, Counter[tuple[int, int, int]]] = {
        error: Counter() for error in BRANCHES
    }

    for refined29, error, logical_weight in _negative_factor29_sources():
        modulus = BRANCHES[error]["raw_factor"]
        quotient_class = 0 if error == -1 else 24
        quotient_coordinates: list[int] = []
        values: list[int] = []
        signatures: Counter[tuple[int, int, int]] = Counter()
        for lift in range(modulus):
            refined = refined29 + FACTOR29_SOURCE_MODULUS * lift
            quotient, multiplier28 = _factor29_coordinates_mod(refined, modulus)
            assert quotient % 29 == quotient_class
            quotient_coordinates.append(((quotient - quotient_class) // 29) % modulus)
            quotient_coordinate_counts[error][quotient_coordinates[-1]] += 1
            multiplier29 = centered_transport_next_multiplier_mod(
                28,
                -1,
                multiplier28,
                payment=1,
                successor_error=error,
                quotient_modulus=modulus,
            )
            values.append(multiplier29)
            signature = centered_successor_signature(29, error, multiplier29)
            signatures[signature] += 1
            exhaustive_refinements[error] += 1

        # These validate every actual lift, not a sample or a longer-horizon
        # surrogate, before retaining the compressed summaries.
        offset, slope = certify_complete_affine_lift_family(
            values, modulus=modulus
        )
        quotient_offset, quotient_slope = certify_complete_affine_lift_family(
            quotient_coordinates, modulus=modulus
        )
        profile = _profile(signatures)
        assert sum(profile) == modulus
        source_families[error] += 1
        affine_families[error][(offset, slope)] += 1
        quotient_affine_families[error][
            (quotient_offset, quotient_slope)
        ] += 1
        source_profiles[error][profile] += 1
        if logical_weight:
            weighted_profiles[error][profile] += logical_weight
            for signature, count in signatures.items():
                weighted_modes[error][signature] += logical_weight * count

    assert source_families == EXPECTED_SOURCE_FAMILIES
    assert exhaustive_refinements == EXPECTED_EXHAUSTIVE_REFINEMENTS
    assert affine_families[-1] == {(1, 0): EXPECTED_SOURCE_FAMILIES[-1]}
    assert source_profiles[-1] == {
        (0, 0, 30): EXPECTED_SOURCE_FAMILIES[-1]
    }
    assert weighted_profiles[-1] == {
        (0, 0, 30): EXPECTED_LOGICAL_PARENTS[-1]
    }
    assert weighted_modes[-1] == {
        (1, 30, -1): EXPECTED_LOGICAL_PARENTS[-1] * 30
    }
    assert quotient_coordinate_counts[-1] == {
        0: 10_886_400,
        6: 5_443_200,
    }

    factor35_inert_sources = EXPECTED_SOURCE_FAMILIES[-6] // 5
    factor35_active_sources = 4 * factor35_inert_sources
    assert affine_families[-6][(6, 0)] == factor35_inert_sources
    assert set(affine_families[-6]) == {
        (offset, slope)
        for offset in range(1, 35, 5)
        for slope in (5, 15, 20, 30)
    } | {(6, 0)}
    assert sum(
        count
        for key, count in affine_families[-6].items()
        if key != (6, 0)
    ) == factor35_active_sources
    assert source_profiles[-6] == {
        (0, 0, 35): factor35_inert_sources,
        (0, 25, 10): factor35_active_sources,
    }
    assert weighted_profiles[-6] == {
        (0, 0, 35): EXPECTED_LOGICAL_PARENTS[-6] // 5,
        (0, 25, 10): 4 * EXPECTED_LOGICAL_PARENTS[-6] // 5,
    }
    assert weighted_modes[-6] == {
        (1, 35, -6): EXPECTED_LOGICAL_PARENTS[-6] * 15,
        (1, 35, 4): EXPECTED_LOGICAL_PARENTS[-6] * 8,
        (1, 35, 9): EXPECTED_LOGICAL_PARENTS[-6] * 8,
        (7, 5, 2): EXPECTED_LOGICAL_PARENTS[-6] * 4,
    }
    assert set(quotient_coordinate_counts[-6]) == {
        0,
        4,
        5,
        9,
        10,
        14,
        15,
        19,
        20,
        24,
        25,
        29,
        30,
        34,
    }
    assert not ({1, 8} & set(quotient_coordinate_counts[-6]))

    def encode_counter(counter: Counter[Any], formatter) -> dict[str, int]:
        return {formatter(key): value for key, value in sorted(counter.items())}

    branches = {}
    for error, branch in BRANCHES.items():
        modulus = branch["raw_factor"]
        quotient_class = 0 if error == -1 else 24
        generic_modes: dict[str, dict[str, Any]] = {}
        for coordinate in range(modulus):
            quotient = 29 * coordinate + quotient_class
            multiplier28 = 756 * quotient * quotient + 26 * quotient + 1
            assert centered_successor_signature(28, -1, multiplier28) == (
                1,
                29,
                error,
            )
            multiplier29 = centered_transport_next_multiplier_mod(
                28,
                -1,
                multiplier28,
                payment=1,
                successor_error=error,
                quotient_modulus=modulus,
            )
            signature = centered_successor_signature(29, error, multiplier29)
            key = f"payment={signature[0]},height={signature[1]},error={signature[2]}"
            row = generic_modes.setdefault(
                key, {"quotient_coordinates": [], "next_multiplier_residues": []}
            )
            row["quotient_coordinates"].append(coordinate)
            if multiplier29 not in row["next_multiplier_residues"]:
                row["next_multiplier_residues"].append(multiplier29)
        branches[str(error)] = {
            "incoming_state": {"height": 29, "error": error},
            "raw_factor": branch["raw_factor"],
            "incoming_multiplicity_per_factor28_parent": branch["multiplicity"],
            "exhaustive_source_family_count": source_families[error],
            "exhaustive_source_refinement_count": exhaustive_refinements[error],
            "affine_lift_family_counts": encode_counter(
                affine_families[error],
                lambda key: f"offset={key[0]},slope={key[1]}",
            ),
            "factor27_divided_quotient_affine_counts": encode_counter(
                quotient_affine_families[error],
                lambda key: f"offset={key[0]},slope={key[1]}",
            ),
            "actual_factor27_divided_quotient_coordinate_counts": {
                str(key): value
                for key, value in sorted(quotient_coordinate_counts[error].items())
            },
            "generic_quotient_coordinate_mode_table": generic_modes,
            "source_parent_profile_counts": encode_counter(
                source_profiles[error],
                lambda key: (
                    f"cofinal={key[0]},positive={key[1]},negative={key[2]}"
                ),
            ),
            "weighted_logical_parent_profile_counts": encode_counter(
                weighted_profiles[error],
                lambda key: (
                    f"cofinal={key[0]},positive={key[1]},negative={key[2]}"
                ),
            ),
            "weighted_successor_mode_counts": encode_counter(
                weighted_modes[error],
                lambda key: (
                    f"payment={key[0]},height={key[1]},error={key[2]}"
                ),
            ),
        }
    return {
        "factor29_negative_parent_count": EXPECTED_FACTOR28_NEGATIVE,
        "branches": branches,
        "affine_certificate": (
            "Every listed affine family was checked against every lift in its "
            "complete composite-modulus cylinder."
        ),
        "aggregate_boundary_transfer": {
            "factor30_negative_continuation": "1",
            "factor35_inert_source_fraction": "1/5",
            "factor35_active_source_fraction": "4/5",
            "factor35_active_negative_continuation": "2/7",
            "factor35_weighted_negative_continuation": "3/7",
            "factor29_then_split_negative_continuation": "73/203",
            "formerly_inert_factor25_chain_continuation": "1460/18473",
        },
    }


def build_receipt(census: dict[str, Any] | None = None) -> dict[str, Any]:
    previous = json.loads((REPO_ROOT / FACTOR29_RECEIPT_REF).read_text())
    assert previous["status"] == "verified_uniform_factor29_boundary_killing"
    if census is None:
        census = complete_factor30_35_split_census()
    assert census["aggregate_boundary_transfer"] == {
        "factor30_negative_continuation": "1",
        "factor35_inert_source_fraction": "1/5",
        "factor35_active_source_fraction": "4/5",
        "factor35_active_negative_continuation": "2/7",
        "factor35_weighted_negative_continuation": "3/7",
        "factor29_then_split_negative_continuation": "73/203",
        "formerly_inert_factor25_chain_continuation": "1460/18473",
    }
    contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Under a_(n+1)/a_n^2 -> 1 and rational reciprocal sum, force "
            "eventual Sylvester recurrence."
        ),
        claim_ceiling=(
            "Factor 30 is uniformly inert. At factor 35 exactly one fifth of "
            "actual source families are inert and four fifths have profile "
            "(0,25,10), giving weighted continuation 3/7. This exact split does "
            "not solve unrestricted #243."
        ),
        hypothesis_id="factor30_or_35_kills_each_factor29_negative_mode",
        hypothesis_statement=(
            "At least one split successor factor removes negative support from "
            "each actual factor-29 negative source family."
        ),
        probe_id="exact_factor30_35_complete_source_cylinder",
        probe_question=(
            "Are the apparent factor-30 rigid and factor-35 active/inert profiles "
            "genuine on every source family?"
        ),
        computation=(
            "Enumerate every actual negative factor-29 source and every one of "
            "its 30 or 35 next lifts; verify every affine summary pointwise."
        ),
        falsifier=(
            "Any full source family that disagrees with its affine certificate "
            "or introduces an unreported parent profile."
        ),
        stop_condition=(
            "Stop when both complete split cylinders are classified; do not "
            "extend a single orbit horizon."
        ),
        survival_consequence=(
            "The active factor-35 fibers kill five sevenths of their negative "
            "boundary, lowering the factor-29-plus-split continuation to 73/203."
        ),
        falsification_consequence=(
            "An all-negative profile isolates a source-rigid boundary requiring "
            "a later structurally distinct activation factor."
        ),
        consumer_ref=NOTE_REF,
        consumer_declarations=["factor-30/factor-35 split consequence table"],
        analysis_refs=[NOTE_REF, PACKET_REF, FACTOR29_RECEIPT_REF],
        source_refs=[
            SCRIPT_REF,
            FACTOR29_SCRIPT_REF,
            FACTOR29_RECEIPT_REF,
            LIBRARY_REF,
            TEST_REF,
        ],
        result_status="exact_one_way_result",
        result_summary=(
            "All factor-30 families are constant multiplier one and all-negative. "
            "Factor 35 splits exactly 1/5 inert and 4/5 active with profile "
            "(0,25,10); every affine summary is pointwise certified."
        ),
        progress_class="mechanism_opened",
        decision_basis=(
            "All actual source refinements were evaluated, with logical weights "
            "restored only after source-local profiles were exact."
        ),
        next_analytic_target=(
            "Probe raw factor 31 on the rigid (30,-1) branch and raw factor 41 "
            "on the surviving (35,-6) branch; preserve the factor-35 slope-zero "
            "versus nonzero source stratification."
        ),
        resource_bounds={
            "factor30_source_refinements": EXPECTED_EXHAUSTIVE_REFINEMENTS[-1],
            "factor35_source_refinements": EXPECTED_EXHAUSTIVE_REFINEMENTS[-6],
            "total_source_refinements": sum(EXPECTED_EXHAUSTIVE_REFINEMENTS.values()),
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos243-t0-factor30-35-split-receipt/1",
        "status": "verified_factor30_35_split",
        "complete_factor30_35_census": census,
        "mechanism_decision": {
            "factor30_height29_error_minus1": "uniformly_inert",
            "factor35_height29_error_minus6": "one_fifth_inert_four_fifths_active",
            "factor35_weighted_negative_continuation": "3/7",
            "factor29_then_split_negative_continuation": "73/203",
            "next_step": contract["result"]["progress"]["next_analytic_target"],
        },
        "experiment_contract": contract,
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [
                SCRIPT_REF,
                FACTOR29_SCRIPT_REF,
                FACTOR29_RECEIPT_REF,
                NOTE_REF,
                PACKET_REF,
                LIBRARY_REF,
                TEST_REF,
            ]
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--explore", action="store_true")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    parser.add_argument(
        "--census-input",
        type=Path,
        help="Reuse a completed exact census; --check always recomputes from source.",
    )
    args = parser.parse_args()
    if args.explore:
        payload = complete_factor30_35_split_census()
    else:
        census = None
        if args.census_input and not args.check:
            census = json.loads(args.census_input.read_text(encoding="utf-8"))
        payload = build_receipt(census)
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.explore:
        print(rendered, end="")
        return 0
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
