#!/usr/bin/env python3
"""Certify uniform factor-28 activation after the rigid #243 factor-27 step."""

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
)

from check_erdos243_t0_factor26_activation import (  # noqa: E402
    CURRENT_SOURCE_MODULUS,
    TARGET_SOURCE_MODULUS,
    _load_parent_cache,
)
from check_erdos243_t0_factor27_singleton import (  # noqa: E402
    EXPECTED_FACTOR26_NEGATIVE_PARENTS,
    EXPECTED_FACTOR27_REFINEMENTS,
    FACTOR27_SOURCE_MODULUS,
    _multiplier25_modulus,
)


SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_t0_factor28_activation.py"
)
FACTOR27_SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_t0_factor27_singleton.py"
)
FACTOR27_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos243_t0_factor27_singleton_receipt.json"
)
LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/"
    "CleanRecoveryLengthCounterexample.lean"
)
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
    "erdos243_t0_factor28_activation_receipt.json"
)

FACTOR28_SOURCE_MODULUS = FACTOR27_SOURCE_MODULUS * 28
EXPECTED_FACTOR28_REFINEMENTS = EXPECTED_FACTOR27_REFINEMENTS * 28
EXPECTED_FACTOR28_POSITIVE = EXPECTED_FACTOR27_REFINEMENTS * 8
EXPECTED_FACTOR28_NEGATIVE = EXPECTED_FACTOR27_REFINEMENTS * 20
EXPECTED_EXHAUSTIVE_SOURCE_SAMPLES = 18 * 2 * 4 * 27 * 28


def _multiplier27_mod28(multiplier26_mod756: int) -> int:
    numerator = (
        26 * multiplier26_mod756 * multiplier26_mod756
        - 27 * multiplier26_mod756
        + 28
    )
    assert numerator % 27 == 0
    return (numerator // 27) % 28


def _multiplier26_mod756(multiplier25_mod19656: int) -> int:
    numerator = (
        25 * multiplier25_mod19656 * multiplier25_mod19656
        - 26 * multiplier25_mod19656
        + 27
    )
    assert numerator % 26 == 0
    return (numerator // 26) % (27 * 28)


def complete_factor28_activation_census() -> dict[str, Any]:
    cached = _load_parent_cache()
    assert cached is not None
    parent_residues, parent_weights = cached
    assert parent_residues.size == 18
    exhaustive_c: Counter[int] = Counter()
    exhaustive_d: Counter[int] = Counter()
    exhaustive_e: Counter[int] = Counter()
    weighted_e: Counter[int] = Counter()
    weighted_modes: Counter[tuple[int, int, int]] = Counter()
    weighted_profiles: Counter[tuple[int, int, int]] = Counter()

    for p_current, parent_weight in zip(parent_residues, parent_weights, strict=True):
        parity_profiles: list[list[tuple[int, int, int]]] = []
        for quotient_parity in (0, 1):
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
            local_profiles: list[tuple[int, int, int]] = []
            for target26 in surviving_factor26:
                for lift27 in range(27):
                    target27 = target26 + TARGET_SOURCE_MODULUS * lift27
                    signatures: Counter[tuple[int, int, int]] = Counter()
                    for lift28 in range(28):
                        refined = target27 + FACTOR27_SOURCE_MODULUS * lift28
                        multiplier25 = _multiplier25_modulus(
                            refined, FACTOR28_SOURCE_MODULUS
                        )
                        assert multiplier25 % (26 * 27) == 1
                        multiplier26 = _multiplier26_mod756(multiplier25)
                        assert multiplier26 % 27 == 1
                        multiplier27 = _multiplier27_mod28(multiplier26)
                        exhaustive_c[multiplier25] += 1
                        exhaustive_d[multiplier26] += 1
                        exhaustive_e[multiplier27] += 1
                        signatures[
                            centered_successor_signature(27, -1, multiplier27)
                        ] += 1
                    cofinal = sum(
                        count for (_, height, _), count in signatures.items() if height == 1
                    )
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
                    profile = (cofinal, positive, negative)
                    assert profile == (0, 8, 20)
                    local_profiles.append(profile)
                    if quotient_parity == 0:
                        logical_weight = 2 * int(parent_weight)
                        weighted_profiles[profile] += logical_weight
                        for signature, count in signatures.items():
                            weighted_modes[signature] += logical_weight * count
                        for multiplier27, count in Counter(
                            _multiplier27_mod28(
                                _multiplier26_mod756(
                                    _multiplier25_modulus(
                                        target27 + FACTOR27_SOURCE_MODULUS * lift28,
                                        FACTOR28_SOURCE_MODULUS,
                                    )
                                )
                            )
                            for lift28 in range(28)
                        ).items():
                            weighted_e[multiplier27] += logical_weight * count
            parity_profiles.append(local_profiles)
        assert sorted(parity_profiles[0]) == sorted(parity_profiles[1])

    assert sum(exhaustive_e.values()) == EXPECTED_EXHAUSTIVE_SOURCE_SAMPLES
    assert exhaustive_e == {1: 77_760, 21: 31_104}
    assert weighted_e == {
        1: EXPECTED_FACTOR28_NEGATIVE,
        21: EXPECTED_FACTOR28_POSITIVE,
    }
    assert weighted_profiles == {(0, 8, 20): EXPECTED_FACTOR27_REFINEMENTS}
    assert weighted_modes == {
        (1, 28, -1): EXPECTED_FACTOR28_NEGATIVE,
        (7, 4, 1): EXPECTED_FACTOR28_POSITIVE,
    }
    return {
        "factor27_negative_parent_count": EXPECTED_FACTOR27_REFINEMENTS,
        "factor28_logical_refinement_count": EXPECTED_FACTOR28_REFINEMENTS,
        "exhaustive_source_sample_count": EXPECTED_EXHAUSTIVE_SOURCE_SAMPLES,
        "factor25_multiplier_counts_mod_19656": {
            str(key): value for key, value in sorted(exhaustive_c.items())
        },
        "factor26_multiplier_counts_mod_756": {
            str(key): value for key, value in sorted(exhaustive_d.items())
        },
        "factor27_multiplier_counts_mod_28": {
            str(key): value for key, value in sorted(weighted_e.items())
        },
        "factor28_parent_profile_counts": {
            "cofinal=0,positive=8,negative=20": EXPECTED_FACTOR27_REFINEMENTS,
        },
        "factor28_successor_mode_counts": {
            f"payment={key[0]},height={key[1]},error={key[2]}": value
            for key, value in sorted(weighted_modes.items())
        },
        "quotient_image_mod_28": [0, 4, 12],
        "uniform_negative_continuation_ratio": "5/7",
    }


def build_receipt() -> dict[str, Any]:
    previous = json.loads(
        (REPO_ROOT / FACTOR27_RECEIPT_REF).read_text(encoding="utf-8")
    )
    assert previous["status"] == "verified_factor27_singleton_boundary_persistence"
    census = complete_factor28_activation_census()
    contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Under a_(n+1)/a_n^2 -> 1 and rational reciprocal sum, force "
            "eventual Sylvester recurrence."
        ),
        claim_ceiling=(
            "Exact factor-28 classification after the rigid factor-27 step: every "
            "actual parent has 8 positive and 20 continuing-negative children, "
            "with no immediate cofinal child. This opens a uniform sign-switch "
            "mechanism but does not solve unrestricted #243."
        ),
        hypothesis_id="factor28_activates_every_factor27_multiplier_one_fiber",
        hypothesis_statement=(
            "Every actual multiplier-one height-27 parent loses at least one of "
            "its 28 children from negative support."
        ),
        probe_id="exact_factor28_parent_local_activation_census",
        probe_question=(
            "Does factor 28 break the factor-27 singleton boundary, and is any "
            "activation uniform across actual parents?"
        ),
        computation=(
            "Exhaust all 108864 source samples from the 18 parent residues, two "
            "factor-26 parities, four surviving targets, 27 factor-27 lifts, and "
            "28 factor-28 lifts using exact integer quotient propagation."
        ),
        falsifier=(
            "Any actual factor-27 parent with 28 continuing-negative children, or "
            "any parent profile other than (0,8,20)."
        ),
        stop_condition=(
            "Stop after the complete parent-local factor-28 profile and multiplier "
            "images are exact; do not extend individual orbits."
        ),
        survival_consequence=(
            "A common subunit continuation profile supplies an exact activation "
            "block for the negative-mass route."
        ),
        falsification_consequence=(
            "An all-negative parent would force a later activation search and "
            "eliminate factor 28 as a uniform mechanism."
        ),
        consumer_ref=LEAN_REF,
        consumer_declarations=[
            "ErdosProblems.Erdos243.heightTwentySeven_multiplierQuotientIdentity",
            "ErdosProblems.Erdos243.heightTwentySeven_quotientZeroMode",
            "ErdosProblems.Erdos243.heightTwentySeven_quotientFourMode",
            "ErdosProblems.Erdos243.heightTwentySeven_quotientTwelveMode",
        ],
        analysis_refs=[NOTE_REF, PACKET_REF, FACTOR27_RECEIPT_REF],
        source_refs=[SCRIPT_REF, FACTOR27_SCRIPT_REF, FACTOR27_RECEIPT_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "Every one of the 55527553641600 actual parents has profile (0,8,20); "
            "the exact q-image is {0,4,12} mod 28, and q=4 alone forces multiplier "
            "21, payment seven, height four, and centered error +1."
        ),
        progress_class="mechanism_opened",
        decision_basis=(
            "The complete exact parent histogram contains one profile and zero "
            "all-negative fibers."
        ),
        next_analytic_target=(
            "Use the uniform 5/7 continuation in the amortized boundary-loss route "
            "and probe factor 29 only on the multiplier-one (28,-1) survivors."
        ),
        resource_bounds={
            "exhaustive_source_sample_count": EXPECTED_EXHAUSTIVE_SOURCE_SAMPLES,
            "logical_parent_count": EXPECTED_FACTOR27_REFINEMENTS,
            "children_per_parent": 28,
            "logical_refinement_count": EXPECTED_FACTOR28_REFINEMENTS,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos243-t0-factor28-activation-receipt/1",
        "status": "verified_uniform_factor28_positive_activation",
        "complete_factor28_census": census,
        "mechanism_decision": {
            "factor28_uniform_activation": "opened",
            "positive_children_per_parent": 8,
            "continuing_negative_children_per_parent": 20,
            "uniform_negative_continuation_ratio": "5/7",
            "positive_state": {"height": 4, "error": 1},
            "surviving_negative_state": {"height": 28, "error": -1},
            "next_raw_factor": 29,
        },
        "experiment_contract": contract,
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [
                SCRIPT_REF,
                FACTOR27_SCRIPT_REF,
                FACTOR27_RECEIPT_REF,
                LEAN_REF,
                NOTE_REF,
                PACKET_REF,
            ]
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--explore", action="store_true")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.explore:
        print(json.dumps(complete_factor28_activation_census(), indent=2, sort_keys=True))
        return 0
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
