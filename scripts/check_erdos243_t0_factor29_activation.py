#!/usr/bin/env python3
"""Certify uniform factor-29 boundary killing on the exact #243 source."""

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
    EXPECTED_FACTOR28_NEGATIVE,
    FACTOR28_SOURCE_MODULUS,
    _multiplier26_mod756,
    _multiplier27_mod28,
)


SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_t0_factor29_activation.py"
)
FACTOR28_SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_t0_factor28_activation.py"
)
FACTOR28_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos243_t0_factor28_activation_receipt.json"
)
LIBRARY_REF = "system/lib/formal_math_residue_cylinder.py"
TEST_REF = "system/server/tests/test_formal_math_residue_cylinder.py"
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
    "erdos243_t0_factor29_activation_receipt.json"
)

FACTOR29_SOURCE_MODULUS = FACTOR28_SOURCE_MODULUS * 29
EXPECTED_FACTOR29_REFINEMENTS = EXPECTED_FACTOR28_NEGATIVE * 29
EXPECTED_FACTOR29_COFINAL = EXPECTED_FACTOR28_NEGATIVE * 8
EXPECTED_FACTOR29_POSITIVE = EXPECTED_FACTOR28_NEGATIVE * 6
EXPECTED_FACTOR29_NEGATIVE = EXPECTED_FACTOR28_NEGATIVE * 15
EXPECTED_FACTOR28_SOURCE_PARENTS = 18 * 2 * 4 * 27 * 20
EXPECTED_EXHAUSTIVE_SOURCE_SAMPLES = EXPECTED_FACTOR28_SOURCE_PARENTS * 29
EXPECTED_LOCAL_QUOTIENT_COUNTS = {0: 7, 15: 8, 24: 8, 25: 4, 27: 2}
EXPECTED_LOCAL_MODE_COUNTS = {
    (29, 1, 0): 8,
    (1, 29, -6): 8,
    (1, 29, -1): 7,
    (1, 29, 5): 4,
    (1, 29, 7): 2,
}


def _multiplier26_mod21924(multiplier25_mod570024: int) -> int:
    numerator = (
        25 * multiplier25_mod570024 * multiplier25_mod570024
        - 26 * multiplier25_mod570024
        + 27
    )
    return exact_quotient_value_mod(
        numerator,
        divisor=26,
        quotient_modulus=27 * 28 * 29,
    )


def _multiplier27_mod812(multiplier26_mod21924: int) -> int:
    numerator = (
        26 * multiplier26_mod21924 * multiplier26_mod21924
        - 27 * multiplier26_mod21924
        + 28
    )
    return exact_quotient_value_mod(
        numerator,
        divisor=27,
        quotient_modulus=28 * 29,
    )


def _multiplier28_mod29(multiplier27_mod812: int) -> int:
    return centered_transport_next_multiplier_mod(
        27,
        -1,
        multiplier27_mod812,
        payment=1,
        successor_error=-1,
        quotient_modulus=29,
    )


def complete_factor29_activation_census() -> dict[str, Any]:
    cached = _load_parent_cache()
    assert cached is not None
    parent_residues, parent_weights = cached
    assert parent_residues.size == 18

    exhaustive_quotients: Counter[int] = Counter()
    exhaustive_multiplier27: Counter[int] = Counter()
    exhaustive_multiplier28: Counter[int] = Counter()
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
                    surviving_factor28: list[int] = []
                    for lift28 in range(28):
                        refined28 = target27 + FACTOR27_SOURCE_MODULUS * lift28
                        multiplier25 = _multiplier25_modulus(
                            refined28, FACTOR28_SOURCE_MODULUS
                        )
                        multiplier26 = _multiplier26_mod756(multiplier25)
                        multiplier27 = _multiplier27_mod28(multiplier26)
                        if centered_successor_signature(27, -1, multiplier27) == (
                            1,
                            28,
                            -1,
                        ):
                            surviving_factor28.append(refined28)
                    assert len(surviving_factor28) == 20

                    for target28 in surviving_factor28:
                        signatures: Counter[tuple[int, int, int]] = Counter()
                        quotient_counts: Counter[int] = Counter()
                        for lift29 in range(29):
                            refined29 = target28 + FACTOR28_SOURCE_MODULUS * lift29
                            multiplier25 = _multiplier25_modulus(
                                refined29, FACTOR29_SOURCE_MODULUS
                            )
                            multiplier26 = _multiplier26_mod21924(multiplier25)
                            multiplier27 = _multiplier27_mod812(multiplier26)
                            assert multiplier27 % 28 == 1
                            quotient = ((multiplier27 - 1) // 28) % 29
                            multiplier28 = _multiplier28_mod29(multiplier27)
                            signature = centered_successor_signature(
                                28, -1, multiplier28
                            )
                            quotient_counts[quotient] += 1
                            signatures[signature] += 1
                            exhaustive_quotients[quotient] += 1
                            exhaustive_multiplier27[multiplier27] += 1
                            exhaustive_multiplier28[multiplier28] += 1

                        assert quotient_counts == EXPECTED_LOCAL_QUOTIENT_COUNTS
                        assert signatures == EXPECTED_LOCAL_MODE_COUNTS
                        profile = (8, 6, 15)
                        local_profiles.append(profile)
                        if quotient_parity == 0:
                            logical_weight = 2 * int(parent_weight)
                            weighted_profiles[profile] += logical_weight
                            for signature, count in signatures.items():
                                weighted_modes[signature] += logical_weight * count
            parity_profiles.append(local_profiles)
        assert sorted(parity_profiles[0]) == sorted(parity_profiles[1])

    assert sum(exhaustive_quotients.values()) == EXPECTED_EXHAUSTIVE_SOURCE_SAMPLES
    assert exhaustive_quotients == {
        residue: EXPECTED_FACTOR28_SOURCE_PARENTS * count
        for residue, count in EXPECTED_LOCAL_QUOTIENT_COUNTS.items()
    }
    assert weighted_profiles == {(8, 6, 15): EXPECTED_FACTOR28_NEGATIVE}
    assert weighted_modes == {
        signature: EXPECTED_FACTOR28_NEGATIVE * count
        for signature, count in EXPECTED_LOCAL_MODE_COUNTS.items()
    }
    return {
        "factor28_negative_parent_count": EXPECTED_FACTOR28_NEGATIVE,
        "factor29_logical_refinement_count": EXPECTED_FACTOR29_REFINEMENTS,
        "exhaustive_source_parent_count": EXPECTED_FACTOR28_SOURCE_PARENTS,
        "exhaustive_source_sample_count": EXPECTED_EXHAUSTIVE_SOURCE_SAMPLES,
        "factor27_quotient_counts_mod_29": {
            str(key): value for key, value in sorted(exhaustive_quotients.items())
        },
        "factor27_multiplier_counts_mod_812": {
            str(key): value for key, value in sorted(exhaustive_multiplier27.items())
        },
        "factor28_multiplier_counts_mod_29": {
            str(key): value for key, value in sorted(exhaustive_multiplier28.items())
        },
        "factor29_parent_profile_counts": {
            "cofinal=8,positive=6,negative=15": EXPECTED_FACTOR28_NEGATIVE,
        },
        "factor29_successor_mode_counts": {
            f"payment={key[0]},height={key[1]},error={key[2]}": value
            for key, value in sorted(weighted_modes.items())
        },
        "uniform_negative_continuation_ratio": "15/29",
    }


def build_receipt() -> dict[str, Any]:
    previous = json.loads(
        (REPO_ROOT / FACTOR28_RECEIPT_REF).read_text(encoding="utf-8")
    )
    assert previous["status"] == "verified_uniform_factor28_positive_activation"
    census = complete_factor29_activation_census()
    contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Under a_(n+1)/a_n^2 -> 1 and rational reciprocal sum, force "
            "eventual Sylvester recurrence."
        ),
        claim_ceiling=(
            "Exact factor-29 classification on the multiplier-one factor-28 "
            "survivors: every actual parent has 8 cofinal, 6 positive, and 15 "
            "continuing-negative children. This kills the homogeneous boundary "
            "mode at factor 29 but does not solve unrestricted #243."
        ),
        hypothesis_id="factor29_uniformly_kills_the_factor28_homogeneous_boundary",
        hypothesis_statement=(
            "Every actual multiplier-one height-28 parent has a full-payment "
            "factor-29 child and strictly fewer than 29 negative children."
        ),
        probe_id="exact_factor29_parent_local_activation_census",
        probe_question=(
            "Does factor 29 uniformly kill part of the exact factor-28 negative "
            "boundary, and which quotient classes cause return or sign switch?"
        ),
        computation=(
            "Exhaust all 2255040 source samples from the 18 parent residues, "
            "two factor-26 parities, four surviving factor-26 targets, 27 "
            "factor-27 lifts, 20 negative factor-28 lifts, and 29 factor-29 "
            "lifts using exact modular quotient propagation."
        ),
        falsifier=(
            "Any actual factor-28 parent without profile (8,6,15), especially "
            "an all-negative parent."
        ),
        stop_condition=(
            "Stop after exact parent-local quotient and successor-mode multisets "
            "are established; do not extend individual orbit horizons."
        ),
        survival_consequence=(
            "A common 15/29 continuation profile supplies a second exact "
            "uniform contraction block for the negative-mass route."
        ),
        falsification_consequence=(
            "A split or inert profile would force source-state stratification "
            "before any uniform transfer estimate."
        ),
        consumer_ref=LEAN_REF,
        consumer_declarations=[
            "ErdosProblems.Erdos243.heightTwentyEight_multiplierQuotientIdentity",
            "ErdosProblems.Erdos243.heightTwentyEight_quotientZeroMode",
            "ErdosProblems.Erdos243.heightTwentyEight_quotientFifteenMode",
            "ErdosProblems.Erdos243.heightTwentyEight_quotientTwentyFourMode",
            "ErdosProblems.Erdos243.heightTwentyEight_quotientTwentyFiveMode",
            "ErdosProblems.Erdos243.heightTwentyEight_quotientTwentySevenMode",
            "ErdosProblems.Erdos243.heightTwentyEight_fullPaymentTwentyNine",
        ],
        analysis_refs=[NOTE_REF, PACKET_REF, FACTOR28_RECEIPT_REF],
        source_refs=[
            SCRIPT_REF,
            FACTOR28_SCRIPT_REF,
            FACTOR28_RECEIPT_REF,
            LIBRARY_REF,
            TEST_REF,
        ],
        result_status="exact_one_way_result",
        result_summary=(
            "Every one of the 1110551072832000 actual parents has profile "
            "(8,6,15). The exact quotient multiset is 0^7,15^8,24^8,25^4,27^2; "
            "q=15 forces full payment 29 and q=25,27 switch positive."
        ),
        progress_class="mechanism_eliminated",
        decision_basis=(
            "The complete source census has one parent profile, eight full "
            "returns per parent, and zero inert fibers."
        ),
        next_analytic_target=(
            "Compose the exact factor-26 continuation 4/13 and factor-29 "
            "continuation 15/29 in a source-conditioned negative-mass transfer, "
            "then stratify factors 30, 35, and 36 for the three surviving errors."
        ),
        resource_bounds={
            "exhaustive_source_parent_count": EXPECTED_FACTOR28_SOURCE_PARENTS,
            "exhaustive_source_sample_count": EXPECTED_EXHAUSTIVE_SOURCE_SAMPLES,
            "logical_parent_count": EXPECTED_FACTOR28_NEGATIVE,
            "children_per_parent": 29,
            "logical_refinement_count": EXPECTED_FACTOR29_REFINEMENTS,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos243-t0-factor29-activation-receipt/1",
        "status": "verified_uniform_factor29_boundary_killing",
        "complete_factor29_census": census,
        "mechanism_decision": {
            "factor29_homogeneous_boundary": "killed",
            "cofinal_children_per_parent": 8,
            "positive_children_per_parent": 6,
            "continuing_negative_children_per_parent": 15,
            "uniform_negative_continuation_ratio": "15/29",
            "surviving_negative_states": [
                {"height": 29, "error": -1, "multiplicity": 7},
                {"height": 29, "error": -6, "multiplicity": 8},
            ],
            "positive_states": [
                {"height": 29, "error": 5, "multiplicity": 4},
                {"height": 29, "error": 7, "multiplicity": 2},
            ],
            "next_raw_factors": [30, 35],
        },
        "experiment_contract": contract,
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [
                SCRIPT_REF,
                FACTOR28_SCRIPT_REF,
                FACTOR28_RECEIPT_REF,
                LEAN_REF,
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
    args = parser.parse_args()
    if args.explore:
        print(json.dumps(complete_factor29_activation_census(), indent=2, sort_keys=True))
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
