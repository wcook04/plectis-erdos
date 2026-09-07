#!/usr/bin/env python3
"""Certify factor-27 rigidity on the exact surviving #243 inert branch.

Factor 26 leaves eight genuine negative children per formerly inert parent,
all with multiplier residue one, height 26, and centered error -1.  This
checker starts from the digest-bound factor-26 parent cache, exhausts both
possible quotient parities and all 27 next source lifts, and proves that the
divided multiplier is the singleton one modulo 27.  Hence every actual child
pays one and continues to height 27 with centered error -1.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path
from typing import Any

import numpy as np


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
    EXPECTED_FACTOR26_MULTIPLIER_COUNTS,
    PARENT_CACHE_PATH,
    TARGET_SOURCE_MODULUS,
    _load_parent_cache,
)


SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_t0_factor27_singleton.py"
)
FACTOR26_SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_t0_factor26_activation.py"
)
FACTOR26_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos243_t0_factor26_activation_receipt.json"
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
    "erdos243_t0_factor27_singleton_receipt.json"
)

FACTOR27_SOURCE_MODULUS = TARGET_SOURCE_MODULUS * 27
EXPECTED_FACTOR26_NEGATIVE_PARENTS = EXPECTED_FACTOR26_MULTIPLIER_COUNTS["1"]
EXPECTED_FACTOR27_REFINEMENTS = EXPECTED_FACTOR26_NEGATIVE_PARENTS * 27
EXPECTED_EXHAUSTIVE_SOURCE_SAMPLES = 18 * 2 * 4 * 27


def _multiplier25_modulus(p: int, source_modulus: int) -> int:
    multiplier20 = (380 * p * p + 18 * p + 1) % source_modulus
    assert (multiplier20 - 1) % 21 == 0
    r = ((multiplier20 - 1) // 21) % (source_modulus // 21)
    multiplier21 = (420 * r * r + 19 * r + 1) % (source_modulus // 21)
    assert (multiplier21 - 1) % 22 == 0
    q = ((multiplier21 - 1) // 22) % (source_modulus // (21 * 22))
    multiplier22 = (
        462 * q * q + 20 * q + 1
    ) % (source_modulus // (21 * 22))
    assert (multiplier22 - 1) % 23 == 0
    z = ((multiplier22 - 1) // 23) % (source_modulus // (21 * 22 * 23))
    multiplier23 = (
        506 * z * z + 21 * z + 1
    ) % (source_modulus // (21 * 22 * 23))
    assert (multiplier23 - 1) % 24 == 0
    c = ((multiplier23 - 1) // 24) % (
        source_modulus // (21 * 22 * 23 * 24)
    )
    multiplier24 = (
        552 * c * c + 22 * c + 1
    ) % (source_modulus // (21 * 22 * 23 * 24))
    assert (multiplier24 * multiplier24 - 1) % 25 == 0
    numerator = 24 * multiplier24 * multiplier24 - 25 * multiplier24 + 26
    assert numerator % 25 == 0
    return (numerator // 25) % (source_modulus // (21 * 22 * 23 * 24 * 25))


def _multiplier26_mod27(multiplier25_mod702: int) -> int:
    numerator = (
        25 * multiplier25_mod702 * multiplier25_mod702
        - 26 * multiplier25_mod702
        + 27
    )
    assert numerator % 26 == 0
    return (numerator // 26) % 27


def complete_factor27_singleton_census() -> dict[str, Any]:
    cached = _load_parent_cache()
    assert cached is not None, f"missing or stale factor-26 parent cache: {PARENT_CACHE_PATH}"
    parent_residues, parent_weights = cached
    assert parent_residues.size == 18
    exhaustive_c_mod702: Counter[int] = Counter()
    exhaustive_d_mod27: Counter[int] = Counter()
    weighted_d_mod27: Counter[int] = Counter()
    weighted_modes: Counter[tuple[int, int, int]] = Counter()
    parity_profile_checks = 0

    for p_current, parent_weight in zip(parent_residues, parent_weights, strict=True):
        parity_profiles: list[list[int]] = []
        for quotient_parity in (0, 1):
            factor26_targets = [
                int(p_current)
                + CURRENT_SOURCE_MODULUS * (quotient_parity + 2 * half)
                for half in range(13)
            ]
            surviving_targets = [
                target
                for target in factor26_targets
                if _multiplier25_modulus(target, TARGET_SOURCE_MODULUS) == 1
            ]
            assert len(surviving_targets) == 4
            d_values: list[int] = []
            for target in surviving_targets:
                for lift27 in range(27):
                    refined = target + TARGET_SOURCE_MODULUS * lift27
                    multiplier25 = _multiplier25_modulus(
                        refined, FACTOR27_SOURCE_MODULUS
                    )
                    assert multiplier25 % 26 == 1
                    multiplier26 = _multiplier26_mod27(multiplier25)
                    exhaustive_c_mod702[multiplier25] += 1
                    exhaustive_d_mod27[multiplier26] += 1
                    d_values.append(multiplier26)
            parity_profiles.append(sorted(d_values))
        assert parity_profiles[0] == parity_profiles[1]
        parity_profile_checks += 1
        for multiplier26 in parity_profiles[0]:
            logical_weight = 2 * int(parent_weight)
            weighted_d_mod27[multiplier26] += logical_weight
            weighted_modes[
                centered_successor_signature(26, -1, multiplier26)
            ] += logical_weight

    assert parity_profile_checks == 18
    assert sum(exhaustive_c_mod702.values()) == EXPECTED_EXHAUSTIVE_SOURCE_SAMPLES
    assert exhaustive_c_mod702 == {1: EXPECTED_EXHAUSTIVE_SOURCE_SAMPLES}
    assert exhaustive_d_mod27 == {1: EXPECTED_EXHAUSTIVE_SOURCE_SAMPLES}
    assert weighted_d_mod27 == {1: EXPECTED_FACTOR27_REFINEMENTS}
    assert weighted_modes == {(1, 27, -1): EXPECTED_FACTOR27_REFINEMENTS}
    return {
        "factor26_parent_residue_count": int(parent_residues.size),
        "factor26_negative_parent_count": EXPECTED_FACTOR26_NEGATIVE_PARENTS,
        "factor27_logical_refinement_count": EXPECTED_FACTOR27_REFINEMENTS,
        "exhaustive_source_sample_count": EXPECTED_EXHAUSTIVE_SOURCE_SAMPLES,
        "quotient_parity_profile_checks": parity_profile_checks,
        "factor25_multiplier_counts_mod_702": {
            str(key): value for key, value in sorted(exhaustive_c_mod702.items())
        },
        "factor26_multiplier_counts_mod_27": {
            str(key): value for key, value in sorted(weighted_d_mod27.items())
        },
        "factor27_parent_profile_counts": {
            "cofinal=0,positive=0,negative=27": EXPECTED_FACTOR26_NEGATIVE_PARENTS,
        },
        "factor27_successor_mode_counts": {
            f"payment={key[0]},height={key[1]},error={key[2]}": value
            for key, value in sorted(weighted_modes.items())
        },
        "source_lift_mechanism": {
            "factor26_quotient_parities_exhausted": [0, 1],
            "factor27_lifts_per_distinct_factor26_target": 27,
            "factor25_multiplier_image_mod_702": [1],
            "factor26_multiplier_image_mod_27": [1],
        },
    }


def build_receipt() -> dict[str, Any]:
    previous = json.loads(
        (REPO_ROOT / FACTOR26_RECEIPT_REF).read_text(encoding="utf-8")
    )
    assert previous["status"] == (
        "verified_uniform_factor26_activation_and_forced_cofinal_cascade"
    )
    census = complete_factor27_singleton_census()
    contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Under a_(n+1)/a_n^2 -> 1 and rational reciprocal sum, force "
            "eventual Sylvester recurrence."
        ),
        claim_ceiling=(
            "Exact factor-27 classification of the multiplier-one survivors from "
            "the t=0 factor-26 branch: all 55527553641600 logical refinements pay "
            "one and reach height 27 with centered error -1. This eliminates every "
            "generic factor-27 activation mode but does not solve unrestricted #243."
        ),
        hypothesis_id="factor27_activates_multiplier_one_factor26_survivors",
        hypothesis_statement=(
            "Some actual factor-27 refinement of the surviving (26,-1) branch "
            "returns cofinally or switches to nonnegative centered error."
        ),
        probe_id="exact_factor27_full_lift_singleton_census",
        probe_question=(
            "Does factor 27 activate the exact multiplier-one boundary left by "
            "factor 26, or is its source image rigidly multiplier one again?"
        ),
        computation=(
            "Start from all 18 digest-bound parent residues, exhaust both possible "
            "factor-26 quotient parities, retain all four distinct C=1 targets, "
            "and evaluate all 27 next source lifts with exact Python integers."
        ),
        falsifier=(
            "Any actual source sample whose factor-25 multiplier is not 1 modulo "
            "702, or whose next multiplier is not 1 modulo 27."
        ),
        stop_condition=(
            "Stop after the complete parent-local factor-27 profile is exact; do "
            "not count a longer orbit audit as progress."
        ),
        survival_consequence=(
            "A cofinal or positive class would remove another exact share of the "
            "expanding multiplier-one boundary."
        ),
        falsification_consequence=(
            "The singleton source image eliminates factor 27 as an activation "
            "mechanism and forces the next distinct probe to factor 28."
        ),
        consumer_ref=LEAN_REF,
        consumer_declarations=[
            "ErdosProblems.Erdos243.heightTwentySix_multiplierAtOneMod702Identity",
            "ErdosProblems.Erdos243.heightTwentySix_multiplierOneModTwentySeven",
        ],
        analysis_refs=[NOTE_REF, PACKET_REF, FACTOR26_RECEIPT_REF],
        source_refs=[SCRIPT_REF, FACTOR26_SCRIPT_REF, FACTOR26_RECEIPT_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "All 3888 exhaustive source samples have C=1 mod 702 and D=1 mod 27; "
            "after exact weights are restored, all 55527553641600 logical "
            "factor-27 refinements share profile (0,0,27)."
        ),
        progress_class="mechanism_eliminated",
        decision_basis=(
            "The complete actual source image is a singleton, so every generic "
            "factor-27 payment or sign-switch mode is absent."
        ),
        next_analytic_target=(
            "Probe factor 28 on the exact multiplier-one (27,-1) branch, while "
            "retaining the singleton C mod 702 certificate as its causal parent."
        ),
        resource_bounds={
            "factor26_parent_residue_count": 18,
            "exhaustive_source_sample_count": EXPECTED_EXHAUSTIVE_SOURCE_SAMPLES,
            "logical_parent_count": EXPECTED_FACTOR26_NEGATIVE_PARENTS,
            "children_per_parent": 27,
            "logical_refinement_count": EXPECTED_FACTOR27_REFINEMENTS,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos243-t0-factor27-singleton-receipt/1",
        "status": "verified_factor27_singleton_boundary_persistence",
        "complete_factor27_census": census,
        "mechanism_decision": {
            "factor27_activation": "eliminated",
            "factor27_multiplier_image": [1],
            "factor27_parent_profile": {
                "cofinal_children": 0,
                "positive_children": 0,
                "continuing_negative_children": 27,
            },
            "surviving_state": {"height": 27, "error": -1},
            "next_raw_factor": 28,
        },
        "experiment_contract": contract,
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [
                SCRIPT_REF,
                FACTOR26_SCRIPT_REF,
                FACTOR26_RECEIPT_REF,
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
        print(json.dumps(complete_factor27_singleton_census(), indent=2, sort_keys=True))
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
