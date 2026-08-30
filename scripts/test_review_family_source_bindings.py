#!/usr/bin/env python3
"""Check source bindings for review-only families without consulting the atlas.

The declaration atlas is deliberately fail-closed while its source fingerprint is
stale.  These checks therefore validate the Claims metadata directly against the
current Lean bytes.  Dictionary order below is not a ranking or presentation order.
"""

from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CLAIMS = ROOT / "docs" / "claims.json"


FAMILY_BINDINGS = {
    "integral_shift_classification": {
        "declarations": [
            "ErdosProblems.Erdos251.irrational_initial_iff_all_positive_tailShifts_nonintegral",
            "ErdosProblems.Erdos251.not_irrational_initial_iff_exists_eventually_integral_positive_tailShift",
            "ErdosProblems.Erdos251.tailShift_integral_iff_den_dvd_mersenne",
            "ErdosProblems.Erdos251.tailShift_integral_iff_two_pow_modEq_one",
        ],
        "boundary": "concrete prime-gap producer remains missing",
        "sources": [
            "ErdosProblems/Erdos251/PrimeGapDyadicTail.lean",
            "ErdosProblems/Erdos251/PrimeGapDyadicTail.lean",
            "ErdosProblems/Erdos251/PrimeGapDyadicTail.lean",
            "ErdosProblems/Erdos251/PrimeGapDyadicTail.lean",
        ],
    },
    "totient_certificate_equivalences": {
        "declarations": [
            "Erdos249257.TotientTailPeriodKiller.irrational_totient_series_iff_lcm_diagonal_certificate_supply",
            "ErdosProblems.Erdos249.PeriodMultipleEscape.periodMultipleKillSupply_iff_irrational",
            "Erdos249257.TotientTailPeriodKiller.dtwWindowSeparatedPairs_iff_irrational_totient_series",
        ],
        "boundary": "as hard as the unresolved target",
        "sources": [
            "Erdos249257/LcmConeFlatness.lean",
            "ErdosProblems/Erdos249/PeriodMultipleEscape.lean",
            "Erdos249257/PivotAntiReconstruction.lean",
        ],
    },
    "factorial_channel_and_projection_rigidity": {
        "declarations": [
            "Erdos68.factorialMoment_eq_factorial_pow_mul_channelNumerator_band",
            "Erdos68.exists_index_ge_two_mul_of_factorialMoment_ne_zero_of_channel_eq_zero",
            "Erdos68.channelNumerator_mod_factorialMoment",
            "Erdos68.primeTranslator_channelResidual_eq_one",
            "ErdosProblems.Erdos68.projection_disagreement_excludes_bounded_endpoint",
        ],
        "boundary": "do not produce a cofinal obstruction",
        "sources": [
            "ErdosProblems/Erdos68/ChannelBreakpointRigidity.lean",
            "ErdosProblems/Erdos68/ChannelBreakpointRigidity.lean",
            "ErdosProblems/Erdos68/ChannelIntegralCongruence.lean",
            "ErdosProblems/Erdos68/PrimeUnitTranslator.lean",
            "ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean",
        ],
    },
    "newton_value_decay": {
        "declarations": [
            "ErdosProblems.Erdos1041.newtonFlow_value_hasDerivAt",
            "ErdosProblems.Erdos1041.newtonFlow_scaledValue_hasDerivAt_zero",
        ],
        "boundary": "does not give a short connecting curve",
        "sources": [
            "ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean",
            "ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean",
        ],
    },
    "eventually_periodic_lambert": {
        "declarations": [
            "Erdos249257.irrational_ratWeightSeries_eventuallyPeriodic",
        ],
        "boundary": "not eventually periodic",
        "sources": [
            "Erdos249257/CertificateKernel.lean",
        ],
    },
    "ray_separation": {
        "declarations": [
            "ErdosProblems.Erdos1041.samePositiveRay_of_real_exp_decay",
            "ErdosProblems.Erdos1041.no_newtonConnection_of_not_samePositiveRay",
        ],
        "boundary": "route obstruction, not the global theorem",
        "sources": [
            "ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean",
            "ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean",
        ],
    },
    "bounded_rise_coprimality": {
        "declarations": [
            "ErdosProblems.Erdos243.no_eventuallyBoundedRise_reducedTail",
            "ErdosProblems.Erdos243.reducedTail_pairwiseCoprime",
        ],
        "boundary": "bounded-rise input is not automatic",
        "sources": [
            "ErdosProblems/Erdos243/ReciprocalTailRigidity.lean",
            "ErdosProblems/Erdos243/ReciprocalTailRigidity.lean",
        ],
    },
    "height_fibre_and_shell": {
        "declarations": [
            "ErdosProblems.Erdos269.finiteSmoothKernelSum_groupedByHeight",
            "ErdosProblems.Erdos269.smoothExponentShell_card_quadratic",
        ],
        "boundary": "do not provide the missing divisibility bridge",
        "sources": [
            "ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean",
            "ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean",
        ],
    },
    "totient_shift_propagation": {
        "declarations": [
            "ErdosProblems.Erdos251.tailShift_integral_totient_of_odd_den",
            "ErdosProblems.Erdos251.tailShift_integral_succ",
            "ErdosProblems.Erdos251.tailShift_integral_add",
        ],
        "boundary": "supplies no contradiction for actual prime gaps",
        "sources": [
            "ErdosProblems/Erdos251/PrimeGapDyadicTail.lean",
            "ErdosProblems/Erdos251/PrimeGapDyadicTail.lean",
            "ErdosProblems/Erdos251/PrimeGapDyadicTail.lean",
        ],
    },
    "totient_lambert_coefficients": {
        "declarations": [
            "MersenneLambertLadder.tsum_primWeight_div_two_pow_sub_one",
            "Erdos249257.tsum_primWeight_div_two_pow_sub_one_eq_totient_series",
        ],
        "boundary": "do not prove irrationality",
        "sources": [
            "Erdos249257/MersenneLambertLadder.lean",
            "Erdos249257/CertificateKernel.lean",
        ],
    },
    "dyadic_block_alphabet": {
        "declarations": [
            "ErdosProblems.Erdos269.dyadicBlockBase235_cases",
        ],
        "boundary": "does not supply the needed carry escape",
        "sources": [
            "ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean",
        ],
    },
}


def load_claims() -> dict:
    return json.loads(CLAIMS.read_text(encoding="utf-8"))


def review_families(claims: dict) -> dict[str, list[dict]]:
    rows: dict[str, list[dict]] = {}
    for problem in claims["external_verification_packet"]["review_matrix"]:
        for family in problem["families"]:
            rows.setdefault(family["id"], []).append(family)
    return rows


def test_review_families_bind_exact_declarations_and_boundaries() -> None:
    rows = review_families(load_claims())
    for family_id, expected in FAMILY_BINDINGS.items():
        assert len(rows.get(family_id, [])) == 1, family_id
        family = rows[family_id][0]
        assert family.get("declarations") == expected["declarations"], family_id
        assert expected["boundary"] in family.get("boundary", ""), family_id


def test_review_family_declarations_match_current_lean_bytes() -> None:
    declaration_pattern = re.compile(r"\s*(?:def|lemma|theorem)\s+([A-Za-z0-9_]+)\b")
    for family_id, expected in FAMILY_BINDINGS.items():
        declarations = expected["declarations"]
        sources = expected["sources"]
        assert len(declarations) == len(sources), family_id
        for qualified_name, source in zip(declarations, sources, strict=True):
            lines = (ROOT / source).read_text(encoding="utf-8").splitlines()
            short_name = qualified_name.rsplit(".", 1)[-1]
            matches = [
                index
                for index, line in enumerate(lines, 1)
                if (match := declaration_pattern.match(line)) and match.group(1) == short_name
            ]
            assert len(matches) == 1, f"{qualified_name} in {source}: {matches}"


def test_backfill_stays_review_only_and_strict_prime_is_not_duplicated() -> None:
    claims = load_claims()
    canonical_ids = [row.get("id") for row in claims["claims"]]
    assert not set(FAMILY_BINDINGS).intersection(canonical_ids)
    assert canonical_ids.count("strict_prime_tail_orbit_gap") == 1


if __name__ == "__main__":
    test_review_families_bind_exact_declarations_and_boundaries()
    test_review_family_declarations_match_current_lean_bytes()
    test_backfill_stays_review_only_and_strict_prime_is_not_duplicated()
    print("review-family source bindings: ok")
