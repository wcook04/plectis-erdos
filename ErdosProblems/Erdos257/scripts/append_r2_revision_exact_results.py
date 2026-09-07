#!/usr/bin/env python3
"""Idempotently append r2-revision exact_results into the Erdős 257 packet."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

PACKET = Path(__file__).resolve().parents[1] / "research_packet.json"
ROOT = Path(__file__).resolve().parents[4]  # repo root via Erdos257/scripts -> +4?


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    repo = Path(__file__).resolve()
    # .../formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/scripts/this.py
    erdos257 = repo.parents[1]
    packet_path = erdos257 / "research_packet.json"
    note_sep = erdos257 / "VariableExponentCoverSeparation.md"
    note_dim = erdos257 / "RestrictedAchievementHausdorffDimension.md"
    note_half = erdos257 / "HalfTargetQuantifierDiscipline.md"
    lean_mean = erdos257 / "CoverIndependentPeriodicMean.lean"
    script = erdos257 / "scripts" / "reconstruct_variable_exponent_dagger.py"
    data = json.loads(packet_path.read_text())
    existing = {row.get("id") for row in data.get("exact_results", [])}
    new_rows = [
        {
            "id": "cover_independent_periodic_mean_bound",
            "status": "lean_checked_cesaro_majorant_and_ordinary_periodic_density",
            "statement": "If 0 ≤ g(n) ≤ ∑_{d|n} c_d for a finitely supported nonnegative divisor majorant, then every Cesàro mean of g on {1,…,X} is at most ∑ c_d/d. Consequently every periodic mean of a nonnegative function dominated by such a majorant is at most the majorant cost. The coprime-union density 1-∏(1-1/a) is an ordinary identity used with this bound.",
            "source_path": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/CoverIndependentPeriodicMean.lean",
            "ordinary_density_path": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/VariableExponentCoverSeparation.md",
            "source_sha256": sha256(lean_mean),
            "source_declarations": [
                "ErdosProblems.Erdos257.card_Icc_one_filter_dvd",
                "ErdosProblems.Erdos257.cesaro_le_divisorMajorantCost",
            ],
            "claim_boundary": "Lean checks the averaging inequality and the count of multiples in an initial interval. It does not prove irrationality, does not enumerate A^dagger, and does not currently check the coprime-union density identity.",
            "validation": "Focused lean_fast_build of ErdosProblems.Erdos257.CoverIndependentPeriodicMean; reconstruction script checks the squarefree-frame identities used to apply the bound.",
            "next_consumer_effect": "Feeds the ordinary A.3/B.1 cover-cost comparison. Does not replace reciprocal_summable_supports_base_two.",
            "surviving_obligation": "Coprime-union density remains ordinary. Universal #257 remains open.",
        },
        {
            "id": "variable_exponent_dagger_beyond_weighted_and_fixed_cover",
            "status": "ordinary_proof",
            "statement": "There is an explicit squarefree support A^dagger, assembled from Bertrand-reserved primes q_j and leftover prime-harmonic blocks, that satisfies the manuscript variable-exponent positive-cover criterion (hence hereditary all-base irrationality for every infinite subset) while every fixed-α positive divisor-majorant cover and every finite-prime weighted mass W_{b,P} diverges.",
            "source_path": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/VariableExponentCoverSeparation.md",
            "source_sha256": sha256(note_sep),
            "reconstruction": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/scripts/reconstruct_variable_exponent_dagger.py --quick",
            "reconstruction_sha256": sha256(script),
            "claim_effect": "Separates the already-admitted variable-exponent remainder from both the finite-P weighted test and every fixed-exponent positive cover, without changing the paper lead.",
            "claim_boundary": "Ordinary proof conditional on the manuscript variable-exponent theorem and Bertrand's postulate. Finite reconstruction checks identities and small-j windows; it does not enumerate the infinite 4^j blocks. Historical novelty unassessed. Does not decide primes, 1/2, or universal #257.",
            "validation": "Independent ordinary reading plus reconstruct_variable_exponent_dagger.py identities, elementary inequalities, small Bertrand windows, and a miniature dagger.",
            "next_consumer_effect": "Keep as an enlargement of variable_exponent_fractional_cover_irrationality. Do not promote to Palomar lead.",
            "surviving_obligation": "Lean of the full A^dagger construction and of coprime density remains open. Reciprocal_summable_supports_base_two stays the Lean flagship.",
        },
        {
            "id": "pairwise_coprime_variable_cover_obstruction",
            "status": "ordinary_proof",
            "statement": "If A contains a pairwise-coprime set E of integers ≥2 with divergent reciprocal sum, then every countable finite cover of A by nonnegative divisor majorants of any exponents α_i>0 has infinite total cost. In particular the variable-exponent summability test and every finite-P weighted test fail. The primes are such an E; their irrationality is Tao–Teräväinen, not a cover theorem.",
            "source_path": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/VariableExponentCoverSeparation.md",
            "source_sha256": sha256(note_sep),
            "claim_boundary": "Ordinary averaging-plus-density argument. Lean currently supplies only the Cesàro majorant, not the coprime density identity. Failure of these sufficient tests is not evidence of rationality.",
            "validation": "Ordinary proof; reconstruct_variable_exponent_dagger.py checks 1-∏(1-1/a) and 1-exp(-H) on a small coprime tuple.",
            "next_consumer_effect": "Records that weighted and variable-exponent methods still miss the primes. Does not replace reciprocal_summable_supports_base_two.",
            "surviving_obligation": "Universal #257 remains open. Prime-support irrationality remains the Tao–Teräväinen theorem.",
        },
        {
            "id": "restricted_support_hausdorff_dimension",
            "status": "ordinary_proof",
            "statement": "For any allowed index set J, the restricted Mersenne achievement set A_J has Hausdorff dimension equal to liminf |J∩[1,N]|/N. Arithmetic progressions mℕ recover dimension 1/m. Ahlfors regularity and biased-entropy dimension are not claimed.",
            "source_path": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/RestrictedAchievementHausdorffDimension.md",
            "source_sha256": sha256(note_dim),
            "claim_boundary": "Ordinary geometric classification of subsums, not an arithmetic statement about rational points. Strictly more general than the dimension clause of arithmetic_stride_dimension; does not supersede that row's Ahlfors or entropy claims. Topology and Lebesgue measure remain the Lean hereditary subachievement theorems. Fair-coin a.s. irrationality is Kovač–Tao, not restated here.",
            "validation": "Independent ordinary reading. Collision-checked against arithmetic_stride_dimension and hereditary topology/measure rows.",
            "next_consumer_effect": "Expository geometry only. Does not settle Erdős #257 or any rational target.",
            "surviving_obligation": "Ahlfors regularity and entropy dimension remain advisory pending Lean. Universal #257 remains open.",
        },
        {
            "id": "half_target_quantifier_discipline",
            "status": "claim_language_lock_live_paper_already_correct",
            "statement": "Finite-horizon carry-free shadowing witnesses may depend on the horizon; a global pair (M,δ) is a separate claim. The exact rational second-channel recurrence retains the translations 2^{n+1} on both branches. The interval (0,1) is not a trapping region; x=17/256 is an explicit witness that skip images need not stay in (0,1). Neither correction decides 1/2-membership.",
            "source_path": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/HalfTargetQuantifierDiscipline.md",
            "source_sha256": sha256(note_half),
            "lean_source": "formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/GreedyAchievementSet.lean",
            "source_declarations": [
                "Erdos257PeriodNoncollapse.greedyMersenneSecondChannelPhaseRat_succ"
            ],
            "claim_boundary": "Locks quantifiers against illegal global strengthening. Live Palomar paper never stated the illegal S1 global shadow or the truncated S2 map. Type B's reviewed short note is not the live manuscript.",
            "validation": "Live declaration includes ±2^{n+1}. Reconstruction script checks x=17/256. Paper pointer added 2026-09-06.",
            "next_consumer_effect": "Any future S1/S2 claim must keep horizon-dependent witnesses and the exact translations.",
            "surviving_obligation": "1/2 and 1/21 remain open. Finite-horizon histograms remain finite arithmetic.",
        },
    ]
    added = []
    for row in new_rows:
        if row["id"] in existing:
            continue
        data["exact_results"].append(row)
        added.append(row["id"])
    delta_extra = (
        " The 2026-09-06 Type B revision packet is assimilated without changing the paper lead: "
        "reciprocal_summable_supports_base_two remains the Lean-checked Palomar flagship "
        "(Erdős already stated the coprimality-free reciprocal-summable case). Ordinary "
        "cover-independent means, the A^dagger separation beyond every fixed-α cover and every "
        "finite-P weight, the pairwise-coprime cover obstruction, and the general restricted "
        "Hausdorff-dimension formula are recorded as enlargements of the variable-exponent remainder. "
        "S1 global-shadowing and truncated S2 maps are rejected; the live second-channel recurrence "
        "already keeps the 2^{n+1} translations. Universal #257 remains open."
    )
    current_delta = data.get("latest_claim_ceiling_delta") or ""
    if "cover-independent means" not in current_delta:
        data["latest_claim_ceiling_delta"] = current_delta.rstrip() + delta_extra
    neg = (
        "Do not promote a finite-horizon carry-free identity to a global shadowing pair, "
        "and do not omit the rank-dependent translations 2^{n+1} from the second-channel "
        "phase map; both strengthenings are false in general (horizon-dependent witnesses; "
        "x=17/256). Those errors occurred in a reviewed short note, not in the live Palomar paper."
    )
    negs = data.setdefault("negative_results", [])
    if not any("17/256" in str(item) for item in negs):
        negs.append(neg)
    policy = data.get("paper_projection", {}).get("policy", "")
    wanted = (
        "The active problem paper explains the checked reciprocal-summable theorem and "
        "explicitly separates reviewed ordinary extensions. The 2026-09-06 revision "
        "packet did not replace that lead. Registry authority is the public docs/papers/corpus.json."
    )
    if "2026-09-06 revision" not in policy:
        data.setdefault("paper_projection", {})["policy"] = wanted
    packet_path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"added": added, "packet": str(packet_path)}, indent=2))


if __name__ == "__main__":
    main()
