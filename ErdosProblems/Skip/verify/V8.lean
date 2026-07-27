import ErdosProblems.Skip.Wire2

open Erdos249257.Wire2

#print axioms seamWordSupport_rightTail_eq
#print axioms Ico_subset_seamWordSupport_of_rightTail
#print axioms notMem_seamWordSupport_of_rightTail
#print axioms cofRanks_two_mul_ge
#print axioms largestCertifiableRank_le
#print axioms cofRanks_subset_of_rightTail
#print axioms allRight_landingExcess_two_impossible_of_earlyRightTail
#print axioms finalMiddleCell_neg_two_impossible_of_earlyRightTail
#print axioms no_landing_beyond_double
#print axioms allRight_landing_scale_rigidity
#print axioms allRight_branch_resolved
#print axioms allRight_branch_resolved_or_half
#print axioms allRight_forces_cofSkip
#print axioms allRight_forces_frozen_skip
#print axioms middleCell_rank_notMem_seamWordSupport
#print axioms cofRanks_not_subset_at_double
#print axioms cof3Ratchet_survivor_count
#print axioms allRight_landingExcess_two_impossible_of_threeHalvesRightTail
#print axioms no_landing_beyond_threeHalves
#print axioms finalMiddleCell_neg_two_unique_scale
#print axioms cof3Ranks_subset_of_rightTail
#print axioms totalFloor3_le_belowPulse
#print axioms cof3Run_bound

/-! ## Adversarial counter-checks (V8) -/

namespace V8

open Erdos249257 HalfCylinderIntegerGreedy

/-- CHECK 1.  The `hright` branch hypothesis carried by every headline theorem
of `Wire2` already decides the #257 half-membership question negatively.  So
the right disjunct of `allRight_branch_resolved_or_half` is unreachable under
its own hypotheses, and no `hright`-conditional theorem can be combined with
the corpus's positive route. -/
theorem hright_decides_half (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    (1 / 2 : ℝ) ∉ mersenneAchievementSet := by
  intro hmem
  exact half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight.mp hmem
    ⟨D + 1, by omega, hright⟩

/-- CHECK 2.  A middle-branch row `D` and an all-right tail starting at any
`S ≤ D` are contradictory *outright*: the middle branch appends `false` at row
`D`, the tail appends `true`.  No cofactor ranks, no ratchet, no `2 * S ≤ D + 1`
and no `61 ≤ D`. -/
theorem middleBranch_contra_rightTail
    (S D : ℕ) (hD : 5 ≤ D) (hSD : S ≤ D)
    (hncarry : ¬ (seamAdjacentCut D hD).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D hD).remainder +
            (seamPerturbedFamily D (by omega : 3 ≤ D)).gap -
            (seamAdjacentCut D hD).belowPulse <
          (seamAdjacentCut D hD).terminalWeight)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    False := by
  have h1 : D ∈ seamWordSupport (seamGreedyWord (D + 1)) := by
    rw [hright D hSD, seamWordSupport_extend_true (by omega)]
    exact Finset.mem_insert_self _ _
  rw [seamGreedyWord_succ_eq_middleBranch D hD hncarry hmiddle,
    seamWordSupport_extend_false (by omega)] at h1
  exact absurd (seamWordSupport_below h1).2 (by omega)

/-- CHECK 3.  `Wire2.finalMiddleCell_neg_two_impossible_of_earlyRightTail`
without `hD : 60 ≤ D`, without `hcell`, and with `S ≤ D` in place of
`2 * S ≤ D + 1`. -/
theorem finalMiddleCell_neg_two_impossible_trivial
    (S D : ℕ) (hD : 5 ≤ D) (hSD : S ≤ D)
    (hncarry : ¬ (seamAdjacentCut D hD).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D hD).remainder +
            (seamPerturbedFamily D (by omega : 3 ≤ D)).gap -
            (seamAdjacentCut D hD).belowPulse <
          (seamAdjacentCut D hD).terminalWeight)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    False :=
  middleBranch_contra_rightTail S D hD hSD hncarry hmiddle hright

/-- CHECK 4.  `Wire2.finalMiddleCell_neg_two_unique_scale` with the factor `2`
deleted: `D₁ + 1 ≤ D₂` suffices, `60 ≤ D₁` and `60 ≤ D₂` are not needed, and
`hcell` is not needed.  The advertised "at most a factor `2` apart" is therefore
not what the hypotheses actually permit — they permit no separation at all. -/
theorem finalMiddleCell_neg_two_unique_scale_sharper
    (D₁ D₂ : ℕ) (h₂ : 5 ≤ D₂) (hle : D₁ + 1 ≤ D₂)
    (hright₁ : ∀ s : ℕ, D₁ + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hncarry : ¬ (seamAdjacentCut D₂ h₂).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D₂ h₂).remainder +
            (seamPerturbedFamily D₂ (by omega : 3 ≤ D₂)).gap -
            (seamAdjacentCut D₂ h₂).belowPulse <
          (seamAdjacentCut D₂ h₂).terminalWeight) :
    False :=
  middleBranch_contra_rightTail (D₁ + 1) D₂ h₂ hle hncarry hmiddle hright₁

#print axioms hright_decides_half
#print axioms middleBranch_contra_rightTail
#print axioms finalMiddleCell_neg_two_unique_scale_sharper

end V8

