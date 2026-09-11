import ErdosProblems.Skip.Wire3

/-!
Adversarial verification scratch file for `ErdosProblems/Skip/Wire3.lean`.
Everything here is *checking* Wire3, not extending it.
-/

open Erdos249257 Wire3

#print axioms Erdos249257.Wire3.rightTail_support_eq
#print axioms Erdos249257.Wire3.rightTail_mem_support
#print axioms Erdos249257.Wire3.rightTail_not_mem_support
#print axioms Erdos249257.Wire3.cofRanks_ge_half
#print axioms Erdos249257.Wire3.rightTail_cofRanks_subset
#print axioms Erdos249257.Wire3.rightTail_not_cofinal_cofSkip
#print axioms Erdos249257.Wire3.rightTail_cofSkip_lt
#print axioms Erdos249257.Wire3.rightTail_landingExcess_two_impossible
#print axioms Erdos249257.Wire3.allRight_tailStart_gt_half
#print axioms Erdos249257.Wire3.allRight_producer_above
#print axioms Erdos249257.Wire3.rightTail_landing_belowPulse_le_two
#print axioms Erdos249257.Wire3.rightTail_landing_pulseFloor_le_two
#print axioms Erdos249257.Wire3.two_le_cofFloor
#print axioms Erdos249257.Wire3.rightTail_landing_cofSkip
#print axioms Erdos249257.Wire3.rightTail_frozen_skipped_rank
#print axioms Erdos249257.Wire3.forcedRanks_subset
#print axioms Erdos249257.Wire3.pulseFloor_add_rowPulse_le_belowPulse
#print axioms Erdos249257.Wire3.pulseFloor_add_two_rowPulse_le_belowPulse
#print axioms Erdos249257.Wire3.rightTail_frozen_skip
#print axioms Erdos249257.Wire3.rightTail_frozen_skip_of_dvd
#print axioms Erdos249257.Wire3.rightTail_frozen_skip_cofactorThree
#print axioms Erdos249257.Wire3.rightTail_frozen_skip_pair
#print axioms Erdos249257.Wire3.rightTail_frozen_skipped_rank_of_residue
#print axioms Erdos249257.Wire3.exists_skipped_bit_of_not_subset
#print axioms Erdos249257.Wire3.half_mem_of_cofinal_cofSkip
#print axioms Erdos249257.Wire3.half_mem_or_eventually_cofRanks_subset
#print axioms Erdos249257.Wire3.rightTail_eventually_cofRanks_subset_explicit
#print axioms Erdos249257.Wire3.allRight_branch_resolved
#print axioms Erdos249257.Wire3.half_mem_or_allRight_landingExcess_two_impossible

namespace Erdos249257

namespace VerifyWire3

open HalfCylinderIntegerGreedy

/-- A cofactor floor of `2` or more already forces the *forced-rank* pulse floor
to be at least `3`.  (`s % 6 ∈ {1,4}` gives `3 ∣ 2s+1`, so rank `3` alone pulses
`2`; `s % 6 = 5` gives `3 ∣ 2s+2`, so ranks `3` and `6` pulse `1` each; and rank
`2` always pulses `1`.) -/
theorem three_le_pulseFloor_of_two_le_cofFloor (s : ℕ)
    (h : 2 ≤ AngleB2.cofFloor s) : 3 ≤ Recon257.pulseFloor s := by
  have h6 : s % 6 = 1 ∨ s % 6 = 4 ∨ s % 6 = 5 := by
    unfold AngleB2.cofFloor at h
    split_ifs at h <;> omega
  have key : 3 ≤ rowPulse s 2 + rowPulse s 3 + rowPulse s 6 := by
    unfold rowPulse
    rcases h6 with h6 | h6 | h6 <;> (split_ifs <;> omega)
  rw [Recon257.pulseFloor_eq_rowPulseSum]
  omega

/-- **`rightTail_landing_cofSkip` has contradictory hypotheses.**  Wire3's own
`rightTail_landing_pulseFloor_le_two` says the branch forces
`pulseFloor (D+1) ≤ 2`, while `cofFloor (D+1) ≥ 2` forces
`pulseFloor (D+1) ≥ 3`.  So the hypothesis block of `rightTail_landing_cofSkip`,
`rightTail_frozen_skipped_rank` and the last conjunct of
`allRight_branch_resolved` is never satisfiable. -/
theorem cofFloor_branch_vacuous (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2)
    (hcf : 2 ≤ AngleB2.cofFloor (D + 1)) : False := by
  have h1 := Wire3.rightTail_landing_pulseFloor_le_two D hD hright hlanding
  have h2 := three_le_pulseFloor_of_two_le_cofFloor (D + 1) hcf
  omega

/-- **`rightTail_frozen_skip_cofactorThree` is vacuous.**  Its residue
hypothesis `D % 3 = 0` is incompatible with the branch hypotheses. -/
theorem mod_three_branch_vacuous (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2)
    (h3 : D % 3 = 0) : False :=
  cofFloor_branch_vacuous D hD hright hlanding
    (Wire3.two_le_cofFloor (D + 1) (by omega))

/-- **`rightTail_frozen_skipped_rank_of_residue` is vacuous** for the same
reason: `D % 6 ∈ {0,3,4}` cannot hold on the branch. -/
theorem residue_branch_vacuous (D : ℕ) (hD : 60 ≤ D)
    (hres : D % 6 = 0 ∨ D % 6 = 3 ∨ D % 6 = 4)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2) : False :=
  cofFloor_branch_vacuous D hD hright hlanding
    (Wire3.two_le_cofFloor (D + 1) (by omega))

/-- The positive statement Wire3 could have made instead: on the branch the
landing row is confined to `D % 6 ∈ {1, 2, 5}`.  Half of all residues die. -/
theorem branch_residue_restriction (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    D % 6 = 1 ∨ D % 6 = 2 ∨ D % 6 = 5 := by
  by_contra hcon
  exact residue_branch_vacuous D hD (by omega) hright hlanding

end VerifyWire3

end Erdos249257
