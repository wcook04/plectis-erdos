import ErdosProblems.Skip.D1

/-! Adversarial verification scratch file for `ErdosProblems/Skip/D1.lean`. -/

namespace Erdos249257
namespace SkipD1

-- axioms of every theorem in D1
#print axioms largestSkipHalfAt_of_largestSkipLateAt
#print axioms largestSkipHalfAt_of_skipped
#print axioms cofRanks_half
#print axioms halfCofRank_not_late
#print axioms cofRanks_eq
#print axioms rowPulse_pos_of_cofactorEq
#print axioms cofactorEq_of_half_of_rowPulse_pos
#print axioms mem_cofRanks_iff_half_rowPulse_pos
#print axioms cofactor_ge_five_not_half
#print axioms cofactorThree_of_late_of_rowPulse_pos
#print axioms cofRanks_subset_or_largestSkipHalfAt
#print axioms seamGreedyUnboundedSkippedRanksAlong_of_cofinal_largestSkipHalfAt
#print axioms half_mem_of_cofinal_largestSkipHalfAt
#print axioms half_mem_or_eventually_cofRanks_subset
#print axioms allRight_landingExcess_two_forces_halfSkip
#print axioms allRight_landingExcess_two_forces_halfSkip_landingRow
#print axioms exists_bound_allRight_landingExcess_two_impossible
#print axioms exists_bound_finalMiddleCell_neg_two_impossible

-- upstream load-bearing results
#print axioms Erdos249257.AngleB2.allRight_landingExcess_two_impossible
#print axioms Erdos249257.AngleB2.cofRatchet_finite_core
#print axioms Erdos249257.seamGreedyEventuallyRight_iff_half_not_mem
#print axioms Erdos249257.half_mem_mersenneAchievementSet_of_unboundedSkippedRanks

-- full elaborated statements (hunting for hidden hypotheses)
#check @exists_bound_allRight_landingExcess_two_impossible
#check @exists_bound_finalMiddleCell_neg_two_impossible
#check @half_mem_or_eventually_cofRanks_subset
#check @allRight_landingExcess_two_forces_halfSkip_landingRow
#check @cofRanks_subset_or_largestSkipHalfAt
#check @LargestSkipHalfAt
#print Erdos249257.mersenneAchievementSet
#print Erdos249257.SeamGreedyEventuallyRight
#print Erdos249257.IsLargestFalseRank
#print Erdos249257.AngleB2.cofRanks

/-! ## Adversarial probe: is the bound `S` ever reachable by a live class? -/

open HalfCylinderIntegerGreedy

/-- Any certification threshold `S` witnessing the second disjunct of
`half_mem_or_eventually_cofRanks_subset` must lie strictly ABOVE the landing row
`D + 1` of every class satisfying the branch hypotheses.  (If it did not, the
three ratchet rows would be certified and `AngleB2` would close the class
outright.) -/
theorem probe_certificationThreshold_gt_landing
    (D S : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2)
    (hS : ∀ s : ℕ, S ≤ s →
      AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s)) :
    D + 1 < S := by
  by_contra hcon
  exact AngleB2.allRight_landingExcess_two_impossible D hD hright hlanding
    (fun s hs1 _ => hS s (by omega))

/-- Consequently the bound produced in the second branch of
`exists_bound_allRight_landingExcess_two_impossible` can never be `≤ D` for a
class `D` that actually satisfies the branch hypotheses: the theorem is
applicable only where its hypotheses are unsatisfiable. -/
theorem probe_bound_never_reaches_live_class
    (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    ¬ ∃ S : ℕ, (∀ s : ℕ, S ≤ s →
        AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s)) ∧ S ≤ D := by
  rintro ⟨S, hS, hSD⟩
  have := probe_certificationThreshold_gt_landing D S hD hright hlanding hS
  omega

/-- And the half-late rows the file's positive branch needs are, on a live
class, bounded: the frozen largest false rank `d` of the landing row makes
row `s` half-late exactly while `s < 2 * d`, so no cofinal supply arises from
this branch. -/
theorem probe_live_class_halfLate_at_landing
    (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    ∃ d : ℕ, IsLargestFalseRank (seamGreedyWord (D + 1)) d ∧ D + 1 < 2 * d ∧ d < D + 1 := by
  obtain ⟨d, hmax, hmargin⟩ :=
    allRight_landingExcess_two_forces_halfSkip_landingRow D hD hright hlanding
  exact ⟨d, hmax, hmargin, hmax.2.1⟩

#print axioms probe_certificationThreshold_gt_landing
#print axioms probe_bound_never_reaches_live_class
#print axioms probe_live_class_halfLate_at_landing

end SkipD1
end Erdos249257
