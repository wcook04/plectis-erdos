import ErdosProblems.Skip.D4
import ErdosProblems.Skip.D1

/-! Adversarial verification scratch file for `ErdosProblems/Skip/D4.lean`. -/

namespace Erdos249257
namespace SkipD4

open HalfCylinderIntegerGreedy

-- axioms of every theorem in D4
#print axioms cofactorFive_not_late
#print axioms cofactorFive_even_not_late
#print axioms cofactorSeven_not_late
#print axioms cofactorSeven_even_not_late
#print axioms cofactorFive_lt_cofactorFour
#print axioms cofactorSeven_lt_cofactorFive
#print axioms cofactor_ge_four_not_late
#print axioms cofRanks_two_mul_ge
#print axioms exists_skipped_bit_of_not_subset
#print axioms half_mem_of_cofinal_cofSkip
#print axioms half_mem_or_eventually_cofRanks_subset
#print axioms half_mem_or_allRight_landingExcess_two_impossible
#print axioms half_mem_or_finalMiddleCell_neg_two_impossible
#print axioms cof3Rank_lower
#print axioms cof5Rank_lower
#print axioms cof35Ranks_ge
#print axioms cof35Ranks_lt
#print axioms cof35Ranks_three_mul_ge
#print axioms cof35Floor_le_pulse
#print axioms totalFloor35_le_belowPulse
#print axioms cof35Ratchet_finite_core
#print axioms cof35Ratchet_run_eq_zero
#print axioms cof35Run_bound
#print axioms cof35_allRight_landingExcess_two_impossible
#print axioms exists_skipped_bit_of_not_cof35_subset
#print axioms cof35_half_mem_of_cofinal_skip
#print axioms cof35_half_mem_or_eventually_subset
#print axioms cof35_half_mem_or_allRight_impossible

-- full elaborated statements
#check @half_mem_or_eventually_cofRanks_subset
#check @half_mem_or_allRight_landingExcess_two_impossible
#check @cof35_half_mem_or_allRight_impossible
#check @cof35_allRight_landingExcess_two_impossible

/-! ### Test 1: D4's headline dichotomy is a verbatim duplicate of D1's.
If the statements were not literally the same term, this would fail. -/
example :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ∨
      ∃ S : ℕ, ∀ s : ℕ, S ≤ s →
        AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s) :=
  SkipD1.half_mem_or_eventually_cofRanks_subset

/-! ### Test 2: D4's "all-right-tail branch resolved" theorem is strictly
weaker than `SkipD1.exists_bound_allRight_landingExcess_two_impossible`,
which was already proved without any disjunction.  The left disjunct is
pure padding: it follows by `Or.inr` from the existing result. -/
example :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ∨
      ∃ S : ℕ, 60 ≤ S ∧ ∀ D : ℕ, S ≤ D →
        (∀ s : ℕ, D + 1 ≤ s →
          seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) →
        Recon257.seamExcess (D + 1) = 2 → False :=
  Or.inr SkipD1.exists_bound_allRight_landingExcess_two_impossible

/-! ### Test 3: the disjunction in D4's headline collapses outright.  The
hypothesis `hright` of the right disjunct *is* `SeamGreedyEventuallyRight`,
which the corpus already knows is equivalent to `1/2 ∉ mersenneAchievementSet`.
So the left disjunct can be eliminated from D4's own theorem with no extra
input: D4's statement is equivalent to its right disjunct alone. -/
theorem D4_disjunction_collapses :
    ∃ S : ℕ, 60 ≤ S ∧ ∀ D : ℕ, S ≤ D →
      (∀ s : ℕ, D + 1 ≤ s →
        seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) →
      Recon257.seamExcess (D + 1) = 2 → False := by
  rcases half_mem_or_allRight_landingExcess_two_impossible with hmem | h
  · exact ⟨60, le_rfl, fun D hD hright _ =>
      (seamGreedyEventuallyRight_iff_half_not_mem.mp ⟨D + 1, by omega, hright⟩) hmem⟩
  · exact h

#print axioms D4_disjunction_collapses

/-! ### Test 4: same collapse for the `{3,5}` version. -/
theorem cof35_disjunction_collapses :
    ∃ S : ℕ, 70 ≤ S ∧ ∀ D : ℕ, S ≤ D →
      (∀ s : ℕ, D + 1 ≤ s →
        seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) →
      Recon257.seamExcess (D + 1) = 2 → False := by
  rcases cof35_half_mem_or_allRight_impossible with hmem | h
  · exact ⟨70, le_rfl, fun D hD hright _ =>
      (seamGreedyEventuallyRight_iff_half_not_mem.mp ⟨D + 1, by omega, hright⟩) hmem⟩
  · exact h

#print axioms cof35_disjunction_collapses

/-! ### Test 5: is the "sharp negative" new?  D1 already proves the stronger
uniform statement that no cofactor `≥ 5` rank even reaches `s/2`, which
implies D4's `3 * ((2s+1)/c) ≤ 2s` for `c ≥ 5` and much more. -/
example (s d c : ℕ) (hs : 4 ≤ s) (hc : 5 ≤ c)
    (h : c * d = 2 * s + 1 ∨ c * d = 2 * s + 2) : 2 * d ≤ s :=
  SkipD1.cofactor_ge_five_not_half hs hc h

/-! ### Test 6: non-vacuity probe for the right disjunct.  Can the
hypotheses of the inner implication be satisfied at all?  Record the
statement of the predicate that `hright` unfolds to. -/
#print Erdos249257.SeamGreedyEventuallyRight
#check @Erdos249257.seamGreedyEventuallyRight_iff_half_not_mem

end SkipD4
end Erdos249257
