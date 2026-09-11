import Erdos249257.HalfCylinderSeamLimit

/-!
# Skipped-rank compactness route for the half-cylinder seam

A skipped coordinate in the descending integer-greedy seam word bounds the
final row remainder by that coordinate's truncated Mersenne weight.  This
module records the recursive greedy fact and connects it to the cofinal
subquadratic seam-limit consumer.
-/

namespace Erdos249257

open Set Filter
open HalfCylinderIntegerGreedy

/-! ## A recursive descending-greedy bound -/

/-- If descending integer greedy skips the weight at index `i`, its final
remainder is strictly smaller than that weight. -/
theorem integerGreedyRemainder_lt_of_get?_eq_false
    {weights : List ℕ} {C i w : ℕ}
    (hweight : weights[i]? = some w)
    (hskip : (integerGreedyBits weights C)[i]? = some false) :
    integerGreedyRemainder weights C < w := by
  induction weights generalizing C i w with
  | nil => simp at hweight
  | cons head tail ih =>
      cases i with
      | zero =>
          simp at hweight
          subst w
          by_cases htake : head ≤ C
          · simp [integerGreedyBits, htake] at hskip
          · have htail : integerGreedyRemainder tail C ≤ C :=
              Nat.sub_le _ _
            have hClt : C < head := Nat.lt_of_not_ge htake
            simpa [integerGreedyRemainder, integerGreedyBits, htake,
              weightedBoolSum] using htail.trans_lt hClt
      | succ i =>
          simp only [List.getElem?_cons_succ] at hweight
          by_cases htake : head ≤ C
          · have htailSkip :
                (integerGreedyBits tail (C - head))[i]? = some false := by
              simpa [integerGreedyBits, htake] using hskip
            have hlt := ih (C := C - head) hweight htailSkip
            simpa [integerGreedyRemainder, integerGreedyBits, htake,
              weightedBoolSum, Nat.sub_add_eq] using hlt
          · have htailSkip :
                (integerGreedyBits tail C)[i]? = some false := by
              simpa [integerGreedyBits, htake] using hskip
            have hlt := ih (C := C) hweight htailSkip
            simpa [integerGreedyRemainder, integerGreedyBits, htake,
              weightedBoolSum] using hlt

/-- A false coordinate of the concrete seam-greedy word bounds the exact
integer seam remainder by its own truncated weight. -/
theorem seamIntegerGreedyRemainder_lt_truncatedWeight_of_false
    {s : ℕ} (i : Fin (s - 2))
    (hskip : seamGreedyWord s i = false) :
    seamIntegerGreedyRemainder s <
      truncatedMersenneWeight s ((i : ℕ) + 2) := by
  have hi : (i : ℕ) < s - 2 := i.isLt
  have hs : 2 ≤ s := by omega
  have hweight :
      (seamWeights s)[(i : ℕ)]? =
        some (truncatedMersenneWeight s ((i : ℕ) + 2)) := by
    rw [seamWeights_eq_ofFn hs]
    simp
  have hword :
      (integerGreedyBits (seamWeights s) (seamSubsetTarget s))[(i : ℕ)]? =
          some false := by
    rw [← seamGreedyWord_toList s]
    unfold SeamRowWord.toList
    simp [hskip]
  exact integerGreedyRemainder_lt_of_get?_eq_false hweight hword

/-- After normalization by `4^s`, a skipped seam coordinate bounds the row
remainder by the corresponding Mersenne weight. -/
theorem seamGreedyNormalizedRemainder_lt_mersenneWeight_of_false
    {s : ℕ} (i : Fin (s - 2))
    (hskip : seamGreedyWord s i = false) :
    seamGreedyNormalizedRemainder s < mersenneWeight ((i : ℕ) + 2) := by
  have hrem :=
    seamIntegerGreedyRemainder_lt_truncatedWeight_of_false i hskip
  have hcast :
      (seamIntegerGreedyRemainder s : ℝ) <
        (truncatedMersenneWeight s ((i : ℕ) + 2) : ℝ) := by
    exact_mod_cast hrem
  have hweight := truncatedMersenneWeight_cast_le_scaled
    (s := s) (d := (i : ℕ) + 2) (by omega : 1 ≤ (i : ℕ) + 2)
  rw [seamGreedyNormalizedRemainder]
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (4 : ℝ) ^ s)).2
  simpa [mul_comm] using hcast.trans_le hweight

/-! ## Unbounded skipped ranks force the half limit -/

/-- The Mersenne weights tend to zero along increasing ranks. -/
theorem tendsto_mersenneWeight_atTop_zero :
    Tendsto mersenneWeight atTop (nhds 0) := by
  have hpow : Tendsto (fun d : ℕ => (2 : ℝ) ^ d) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hden : Tendsto (fun d : ℕ => (2 : ℝ) ^ d - 1) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [hpow (eventually_ge_atTop (b + 1))] with d hd
    change b + 1 ≤ (2 : ℝ) ^ d at hd
    linarith
  unfold mersenneWeight
  simpa only [one_div, Function.comp_apply] using
    tendsto_inv_atTop_zero.comp hden

/-- Along cofinal rows, choose one skipped seam coordinate per row whose
rank itself tends to infinity. -/
def SeamGreedyUnboundedSkippedRanksAlong (rows : ℕ → ℕ) : Prop :=
  ∃ skip : ∀ j, Fin (rows j - 2),
    Tendsto rows atTop atTop ∧
      Tendsto (fun j => ((skip j : ℕ) + 2)) atTop atTop ∧
        ∀ j, seamGreedyWord (rows j) (skip j) = false

/-- Unbounded skipped seam ranks make the normalized integer remainder
vanish along the chosen cofinal rows. -/
theorem seamGreedyRemainderSubquadraticAlong_of_unboundedSkippedRanks
    (rows : ℕ → ℕ)
    (hskips : SeamGreedyUnboundedSkippedRanksAlong rows) :
    SeamGreedyRemainderSubquadraticAlong rows := by
  rcases hskips with ⟨skip, hrows, hranks, hskip⟩
  refine ⟨hrows, ?_⟩
  have hupper : Tendsto
      (fun j => mersenneWeight ((skip j : ℕ) + 2)) atTop (nhds 0) :=
    tendsto_mersenneWeight_atTop_zero.comp hranks
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun j => by
      exact div_nonneg (by positivity) (by positivity)
  · exact Filter.Eventually.of_forall fun j =>
      (seamGreedyNormalizedRemainder_lt_mersenneWeight_of_false
        (skip j) (hskip j)).le
  · exact hupper

/-- Cofinal unbounded skipped seam ranks therefore give an exact
representation of `1/2` in the Mersenne achievement set. -/
theorem half_mem_mersenneAchievementSet_of_unboundedSkippedRanks
    (rows : ℕ → ℕ)
    (hskips : SeamGreedyUnboundedSkippedRanksAlong rows) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  exact half_mem_mersenneAchievementSet_of_subquadraticAlong rows
    (seamGreedyRemainderSubquadraticAlong_of_unboundedSkippedRanks rows hskips)

#print axioms integerGreedyRemainder_lt_of_get?_eq_false
#print axioms seamIntegerGreedyRemainder_lt_truncatedWeight_of_false
#print axioms seamGreedyNormalizedRemainder_lt_mersenneWeight_of_false
#print axioms tendsto_mersenneWeight_atTop_zero
#print axioms seamGreedyRemainderSubquadraticAlong_of_unboundedSkippedRanks
#print axioms half_mem_mersenneAchievementSet_of_unboundedSkippedRanks

end Erdos249257
