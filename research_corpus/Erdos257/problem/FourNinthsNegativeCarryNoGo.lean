import ErdosProblems.Erdos257.FourNinthsSkippedTwoAdicAntiConcentration

/-!
# Exact local no-go for four-ninths adaptive suffix divisibility

The adaptive suffix certificates are necessary reachability constraints, but divisibility
and the pointwise digit bounds alone do not contradict a long carry.  This companion records
the smallest exact countermodel, keeping the producer module itself focused on the actual
executable diagonal.
-/

namespace ErdosProblems.Erdos257

namespace FourNinthsNegativeCarryNoGo

open Erdos257PeriodNoncollapse
open FourNinthsUpperSaturation

/-- Put `-4` in the newest base-four digit and `-3` in every older digit.  The
length-`k+1` suffix is exactly `-4^(k+1)`, so arbitrarily deep adaptive divisibility is
compatible with the source-current upper digit bound.  A successful exclusion must use
reachability or selected-divisor ancestry rather than only these local constraints. -/
theorem constantNegativeCarrySuffix_eq (k : ℕ) :
    (∑ t ∈ Finset.range (k + 1),
      (4 : ℤ) ^ t * if t = 0 then -4 else -3) =
        -(4 : ℤ) ^ (k + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Nat.succ_ne_zero, ↓reduceIte, pow_succ]
      ring

/-- The two reachability-sensitive producer lanes are jointly exhaustive for this concrete
counterexample route: failure of `4/9` membership forces failure of the selected-landing
rank producer or failure of skipped full-rank two-adic avoidance. -/
theorem four_ninths_not_mem_forces_rankFailure_or_twoAdicFailure
    (hnot : (4 / 9 : ℝ) ∉ mersenneAchievementSet) :
    ¬ FourNinthsSelectedLandingRankProducer ∨
      ¬ FourNinthsSkippedRemainderTwoAdicAvoidance := by
  by_contra h
  push Not at h
  exact hnot
    (four_ninths_mem_mersenneAchievementSet_of_rankProducer_of_twoAdicAvoidance
      h.1 h.2)

/-- Expanded source-current obstruction fork.  Nonmembership forces either an actual
selected transition in the accumulated-history rank window, or an actual skipped row whose
remainder has the full dyadic divisibility required by saturation. -/
theorem four_ninths_not_mem_forces_historyBadWindow_or_skippedDivisibility
    (hnot : (4 / 9 : ℝ) ∉ mersenneAchievementSet) :
    (∃ d : ℕ, FourNinthsDiagonalTakesAt d ∧
      4 * fourNinthsWeightedHistory fourNinthsDiagonalHistoryIncrement d +
          (fourNinthsPairPulse (d + 1) : ℤ) -
          (fourNinthsDiagonalLoad
            (fourNinthsDiagonalState d) (d + 1) : ℤ) <
        (((2 ^ (d + 1) + 1 : ℕ) : ℤ) + ((d + 1 : ℕ) : ℤ))) ∨
      (∃ d : ℕ, ¬ FourNinthsDiagonalTakesAt d ∧
        (2 : ℤ) ^ (d + 1) ∣ (fourNinthsDiagonalState (d + 1)).rho) := by
  rcases four_ninths_not_mem_forces_rankFailure_or_twoAdicFailure hnot with
    hrank | htwoAdic
  · exact Or.inl
      (fourNinths_not_selectedLandingRankProducer_iff_exists_historyBadWindow.mp
        hrank)
  · right
    unfold FourNinthsSkippedRemainderTwoAdicAvoidance at htwoAdic
    push Not at htwoAdic
    exact htwoAdic

#print axioms constantNegativeCarrySuffix_eq
#print axioms four_ninths_not_mem_forces_rankFailure_or_twoAdicFailure
#print axioms four_ninths_not_mem_forces_historyBadWindow_or_skippedDivisibility

end FourNinthsNegativeCarryNoGo

end ErdosProblems.Erdos257
