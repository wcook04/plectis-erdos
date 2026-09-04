import Mathlib
import ErdosProblems.Erdos68.AdjacentUnitCarryWindow

namespace Erdos249257.ExternalVerification68AdjacentUnitCarryWindow

def strictFacTopRat (x : ℚ) (n : ℕ) : ℤ := ⌊(n.factorial : ℚ) * x⌋ + 1
def factorialGapPrefix (n : ℕ) : ℚ := ∑ k ∈ Finset.Icc 2 n, 1 / ((k.factorial : ℚ) - 1)
def predecessorScaled (m : ℕ) : ℚ := ((m - 1).factorial : ℚ) * factorialGapPrefix (m - 1)
def predecessorNumerator (m : ℕ) : ℤ := let q := predecessorScaled m; (⌊q⌋ + 1) * q.den - q.num
def transitionNormalizer (m : ℕ) : ℕ := (predecessorScaled m).den * (m.factorial - 1) / (predecessorScaled (m + 1)).den
noncomputable def predecessorGap (m : ℕ) : ℝ := (strictFacTopRat (factorialGapPrefix (m - 1)) (m - 1) : ℝ) - ((m - 1).factorial : ℝ) * (factorialGapPrefix (m - 1) : ℝ)
noncomputable def stepCarry (m : ℕ) : ℤ := -⌊1 + 1 / ((m.factorial : ℝ) - 1) - (m : ℝ) * predecessorGap m⌋
def windowDen (m : ℕ) : ℤ := ((predecessorScaled m).den : ℤ) * ((m.factorial : ℤ) - 1) * (((m + 1).factorial : ℤ) - 1)
def windowLower (m : ℕ) : ℤ := (m + 2 : ℤ) * windowDen m + (m + 1 : ℤ) * ((predecessorScaled m).den : ℤ) * (((m + 1).factorial : ℤ) - 1) + ((predecessorScaled m).den : ℤ) * ((m.factorial : ℤ) - 1)
def windowState (m : ℕ) : ℤ := (m : ℤ) * (m + 1 : ℤ) * predecessorNumerator m * ((m.factorial : ℤ) - 1) * (((m + 1).factorial : ℤ) - 1)
def windowOffset (m : ℕ) : ℤ := windowState m - windowLower m

private macro "source_simpa" t:term : tactic => `(tactic| simpa [strictFacTopRat, factorialGapPrefix, predecessorScaled, predecessorNumerator, transitionNormalizer, predecessorGap, stepCarry, windowDen, windowLower, windowState, windowOffset, ErdosProblems.Erdos68.strictFacTopRat, ErdosProblems.Erdos68.factorialGapPrefix, ErdosProblems.Erdos68.factorialGapPredecessorScaledRat, ErdosProblems.Erdos68.factorialGapPredecessorGapNumerator, ErdosProblems.Erdos68.factorialGapPredecessorTransitionNormalizer, ErdosProblems.Erdos68.factorialGapPredecessorGap, ErdosProblems.Erdos68.factorialGapStepCarry, ErdosProblems.Erdos68.adjacentUnitCarryWindowDen, ErdosProblems.Erdos68.adjacentUnitCarryWindowLowerNum, ErdosProblems.Erdos68.adjacentUnitCarryWindowStateNum, ErdosProblems.Erdos68.adjacentUnitCarryWindowOffset] using $t)

theorem consecutive_unit_carries_iff_positive_offset_le_den {m : ℕ} (hm : 3 ≤ m) : (stepCarry m = 1 ∧ stepCarry (m + 1) = 1) ↔ 0 < windowOffset m ∧ windowOffset m ≤ windowDen m := by source_simpa (ErdosProblems.Erdos68.consecutive_unit_carries_iff_positive_offset_le_den hm)
theorem twoStep_den_mul_transitionNormalizers {m : ℕ} (hm : 3 ≤ m) : (predecessorScaled (m + 2)).den * transitionNormalizer (m + 1) * transitionNormalizer m = (predecessorScaled m).den * (m.factorial - 1) * ((m + 1).factorial - 1) := by source_simpa (ErdosProblems.Erdos68.twoStep_den_mul_transitionNormalizers hm)
theorem adjacentUnitCarryWindowDen_eq_twoStep_den {m : ℕ} (hm : 3 ≤ m) : windowDen m = ((predecessorScaled (m + 2)).den : ℤ) * transitionNormalizer (m + 1) * transitionNormalizer m := by source_simpa (ErdosProblems.Erdos68.adjacentUnitCarryWindowDen_eq_twoStep_den hm)
theorem adjacentUnitCarryWindowOffset_eq_twoStep_factorization {m : ℕ} (hm : 3 ≤ m) : windowOffset m = predecessorNumerator (m + 2) * transitionNormalizer (m + 1) * transitionNormalizer m + windowDen m * (((m + 1 : ℕ) : ℤ) * stepCarry m + stepCarry (m + 1) - (m + 2 : ℤ)) := by source_simpa (ErdosProblems.Erdos68.adjacentUnitCarryWindowOffset_eq_twoStep_factorization hm)

end Erdos249257.ExternalVerification68AdjacentUnitCarryWindow
