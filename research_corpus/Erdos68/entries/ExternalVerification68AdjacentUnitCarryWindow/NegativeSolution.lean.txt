import Mathlib
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
theorem consecutive_unit_carries_iff_positive_offset_le_den (_extra : True) {m : ℕ} (hm : 3 ≤ m) :
    (stepCarry m = 1 ∧ stepCarry (m + 1) = 1) ↔ 0 < windowOffset m ∧ windowOffset m ≤ windowDen m := by sorry
end Erdos249257.ExternalVerification68AdjacentUnitCarryWindow
