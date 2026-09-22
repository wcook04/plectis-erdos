import Erdos249257.TerminalOnlyScaledVanishing

namespace ErdosProblems.Erdos257.PaperCompleteR20
open Erdos249257 Erdos249257.HalfCarryReachability

/-- At every positive square depth the analytic tail bound is exactly the
integer strip, with constant four and no rounding slack. -/
theorem square_depth_witness (A : Set ℕ) (hone : 1 ∉ A)
    (hhalf : erdosSupportSeries 2 A = (1 : ℝ) / 2)
    (k : ℕ) (hk : 1 ≤ k) :
    (integerHalfCarry A (k^2-1) : ℝ) = binaryCoeffTail (supportCoeff A) (k^2) ∧
    binaryCoeffTail (supportCoeff A) (k^2) ≤ 2*(k : ℝ)+4 ∧
    (halfStripBound (k^2) : ℝ) = 2*(k : ℝ)+4 := by
  have hpos : 1 ≤ k^2 := by nlinarith
  have hi : k^2-1+1 = k^2 := Nat.sub_add_cancel hpos
  have hs : Real.sqrt ((k^2 : ℕ) : ℝ) = (k : ℝ) := by
    push_cast
    rw [Real.sqrt_sq (by positivity)]
  refine ⟨?_, ?_, ?_⟩
  · rw [integerHalfCarry_eq_scaled_residual_add_tail A hone, hhalf, sub_self,
      mul_zero, zero_add, hi]
  · have ht := binaryCoeffTail_supportCoeff_le_two_sqrt_add_four A (k^2)
    convert ht using 1 <;> norm_num [Nat.cast_pow, Real.sqrt_sq_eq_abs]
  · simp [halfStripBound, Nat.sqrt_eq']

/-- An achieving support has cofinally many carries inside the original
integer strip; this does not assert achievement for an arbitrary support. -/
theorem achieving_support_cofinal_strip (A : Set ℕ) (hone : 1 ∉ A)
    (hhalf : erdosSupportSeries 2 A = (1 : ℝ)/2) :
    ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
      (integerHalfCarry A N : ℝ) ≤ (halfStripBound (N+1) : ℝ) := by
  intro K
  let k := K+1
  have hk : 1 ≤ k := by omega
  have hpos : 1 ≤ k^2 := by nlinarith
  refine ⟨k^2-1, ?_, ?_⟩
  · have hbig : K+1 ≤ k^2 := by dsimp [k]; nlinarith
    omega
  · have h := square_depth_witness A hone hhalf k hk
    rw [Nat.sub_add_cancel hpos, h.1, h.2.2]
    exact h.2.1

#print axioms square_depth_witness
#print axioms achieving_support_cofinal_strip
end ErdosProblems.Erdos257.PaperCompleteR20
