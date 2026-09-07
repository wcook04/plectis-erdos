/- Deliberate mismatch: substitutes the factorial diagonal for the LCM diagonal. -/
import Mathlib

namespace Erdos249257.ExternalVerification251LcmDiagonalCriterion

def RealDyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℝ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)

def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ :=
  T (N + h) - T N

def RealIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z

theorem irrationalInitial_iff_allLcmDiagonal_nonintegral
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔
      ∀ j : ℕ,
        ¬ RealIntegral (realTailShift T j.factorial j.factorial) := by
  sorry

end Erdos249257.ExternalVerification251LcmDiagonalCriterion
