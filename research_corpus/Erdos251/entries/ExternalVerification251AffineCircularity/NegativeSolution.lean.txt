/- Deliberate mismatch: the signed normal form omits its negative branch. -/
import Mathlib

namespace Erdos249257.ExternalVerification251AffineCircularity

def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)

def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ := T (N + h) - T N

theorem adjacent_small_mismatch_iff_signed_two_window
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (h N : ℕ)
    (heven : ∃ k : ℤ, g (N + h + 1) - g (N + 1) = 2 * k) :
    (-1 < tailShift T h N ∧ tailShift T h N < 1 ∧
        -1 < tailShift T h (N + 1) ∧ tailShift T h (N + 1) < 1 ∧
        g (N + h + 1) ≠ g (N + 1)) ↔
      (g (N + h + 1) - g (N + 1) = 2 ∧
        1 / 2 < tailShift T h N ∧ tailShift T h N < 1) := by
  sorry

end Erdos249257.ExternalVerification251AffineCircularity
