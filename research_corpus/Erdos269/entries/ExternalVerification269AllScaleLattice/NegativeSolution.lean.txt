/- Deliberate mismatch: weakens the positive-denominator hypothesis to a
nonnegative one in the collision theorem. -/
import Mathlib

namespace Erdos249257.ExternalVerification269AllScaleLattice

noncomputable def dyadicShellTsumTailR235 (_a : ℕ) : ℝ := 0
noncomputable def dyadicNormalizedTailStateR235
    (_tail : ℕ → ℝ) (_a : ℕ) : ℝ := 0

theorem exists_normalizedTailState_collision_of_value_eq_rat
    {p q : ℤ} (hq : 0 ≤ q)
    (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ)) :
    ∃ i j : ℕ, i < j ∧ ∃ z : ℤ,
      dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (1 + j) -
        dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (1 + i) =
          (z : ℝ) := by
  sorry

end Erdos249257.ExternalVerification269AllScaleLattice
