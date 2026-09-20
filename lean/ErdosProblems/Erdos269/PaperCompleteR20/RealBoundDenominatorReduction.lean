import ErdosProblems.Erdos269.RestrictedFloorSum
import Mathlib.Data.Real.Basic

/-!
# Denominator reduction with the literal real upper bound

The paper quantifies the upper-bound parameter over all reals and asserts an
equivalence. Positive common-factor cancellation preserves both directions;
no integrality of that parameter or bound function is needed.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR20

theorem positive_real_bound_commonFactor_iff
    {c d s B : ℤ} (hs : 0 < s) (hfactor : c = s * d) (t : ℝ) :
    (0 < c ∧ (c : ℝ) ≤ ((s * B : ℤ) : ℝ) * t) ↔
      (0 < d ∧ (d : ℝ) ≤ (B : ℝ) * t) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  rw [hfactor]
  push_cast
  rw [mul_pos_iff_of_pos_left hs, mul_assoc, mul_le_mul_iff_right₀ hsR]

/-- Complete conditional denominator reduction: recurrence, every window,
and the positive upper-bound equivalence for every real parameter. -/
theorem conditional_denominator_reduction_real_bound
    (c d b m : ℕ → ℤ) (s B : ℤ) (hs : 0 < s)
    (hfactor : ∀ n, c n = s * d n)
    (hrec : ∀ n, c (n + 1) = b n * c n - (s * B) * m n) :
    (∀ n, d (n + 1) = b n * d n - B * m n) ∧
    (∀ lo len, d (lo + len) = windowBase b lo len * d lo -
      B * windowForcing b m lo len) ∧
    (∀ n (t : ℝ),
      (0 < c n ∧ (c n : ℝ) ≤ ((s * B : ℤ) : ℝ) * t) ↔
        (0 < d n ∧ (d n : ℝ) ≤ (B : ℝ) * t)) :=
  ⟨integralCarry_cancel_commonFactor c d b m s B hs.ne' hfactor hrec,
    reducedIntegralCarry_window c d b m s B hs.ne' hfactor hrec,
    fun n t => positive_real_bound_commonFactor_iff hs (hfactor n) t⟩

#print axioms conditional_denominator_reduction_real_bound

end ErdosProblems.Erdos269.PaperCompleteR20
