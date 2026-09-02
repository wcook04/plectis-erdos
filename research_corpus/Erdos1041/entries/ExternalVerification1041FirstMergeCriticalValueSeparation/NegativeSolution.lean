/- Deliberate mismatch: the exact-threshold endpoint is omitted. -/
import Mathlib

namespace Erdos249257.ExternalVerification1041FirstMergeCriticalValueSeparation

noncomputable def firstMergeSquaredCoefficient (n : ℕ) (S : ℝ) : ℝ :=
  (1 + S) ^ ((2 : ℝ) / (n : ℝ)) * Real.log (S / (S - 1))

theorem firstMerge_length_lt_two_of_squared_bound
    {n : ℕ} {S length : ℝ}
    (hbound : length ^ 2 ≤ 4 * firstMergeSquaredCoefficient n S)
    (hthreshold : firstMergeSquaredCoefficient n S < 1) :
    length < 2 := by
  have hsq : length ^ 2 < 4 := lt_of_le_of_lt hbound (by nlinarith)
  nlinarith [sq_nonneg (length - 2)]

end Erdos249257.ExternalVerification1041FirstMergeCriticalValueSeparation
