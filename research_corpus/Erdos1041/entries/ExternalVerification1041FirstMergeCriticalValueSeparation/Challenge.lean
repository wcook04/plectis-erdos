/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #1041 first-merge threshold kernel

The ordinary paper theorem turns critical-value separation into an analytic
continuation disk and a connector-length estimate.  These two checked
endpoints are exactly its formal numerical kernel: the three all-degree
threshold regimes and the final squared-length consumer.  They do not assert
the covering-space, univalence, area, or Pólya inputs.
-/

namespace Erdos249257.ExternalVerification1041FirstMergeCriticalValueSeparation

noncomputable def firstMergeSquaredCoefficient (n : ℕ) (S : ℝ) : ℝ :=
  (1 + S) ^ ((2 : ℝ) / (n : ℝ)) * Real.log (S / (S - 1))

/-- The three exact convenient separation regimes. -/
theorem firstMerge_exact_convenient_thresholds :
    (∀ n : ℕ, 3 ≤ n → firstMergeSquaredCoefficient n 4 < 1) ∧
    (∀ n : ℕ, 4 ≤ n → firstMergeSquaredCoefficient n 3 < 1) ∧
    (∀ n : ℕ, 6 ≤ n → firstMergeSquaredCoefficient n 2 < 1) := by
  sorry

/-- Any connector satisfying the squared analytic estimate is strictly shorter
than two whenever the squared coefficient is below one; no sign hypothesis is
needed. -/
theorem firstMerge_length_lt_two_of_squared_bound
    {n : ℕ} {S length : ℝ}
    (hbound : length ^ 2 ≤ 4 * firstMergeSquaredCoefficient n S)
    (hthreshold : firstMergeSquaredCoefficient n S < 1) :
    length < 2 := by
  sorry

end Erdos249257.ExternalVerification1041FirstMergeCriticalValueSeparation
