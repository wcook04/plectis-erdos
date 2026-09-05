/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos1041.FirstMergeCriticalValueSeparation

namespace Erdos249257.ExternalVerification1041FirstMergeCriticalValueSeparation

noncomputable def firstMergeSquaredCoefficient (n : ℕ) (S : ℝ) : ℝ :=
  (1 + S) ^ ((2 : ℝ) / (n : ℝ)) * Real.log (S / (S - 1))

theorem firstMerge_exact_convenient_thresholds :
    (∀ n : ℕ, 3 ≤ n → firstMergeSquaredCoefficient n 4 < 1) ∧
    (∀ n : ℕ, 4 ≤ n → firstMergeSquaredCoefficient n 3 < 1) ∧
    (∀ n : ℕ, 6 ≤ n → firstMergeSquaredCoefficient n 2 < 1) := by
  simpa [firstMergeSquaredCoefficient,
    ErdosProblems.Erdos1041.firstMergeSquaredCoefficient] using
    ErdosProblems.Erdos1041.firstMerge_exact_convenient_thresholds

theorem firstMerge_length_lt_two_of_squared_bound
    {n : ℕ} {S length : ℝ}
    (hbound : length ^ 2 ≤ 4 * firstMergeSquaredCoefficient n S)
    (hthreshold : firstMergeSquaredCoefficient n S < 1) :
    length < 2 := by
  apply ErdosProblems.Erdos1041.firstMerge_length_lt_two_of_squared_bound
  · simpa [firstMergeSquaredCoefficient,
      ErdosProblems.Erdos1041.firstMergeSquaredCoefficient] using hbound
  · simpa [firstMergeSquaredCoefficient,
      ErdosProblems.Erdos1041.firstMergeSquaredCoefficient] using hthreshold

end Erdos249257.ExternalVerification1041FirstMergeCriticalValueSeparation
