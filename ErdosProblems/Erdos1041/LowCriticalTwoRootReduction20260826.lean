import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Scalar kernel for the deep-low-critical two-spoke theorem

The ordinary complex-polynomial proof is in
`LowCriticalTwoRootReduction20260826.md`.  This module checks the load-bearing
uniform scalar estimate for the second-nearest spoke.
-/

namespace ErdosProblems.Erdos1041.LowCriticalTwoRootReduction20260826

/-- The crude but uniform envelope used for the second-nearest critical spoke. -/
theorem secondNearest_segment_envelope
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * (1 + ((n : ℝ) - 1) * t) * (1 + t) ^ (n - 2) ≤
      (n : ℝ) * 2 ^ (n - 2) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hfirst0 : 0 ≤ 1 - t := by linarith
  have hfirst1 : 1 - t ≤ 1 := by linarith
  have hcoef0 : 0 ≤ (n : ℝ) - 1 := by linarith
  have hscaled : ((n : ℝ) - 1) * t ≤ ((n : ℝ) - 1) * 1 :=
    mul_le_mul_of_nonneg_left ht1 hcoef0
  have hsecond0 : 0 ≤ 1 + ((n : ℝ) - 1) * t := by positivity
  have hsecond : 1 + ((n : ℝ) - 1) * t ≤ n := by linarith
  have hbase0 : 0 ≤ 1 + t := by linarith
  have hbase : 1 + t ≤ 2 := by linarith
  have hpow : (1 + t) ^ (n - 2) ≤ (2 : ℝ) ^ (n - 2) :=
    pow_le_pow_left₀ hbase0 hbase (n - 2)
  calc
    (1 - t) * (1 + ((n : ℝ) - 1) * t) * (1 + t) ^ (n - 2)
        ≤ 1 * (n : ℝ) * 2 ^ (n - 2) := by gcongr
    _ = (n : ℝ) * 2 ^ (n - 2) := by ring

/-- For `n ≥ 2`, the nearest-spoke crude envelope is no larger than the common
two-spoke budget. -/
theorem nearest_segment_envelope_le_common_budget
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * (1 + t) ^ (n - 1) ≤ (n : ℝ) * 2 ^ (n - 2) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hfirst0 : 0 ≤ 1 - t := by linarith
  have hfirst1 : 1 - t ≤ 1 := by linarith
  have hbase0 : 0 ≤ 1 + t := by linarith
  have hbase : 1 + t ≤ 2 := by linarith
  have hpow : (1 + t) ^ (n - 1) ≤ (2 : ℝ) ^ (n - 1) :=
    pow_le_pow_left₀ hbase0 hbase (n - 1)
  have htwo : (2 : ℝ) ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
    ring
  calc
    (1 - t) * (1 + t) ^ (n - 1) ≤ 1 * 2 ^ (n - 1) := by gcongr
    _ = 2 * 2 ^ (n - 2) := by rw [htwo]; ring
    _ ≤ (n : ℝ) * 2 ^ (n - 2) := by gcongr

end ErdosProblems.Erdos1041.LowCriticalTwoRootReduction20260826
