-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
import ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactorEstimate

/-! Probe: which single tactic closes the affine form of the pivot angle. -/

open Erdos249257.TotientTailPeriodKiller

namespace FiberMeanAngleProbe

theorem angle_ring {h L m p : ℕ} {θ : ℝ}
    (hθ : θ = Real.pi * ((2 : ℝ) ^ h - 1) * (Nat.totient m : ℝ) / (2 : ℝ) ^ (L - 26)) :
    pivotPrimeAngle h L 26 m p = θ * p - θ := by
  rw [pivotPrimeAngle, hθ]
  ring

theorem angle_field_simp {h L m p : ℕ} {θ : ℝ}
    (hθ : θ = Real.pi * ((2 : ℝ) ^ h - 1) * (Nat.totient m : ℝ) / (2 : ℝ) ^ (L - 26)) :
    pivotPrimeAngle h L 26 m p = θ * p - θ := by
  rw [pivotPrimeAngle, hθ]
  field_simp

theorem angle_field_simp_ring {h L m p : ℕ} {θ : ℝ}
    (hθ : θ = Real.pi * ((2 : ℝ) ^ h - 1) * (Nat.totient m : ℝ) / (2 : ℝ) ^ (L - 26)) :
    pivotPrimeAngle h L 26 m p = θ * p - θ := by
  rw [pivotPrimeAngle, hθ]
  field_simp
  ring

end FiberMeanAngleProbe
