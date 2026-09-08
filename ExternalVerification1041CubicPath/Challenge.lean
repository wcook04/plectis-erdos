/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

namespace Erdos249257.ExternalVerification1041CubicPath

noncomputable section
open Polynomial Set
open scoped BigOperators

/-- The two-segment path with endpoints at times zero and two. -/
def hub (a c b : ℂ) (t : ℝ) : ℂ :=
  c + ((max (1 - t) 0 : ℝ) : ℂ) * (a - c) +
    ((max (t - 1) 0 : ℝ) : ℂ) * (b - c)

theorem cubic_paper_complete (p : ℂ[X]) (z : Fin 3 → ℂ)
    (hp : p = ∏ i, (X - C (z i))) (hz : ∀ i, ‖z i‖ < 1) :
    ∃ i j : Fin 3, ∃ c : ℂ, i ≠ j ∧
      Continuous (hub (z i) c (z j)) ∧
      BoundedVariationOn (hub (z i) c (z j)) (Icc (0 : ℝ) 2) ∧
      ((∀ t ∈ Icc (0 : ℝ) 2, ‖p.eval (hub (z i) c (z j) t)‖ < 1) ∧
        eVariationOn (hub (z i) c (z j)) (Icc (0 : ℝ) 2) < ENNReal.ofReal 2) ∧
      (∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧
        γ 0 = z i ∧ γ 2 = z j ∧
        (∀ t ∈ Icc (0 : ℝ) 2, ‖p.eval (γ t)‖ < 1) ∧
        BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
        eVariationOn γ (Icc (0 : ℝ) 2) < ENNReal.ofReal 2) ∧
      (Squarefree p → z i ≠ z j) := by
  sorry

end

end Erdos249257.ExternalVerification1041CubicPath
