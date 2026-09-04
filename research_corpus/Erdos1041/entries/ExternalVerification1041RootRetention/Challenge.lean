/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the #1041 root-retention boundary

The Challenge contains only the literal theorem type.  It does not import
the project-local source module or expose its namespace vocabulary.
-/

namespace Erdos249257.ExternalVerification1041RootRetention

/-- A strict quantitative margin keeps every root of a constant perturbation
inside the open unit disk. -/
theorem constant_perturbation_roots_in_unitDisk
    (f : ℂ[X]) (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hsplit : f.Splits) {ρ ε : ℝ} (hρ : 0 ≤ ρ)
    (hroots : ∀ b ∈ f.roots, ‖b‖ ≤ ρ)
    (hε : 0 < ε)
    (hmargin :
      ((f.natDegree + 1) * ε) ^ (f.natDegree : ℝ)⁻¹ + ρ < 1)
    {shift : ℂ} (hshift : ‖shift‖ < ε) :
    ∀ a : ℂ, (f + C shift).eval a = 0 → ‖a‖ < 1 := by
  sorry

end Erdos249257.ExternalVerification1041RootRetention
