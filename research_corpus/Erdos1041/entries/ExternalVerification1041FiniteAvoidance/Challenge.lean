/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the #1041 finite-avoidance kernel

The Challenge contains only the literal geometric conclusion.  It does not
import the project-local source module or expose its affine-line definition.
-/

namespace Erdos249257.ExternalVerification1041FiniteAvoidance

/-- A finite family of real affine lines admits an arbitrarily small point
outside every line in the complex plane. -/
theorem exists_small_avoiding_finite_realAffineLines
    {κ : Type*} [Fintype κ] (p v : κ → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ z : ℂ, ‖z‖ < ε ∧
      ∀ k, z ∉ Set.range (fun t : ℝ => t • v k + p k) := by
  sorry

end Erdos249257.ExternalVerification1041FiniteAvoidance
