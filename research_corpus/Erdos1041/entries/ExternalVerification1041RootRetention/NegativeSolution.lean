/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041RootRetention.Statements
import ErdosProblems.Erdos1041.NewtonFlowRaySeparation

/-!
# Deliberate nearby mismatch for the #1041 root-retention boundary

The negative fixture adds an irrelevant proposition argument after the
challenge hypotheses.  It can reuse the source proof, but its declaration
type is not the Challenge type, so Comparator must reject it before semantic
acceptance.
-/

namespace Erdos249257.ExternalVerification1041RootRetention

theorem constant_perturbation_roots_in_unitDisk
    (f : ℂ[X]) (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hsplit : f.Splits) {ρ ε : ℝ} (hρ : 0 ≤ ρ)
    (hroots : ∀ b ∈ f.roots, ‖b‖ ≤ ρ)
    (hε : 0 < ε)
    (hmargin :
      ((f.natDegree + 1) * ε) ^ (f.natDegree : ℝ)⁻¹ + ρ < 1)
    {shift : ℂ} (hshift : ‖shift‖ < ε) (hweak : True) :
    ∀ a : ℂ, (f + C shift).eval a = 0 → ‖a‖ < 1 := by
  exact ErdosProblems.Erdos1041.constant_perturbation_roots_in_unitDisk
    f hf hdeg hsplit hρ hroots hε hmargin hshift

end Erdos249257.ExternalVerification1041RootRetention
