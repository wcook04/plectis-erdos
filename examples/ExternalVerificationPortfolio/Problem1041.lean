-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
import Erdos249257
import ExternalVerification.Solution

/-!
# Erdős #1041 external verification consumer

This downstream module records two source-current public perturbation
interfaces.  They are unconditional local mechanisms under their stated
hypotheses, but neither constructs the global curve required by Erdős #1041.
-/

namespace ExternalVerificationPortfolio.Problem1041

#check Erdos249257.ExternalVerification.exists_small_translation_separating_arguments
#check Erdos249257.ExternalVerification.constant_perturbation_roots_in_unitDisk

/-- An injective finite family can be translated by an arbitrarily small
amount so that no value is zero and no two values share a positive ray. -/
theorem finite_values_admit_small_ray_separating_translation
    {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (hc : Function.Injective c) {ε : ℝ} (hε : 0 < ε) :
    ∃ shift : ℂ, ‖shift‖ < ε ∧
      (∀ i, c i + shift ≠ 0) ∧
      ∀ i j, i ≠ j →
        ¬Erdos249257.ExternalVerification.SamePositiveRay
          (c i + shift) (c j + shift) :=
  Erdos249257.ExternalVerification.exists_small_translation_separating_arguments
    c hc hε

/-- A sufficiently small constant perturbation preserves the open-unit-disk
root condition under the exact split, monic, and quantitative margin data. -/
theorem constant_perturbation_preserves_open_unit_disk
    (f : Polynomial ℂ) (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hsplit : f.Splits) {ρ ε : ℝ} (hρ : 0 ≤ ρ)
    (hroots : ∀ b ∈ f.roots, ‖b‖ ≤ ρ) (hε : 0 < ε)
    (hmargin :
      ((f.natDegree + 1) * ε) ^ (f.natDegree : ℝ)⁻¹ + ρ < 1)
    {shift : ℂ} (hshift : ‖shift‖ < ε) :
    ∀ a : ℂ, (f + Polynomial.C shift).eval a = 0 → ‖a‖ < 1 :=
  Erdos249257.ExternalVerification.constant_perturbation_roots_in_unitDisk
    f hf hdeg hsplit hρ hroots hε hmargin hshift

end ExternalVerificationPortfolio.Problem1041
