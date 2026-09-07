/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.AbelControlPolygon

/-!
# Source transport for the all-degree monic trinomial theorem

Exact transport of
`ErdosProblems.Erdos1041.AbelControlPolygon.trinomial_erdos1041_conclusion`.
No hypothesis is weakened or strengthened.
-/

namespace Erdos249257.ExternalVerification1041AllDegreeTrinomial

theorem trinomial_erdos1041_conclusion {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n)
    {a b ζ₁ ζ₂ : ℂ}
    (hroots : ∀ ζ : ℂ, ζ ^ n + a * ζ ^ m + b = 0 → ‖ζ‖ < 1)
    (h₁ : ζ₁ ^ n + a * ζ₁ ^ m + b = 0) (h₂ : ζ₂ ^ n + a * ζ₂ ^ m + b = 0) :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        ‖((t : ℂ) * ζ₁) ^ n + a * ((t : ℂ) * ζ₁) ^ m + b‖ < 1) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        ‖((t : ℂ) * ζ₂) ^ n + a * ((t : ℂ) * ζ₂) ^ m + b‖ < 1) ∧
      ‖ζ₁‖ + ‖ζ₂‖ < 2 :=
  ErdosProblems.Erdos1041.AbelControlPolygon.trinomial_erdos1041_conclusion
    hm hmn hroots h₁ h₂

end Erdos249257.ExternalVerification1041AllDegreeTrinomial
