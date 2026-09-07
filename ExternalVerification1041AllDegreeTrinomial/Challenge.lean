/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the all-degree monic trinomial theorem

This is the short-note Theorem 1 of the Erdős #1041 writeup
(`res:trinomial-all-degree`): every Schur-stable monic trinomial
`z^n + a z^m + b` has radial spokes from the origin to each zero inside
`{|f| < 1}`, so any two zeros are joined through the origin by a broken
line of length strictly less than two.

The compared declaration is an exact transport of
`ErdosProblems.Erdos1041.AbelControlPolygon.trinomial_erdos1041_conclusion`.
The unrestricted Erdős–Herzog–Piranian problem, for polynomials with more
than two non-leading terms, remains open.
-/

namespace Erdos249257.ExternalVerification1041AllDegreeTrinomial

/-- **All-degree monic trinomials.** Let `1 ≤ m < n` and
`f z = z^n + a z^m + b`, with every zero in the open unit disc. For any
zero `ζ`, the entire segment `[0, ζ]` lies in `{|f| < 1}`. Distinct zeros
`ζ₁, ζ₂` are therefore joined by the broken line `ζ₁ → 0 → ζ₂` of length
`‖ζ₁‖ + ‖ζ₂‖ < 2` inside the open unit lemniscate. -/
theorem trinomial_erdos1041_conclusion {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n)
    {a b ζ₁ ζ₂ : ℂ}
    (hroots : ∀ ζ : ℂ, ζ ^ n + a * ζ ^ m + b = 0 → ‖ζ‖ < 1)
    (h₁ : ζ₁ ^ n + a * ζ₁ ^ m + b = 0) (h₂ : ζ₂ ^ n + a * ζ₂ ^ m + b = 0) :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        ‖((t : ℂ) * ζ₁) ^ n + a * ((t : ℂ) * ζ₁) ^ m + b‖ < 1) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        ‖((t : ℂ) * ζ₂) ^ n + a * ((t : ℂ) * ζ₂) ^ m + b‖ < 1) ∧
      ‖ζ₁‖ + ‖ζ₂‖ < 2 := by
  sorry

end Erdos249257.ExternalVerification1041AllDegreeTrinomial
