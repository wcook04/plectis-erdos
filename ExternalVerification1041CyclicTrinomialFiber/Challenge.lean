/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #1041 cyclic-trinomial fibre spokes

These Mathlib-only statements record the exact spoke identity for
`f(z) = z^m + a z^r + c` at a root of the trinomial, the sublevel bound
`‖f(u w)‖ ≤ ‖f(0)‖` it supplies along the whole spoke of a root with
`‖w‖^m ≤ ‖c‖`, the two strict unit-lemniscate specialisations, and the metric
budget for two short fibre displacements.
-/

namespace Erdos249257.ExternalVerification1041CyclicTrinomialFiber

/-- Eliminating the middle coefficient at a quotient root gives the exact
two-term radial-spoke factorization. -/
theorem trinomialRoot_spoke_factorization
    {m r : ℕ} {a c w : ℂ} {u : ℝ}
    (hroot : w ^ m + a * w ^ r + c = 0) :
    (u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + c =
      ((1 - u ^ r : ℝ) : ℂ) * c -
        ((u ^ r - u ^ m : ℝ) : ℂ) * w ^ m := by
  sorry

/-- A quotient root whose m-th power radius is at most the constant-term radius
keeps the whole spoke inside the exact sublevel set of the constant term. -/
theorem trinomialRoot_spoke_norm_le_constant
    {m r : ℕ} (hrm : r ≤ m) {a c w : ℂ}
    (hroot : w ^ m + a * w ^ r + c = 0)
    (hw : ‖w‖ ^ m ≤ ‖c‖) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + c‖ ≤ ‖c‖ := by
  sorry

/-- The strict unit-lemniscate form of the sublevel bound, available once the
constant term lies in the open unit disk. -/
theorem trinomialRoot_spoke_norm_lt_one
    {m r : ℕ} (hrm : r ≤ m) {a c w : ℂ}
    (hroot : w ^ m + a * w ^ r + c = 0)
    (hw : ‖w‖ ^ m ≤ ‖c‖) (hc : ‖c‖ < 1) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + c‖ < 1 := by
  sorry

/-- Every quotient-root spoke is strictly inside the unit lemniscate when
the quotient root and constant term both lie in the open unit disk. -/
theorem trinomialRoot_spoke_norm_lt_one_of_norm_lt_one
    {m r : ℕ} (hr : 1 ≤ r) (hrm : r ≤ m) {a c w : ℂ}
    (hroot : w ^ m + a * w ^ r + c = 0)
    (hw : ‖w‖ < 1) (hc : ‖c‖ < 1) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + c‖ < 1 := by
  sorry

/-- Two selected fibre displacements of radius below one have total broken-line
length strictly below two. -/
theorem cyclicTrinomial_two_short_fiber_displacements {y₁ y₂ : ℂ}
    (hy₁ : ‖y₁‖ < 1) (hy₂ : ‖y₂‖ < 1) :
    ‖y₁‖ + ‖y₂‖ < 2 := by
  sorry

end Erdos249257.ExternalVerification1041CyclicTrinomialFiber
