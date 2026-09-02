/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #249 actual-LCM orbit frontier

This Mathlib-only interface exposes the exact actual-LCM diagonal orbit and
the equivalence between its cofinal non-integrality and irrationality of the
binary totient series.  It also records the scaled-series identity that makes
the orbit an integer translate of the original target.

The theorem does not produce any non-integral orbit value.  In particular, it
does not prove Erdős Problem 249 or the stronger quantitative separation
condition used by a different conditional route.
-/

namespace Erdos249257.ExternalVerification249ActualLcmOrbit

open scoped BigOperators

/-- The universal period `lcm(1,...,t)`, in its source-recursive form. -/
def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)

/-- The local binary totient tail. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)

/-- The integer prefix of the scaled binary totient series. -/
def totientPrefix (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), Nat.totient n * 2 ^ (N - n)

/-- The actual LCM height at the power-two endpoint `2^a`. -/
def actualLcmHeight (a : ℕ) : ℕ :=
  periodLcm (2 ^ a)

/-- The actual power-two LCM-diagonal tail orbit. -/
noncomputable def actualLcmTailOrbit (a : ℕ) : ℝ :=
  totientTail (2 * actualLcmHeight a) - totientTail (actualLcmHeight a)

/-- Cofinal non-integrality of the actual LCM-diagonal orbit. -/
def PowerTwoActualLcmOrbitNonintegralitySupply : Prop :=
  ∀ a₀ : ℕ, ∃ a, a₀ ≤ a ∧
    actualLcmTailOrbit a ∉ Set.range ((↑) : ℤ → ℝ)

/-- The actual orbit is an integer translate of a scaled copy of the target. -/
theorem actualLcmTailOrbit_eq_scaled_totientSeries_sub_prefix (a : ℕ) :
    actualLcmTailOrbit a =
      (2 : ℝ) ^ actualLcmHeight a *
          ((2 : ℝ) ^ actualLcmHeight a - 1) *
          (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) -
        ((totientPrefix (2 * actualLcmHeight a) : ℝ) -
          (totientPrefix (actualLcmHeight a) : ℝ)) := by
  sorry

/-- The sharp actual-LCM orbit frontier for Erdős Problem 249. -/
theorem irrational_totientSeries_iff_actualLcmOrbitNonintegralitySupply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      PowerTwoActualLcmOrbitNonintegralitySupply := by
  sorry

end Erdos249257.ExternalVerification249ActualLcmOrbit
