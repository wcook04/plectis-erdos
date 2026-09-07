/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-! Deliberate type mismatch for the actual-LCM Comparator package. -/

namespace Erdos249257.ExternalVerification249ActualLcmOrbit

open scoped BigOperators

def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)

noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)

def totientPrefix (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), Nat.totient n * 2 ^ (N - n)

def actualLcmHeight (a : ℕ) : ℕ :=
  periodLcm (2 ^ a)

noncomputable def actualLcmTailOrbit (a : ℕ) : ℝ :=
  totientTail (2 * actualLcmHeight a) - totientTail (actualLcmHeight a)

def PowerTwoActualLcmOrbitNonintegralitySupply : Prop :=
  ∀ a₀ : ℕ, ∃ a, a₀ ≤ a ∧
    actualLcmTailOrbit a ∉ Set.range ((↑) : ℤ → ℝ)

theorem actualLcmTailOrbit_eq_scaled_totientSeries_sub_prefix (a : ℕ) :
    actualLcmTailOrbit a =
      (2 : ℝ) ^ actualLcmHeight a *
          ((2 : ℝ) ^ actualLcmHeight a - 1) *
          (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) -
        ((totientPrefix (2 * actualLcmHeight a) : ℝ) -
          (totientPrefix (actualLcmHeight a) : ℝ)) := by
  sorry

theorem irrational_totientSeries_iff_actualLcmOrbitNonintegralitySupply
    (_extra : True) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      PowerTwoActualLcmOrbitNonintegralitySupply := by
  sorry

end Erdos249257.ExternalVerification249ActualLcmOrbit
