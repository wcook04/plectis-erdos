/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos257PeriodNoncollapse.TotientActualLcmOrbitNonintegrality

/-! Exact source transport for the Erdős #249 actual-LCM orbit frontier. -/

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

private theorem periodLcm_eq_source :
    ∀ t : ℕ, periodLcm t =
      Erdos257PeriodNoncollapse.TotientTailPeriodKiller.periodLcm t
  | 0 => rfl
  | t + 1 => by
      simp only [periodLcm,
        Erdos257PeriodNoncollapse.TotientTailPeriodKiller.periodLcm]
      rw [periodLcm_eq_source t]

theorem actualLcmTailOrbit_eq_scaled_totientSeries_sub_prefix (a : ℕ) :
    actualLcmTailOrbit a =
      (2 : ℝ) ^ actualLcmHeight a *
          ((2 : ℝ) ^ actualLcmHeight a - 1) *
          (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) -
        ((totientPrefix (2 * actualLcmHeight a) : ℝ) -
          (totientPrefix (actualLcmHeight a) : ℝ)) := by
  simpa [actualLcmTailOrbit, actualLcmHeight, totientTail, totientPrefix,
    Erdos257PeriodNoncollapse.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmTailOrbit,
    Erdos257PeriodNoncollapse.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmHeight,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.totientTail,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.totientPrefix,
    periodLcm_eq_source] using
    Erdos257PeriodNoncollapse.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmTailOrbit_eq_scaled_totientSeries_sub_prefix a

theorem irrational_totientSeries_iff_actualLcmOrbitNonintegralitySupply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      PowerTwoActualLcmOrbitNonintegralitySupply := by
  simpa [PowerTwoActualLcmOrbitNonintegralitySupply,
    actualLcmTailOrbit, actualLcmHeight, totientTail,
    Erdos257PeriodNoncollapse.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.PowerTwoActualLcmOrbitNonintegralitySupply,
    Erdos257PeriodNoncollapse.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmTailOrbit,
    Erdos257PeriodNoncollapse.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmHeight,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.totientTail,
    periodLcm_eq_source] using
    Erdos257PeriodNoncollapse.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.irrational_totientSeries_iff_actualLcmOrbitNonintegralitySupply

end Erdos249257.ExternalVerification249ActualLcmOrbit
