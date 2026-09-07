/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos257.MersenneSubseriesRigidity

/-!
# Deliberate declaration mismatch for achievement-set geometry

The extra `True` hypothesis changes the theorem type.  The proof remains a
truthful source transport, but Comparator must reject it as a mismatch with
the Challenge declaration.
-/

namespace Erdos249257.ExternalVerification257AchievementSetGeometry

open scoped ENNReal

open Set MeasureTheory

noncomputable section

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

noncomputable def mersenneDigitTerm (k : ℕ) (b : ℕ → Fin 2) : ℝ :=
  ((b k : ℕ) : ℝ) * mersenneWeight (k + 1)

noncomputable def positiveMersenneDigitValue (b : ℕ → Fin 2) : ℝ :=
  ∑' k : ℕ, mersenneDigitTerm k b

def SupportedMersenneDigits (J : Set ℕ) :=
  {b : ℕ → Fin 2 // ∀ k, k ∉ J → b k = 0}

noncomputable def supportedMersenneDigitValue
    (J : Set ℕ) (b : SupportedMersenneDigits J) : ℝ :=
  positiveMersenneDigitValue b.1

def supportedMersenneAchievementSet (J : Set ℕ) : Set ℝ :=
  Set.range (supportedMersenneDigitValue J)

theorem supportedMersenneAchievementSet_geometry_and_volume
    (_extra : True) (J : Set ℕ) :
    Function.Injective (supportedMersenneDigitValue J) ∧
      IsCompact (supportedMersenneAchievementSet J) ∧
      IsNowhereDense (supportedMersenneAchievementSet J) ∧
      (J.Infinite → Perfect (supportedMersenneAchievementSet J)) ∧
      ((∃ F : Finset ℕ,
          J = (↑F : Set ℕ)ᶜ ∧
            volume (supportedMersenneAchievementSet J) =
              ((2 : ℝ≥0∞) ^ F.card)⁻¹) ∨
        (Jᶜ.Infinite ∧
          volume (supportedMersenneAchievementSet J) = 0)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [supportedMersenneDigitValue, SupportedMersenneDigits,
      positiveMersenneDigitValue, mersenneDigitTerm, mersenneWeight,
      ErdosProblems.Erdos257.supportedMersenneDigitValue,
      ErdosProblems.Erdos257.SupportedMersenneDigits,
      Erdos257PeriodNoncollapse.positiveMersenneDigitValue,
      Erdos257PeriodNoncollapse.mersenneDigitTerm,
      Erdos257PeriodNoncollapse.mersenneWeight] using
      ErdosProblems.Erdos257.supportedMersenneDigitValue_injective J
  · simpa [supportedMersenneAchievementSet, supportedMersenneDigitValue,
      SupportedMersenneDigits, positiveMersenneDigitValue,
      mersenneDigitTerm, mersenneWeight,
      ErdosProblems.Erdos257.supportedMersenneAchievementSet,
      ErdosProblems.Erdos257.supportedMersenneDigitValue,
      ErdosProblems.Erdos257.SupportedMersenneDigits,
      Erdos257PeriodNoncollapse.positiveMersenneDigitValue,
      Erdos257PeriodNoncollapse.mersenneDigitTerm,
      Erdos257PeriodNoncollapse.mersenneWeight] using
      ErdosProblems.Erdos257.isCompact_supportedMersenneAchievementSet J
  · simpa [supportedMersenneAchievementSet, supportedMersenneDigitValue,
      SupportedMersenneDigits, positiveMersenneDigitValue,
      mersenneDigitTerm, mersenneWeight,
      ErdosProblems.Erdos257.supportedMersenneAchievementSet,
      ErdosProblems.Erdos257.supportedMersenneDigitValue,
      ErdosProblems.Erdos257.SupportedMersenneDigits,
      Erdos257PeriodNoncollapse.positiveMersenneDigitValue,
      Erdos257PeriodNoncollapse.mersenneDigitTerm,
      Erdos257PeriodNoncollapse.mersenneWeight] using
      ErdosProblems.Erdos257.isNowhereDense_supportedMersenneAchievementSet J
  · intro hJ
    simpa [supportedMersenneAchievementSet, supportedMersenneDigitValue,
      SupportedMersenneDigits, positiveMersenneDigitValue,
      mersenneDigitTerm, mersenneWeight,
      ErdosProblems.Erdos257.supportedMersenneAchievementSet,
      ErdosProblems.Erdos257.supportedMersenneDigitValue,
      ErdosProblems.Erdos257.SupportedMersenneDigits,
      Erdos257PeriodNoncollapse.positiveMersenneDigitValue,
      Erdos257PeriodNoncollapse.mersenneDigitTerm,
      Erdos257PeriodNoncollapse.mersenneWeight] using
      ErdosProblems.Erdos257.perfect_supportedMersenneAchievementSet hJ
  · simpa [supportedMersenneAchievementSet, supportedMersenneDigitValue,
      SupportedMersenneDigits, positiveMersenneDigitValue,
      mersenneDigitTerm, mersenneWeight,
      ErdosProblems.Erdos257.supportedMersenneAchievementSet,
      ErdosProblems.Erdos257.supportedMersenneDigitValue,
      ErdosProblems.Erdos257.SupportedMersenneDigits,
      Erdos257PeriodNoncollapse.positiveMersenneDigitValue,
      Erdos257PeriodNoncollapse.mersenneDigitTerm,
      Erdos257PeriodNoncollapse.mersenneWeight] using
      ErdosProblems.Erdos257.volume_supportedMersenneAchievementSet_dichotomy J

end

end Erdos249257.ExternalVerification257AchievementSetGeometry
