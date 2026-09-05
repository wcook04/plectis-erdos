/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for supported Mersenne achievement-set geometry

For every set `J` of allowed binary coordinates, this module defines the
corresponding base-two Mersenne achievement set literally.  The single
compared theorem packages unique coding, compact nowhere-dense geometry,
perfection for infinite support, and the complete Lebesgue-measure dichotomy:
finite omitted support gives the exact dyadic volume, while infinitely many
omitted coordinates give volume zero.

These geometric and measure-theoretic conclusions do not prove irrationality
of every infinite Mersenne subseries or solve universal Erdős #257.
-/

namespace Erdos249257.ExternalVerification257AchievementSetGeometry

open scoped ENNReal

open Set MeasureTheory

noncomputable section

/-- The real Mersenne weight `1 / (2^n - 1)`. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

/-- The contribution of the `k`th binary digit. -/
noncomputable def mersenneDigitTerm (k : ℕ) (b : ℕ → Fin 2) : ℝ :=
  ((b k : ℕ) : ℝ) * mersenneWeight (k + 1)

/-- The value of a positive-index binary Mersenne digit string. -/
noncomputable def positiveMersenneDigitValue (b : ℕ → Fin 2) : ℝ :=
  ∑' k : ℕ, mersenneDigitTerm k b

/-- Binary digit strings supported on `J`. -/
def SupportedMersenneDigits (J : Set ℕ) :=
  {b : ℕ → Fin 2 // ∀ k, k ∉ J → b k = 0}

/-- The Mersenne digit map restricted to the selected support. -/
noncomputable def supportedMersenneDigitValue
    (J : Set ℕ) (b : SupportedMersenneDigits J) : ℝ :=
  positiveMersenneDigitValue b.1

/-- The achievement set obtained by allowing binary digits only on `J`. -/
def supportedMersenneAchievementSet (J : Set ℕ) : Set ℝ :=
  Set.range (supportedMersenneDigitValue J)

/-- Complete geometry and Lebesgue-measure classification for every selected
Mersenne support. -/
theorem supportedMersenneAchievementSet_geometry_and_volume (J : Set ℕ) :
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
  sorry

end

end Erdos249257.ExternalVerification257AchievementSetGeometry
