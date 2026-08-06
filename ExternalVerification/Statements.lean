/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib.Data.Nat.Totient
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.Real.Irrational

/-!
# External-verification statement vocabulary

This module contains only the definitions needed to state the deliberately
small external-verification packet.  It imports Mathlib, not the proof-bearing
`Erdos249257` modules.  `ExternalVerification.Challenge` and
`ExternalVerification.Solution` therefore share byte-identical statement
constants while the challenge import closure remains independent of the
submitted proofs.
-/

namespace Erdos249257.ExternalVerification

open Module MeasureTheory

/-- The `(j,r)` dyadic-kernel channel of Euler's totient, restated for the
external verification boundary. -/
def totientKernelSeq (j r : ℕ) : ℕ → ℚ := fun n =>
  Nat.totient (2 ^ j * n + r)

/-- Every dyadic totient channel at levels `0,...,e`. -/
abbrev TotientKernelThroughLevelIndex (e : ℕ) :=
  Σ j : Fin (e + 1), Fin (2 ^ j.val)

/-- The complete finite dyadic kernel through level `e`. -/
def totientKernelThroughLevelFamily (e : ℕ) :
    TotientKernelThroughLevelIndex e → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j.val r.val

/-- The full dyadic-kernel index. -/
abbrev TotientDyadicKernelIndex := Σ j : ℕ, Fin (2 ^ j)

/-- Every canonical dyadic section of Euler's totient. -/
def fullTotientKernelFamily : TotientDyadicKernelIndex → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j r.val

/-- The positive-index real Mersenne weight. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

/-- The value coded by a set of positive exponents. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

/-- The normalized Mersenne achievement set. -/
def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}

end Erdos249257.ExternalVerification
