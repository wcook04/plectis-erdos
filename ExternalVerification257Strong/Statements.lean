/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-! Independent statement vocabulary for the stronger #257 support and repair
results. This statement module depends only on Mathlib. -/

namespace Erdos249257.ExternalVerification.Strong257

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

/-- The value coded by a set of positive exponents. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

/-- The normalized Mersenne achievement set. -/
def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}


noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a


structure OrthogonalPetalBouquet (A : Set ℕ) where
  Q : ℕ
  Q_pos : 0 < Q
  exceptional : Finset ℕ
  core : ℕ → ℕ
  petal : ℕ → ℕ
  exceptional_pos : ∀ d ∈ exceptional, 0 < d
  exceptional_dvd_Q : ∀ d ∈ exceptional, d ∣ Q
  core_pos : ∀ i, 0 < core i
  core_dvd_Q : ∀ i, core i ∣ Q
  petal_one_lt : ∀ i, 1 < petal i
  petal_coprime_Q : ∀ i, Nat.Coprime (petal i) Q
  petal_pairwise : ∀ i j, i ≠ j → Nat.Coprime (petal i) (petal j)
  support_eq :
    A = (↑exceptional : Set ℕ) ∪ Set.range (fun i => core i * petal i)
  summable_inv_petal : Summable (fun i => (1 : ℝ) / (petal i : ℝ))



noncomputable def reciprocalSupportTerm (A : Set ℕ) (a : ℕ) : ℝ :=
  Set.indicator A (fun a : ℕ => (1 : ℝ) / (a : ℝ)) a

noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else greedyMersenneRemainder x n

noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧
    mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}

def binaryCoeffPrefixNumerator (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | N + 1 => 2 * binaryCoeffPrefixNumerator c N + c (N + 1)

noncomputable def greedyBinaryDefect (x : ℝ) (N : ℕ) : ℕ :=
  ⌊(2 : ℝ) ^ N * x⌋₊ -
    binaryCoeffPrefixNumerator (supportCoeff (greedyMersenneSupport x)) N

end Erdos249257.ExternalVerification.Strong257
