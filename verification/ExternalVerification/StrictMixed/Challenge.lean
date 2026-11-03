/- Copyright (c) 2026 Will Cook. Released under Apache 2.0. -/
import Mathlib

/-! Mathlib-only statement vocabulary for short-note Corollary 5.2.
All definitions are inline so protected compilation needs no submitted imports.
The names and bodies below restate the public definitions; no proof-bearing
corpus module is imported. The frame index `j` represents printed `j + 1`.
-/

noncomputable section

namespace Erdos249257

def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

end Erdos249257

namespace ErdosProblems.Erdos257.PaperCompleteR7

def primeSetPart (P : Finset ℕ) (a : ℕ) : ℕ :=
  ∏ p ∈ P, p ^ a.factorization p

def primeWeightedTerm (b : ℕ) (P : Finset ℕ) (a : ℕ) : ℝ :=
  (primeSetPart P a : ℝ) /
    ((a : ℝ) * ((b : ℝ) ^ primeSetPart P a - 1))

def FinitePrimeWeighted (b : ℕ) (A : Set ℕ) : Prop :=
  ∃ P : Finset ℕ, P.Nonempty ∧ (∀ p ∈ P, Nat.Prime p) ∧
    Summable (Set.indicator A (primeWeightedTerm b P))

structure PositiveCoverData where
  frame : ℕ → Finset ℕ
  exponent : ℕ → ℝ
  coefficient : ℕ → ℕ → ℝ
  frame_positive : ∀ j, 0 ∉ frame j
  exponent_bounds : ∀ j, 0 < exponent j ∧ exponent j ≤ 1
  coefficient_nonneg : ∀ j d, 0 < d → 0 ≤ coefficient j d
  column_summable : ∀ j, Summable (fun d : ℕ => coefficient j d / (d : ℝ))
  majorises : ∀ j n, 0 < n →
    (((frame j).filter (fun a => a ∣ n)).card : ℝ) ^ exponent j ≤
      ∑ d ∈ n.divisors, coefficient j d

def PositiveCoverData.cost (C : PositiveCoverData) (j : ℕ) : ℝ :=
  ∑' d : ℕ, C.coefficient j d / (d : ℝ)

def PositiveCoverData.host (C : PositiveCoverData) : Set ℕ :=
  {a | ∃ j, a ∈ C.frame j}

def PositiveCoverData.StrengthenedCostSummable (C : PositiveCoverData) : Prop :=
  Summable (fun j : ℕ =>
    C.cost j * (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * C.exponent j) /
      ((2 : ℝ) ^ C.exponent j - 1))

def HasStrengthenedPositiveCover (A : Set ℕ) : Prop :=
  ∃ C : PositiveCoverData, A ⊆ C.host ∧ C.StrengthenedCostSummable

end ErdosProblems.Erdos257.PaperCompleteR7

end

/-! Trusted challenge for the complete existential Corollary 5.2.
Its single statement hole is a Comparator input, never proof evidence.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR8
open ErdosProblems.Erdos257.PaperCompleteR7 Erdos249257

theorem exists_strict_mixed_support_host :
    ∃ U : Set ℕ, U.Infinite ∧ 0 ∉ U ∧
      ¬ HasStrengthenedPositiveCover U ∧
      (∀ b : ℕ, 2 ≤ b → ¬ FinitePrimeWeighted b U) ∧
      (∀ A : Set ℕ, A ⊆ U → A.Infinite → ∀ b : ℕ, 2 ≤ b →
        Irrational (erdosSupportSeries b A)) := by
  sorry

end ErdosProblems.Erdos257.PaperCompleteR8
