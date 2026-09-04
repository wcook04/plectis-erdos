/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #257 four-ninths tetraprime frontier

This Mathlib-only specification exposes the strongest coherent interface of
the checked `4/9` counterexample programme: the exact modulus-420 base kernel,
a uniform defect ceiling on every repaired prime row, and the final reduction
from the genuinely moving large-prime and composite-margin obligations to an
infinite rational counterexample.  The last two obligations remain hypotheses;
the package does not refute Erdős #257 unconditionally.
-/

namespace Erdos249257.ExternalVerification257FourNinthsTetraprime

open Set

noncomputable section

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n

noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧
    mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}

noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card

def binaryCoeffPrefixNumerator (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | N + 1 => 2 * binaryCoeffPrefixNumerator c N + c (N + 1)

def fourNinthsBinaryFloor (N : ℕ) : ℕ :=
  4 * 2 ^ N / 9

noncomputable def fourNinthsGreedyDefect (N : ℕ) : ℕ :=
  fourNinthsBinaryFloor N -
    binaryCoeffPrefixNumerator
      (supportCoeff (greedyMersenneSupport (4 / 9 : ℝ))) N

noncomputable def fourNinthsSelectedDivisors
    (A : Set ℕ) (n : ℕ) : Finset ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  n.divisors.filter fun d => d ∈ A

/-- The selected-divisor union visible in the `2`, `3`, `5`, and `7` parent
columns of a modulus-420 row. -/
noncomputable def fourNinthsTetraprimeUnionLoad (n : ℕ) : ℕ :=
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  (((fourNinthsSelectedDivisors A (n / 2) ∪
      fourNinthsSelectedDivisors A (n / 3)) ∪
        fourNinthsSelectedDivisors A (n / 5)) ∪
          fourNinthsSelectedDivisors A (n / 7)).card

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A
    (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

def UniversalMersenneSubseriesIrrationality : Prop :=
  ∀ A : Set ℕ, A.Infinite → Irrational (erdosSupportSeries 2 A)

def FourNinthsMultiple420TetraprimeRepair : Prop :=
  ∀ k : ℕ,
    fourNinthsGreedyDefect (420 * (k + 1) - 1) ≤
      fourNinthsTetraprimeUnionLoad (420 * (k + 1))

def FourNinthsMultiple420LargePrimeBoundary : Prop :=
  ∀ p : ℕ, p.Prime → 7 < p →
    fourNinthsGreedyDefect (420 * p - 1) ≤
      fourNinthsTetraprimeUnionLoad (420 * p)

def FourNinthsMultiple420CompositeMarginFive : Prop :=
  ∀ k : ℕ, 1 < k → ¬ k.Prime →
    fourNinthsGreedyDefect (420 * k - 1) + 5 ≤
      fourNinthsTetraprimeUnionLoad (420 * k)

/-- Exact kernel-checked base data: the row-420 load is twelve, the preceding
defect is seven, and the four prime cofactors at most seven all repair. -/
theorem fourNinthsTetraprime_baseKernel :
    fourNinthsTetraprimeUnionLoad 420 = 12 ∧
    fourNinthsGreedyDefect 419 = 7 ∧
    ∀ p : ℕ, p.Prime → p ≤ 7 →
      fourNinthsGreedyDefect (420 * p - 1) ≤
        fourNinthsTetraprimeUnionLoad (420 * p) := by
  sorry

/-- Any repaired prime-cofactor row above seven has defect at most `35`; the
moving part is confined to a proper-divisor column of width `23`. -/
theorem fourNinthsTetraprimePrimeRepair_defect_le_thirty_five
    {p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (hrepair : fourNinthsGreedyDefect (420 * p - 1) ≤
      fourNinthsTetraprimeUnionLoad (420 * p)) :
    fourNinthsGreedyDefect (420 * p - 1) ≤ 35 := by
  sorry

/-- Complete frontier endpoint.  The large-prime boundary and five-unit
composite margin imply the full modulus-420 repair producer, an infinite
support of exact value `4/9`, and failure of the universal assertion. -/
theorem fourNinthsTetraprime_completeCounterexample
    (hprime : FourNinthsMultiple420LargePrimeBoundary)
    (hmargin : FourNinthsMultiple420CompositeMarginFive) :
    FourNinthsMultiple420TetraprimeRepair ∧
    (∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (4 : ℝ) / 9) ∧
    ¬ UniversalMersenneSubseriesIrrationality := by
  sorry

end

end Erdos249257.ExternalVerification257FourNinthsTetraprime
