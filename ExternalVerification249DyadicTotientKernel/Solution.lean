/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.TotientMahlerDefect

/-!
# Source transport for the dyadic totient-kernel structure in Erdős #249
-/

namespace Erdos249257.ExternalVerification249DyadicTotientKernel

def totientKernelSeq (j r : ℕ) : ℕ → ℚ := fun n =>
  Nat.totient (2 ^ j * n + r)

abbrev TotientCanonicalIndex (e : ℕ) :=
  Fin 2 ⊕ Σ j : Fin e, Fin (2 ^ j.val)

def canonicalTotientKernelFamily (e : ℕ) :
    TotientCanonicalIndex e → ℕ → ℚ
  | Sum.inl i => totientKernelSeq i.val 0
  | Sum.inr ⟨j, r⟩ => totientKernelSeq (j.val + 1) (2 * r.val + 1)

abbrev TotientKernelThroughLevelIndex (e : ℕ) :=
  Σ j : Fin (e + 1), Fin (2 ^ j.val)

def totientKernelThroughLevelFamily (e : ℕ) :
    TotientKernelThroughLevelIndex e → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j.val r.val

abbrev TotientDyadicKernelIndex := Σ j : ℕ, Fin (2 ^ j)

def fullTotientKernelFamily : TotientDyadicKernelIndex → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j r.val

abbrev TotientOddCoreIndex := Fin 2 ⊕ Σ j : ℕ, Fin (2 ^ j)

def oddCoreTotientKernelFamily : TotientOddCoreIndex → ℕ → ℚ
  | Sum.inl i => totientKernelSeq i.val 0
  | Sum.inr ⟨j, r⟩ => totientKernelSeq (j + 1) (2 * r.val + 1)

theorem dyadicTotientKernelOddCoreBasisAndFiniteRanks :
    LinearIndependent ℚ oddCoreTotientKernelFamily ∧
      Submodule.span ℚ (Set.range fullTotientKernelFamily) =
        Submodule.span ℚ (Set.range oddCoreTotientKernelFamily) ∧
      ∀ e : ℕ, 1 ≤ e →
        Submodule.span ℚ
            (Set.range (totientKernelThroughLevelFamily e)) =
          Submodule.span ℚ
            (Set.range (canonicalTotientKernelFamily e)) ∧
        Module.finrank ℚ
            (Submodule.span ℚ
              (Set.range (totientKernelThroughLevelFamily e))) = 2 ^ e + 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [oddCoreTotientKernelFamily, totientKernelSeq,
      Erdos249257.oddCoreTotientKernelFamily,
      Erdos249257.totientKernelSeq] using
      Erdos249257.linearIndependent_oddCoreTotientKernelFamily
  · simpa [fullTotientKernelFamily, oddCoreTotientKernelFamily,
      totientKernelSeq, Erdos249257.fullTotientKernelFamily,
      Erdos249257.oddCoreTotientKernelFamily,
      Erdos249257.totientKernelSeq] using
      Erdos249257.span_range_fullTotientKernel_eq_span_range_oddCore
  · intro e he
    constructor
    · simpa [totientKernelThroughLevelFamily,
        canonicalTotientKernelFamily, totientKernelSeq,
        Erdos249257.totientKernelThroughLevelFamily,
        Erdos249257.canonicalTotientKernelFamily,
        Erdos249257.totientKernelSeq] using
        Erdos249257.span_totientKernelThroughLevelFamily_eq_canonical
          e he
    · simpa [totientKernelThroughLevelFamily, totientKernelSeq,
        Erdos249257.totientKernelThroughLevelFamily,
        Erdos249257.totientKernelSeq] using
        Erdos249257.finrank_totientKernelThroughLevelFamily_eq e he

end Erdos249257.ExternalVerification249DyadicTotientKernel
