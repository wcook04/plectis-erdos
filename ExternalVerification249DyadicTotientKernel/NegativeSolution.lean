/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Deliberately incomplete result for the #249 dyadic-kernel package

This same-named declaration omits the exact finite-truncation ranks.
Comparator must reject the watered-down statement as a type mismatch.
-/

namespace Erdos249257.ExternalVerification249DyadicTotientKernel

def totientKernelSeq (j r : ℕ) : ℕ → ℚ := fun n =>
  Nat.totient (2 ^ j * n + r)

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
        Submodule.span ℚ (Set.range oddCoreTotientKernelFamily) := by
  sorry

end Erdos249257.ExternalVerification249DyadicTotientKernel
