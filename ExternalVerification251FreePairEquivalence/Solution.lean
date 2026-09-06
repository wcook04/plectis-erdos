/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.FreePairReduction

/-!
# Source transport for the Erdős #251 free-pair equivalence

The declarations below restate the Mathlib-only challenge vocabulary and
transport the exact source theorems without strengthening their hypotheses.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification251FreePairEquivalence

noncomputable abbrev prime0 := ErdosProblems.Erdos251.prime0
noncomputable abbrev primeGap0 := ErdosProblems.Erdos251.primeGap0
noncomputable abbrev primeGapDyadicTerm := ErdosProblems.Erdos251.primeGapDyadicTerm
abbrev DyadicTailRecurrence := ErdosProblems.Erdos251.DyadicTailRecurrence
abbrev RealDyadicTailRecurrence := ErdosProblems.Erdos251.RealDyadicTailRecurrence
abbrev realTailShift := ErdosProblems.Erdos251.realTailShift
abbrev RatIntegral := ErdosProblems.Erdos251.RatIntegral
abbrev RealIntegral := ErdosProblems.Erdos251.RealIntegral
abbrev CofinalNonintegralTailShifts := ErdosProblems.Erdos251.CofinalNonintegralTailShifts
abbrev CofinalFreePairNonintegral := ErdosProblems.Erdos251.CofinalFreePairNonintegral
noncomputable abbrev primeGapRealTail := ErdosProblems.Erdos251.primeGapRealTail

theorem irrational_primeGap_tsum_iff_cofinalFreePairNonintegral :
    Irrational (∑' n : ℕ, primeGapDyadicTerm n) ↔
      CofinalFreePairNonintegral primeGapRealTail :=
  ErdosProblems.Erdos251.irrational_primeGap_tsum_iff_cofinalFreePairNonintegral

theorem irrational_initial_iff_cofinalFreePairNonintegral {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔ CofinalFreePairNonintegral T :=
  ErdosProblems.Erdos251.irrational_initial_iff_cofinalFreePairNonintegral hrec

theorem cofinalFreePairNonintegral_iff_cofinalNonintegralTailShifts
    {g : ℕ → ℤ} {T : ℕ → ℝ} (hrec : RealDyadicTailRecurrence g T) :
    CofinalFreePairNonintegral T ↔ CofinalNonintegralTailShifts T :=
  ErdosProblems.Erdos251.cofinalFreePairNonintegral_iff_cofinalNonintegralTailShifts hrec

theorem exists_free_pair_lattice {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) :
    ∃ N₀ t : ℕ, 0 < t ∧ ∀ N M : ℕ, N₀ ≤ N → N₀ ≤ M →
      (RatIntegral (T M - T N) ↔ N ≡ M [MOD t]) :=
  ErdosProblems.Erdos251.exists_free_pair_lattice hrec

theorem free_pair_integral_iff_modEq {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) {N₀ : ℕ} (hodd : Odd (T N₀).den)
    {N M : ℕ} (hN : N₀ ≤ N) (hM : N₀ ≤ M) :
    RatIntegral (T M - T N) ↔ N ≡ M [MOD orderOf (2 : ZMod (T N₀).den)] :=
  ErdosProblems.Erdos251.free_pair_integral_iff_modEq hrec hodd hN hM

theorem primeGapRealTail_recurrence :
    RealDyadicTailRecurrence (fun n => (primeGap0 n : ℤ)) primeGapRealTail :=
  ErdosProblems.Erdos251.primeGapRealTail_recurrence

theorem primeGapRealTail_zero :
    primeGapRealTail 0 = 2 * (∑' n : ℕ, primeGapDyadicTerm n) - 1 :=
  ErdosProblems.Erdos251.primeGapRealTail_zero

end Erdos249257.ExternalVerification251FreePairEquivalence
