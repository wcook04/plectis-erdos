/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos251.PrimeGapDyadicTail

/-!
# Source transport for the Erdős #251 prime-gap identity

The declarations below restate the challenge vocabulary and transport the
exact source theorems.  Where a source theorem carries the summability
hypothesis, that hypothesis is discharged by the unconditional source proof
`ErdosProblems.Erdos251.summable_primeDyadicTerm`.
-/

namespace Erdos249257.ExternalVerification251PrimeGapIdentity

noncomputable abbrev prime0 := ErdosProblems.Erdos251.prime0
noncomputable abbrev primeGap0 := ErdosProblems.Erdos251.primeGap0
noncomputable abbrev primeDyadicTerm := ErdosProblems.Erdos251.primeDyadicTerm
noncomputable abbrev primeDisplayedDyadicTerm :=
  ErdosProblems.Erdos251.primeDisplayedDyadicTerm
noncomputable abbrev primeGapDyadicTerm :=
  ErdosProblems.Erdos251.primeGapDyadicTerm

theorem prime0_le_polynomial (n : ℕ) :
    prime0 n ≤ 1250 * (n + 1) ^ 4 :=
  ErdosProblems.Erdos251.prime0_le_polynomial n

theorem primeSeries_summable : Summable primeDyadicTerm :=
  ErdosProblems.Erdos251.summable_primeDyadicTerm

theorem primeGapSeries_summable : Summable primeGapDyadicTerm :=
  ErdosProblems.Erdos251.summable_primeGapDyadicTerm

theorem primeSeries_eq_two_add_primeGapSeries :
    (∑' n : ℕ, primeDyadicTerm n) =
      2 + ∑' n : ℕ, primeGapDyadicTerm n :=
  ErdosProblems.Erdos251.tsum_primeDyadicTerm_eq_two_add_primeGap_unconditional

theorem primeSeries_irrational_iff_primeGapSeries :
    Irrational (∑' n : ℕ, primeDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n) :=
  ErdosProblems.Erdos251.irrational_tsum_primeDyadicTerm_iff_primeGap
    ErdosProblems.Erdos251.summable_primeDyadicTerm

theorem primeDisplayedSeries_eq_four_add_two_primeGapSeries :
    (∑' n : ℕ, primeDisplayedDyadicTerm n) =
      4 + 2 * ∑' n : ℕ, primeGapDyadicTerm n :=
  ErdosProblems.Erdos251.tsum_primeDisplayedDyadicTerm_eq_four_add_two_primeGap
    ErdosProblems.Erdos251.summable_primeDyadicTerm

theorem primeDisplayedSeries_irrational_iff_primeGapSeries :
    Irrational (∑' n : ℕ, primeDisplayedDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n) :=
  ErdosProblems.Erdos251.irrational_tsum_primeDisplayedDyadicTerm_iff_primeGap
    ErdosProblems.Erdos251.summable_primeDyadicTerm

end Erdos249257.ExternalVerification251PrimeGapIdentity
