/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos251.PrimeGapDyadicTail

namespace Erdos249257.ExternalVerification251PrimeGapIdentity

abbrev prime0 := ErdosProblems.Erdos251.prime0
abbrev primeGap0 := ErdosProblems.Erdos251.primeGap0
abbrev primeDyadicTerm := ErdosProblems.Erdos251.primeDyadicTerm
abbrev primeGapDyadicTerm := ErdosProblems.Erdos251.primeGapDyadicTerm

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

end Erdos249257.ExternalVerification251PrimeGapIdentity
