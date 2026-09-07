/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos251.KernelDenominatorFloor

open scoped BigOperators

namespace Erdos249257.ExternalVerification251KernelDenominatorFloor

noncomputable abbrev prime0 := ErdosProblems.Erdos251.prime0
noncomputable abbrev primeGap0 := ErdosProblems.Erdos251.primeGap0
noncomputable abbrev primeDyadicTerm := ErdosProblems.Erdos251.primeDyadicTerm
noncomputable abbrev primeGapDyadicTerm := ErdosProblems.Erdos251.primeGapDyadicTerm
abbrev noSmallDivisor := ErdosProblems.Erdos251.noSmallDivisor
abbrev isPrimeTD := ErdosProblems.Erdos251.isPrimeTD
abbrev primeSumLoop := ErdosProblems.Erdos251.primeSumLoop
abbrev certCheck := ErdosProblems.Erdos251.certCheck
abbrev certX := ErdosProblems.Erdos251.certX
abbrev certC := ErdosProblems.Erdos251.certC
abbrev certU := ErdosProblems.Erdos251.certU
abbrev certV := ErdosProblems.Erdos251.certV
abbrev certU' := ErdosProblems.Erdos251.certU'
abbrev certV' := ErdosProblems.Erdos251.certV'

/-- The kernel re-runs the `10^4` trial-division sieve and decides the six
conditions on the certificate literals. -/
theorem cert_10000 : certCheck certC certU certV certU' certV' certX = true :=
  ErdosProblems.Erdos251.cert_10000

/-- A passing certificate at any truncation index `c ≥ 9` forces every rational
`a / b` equal to the prime series to satisfy `v + v' ≤ b`. -/
theorem den_bound_of_certCheck (c u v u' v' X : ℕ) (hc : 9 ≤ c)
    (h : certCheck c u v u' v' X = true) :
    ∀ (a : ℤ) (b : ℕ), 0 < b → (∑' n, primeDyadicTerm n) = a / b → v + v' ≤ b :=
  ErdosProblems.Erdos251.den_bound_of_certCheck c u v u' v' X hc h

/-- Every rational `a / b` equal to `S` has `b ≥ 2^589 > 10^177`. -/
theorem kernel_denominator_floor (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hS : (∑' n, primeDyadicTerm n) = a / b) : (2 ^ 589 : ℕ) ≤ b :=
  ErdosProblems.Erdos251.kernel_denominator_floor a b hb hS

/-- The same floor for the prime-gap series `S - 2` of Erdős #251. -/
theorem kernel_denominator_floor_primeGap (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hS : (∑' n, primeGapDyadicTerm n) = a / b) : (2 ^ 589 : ℕ) ≤ b :=
  ErdosProblems.Erdos251.kernel_denominator_floor_primeGap a b hb hS

end Erdos249257.ExternalVerification251KernelDenominatorFloor
