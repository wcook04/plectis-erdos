/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos257PeriodNoncollapse.CertificateKernel

/-!
# Source transport for finite-period noncollapse in Erdős #257

The proof transports the source theorem over the literal rational denominator.
It exposes the constructed coprimality witness and exact multiplicative order
as one result, and the strict denominator-growth corollary as a second result.
-/

namespace Erdos249257.ExternalVerification257FinitePeriodNoncollapse

def finiteErdosSum (F : Finset ℕ) (b : ℕ) : ℚ :=
  ∑ n ∈ F, 1 / ((b : ℚ) ^ n - 1)

theorem finite_period_noncollapse_rat_den
    (F : Finset ℕ) (b : ℕ)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b) :
    ∃ hcop : Nat.Coprime b (finiteErdosSum F b).den,
      orderOf (ZMod.unitOfCoprime b hcop) = F.lcm id := by
  have hcop : Nat.Coprime b (finiteErdosSum F b).den := by
    simpa [finiteErdosSum,
      Erdos257PeriodNoncollapse.finiteErdosSum] using
      Erdos257PeriodNoncollapse.coprime_base_den_finiteErdosSum
        F b h0 hb
  refine ⟨hcop, ?_⟩
  simpa [finiteErdosSum,
      Erdos257PeriodNoncollapse.finiteErdosSum] using
      Erdos257PeriodNoncollapse.finite_period_noncollapse_rat_den
        F b hF h0 hb

theorem lcm_lt_den_finiteErdosSum
    (F : Finset ℕ) (b : ℕ)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b)
    (h2 : 2 ≤ F.lcm id) :
    F.lcm id < (finiteErdosSum F b).den := by
  simpa [finiteErdosSum,
      Erdos257PeriodNoncollapse.finiteErdosSum] using
      Erdos257PeriodNoncollapse.lcm_lt_den_finiteErdosSum
        F b hF h0 hb h2

end Erdos249257.ExternalVerification257FinitePeriodNoncollapse
