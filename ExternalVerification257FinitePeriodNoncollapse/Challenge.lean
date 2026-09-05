/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for finite-period noncollapse in Erdős #257

For every finite nonempty set `F` of positive exponents and every integer base
`b ≥ 2`, let `Q` be the reduced denominator of the literal rational sum

`∑ n ∈ F, 1 / (b^n - 1)`.

The theorem proves that `b` is coprime to `Q`, its multiplicative order modulo
`Q` is exactly `lcm F`, and consequently `Q > lcm F` whenever the lcm is at
least two.  Thus reduction to lowest terms never destroys the full finite
period.  This is a finite-support theorem and does not prove the universal
infinite-support assertion in Erdős #257.
-/

namespace Erdos249257.ExternalVerification257FinitePeriodNoncollapse

/-- The literal finite Erdős sum as a rational number. -/
def finiteErdosSum (F : Finset ℕ) (b : ℕ) : ℚ :=
  ∑ n ∈ F, 1 / ((b : ℚ) ^ n - 1)

/-- Exact finite-period noncollapse over the actual reduced denominator,
including production of the coprimality witness needed to state the order. -/
theorem finite_period_noncollapse_rat_den
    (F : Finset ℕ) (b : ℕ)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b) :
    ∃ hcop : Nat.Coprime b (finiteErdosSum F b).den,
      orderOf (ZMod.unitOfCoprime b hcop) = F.lcm id := by
  sorry

/-- The strict denominator-growth consequence of finite-period noncollapse. -/
theorem lcm_lt_den_finiteErdosSum
    (F : Finset ℕ) (b : ℕ)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b)
    (h2 : 2 ≤ F.lcm id) :
    F.lcm id < (finiteErdosSum F b).den := by
  sorry

end Erdos249257.ExternalVerification257FinitePeriodNoncollapse
