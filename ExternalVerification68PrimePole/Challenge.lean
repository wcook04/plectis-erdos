/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #68 finite prime-pole formula

This module states one finite common-denominator identity.  At a positive
maximal `q`-adic exponent among the factorial gaps through `M`, the numerator
of the literal LCM presentation reduces modulo `q` to the LCM cofactor times
the reciprocal sum of the maximal-hit cofactors.

The statement assigns no valuation to the infinite real series.  In
particular, survival of one finite prime-power factor is not an irrationality
theorem for Erdős #68.
-/

namespace Erdos249257.ExternalVerification68PrimePole

open scoped BigOperators

/-- The LCM of the factorial-gap denominators through `M`. -/
def factorialGapPrefixLCM (M : ℕ) : ℕ :=
  (Finset.Icc 2 M).lcm fun n => n.factorial - 1

/-- The numerator obtained by writing the finite reciprocal sum over the
literal prefix LCM. -/
def factorialGapPrefixLCMNumerator (M : ℕ) : ℕ :=
  ∑ n ∈ Finset.Icc 2 M,
    factorialGapPrefixLCM M / (n.factorial - 1)

/-- The indices whose factorial gaps have exact `q`-adic exponent `e`. -/
def factorialGapMaxHits (q M e : ℕ) : Finset ℕ :=
  (Finset.Icc 2 M).filter fun n =>
    q ^ e ∣ n.factorial - 1 ∧
      ¬q ^ (e + 1) ∣ n.factorial - 1

/-- The reciprocal sum, modulo `q`, of the maximal-hit cofactors. -/
def factorialGapPrincipalResidue (q M e : ℕ) : ZMod q :=
  ∑ n ∈ factorialGapMaxHits q M e,
    (((n.factorial - 1) / q ^ e : ℕ) : ZMod q)⁻¹

/-- The finite prime-pole numerator formula at a positive maximal `q`-adic
exponent. -/
theorem factorialGapPrefixLCMNumerator_mod_prime
    {q M e : ℕ}
    (hq : q.Prime)
    (he : 1 ≤ e)
    (hmax :
      ∀ n ∈ Finset.Icc 2 M,
        ¬q ^ (e + 1) ∣ n.factorial - 1)
    (hattain :
      ∃ n ∈ Finset.Icc 2 M,
        q ^ e ∣ n.factorial - 1) :
    (factorialGapPrefixLCMNumerator M : ZMod q) =
      ((factorialGapPrefixLCM M / q ^ e : ℕ) : ZMod q) *
        factorialGapPrincipalResidue q M e := by
  sorry

end Erdos249257.ExternalVerification68PrimePole
