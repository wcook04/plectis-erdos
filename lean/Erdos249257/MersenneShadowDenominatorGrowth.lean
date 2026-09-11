import Erdos249257.MersenneShadowCyclotomicNoncollapse
import Mathlib.NumberTheory.Bertrand

/-!
# Quantitative growth of the surviving upper-half Mersenne channels

This module turns T4's channel-product divisibility into an explicit lower
bound for the reduced denominator, while retaining an individual prime-index
channel for the later diagonal-pincer consumer.

The results here are denominator statements only.  They do not rule out
cancellation by the foreign-defect term and therefore do not prove Erdős
#249.
-/

open scoped BigOperators

namespace Erdos249257.MersenneShadowDenominatorGrowth

open MersenneShadowCyclotomicNoncollapse

private theorem two_pow_pred_le_mersenne
    {p : ℕ} (hp : 0 < p) :
    2 ^ (p - 1) ≤ RadicalMobiusShadow.mersenne p := by
  rw [RadicalMobiusShadow.mersenne]
  have hlt : 2 ^ (p - 1) < 2 ^ p :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

/-- Every selected channel dominates its corresponding predecessor power of
two, independently of any prime-distribution estimate. -/
theorem upperHalfMersenneProduct_factorwise_lower_bound (t : ℕ) :
    (∏ p ∈ upperHalfPrimes t, 2 ^ (p - 1)) ≤
      ∏ p ∈ upperHalfPrimes t, RadicalMobiusShadow.mersenne p := by
  apply Finset.prod_le_prod'
  intro p hp
  exact two_pow_pred_le_mersenne (Finset.mem_filter.mp hp).2.pos

/-- Normalized form of the factorwise bound, retaining the full sum of the
selected prime exponents. -/
theorem upperHalfMersenneProduct_sum_lower_bound (t : ℕ) :
    2 ^ (∑ p ∈ upperHalfPrimes t, (p - 1)) ≤
      ∏ p ∈ upperHalfPrimes t, RadicalMobiusShadow.mersenne p := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact upperHalfMersenneProduct_factorwise_lower_bound t

/-- Bertrand's postulate supplies an upper-half prime at every scale at least
two.  The proof retains the inequality `2 * (t / 2) ≤ t`, which is the correct
odd-`t` endpoint. -/
theorem upperHalfPrimes_nonempty {t : ℕ} (ht : 2 ≤ t) :
    (upperHalfPrimes t).Nonempty := by
  have hn0 : t / 2 ≠ 0 := by omega
  obtain ⟨p, hpPrime, hpLower, hpUpper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (t / 2) hn0
  refine ⟨p, Finset.mem_filter.mpr
    ⟨Finset.mem_Ioc.mpr ⟨hpLower, ?_⟩, hpPrime⟩⟩
  omega

/-- Elementary numerical growth of the full surviving channel product. -/
theorem upperHalfMersenneProduct_lower_bound {t : ℕ} (ht : 5 ≤ t) :
    2 ^ (t / 2) ≤
      ∏ p ∈ upperHalfPrimes t, RadicalMobiusShadow.mersenne p := by
  obtain ⟨p, hp⟩ := upperHalfPrimes_nonempty (by omega : 2 ≤ t)
  have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
  have hpLower : t / 2 < p :=
    (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
  have hfactorOne : ∀ q ∈ upperHalfPrimes t,
      1 ≤ RadicalMobiusShadow.mersenne q := by
    intro q hq
    have hqPrime : q.Prime := (Finset.mem_filter.mp hq).2
    have hpow : 1 < 2 ^ q := Nat.one_lt_two_pow hqPrime.ne_zero
    simp only [RadicalMobiusShadow.mersenne]
    omega
  have hpow : 2 ^ (t / 2) ≤ 2 ^ (p - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hfactor : 2 ^ (p - 1) ≤ RadicalMobiusShadow.mersenne p :=
    two_pow_pred_le_mersenne hpPrime.pos
  have hpProduct : RadicalMobiusShadow.mersenne p ≤
      ∏ q ∈ upperHalfPrimes t, RadicalMobiusShadow.mersenne q :=
    Finset.single_le_prod' hfactorOne hp
  exact hpow.trans (hfactor.trans hpProduct)

/-- T4 plus the elementary product bound gives an explicit lower bound for
the reduced denominator of the scaled LCM-height Möbius shadow. -/
theorem lcmHeight_scaledMobiusShadow_den_lower_bound
    {t : ℕ} (ht : 5 ≤ t) :
    2 ^ (t / 2) ≤
      ((lcmHeight t : ℚ) *
        RadicalMobiusShadow.numericMobiusShadow (lcmHeight t)).den := by
  exact (upperHalfMersenneProduct_lower_bound ht).trans
    (Nat.le_of_dvd
      (Rat.pos ((lcmHeight t : ℚ) *
        RadicalMobiusShadow.numericMobiusShadow (lcmHeight t)))
      (lcmHeight_upperHalf_product_dvd_den ht))

/-- A concrete upper-half channel survives in the reduced denominator, with
both the lower size bound used for growth and the upper bit-scale bound needed
by a later discrete channel-separation argument. -/
theorem exists_upperHalf_mersenne_channel_dvd_den_with_bounds
    {t : ℕ} (ht : 5 ≤ t) :
    ∃ p ∈ upperHalfPrimes t,
      2 ^ (t / 2) ≤ RadicalMobiusShadow.mersenne p ∧
      RadicalMobiusShadow.mersenne p < 2 ^ t ∧
      RadicalMobiusShadow.mersenne p ∣
        ((lcmHeight t : ℚ) *
          RadicalMobiusShadow.numericMobiusShadow (lcmHeight t)).den := by
  obtain ⟨p, hp⟩ := upperHalfPrimes_nonempty (by omega : 2 ≤ t)
  have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
  have hpBounds := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
  have hpowLower : 2 ^ (t / 2) ≤ 2 ^ (p - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpowUpper : 2 ^ p ≤ 2 ^ t :=
    Nat.pow_le_pow_right (by norm_num) hpBounds.2
  have hmersenneUpper : RadicalMobiusShadow.mersenne p < 2 ^ p := by
    simp only [RadicalMobiusShadow.mersenne]
    have hpos : 0 < 2 ^ p := pow_pos (by norm_num) p
    omega
  have hfactorDvd : RadicalMobiusShadow.mersenne p ∣
      ∏ q ∈ upperHalfPrimes t, RadicalMobiusShadow.mersenne q := by
    exact Finset.dvd_prod_of_mem (fun q ↦ RadicalMobiusShadow.mersenne q) hp
  refine ⟨p, hp, ?_, hmersenneUpper.trans_le hpowUpper,
    hfactorDvd.trans (lcmHeight_upperHalf_product_dvd_den ht)⟩
  exact hpowLower.trans (two_pow_pred_le_mersenne hpPrime.pos)

/-! ## Exact LCM-height denominator -/

private theorem primeFactors_thirty : Nat.primeFactors 30 = {2, 3, 5} := by
  rw [show 30 = 2 * (3 * 5) by norm_num,
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.prime_two.primeFactors,
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    (by norm_num : Nat.Prime 3).primeFactors,
    (by norm_num : Nat.Prime 5).primeFactors]
  ext q
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]

private theorem primeFactors_sixty : Nat.primeFactors 60 = {2, 3, 5} := by
  rw [show 60 = 2 * 30 by norm_num,
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.prime_two.primeFactors, primeFactors_thirty]
  ext q
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
  aesop

/-- The exact reduced denominator at every LCM height.  The numerator is
replaced completely by the scale times the odd Jordan scalar. -/
theorem lcmHeight_scaledMobiusShadow_den_exact (t : ℕ) :
    ((lcmHeight t : ℚ) *
        RadicalMobiusShadow.numericMobiusShadow (lcmHeight t)).den =
      RadicalMobiusShadow.mersenne (lcmRadical t) /
        Nat.gcd (RadicalMobiusShadow.mersenne (lcmRadical t))
          (lcmScale t *
            (CyclicTensorMobiusShadow.oddJordanScalar (lcmRadical t)).natAbs) := by
  rw [RadicalMobiusShadow.scaledMobiusShadow_eq_radicalNumerator
    (lcmHeight t) (lcmHeight_pos t)]
  have hmul :
      ((lcmScale t : ℕ) : ℚ) *
          Rat.divInt
            (RadicalMobiusShadow.mobiusNumerator (lcmRadical t))
            (RadicalMobiusShadow.mersenne (lcmRadical t) : ℤ) =
        Rat.divInt
          ((lcmScale t : ℤ) *
            RadicalMobiusShadow.mobiusNumerator (lcmRadical t))
          (RadicalMobiusShadow.mersenne (lcmRadical t) : ℤ) := by
    rw [Rat.natCast_eq_divInt, Rat.divInt_mul_divInt]
    simp
  change
    (((lcmScale t : ℕ) : ℚ) *
      Rat.divInt
        (RadicalMobiusShadow.mobiusNumerator (lcmRadical t))
        (RadicalMobiusShadow.mersenne (lcmRadical t) : ℤ)).den = _
  rw [hmul]
  exact scaledMobiusNumerator_den_exact
    (RadicalMobiusShadow.squarefreeKernel_squarefree (lcmHeight t))
    (lcmScale t)

/-- Concrete scale and radical at the first nontrivial LCM height. -/
theorem lcmRadical_five_fixture : lcmRadical 5 = 30 := by
  rw [lcmRadical, lcmHeight_five_fixture]
  simp only [RadicalMobiusShadow.squarefreeKernel, primeFactors_sixty]
  norm_num

theorem lcmScale_five_fixture : lcmScale 5 = 2 := by
  rw [lcmScale, lcmHeight_five_fixture, lcmRadical_five_fixture]

/-- At `t = 5`, exact cancellation is `3`, so the denominator is `M₃₀/3`. -/
theorem lcmHeight_five_scaledMobiusShadow_den_exact :
    ((lcmHeight 5 : ℚ) *
        RadicalMobiusShadow.numericMobiusShadow (lcmHeight 5)).den =
      RadicalMobiusShadow.mersenne 30 / 3 := by
  rw [lcmHeight_scaledMobiusShadow_den_exact,
    lcmRadical_five_fixture, lcmScale_five_fixture]
  simp only [CyclicTensorMobiusShadow.oddJordanScalar, primeFactors_thirty]
  norm_num [CyclicTensorMobiusShadow.oddJordanScalar,
    RadicalMobiusShadow.mersenne, Finset.prod_filter]

/-- Boundary regression: at `t = 5` the surviving product is
`(2^3 - 1)(2^5 - 1) = 217`. -/
theorem upperHalfMersenneProduct_five_fixture :
    (∏ p ∈ upperHalfPrimes 5, RadicalMobiusShadow.mersenne p) = 217 := by
  rw [upperHalfPrimes_five_fixture]
  norm_num [RadicalMobiusShadow.mersenne]

#print axioms upperHalfMersenneProduct_factorwise_lower_bound
#print axioms upperHalfMersenneProduct_sum_lower_bound
#print axioms upperHalfPrimes_nonempty
#print axioms upperHalfMersenneProduct_lower_bound
#print axioms lcmHeight_scaledMobiusShadow_den_lower_bound
#print axioms exists_upperHalf_mersenne_channel_dvd_den_with_bounds
#print axioms upperHalfMersenneProduct_five_fixture
#print axioms lcmHeight_scaledMobiusShadow_den_exact
#print axioms lcmHeight_five_scaledMobiusShadow_den_exact

end Erdos249257.MersenneShadowDenominatorGrowth
