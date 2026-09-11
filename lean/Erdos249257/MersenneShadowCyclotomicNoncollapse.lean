import Erdos249257.CyclicTensorMobiusShadow
import Erdos249257.RationalDenominatorSurvival
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Tactic

/-!
# Upper-half Mersenne channel noncollapse

This module owns the scale-aware form of T4.  For a finite family of
upper-half primes, its pairwise-coprime Mersenne product `C` contributes
`C / gcd C h` to the reduced denominator after scaling by `h`.  The full
product is exposed only under an explicit proof that the scale is coprime to
`C` (or the sufficient prime-support bound).  No blanket coprimality claim
about arbitrary integer cyclotomic evaluations is used.
-/

open scoped BigOperators

namespace Erdos249257.MersenneShadowCyclotomicNoncollapse

open CyclotomicProjectionOfShadow
open CyclicTensorMobiusShadow

/-! ## Exact base-two local arithmetic -/

/-- The natural geometric sum appearing after evaluating a cyclic subgroup
sum at `X = 2`. -/
def baseTwoRepunit (r q : ℕ) : ℕ :=
  ∑ j ∈ Finset.range q, (2 ^ (r / q)) ^ j

private theorem baseTwoRepunit_mul (r q : ℕ) :
    baseTwoRepunit r q * (2 ^ (r / q) - 1) =
      (2 ^ (r / q)) ^ q - 1 := by
  exact geom_sum_mul_of_one_le (one_le_pow₀ (by norm_num)) q

/-- Concrete evaluation of the local numerator factor. -/
theorem localNumeratorValue_eq (r q : ℕ) :
    localNumeratorValue r q =
      (q : ℤ) * (baseTwoRepunit r q : ℕ) - 1 := by
  simp [localNumeratorValue, localNumeratorFactor, subgroupSum,
    RepunitMobiusNumerator.spacedRepunit, Polynomial.eval_finset_sum,
    baseTwoRepunit, pow_mul]

/-- Concrete evaluation of the integral local cofactor. -/
theorem localCofactorValue_eq (r q : ℕ) :
    localCofactorValue r q =
      (q : ℤ) * (baseTwoRepunit r q : ℕ) - ((q : ℤ) ^ 2 - 1) := by
  simp [localCofactorValue, localCofactorFactor, subgroupSum,
    RepunitMobiusNumerator.spacedRepunit, Polynomial.eval_finset_sum,
    baseTwoRepunit, pow_mul]

/-- For odd prime `q`, the evaluated subgroup sum is coprime to `q² - 1`.
The proof uses the order of `2^(r/q)` modulo a hypothetical common prime. -/
theorem baseTwoRepunit_coprime_prime_sq_sub_one
    {r q : ℕ} (hq : q.Prime) (hqodd : q ≠ 2) :
    Nat.Coprime (baseTwoRepunit r q) (q ^ 2 - 1) := by
  have hq2 : 2 ≤ q := hq.two_le
  apply Nat.coprime_of_dvd
  intro ℓ hℓ hℓS hℓtarget
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  letI : Fact q.Prime := ⟨hq⟩
  letI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hSzero : (baseTwoRepunit r q : ZMod ℓ) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hℓS
  have hxzero : ((2 ^ (r / q) : ℕ) : ZMod ℓ) ≠ 0 := by
    intro hx0
    have hSone : (baseTwoRepunit r q : ZMod ℓ) = 1 := by
      simp [baseTwoRepunit, hx0, hq.ne_zero]
    exact zero_ne_one (hSzero.symm.trans hSone)
  have hxpow : ((2 ^ (r / q) : ℕ) : ZMod ℓ) ^ q = 1 := by
    have hgeom := geom_sum_mul (((2 ^ (r / q) : ℕ) : ZMod ℓ)) q
    have hsum :
        (∑ i ∈ Finset.range q,
          (((2 ^ (r / q) : ℕ) : ZMod ℓ)) ^ i) = 0 := by
      simpa [baseTwoRepunit] using hSzero
    rw [hsum, zero_mul] at hgeom
    exact sub_eq_zero.mp hgeom.symm
  have hxone : ((2 ^ (r / q) : ℕ) : ZMod ℓ) ≠ 1 := by
    intro hx1
    have hqzero : (q : ZMod ℓ) = 0 := by
      simpa [baseTwoRepunit, hx1] using hSzero
    have hℓq : ℓ ∣ q := (ZMod.natCast_eq_zero_iff q ℓ).mp hqzero
    have hℓeq : ℓ = q :=
      (Nat.dvd_prime hq).mp hℓq |>.resolve_left hℓ.ne_one
    subst ℓ
    have hqpow : q ∣ q ^ 2 := dvd_pow_self q (by omega)
    have hqone : q ∣ 1 := by
      have h := Nat.dvd_sub hqpow hℓtarget
      have hdiff : q ^ 2 - (q ^ 2 - 1) = 1 :=
        Nat.sub_sub_self (one_le_pow₀ (by omega : 1 ≤ q))
      rw [hdiff] at h
      exact h
    exact hq.ne_one (Nat.dvd_one.mp hqone)
  have horder : orderOf (((2 ^ (r / q) : ℕ) : ZMod ℓ)) = q :=
    orderOf_eq_prime hxpow hxone
  have hqℓ : q ∣ ℓ - 1 := by
    have hd := ZMod.orderOf_dvd_card_sub_one hxzero
    rw [horder] at hd
    exact hd
  have hqle : q ≤ ℓ - 1 :=
    Nat.le_of_dvd (Nat.sub_pos_of_lt hℓ.one_lt) hqℓ
  have hfactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    simpa [pow_two, mul_comm] using (mul_self_tsub_one q)
  rw [hfactor] at hℓtarget
  have hℓle : ℓ ≤ q + 1 := by
    rcases hℓ.dvd_mul.mp hℓtarget with hminus | hplus
    · exact (Nat.le_of_dvd (Nat.sub_pos_of_lt hq.one_lt) hminus).trans
        ((Nat.sub_le q 1).trans (Nat.le_add_right q 1))
    · exact Nat.le_of_dvd (Nat.zero_lt_succ q) hplus
  have hℓeq : ℓ = q + 1 := by omega
  have hqOdd : Odd q := Nat.odd_iff.mpr
    (hq.eq_two_or_odd.resolve_left hqodd)
  have heven : Even ℓ := by
    rw [hℓeq]
    exact hqOdd.add_one
  have hℓtwo : ℓ = 2 := hℓ.even_iff.mp heven
  omega

/-- Every odd-prime evaluated local cofactor is coprime to the full Mersenne
modulus. -/
theorem localCofactorValue_coprime_mersenne
    {r q : ℕ} (hq : q.Prime) (hqodd : q ≠ 2) (hqr : q ∣ r) :
    Nat.Coprime (localCofactorValue r q).natAbs
      (RadicalMobiusShadow.mersenne r) := by
  apply Nat.coprime_of_dvd
  intro ℓ hℓ hℓB
  intro hℓM
  have hdiv : r / q * q = r := Nat.div_mul_cancel hqr
  have hM : RadicalMobiusShadow.mersenne r =
      baseTwoRepunit r q * (2 ^ (r / q) - 1) := by
    unfold RadicalMobiusShadow.mersenne
    calc
      2 ^ r - 1 = (2 ^ (r / q)) ^ q - 1 := by rw [← pow_mul, hdiv]
      _ = baseTwoRepunit r q * (2 ^ (r / q) - 1) :=
        (baseTwoRepunit_mul r q).symm
  rw [hM] at hℓM
  rcases hℓ.dvd_mul.mp hℓM with hℓS | hℓx
  · have hℓBZ : (ℓ : ℤ) ∣ localCofactorValue r q := by
      rw [← Int.natAbs_dvd_natAbs]
      simpa using hℓB
    have hℓSZ : (ℓ : ℤ) ∣ (baseTwoRepunit r q : ℕ) :=
      Int.natCast_dvd_natCast.mpr hℓS
    have hℓprod : (ℓ : ℤ) ∣
        (q : ℤ) * (baseTwoRepunit r q : ℕ) :=
      dvd_mul_of_dvd_right hℓSZ (q : ℤ)
    have hℓtargetZ : (ℓ : ℤ) ∣ ((q : ℤ) ^ 2 - 1) := by
      have h := Int.dvd_sub hℓprod hℓBZ
      rw [localCofactorValue_eq] at h
      simpa only [sub_sub_cancel] using h
    have hℓtarget : ℓ ∣ q ^ 2 - 1 := by
      rw [← Int.natCast_dvd_natCast]
      have hcast : ((q ^ 2 - 1 : ℕ) : ℤ) = (q : ℤ) ^ 2 - 1 := by
        rw [Int.natCast_sub (one_le_pow₀ hq.one_le)]
        norm_num
      rw [hcast]
      exact hℓtargetZ
    exact hℓ.ne_one (Nat.eq_one_of_dvd_coprimes
      (baseTwoRepunit_coprime_prime_sq_sub_one hq hqodd)
      hℓS hℓtarget)
  · letI : Fact ℓ.Prime := ⟨hℓ⟩
    letI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hBzero : (localCofactorValue r q : ZMod ℓ) = 0 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
      rw [← Int.natAbs_dvd_natAbs]
      simpa using hℓB
    have hxone : ((2 ^ (r / q) : ℕ) : ZMod ℓ) = 1 := by
      have hxsub : ((2 ^ (r / q) - 1 : ℕ) : ZMod ℓ) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr hℓx
      rw [Nat.cast_sub (one_le_pow₀ (by norm_num)), Nat.cast_one] at hxsub
      exact sub_eq_zero.mp hxsub
    rw [localCofactorValue_eq] at hBzero
    push_cast at hBzero
    simp [baseTwoRepunit, hxone] at hBzero
    have hone : (1 : ZMod ℓ) = 0 := by
      calc
        1 = (q : ZMod ℓ) * q - ((q : ZMod ℓ) ^ 2 - 1) := by ring
        _ = 0 := hBzero
    exact one_ne_zero hone

/-- Unit form of `localCofactorValue_coprime_mersenne`. -/
theorem localCofactorValue_isUnit_mod_mersenne
    {r q : ℕ} (hq : q.Prime) (hqodd : q ≠ 2) (hqr : q ∣ r) :
    IsUnit (localCofactorValue r q : ZMod (RadicalMobiusShadow.mersenne r)) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_nat_coprime]
  simpa [Nat.coprime_comm] using
    (localCofactorValue_coprime_mersenne hq hqodd hqr)

/-- At the binary prime, squarefreeness makes `r / 2` odd, and the numerator
factor `2 * 2^(r/2) + 1` is coprime to the full Mersenne modulus. -/
theorem localNumeratorValue_two_coprime_mersenne
    {r : ℕ} (hr : Squarefree r) (h2r : 2 ∣ r) :
    Nat.Coprime (localNumeratorValue r 2).natAbs
      (RadicalMobiusShadow.mersenne r) := by
  let n := r / 2
  let x := 2 ^ n
  have hdiv : n * 2 = r := Nat.div_mul_cancel h2r
  have hnodd : Odd n := by
    rw [← Nat.not_even_iff_odd]
    intro hneven
    obtain ⟨k, hk⟩ := hneven
    have hsq : 2 * 2 ∣ r := by
      refine ⟨k, ?_⟩
      omega
    have hu : IsUnit (2 : ℕ) := hr 2 hsq
    norm_num at hu
  have hA : localNumeratorValue r 2 = (2 * x + 1 : ℕ) := by
    rw [localNumeratorValue_eq]
    simp [baseTwoRepunit, x, n]
    ring
  have hAabs : (localNumeratorValue r 2).natAbs = 2 * x + 1 := by
    rw [hA]
    simp only [Int.natAbs_natCast]
  rw [hAabs]
  apply Nat.coprime_of_dvd
  intro ℓ hℓ hℓA
  intro hℓM
  have hM : RadicalMobiusShadow.mersenne r =
      (x - 1) * (x + 1) := by
    unfold RadicalMobiusShadow.mersenne
    calc
      2 ^ r - 1 = x ^ 2 - 1 := by rw [← hdiv, pow_mul]
      _ = (x - 1) * (x + 1) := by
        simpa [pow_two, mul_comm] using (mul_self_tsub_one x)
  rw [hM] at hℓM
  rcases hℓ.dvd_mul.mp hℓM with hminus | hplus
  · have hprod : ℓ ∣ 2 * (x - 1) := dvd_mul_of_dvd_right hminus 2
    have hthree : ℓ ∣ 3 := by
      have h := Nat.dvd_sub hℓA hprod
      have hxpos : 0 < x := pow_pos (by norm_num) n
      have hdiff : 2 * x + 1 - 2 * (x - 1) = 3 := by omega
      rwa [hdiff] at h
    have hℓeq : ℓ = 3 :=
      (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hthree
        |>.resolve_left hℓ.ne_one
    subst ℓ
    have hx3 : (x : ZMod 3) = 2 := by
      rcases hnodd with ⟨k, hk⟩
      calc
        (x : ZMod 3) = (2 : ZMod 3) ^ (2 * k + 1) := by simp [x, hk]
        _ = ((2 : ZMod 3) ^ 2) ^ k * 2 := by rw [pow_add, pow_mul, pow_one]
        _ = 2 := by rw [show (2 : ZMod 3) ^ 2 = 1 by decide]; simp
    have hAzero : ((2 * x + 1 : ℕ) : ZMod 3) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hℓA
    push_cast at hAzero
    rw [hx3] at hAzero
    have hcalc : 2 * (2 : ZMod 3) + 1 = 2 := by decide
    rw [hcalc] at hAzero
    exact (by decide : (2 : ZMod 3) ≠ 0) hAzero
  · have hprod : ℓ ∣ 2 * (x + 1) := dvd_mul_of_dvd_right hplus 2
    have hone : ℓ ∣ 1 := by
      have h := Nat.dvd_sub hprod hℓA
      have hdiff : 2 * (x + 1) - (2 * x + 1) = 1 := by omega
      rwa [hdiff] at h
    exact hℓ.ne_one (Nat.dvd_one.mp hone)

/-- Unit form of the squarefree binary numerator theorem. -/
theorem localNumeratorValue_two_isUnit_mod_mersenne
    {r : ℕ} (hr : Squarefree r) (h2r : 2 ∣ r) :
    IsUnit (localNumeratorValue r 2 :
      ZMod (RadicalMobiusShadow.mersenne r)) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_nat_coprime]
  simpa [Nat.coprime_comm] using
    (localNumeratorValue_two_coprime_mersenne hr h2r)

/-- Squarefreeness is essential: at `r = 4`, the binary numerator factor has
gcd `3` with `2^4 - 1`. -/
theorem localNumeratorValue_four_gcd :
    Nat.gcd (localNumeratorValue 4 2).natAbs
      (RadicalMobiusShadow.mersenne 4) = 3 := by
  norm_num [localNumeratorValue_eq, baseTwoRepunit,
    RadicalMobiusShadow.mersenne]

/-- Evaluation of the integral local adjugate identity in the Mersenne
quotient. -/
theorem localNumerator_mul_localCofactor_mod_mersenne
    {r q : ℕ} (hqr : q ∣ r) :
    (localNumeratorValue r q : ZMod (RadicalMobiusShadow.mersenne r)) *
      localCofactorValue r q = ((q : ℤ) ^ 2 - 1 : ℤ) := by
  have hpoly :=
    cyclicModulus_dvd_localNumerator_mul_localCofactor_sub_scalar hqr
  have heval := map_dvd (Polynomial.evalRingHom (R := ℤ) 2) hpoly
  change (cyclicModulus r).eval 2 ∣
    (localNumeratorFactor r q * localCofactorFactor r q -
      Polynomial.C ((q : ℤ) ^ 2 - 1)).eval 2 at heval
  have hdiv : (RadicalMobiusShadow.mersenne r : ℤ) ∣
      localNumeratorValue r q * localCofactorValue r q -
        ((q : ℤ) ^ 2 - 1) := by
    simpa [cyclicModulus, RadicalMobiusShadow.mersenne,
      Nat.cast_sub (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))),
      localNumeratorValue, localCofactorValue] using heval
  have hz : ((localNumeratorValue r q * localCofactorValue r q -
      ((q : ℤ) ^ 2 - 1) : ℤ) :
        ZMod (RadicalMobiusShadow.mersenne r)) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiv
  push_cast at hz
  push_cast
  exact sub_eq_zero.mp hz

/-- Prime-by-prime, the numerator factor product is associated to the odd
Jordan scalar in the Mersenne quotient.  The binary factor contributes only
a unit. -/
theorem localNumeratorProduct_associated_oddJordanScalar
    {r : ℕ} (hr : Squarefree r) :
    Associated
      ((∏ q ∈ r.primeFactors, localNumeratorValue r q : ℤ) :
        ZMod (RadicalMobiusShadow.mersenne r))
      (oddJordanScalar r : ZMod (RadicalMobiusShadow.mersenne r)) := by
  classical
  let M := RadicalMobiusShadow.mersenne r
  have hlocal : ∀ q ∈ r.primeFactors,
      Associated
        (localNumeratorValue r q : ZMod M)
        (if q = 2 then 1 else (((q : ℤ) ^ 2 - 1 : ℤ) : ZMod M)) := by
    intro q hqmem
    have hq : q.Prime := Nat.prime_of_mem_primeFactors hqmem
    have hqr : q ∣ r := Nat.dvd_of_mem_primeFactors hqmem
    by_cases hq2 : q = 2
    · subst q
      exact associated_one_iff_isUnit.mpr
        (localNumeratorValue_two_isUnit_mod_mersenne hr hqr)
    · simp only [if_neg hq2]
      have hB : IsUnit (localCofactorValue r q : ZMod M) :=
        localCofactorValue_isUnit_mod_mersenne hq hq2 hqr
      refine ⟨hB.unit, ?_⟩
      simpa only [IsUnit.unit_spec] using
        (localNumerator_mul_localCofactor_mod_mersenne hqr)
  have hprod := Associated.prod r.primeFactors
    (fun q ↦ (localNumeratorValue r q : ZMod M))
    (fun q ↦ if q = 2 then 1 else (((q : ℤ) ^ 2 - 1 : ℤ) : ZMod M))
    hlocal
  simpa [M, oddJordanScalar, Finset.prod_filter] using hprod

/-- Base-two unit normal form: the full Möbius numerator is associated to
the product of the odd-prime scalars modulo the Mersenne denominator. -/
theorem mobiusNumerator_associated_oddJordanScalar
    {r : ℕ} (hr : Squarefree r) :
    Associated
      (RadicalMobiusShadow.mobiusNumerator r :
        ZMod (RadicalMobiusShadow.mersenne r))
      (oddJordanScalar r : ZMod (RadicalMobiusShadow.mersenne r)) := by
  have hdiv := mersenne_dvd_mobiusNumerator_sub_localNumeratorProduct hr
  have hz : ((RadicalMobiusShadow.mobiusNumerator r -
      ∏ q ∈ r.primeFactors, localNumeratorValue r q : ℤ) :
        ZMod (RadicalMobiusShadow.mersenne r)) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiv
  push_cast at hz
  have heq' :
      (RadicalMobiusShadow.mobiusNumerator r :
        ZMod (RadicalMobiusShadow.mersenne r)) =
      ∏ q ∈ r.primeFactors,
        (localNumeratorValue r q : ZMod (RadicalMobiusShadow.mersenne r)) :=
    sub_eq_zero.mp hz
  have heq :
      (RadicalMobiusShadow.mobiusNumerator r :
        ZMod (RadicalMobiusShadow.mersenne r)) =
      ((∏ q ∈ r.primeFactors, localNumeratorValue r q : ℤ) :
        ZMod (RadicalMobiusShadow.mersenne r)) := by
    simpa using heq'
  exact (Associated.of_eq heq).trans
    (localNumeratorProduct_associated_oddJordanScalar hr)

private theorem associated_modulus_dvd_natAbs
    {a b : ℤ} {M d : ℕ} (hdM : d ∣ M)
    (hassoc : Associated (a : ZMod M) (b : ZMod M))
    (hda : d ∣ a.natAbs) : d ∣ b.natAbs := by
  have hassocd := hassoc.map (ZMod.castHom hdM (ZMod d))
  have hdaZ : (d : ℤ) ∣ a := by
    rw [← Int.natAbs_dvd_natAbs]
    simpa using hda
  have ha0 : (a : ZMod d) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdaZ
  have hmapa0 : ZMod.castHom hdM (ZMod d) (a : ZMod M) = 0 := by
    simpa using ha0
  have hmapb0 : ZMod.castHom hdM (ZMod d) (b : ZMod M) = 0 :=
    hassocd.eq_zero_iff.mp hmapa0
  have hb0 : (b : ZMod d) = 0 := by simpa using hmapb0
  have hdbZ : (d : ℤ) ∣ b :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb0
  rw [← Int.natAbs_dvd_natAbs] at hdbZ
  simpa using hdbZ

private theorem associated_modulus_dvd_natAbs_iff
    {a b : ℤ} {M d : ℕ} (hdM : d ∣ M)
    (hassoc : Associated (a : ZMod M) (b : ZMod M)) :
    d ∣ a.natAbs ↔ d ∣ b.natAbs :=
  ⟨associated_modulus_dvd_natAbs hdM hassoc,
    associated_modulus_dvd_natAbs hdM hassoc.symm⟩

/-- Associated residue classes have exactly the same gcd with the modulus. -/
theorem gcd_natAbs_eq_of_associated_mod
    {a b : ℤ} {M : ℕ}
    (hassoc : Associated (a : ZMod M) (b : ZMod M)) :
    Nat.gcd a.natAbs M = Nat.gcd b.natAbs M := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · exact (associated_modulus_dvd_natAbs_iff
        (Nat.gcd_dvd_right a.natAbs M) hassoc).mp
        (Nat.gcd_dvd_left a.natAbs M)
    · exact Nat.gcd_dvd_right a.natAbs M
  · apply Nat.dvd_gcd
    · exact (associated_modulus_dvd_natAbs_iff
        (Nat.gcd_dvd_right b.natAbs M) hassoc).mpr
        (Nat.gcd_dvd_left b.natAbs M)
    · exact Nat.gcd_dvd_right b.natAbs M

/-- Exact cancellation after an arbitrary natural scale: the giant Möbius
numerator may be replaced by the small odd Jordan scalar inside the gcd. -/
theorem scaledMobiusNumerator_gcd_eq_oddJordanScalar
    {r : ℕ} (hr : Squarefree r) (h : ℕ) :
    Nat.gcd
        (((h : ℤ) * RadicalMobiusShadow.mobiusNumerator r).natAbs)
        (RadicalMobiusShadow.mersenne r) =
      Nat.gcd (h * (oddJordanScalar r).natAbs)
        (RadicalMobiusShadow.mersenne r) := by
  have hassoc := (mobiusNumerator_associated_oddJordanScalar hr).mul_left
    (h : ZMod (RadicalMobiusShadow.mersenne r))
  have hassoc' : Associated
      (((h : ℤ) * RadicalMobiusShadow.mobiusNumerator r : ℤ) :
        ZMod (RadicalMobiusShadow.mersenne r))
      (((h : ℤ) * oddJordanScalar r : ℤ) :
        ZMod (RadicalMobiusShadow.mersenne r)) := by
    simpa using hassoc
  have hgcd := gcd_natAbs_eq_of_associated_mod hassoc'
  simpa [Int.natAbs_mul] using hgcd

/-- The unscaled exact cancellation formula. -/
theorem mobiusNumerator_gcd_eq_oddJordanScalar
    {r : ℕ} (hr : Squarefree r) :
    Nat.gcd (RadicalMobiusShadow.mobiusNumerator r).natAbs
        (RadicalMobiusShadow.mersenne r) =
      Nat.gcd (oddJordanScalar r).natAbs
        (RadicalMobiusShadow.mersenne r) := by
  simpa using scaledMobiusNumerator_gcd_eq_oddJordanScalar hr 1

/-- Exact reduced denominator of every naturally scaled base-two Möbius
shadow. -/
theorem scaledMobiusNumerator_den_exact
    {r : ℕ} (hr : Squarefree r) (h : ℕ) :
    (Rat.divInt
      ((h : ℤ) * RadicalMobiusShadow.mobiusNumerator r)
      (RadicalMobiusShadow.mersenne r : ℤ)).den =
      RadicalMobiusShadow.mersenne r /
        Nat.gcd (RadicalMobiusShadow.mersenne r)
          (h * (oddJordanScalar r).natAbs) := by
  have hM : RadicalMobiusShadow.mersenne r ≠ 0 := by
    simp only [RadicalMobiusShadow.mersenne, Nat.sub_ne_zero_iff_lt]
    exact Nat.one_lt_two_pow hr.ne_zero
  rw [Rat.den_divInt, if_neg (Int.natCast_ne_zero.mpr hM)]
  simp only [Int.natAbs_natCast, Int.gcd_eq_natAbs]
  rw [Nat.gcd_comm,
    scaledMobiusNumerator_gcd_eq_oddJordanScalar hr h,
    Nat.gcd_comm]

/-- A prime divisor of a prime-index Mersenne number is above every scale
strictly below `2p`.  The extra factor two comes from oddness of the divisor. -/
theorem prime_dvd_mersenne_gt_scale
    {t p ℓ : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (htp : t < 2 * p)
    (hℓ : ℓ.Prime)
    (hℓM : ℓ ∣ RadicalMobiusShadow.mersenne p) :
    t < ℓ := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  letI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hℓne2 : ℓ ≠ 2 := by
    intro h
    subst ℓ
    rw [Nat.dvd_iff_mod_eq_zero] at hℓM
    simp [RadicalMobiusShadow.mersenne, hp.ne_zero] at hℓM
  have h2ℓ : ¬ℓ ∣ 2 := by
    intro h
    rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h2
    · exact hℓ.ne_one h1
    · exact hℓne2 h2
  have hpow : (2 : ZMod ℓ) ^ p = 1 := by
    have hpowNat : 1 ≤ 2 ^ p := by exact one_le_pow₀ (by norm_num)
    have hz : ((RadicalMobiusShadow.mersenne p : ℕ) : ZMod ℓ) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hℓM
    rw [RadicalMobiusShadow.mersenne, Nat.cast_sub hpowNat,
      Nat.cast_pow, Nat.cast_ofNat] at hz
    exact sub_eq_zero.mp (by simpa using hz)
  have h2ne1 : (2 : ZMod ℓ) ≠ 1 := by
    intro h
    have hz : (1 : ZMod ℓ) = 0 := by
      calc
        (1 : ZMod ℓ) = 2 - 1 := by norm_num
        _ = 0 := sub_eq_zero.mpr h
    exact one_ne_zero hz
  have horder : orderOf (2 : ZMod ℓ) = p :=
    orderOf_eq_prime hpow h2ne1
  have h2ne0 : (2 : ZMod ℓ) ≠ 0 := by
    intro hz
    exact h2ℓ ((ZMod.natCast_eq_zero_iff 2 ℓ).mp hz)
  have hpℓ : p ∣ ℓ - 1 := by
    have := ZMod.orderOf_dvd_card_sub_one h2ne0
    simpa [horder] using this
  have h2pred : 2 ∣ ℓ - 1 := by
    have hodd : Odd ℓ := Nat.odd_iff.mpr
      (hℓ.eq_two_or_odd.resolve_left hℓne2)
    obtain ⟨k, hk⟩ := hodd
    refine ⟨k, ?_⟩
    omega
  have hcop : Nat.Coprime 2 p := by
    exact Nat.coprime_two_left.mpr <| Nat.odd_iff.mpr
      (hp.eq_two_or_odd.resolve_left (by omega))
  have htwop : 2 * p ∣ ℓ - 1 :=
    hcop.mul_dvd_of_dvd_of_dvd h2pred hpℓ
  have hle : 2 * p ≤ ℓ - 1 :=
    Nat.le_of_dvd (Nat.sub_pos_of_lt hℓ.one_lt) htwop
  omega

/-- Strong form of `prime_dvd_mersenne_gt_scale`: a prime factor of a
prime-index Mersenne number is at least `2p + 1` for odd prime `p`. -/
theorem prime_dvd_mersenne_lower_bound
    {p ℓ : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hℓ : ℓ.Prime)
    (hℓM : ℓ ∣ RadicalMobiusShadow.mersenne p) :
    2 * p + 1 ≤ ℓ := by
  have hbase : 2 * p - 1 < ℓ :=
    prime_dvd_mersenne_gt_scale hp hp3 (by omega) hℓ hℓM
  have hℓne2 : ℓ ≠ 2 := by omega
  have hodd : Odd ℓ :=
    Nat.odd_iff.mpr (hℓ.eq_two_or_odd.resolve_left hℓne2)
  obtain ⟨k, hk⟩ := hodd
  omega

/-- Any natural number supported on primes at most `t` is coprime to the
upper-half Mersenne channel. -/
theorem coprime_mersenne_of_primeFactors_le
    {t p a : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (htp : t < 2 * p)
    (ha : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ a → ℓ ≤ t) :
    Nat.Coprime a (RadicalMobiusShadow.mersenne p) := by
  apply Nat.coprime_of_dvd
  intro ℓ hℓ hℓa hℓM
  exact (not_lt_of_ge (ha ℓ hℓ hℓa))
    (prime_dvd_mersenne_gt_scale hp hp3 htp hℓ hℓM)

/-- The supported natural factor is a unit in the upper-half Mersenne
channel. -/
theorem isUnit_mod_mersenne_of_primeFactors_le
    {t p a : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (htp : t < 2 * p)
    (ha : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ a → ℓ ≤ t) :
    IsUnit (a : ZMod (RadicalMobiusShadow.mersenne p)) := by
  exact (ZMod.isUnit_iff_coprime _ _).mpr
    (coprime_mersenne_of_primeFactors_le hp hp3 htp ha)

/-- The abstract residue target supplied by T2 after inverting the geometric
cofactor. -/
noncomputable def upperHalfUnitTarget (h n p : ℕ) (j : ℤ) :
    ZMod (RadicalMobiusShadow.mersenne p) :=
  -(h : ZMod (RadicalMobiusShadow.mersenne p)) *
    (j : ZMod (RadicalMobiusShadow.mersenne p)) *
      (n : ZMod (RadicalMobiusShadow.mersenne p))⁻¹

/-- Once the three arithmetic factors have no prime support above `t`, the
T2 target is a unit in every prime channel with `t < 2p`.  This packages the
unit argument without pretending the LCM-height factor bounds are already
wired. -/
theorem upperHalfUnitTarget_isUnit_of_primeFactors_le
    {t p h n : ℕ} {j : ℤ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (htp : t < 2 * p)
    (hh : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ h → ℓ ≤ t)
    (hn : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ℓ ≤ t)
    (hj : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ j.natAbs → ℓ ≤ t) :
    IsUnit (upperHalfUnitTarget h n p j) := by
  have hhUnit :
      IsUnit (h : ZMod (RadicalMobiusShadow.mersenne p)) :=
    isUnit_mod_mersenne_of_primeFactors_le hp hp3 htp hh
  have hnUnit :
      IsUnit (n : ZMod (RadicalMobiusShadow.mersenne p)) :=
    isUnit_mod_mersenne_of_primeFactors_le hp hp3 htp hn
  have hjCop : Nat.Coprime j.natAbs (RadicalMobiusShadow.mersenne p) :=
    coprime_mersenne_of_primeFactors_le hp hp3 htp hj
  have hjIntCop : IsCoprime (RadicalMobiusShadow.mersenne p : ℤ) j := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa [Nat.coprime_comm] using hjCop
  have hjUnit :
      IsUnit (j : ZMod (RadicalMobiusShadow.mersenne p)) :=
    (ZMod.coe_int_isUnit_iff_isCoprime j
      (RadicalMobiusShadow.mersenne p)).mpr hjIntCop
  have hnInvUnit :
      IsUnit ((n : ZMod (RadicalMobiusShadow.mersenne p))⁻¹) := by
    have hnIntUnit :
        IsUnit (((n : ℤ) : ZMod (RadicalMobiusShadow.mersenne p))) := by
      simpa only [Int.cast_natCast] using hnUnit
    simpa only [Int.cast_natCast] using ZMod.isUnit_inv hnIntUnit
  exact hhUnit.neg.mul hjUnit |>.mul hnInvUnit

/-! ## Exact rational denominator survival under scaling -/

/-- A divisor of a displayed denominator survives rational reduction when
it is coprime to the displayed numerator. -/
theorem divisor_dvd_divInt_den
    {a : ℤ} {D m : ℕ} (hD : 0 < D) (hmD : m ∣ D)
    (hcop : Nat.Coprime m a.natAbs) :
    m ∣ (Rat.divInt a (D : ℤ)).den :=
  RationalDenominatorSurvival.divisor_dvd_divInt_den hD hmD hcop

/-- Exact scale-aware survivor: scaling can cancel the part `gcd C h`, but
cannot cancel any further part of `C` when `C` was coprime to the unscaled
numerator. -/
theorem survivingDivisor_dvd_scaled_divInt_den
    {a : ℤ} {D C h : ℕ} (hD : 0 < D) (hCD : C ∣ D)
    (hcop : Nat.Coprime C a.natAbs) :
    C / Nat.gcd C h ∣
      (Rat.divInt ((h : ℤ) * a) (D : ℤ)).den :=
  RationalDenominatorSurvival.survivingDivisor_dvd_scaled_divInt_den
    hD hCD hcop

/-! ## T2 prime channels and their aggregate product -/

theorem jordanTotientTwo_natAbs_eq_prod {n : ℕ} (hn : Squarefree n) :
    (jordanTotientTwo n).natAbs =
      ∏ q ∈ n.primeFactors, (q ^ 2 - 1) := by
  rw [jordanTotientTwo_eq_prod_primeFactors hn]
  change Int.natAbsHom (∏ p ∈ n.primeFactors, ((p : ℤ) ^ 2 - 1)) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro q hq
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hq2 : 1 ≤ q ^ 2 :=
    one_le_pow₀ (Nat.one_le_iff_ne_zero.mpr hqprime.ne_zero)
  change Int.natAbs ((q : ℤ) ^ 2 - 1) = q ^ 2 - 1
  have hq2Z : (1 : ℤ) ≤ (q : ℤ) ^ 2 := by exact_mod_cast hq2
  have hnonneg : 0 ≤ (q : ℤ) ^ 2 - 1 := by omega
  exact_mod_cast (Int.natAbs_of_nonneg hnonneg)

theorem coprime_mersenne_prime_sq_sub_one
    {t p q : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (htp : t < 2 * p)
    (hq : q.Prime) (hqt : q ≤ t) :
    Nat.Coprime (RadicalMobiusShadow.mersenne p) (q ^ 2 - 1) := by
  apply Nat.coprime_of_dvd
  intro ℓ hℓ hℓM hℓq
  have hstrong : 2 * p < ℓ := by
    have := prime_dvd_mersenne_lower_bound hp hp3 hℓ hℓM
    omega
  have hq2 : 2 ≤ q := hq.two_le
  have hfactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    simpa [pow_two, mul_comm] using (mul_self_tsub_one q)
  rw [hfactor] at hℓq
  rcases hℓ.dvd_mul.mp hℓq with hminus | hplus
  · have hpos : 0 < q - 1 := by omega
    have hle : ℓ ≤ q - 1 := Nat.le_of_dvd hpos hminus
    omega
  · have hpos : 0 < q + 1 := by omega
    have hle : ℓ ≤ q + 1 := Nat.le_of_dvd hpos hplus
    omega

theorem coprime_mersenne_jordanTotientTwo
    {t r p : ℕ} (hr : Squarefree r) (hp : p.Prime) (hp3 : 3 ≤ p)
    (hpr : p ∣ r) (htp : t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t) :
    Nat.Coprime (RadicalMobiusShadow.mersenne p)
      (jordanTotientTwo (r / p)).natAbs := by
  have hquot : r / p ∣ r := Nat.div_dvd_of_dvd hpr
  have hsq : Squarefree (r / p) := hr.squarefree_of_dvd hquot
  rw [jordanTotientTwo_natAbs_eq_prod hsq]
  rw [Nat.coprime_prod_right_iff]
  intro q hq
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
  exact coprime_mersenne_prime_sq_sub_one hp hp3 htp hqprime
    (hcut q hqprime ((Nat.dvd_of_mem_primeFactors hq).trans hquot))

theorem mobiusNumerator_mod_mersenne_prime
    {r p : ℕ} (hr : Squarefree r) (hp : p.Prime) (hpr : p ∣ r) :
    (RadicalMobiusShadow.mersenne p : ℤ) ∣
      RadicalMobiusShadow.mobiusNumerator r + jordanTotientTwo (r / p) := by
  simpa [cyclotomicEval_prime hp,
    ArithmeticFunction.moebius_apply_prime hp] using
      (mobiusNumerator_mod_cyclotomicEval hr hpr)

theorem coprime_natAbs_of_sum_dvd
    {m : ℕ} {a b : ℤ} (hdiv : (m : ℤ) ∣ a + b)
    (hcop : Nat.Coprime m b.natAbs) : Nat.Coprime m a.natAbs := by
  apply Nat.coprime_of_dvd
  intro ℓ hℓ hℓm hℓa
  have hℓmZ : (ℓ : ℤ) ∣ (m : ℤ) := Int.natCast_dvd_natCast.mpr hℓm
  have hℓaZ : (ℓ : ℤ) ∣ a :=
    Int.natAbs_dvd_natAbs.mp (by simpa using hℓa)
  have hℓsumZ : (ℓ : ℤ) ∣ a + b := hℓmZ.trans hdiv
  have hℓbZ : (ℓ : ℤ) ∣ b := by
    have := Int.dvd_sub hℓsumZ hℓaZ
    simpa using this
  have hℓb : ℓ ∣ b.natAbs := by
    simpa using Int.natAbs_dvd_natAbs.mpr hℓbZ
  exact hℓ.ne_one (Nat.eq_one_of_dvd_coprimes hcop hℓm hℓb)

theorem coprime_mersenne_mobiusNumerator
    {t r p : ℕ} (hr : Squarefree r) (hp : p.Prime) (hp3 : 3 ≤ p)
    (hpr : p ∣ r) (htp : t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t) :
    Nat.Coprime (RadicalMobiusShadow.mersenne p)
      (RadicalMobiusShadow.mobiusNumerator r).natAbs := by
  exact coprime_natAbs_of_sum_dvd
    (mobiusNumerator_mod_mersenne_prime hr hp hpr)
    (coprime_mersenne_jordanTotientTwo hr hp hp3 hpr htp hcut)

theorem coprime_mersenne_of_distinct_primes
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Nat.Coprime (RadicalMobiusShadow.mersenne p)
      (RadicalMobiusShadow.mersenne q) := by
  rw [Nat.coprime_iff_gcd_eq_one, RadicalMobiusShadow.mersenne,
    RadicalMobiusShadow.mersenne, Nat.pow_sub_one_gcd_pow_sub_one]
  have hpqdvd : ¬p ∣ q := by
    intro h
    exact hpq ((Nat.dvd_prime hq).mp h |>.resolve_left hp.ne_one)
  have hcop : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr hpqdvd
  rw [hcop.gcd_eq_one]
  norm_num

theorem channelProduct_dvd_mersenne
    {P : Finset ℕ} {r : ℕ} (hprime : ∀ p ∈ P, p.Prime)
    (hpr : ∀ p ∈ P, p ∣ r) :
    (∏ p ∈ P, RadicalMobiusShadow.mersenne p) ∣
      RadicalMobiusShadow.mersenne r := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hpP ih =>
      rw [Finset.prod_insert hpP]
      have hpPrime : p.Prime := hprime p (Finset.mem_insert_self p P)
      have hpD : RadicalMobiusShadow.mersenne p ∣
          RadicalMobiusShadow.mersenne r := by
        simpa [RadicalMobiusShadow.mersenne] using
          (Nat.pow_sub_one_dvd_pow_sub_one 2
            (hpr p (Finset.mem_insert_self p P)))
      have hprodD : (∏ q ∈ P, RadicalMobiusShadow.mersenne q) ∣
          RadicalMobiusShadow.mersenne r := by
        apply ih
        · intro q hq
          exact hprime q (Finset.mem_insert_of_mem hq)
        · intro q hq
          exact hpr q (Finset.mem_insert_of_mem hq)
      have hcop : Nat.Coprime (RadicalMobiusShadow.mersenne p)
          (∏ q ∈ P, RadicalMobiusShadow.mersenne q) := by
        apply Nat.Coprime.prod_right
        intro q hq
        exact coprime_mersenne_of_distinct_primes hpPrime
          (hprime q (Finset.mem_insert_of_mem hq)) (by
            intro hpq
            subst q
            exact hpP hq)
      exact hcop.mul_dvd_of_dvd_of_dvd hpD hprodD

theorem channelProduct_coprime_mobiusNumerator
    {P : Finset ℕ} {t r : ℕ} (ht : 5 ≤ t) (hr : Squarefree r)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t) :
    Nat.Coprime (∏ p ∈ P, RadicalMobiusShadow.mersenne p)
      (RadicalMobiusShadow.mobiusNumerator r).natAbs := by
  apply Nat.Coprime.prod_left
  intro p hpP
  have hp3 : 3 ≤ p := by
    have := hupper p hpP
    omega
  exact coprime_mersenne_mobiusNumerator hr (hprime p hpP) hp3
    (hpr p hpP) (hupper p hpP) hcut

/-! ## T4: aggregate survivor and full-product corollaries -/

/-- Canonical unconditional T4: the pairwise-coprime channel product survives
exactly up to cancellation by the displayed scale `h`. -/
theorem upperHalfChannel_survivorProduct_dvd_den
    (P : Finset ℕ) {t r h : ℕ} (ht : 5 ≤ t) (hr : Squarefree r)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t) :
    let C := ∏ p ∈ P, RadicalMobiusShadow.mersenne p
    C / Nat.gcd C h ∣
      (Rat.divInt ((h : ℤ) * RadicalMobiusShadow.mobiusNumerator r)
        (RadicalMobiusShadow.mersenne r : ℤ)).den := by
  dsimp only
  apply RationalDenominatorSurvival.survivingDivisor_dvd_scaled_divInt_den
  · simp [RadicalMobiusShadow.mersenne]
    exact hr.ne_zero
  · exact channelProduct_dvd_mersenne hprime hpr
  · exact channelProduct_coprime_mobiusNumerator ht hr hprime hpr hupper hcut

/-- A single upper-half prime contributes its Mersenne modulus after removing
exactly the part that the scale can cancel. -/
theorem upperHalfChannel_survivor_dvd_den
    {t r h p : ℕ} (ht : 5 ≤ t) (hr : Squarefree r)
    (hp : p.Prime) (hpr : p ∣ r) (hupper : t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t) :
    RadicalMobiusShadow.mersenne p /
        Nat.gcd (RadicalMobiusShadow.mersenne p) h ∣
      (Rat.divInt ((h : ℤ) * RadicalMobiusShadow.mobiusNumerator r)
        (RadicalMobiusShadow.mersenne r : ℤ)).den := by
  simpa using (upperHalfChannel_survivorProduct_dvd_den {p} ht hr
    (by simp [hp]) (by simp [hpr]) (by simp [hupper]) hcut (h := h))

theorem upperHalfChannel_product_dvd_den_of_coprime_scale
    (P : Finset ℕ) {t r h : ℕ} (ht : 5 ≤ t) (hr : Squarefree r)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t)
    (hscale : Nat.Coprime
      (∏ p ∈ P, RadicalMobiusShadow.mersenne p) h) :
    (∏ p ∈ P, RadicalMobiusShadow.mersenne p) ∣
      (Rat.divInt ((h : ℤ) * RadicalMobiusShadow.mobiusNumerator r)
        (RadicalMobiusShadow.mersenne r : ℤ)).den := by
  simpa [hscale.gcd_eq_one] using
    (upperHalfChannel_survivorProduct_dvd_den P ht hr hprime hpr
      hupper hcut (h := h))

theorem upperHalfChannel_product_dvd_den_of_scale_primeFactors_le
    (P : Finset ℕ) {t r h : ℕ} (ht : 5 ≤ t) (hr : Squarefree r)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t)
    (hhcut : ∀ q : ℕ, q.Prime → q ∣ h → q ≤ t) :
    (∏ p ∈ P, RadicalMobiusShadow.mersenne p) ∣
      (Rat.divInt ((h : ℤ) * RadicalMobiusShadow.mobiusNumerator r)
        (RadicalMobiusShadow.mersenne r : ℤ)).den := by
  apply upperHalfChannel_product_dvd_den_of_coprime_scale P ht hr
    hprime hpr hupper hcut
  apply Nat.Coprime.prod_left
  intro p hpP
  exact (coprime_mersenne_of_primeFactors_le
    (hprime p hpP) (by have := hupper p hpP; omega)
      (hupper p hpP) hhcut).symm

/-! ## The development's concrete LCM height and upper-half family -/

/-- `Hₜ = lcm(1, ..., t)`.  The interval avoids inserting zero into the
finite LCM. -/
def lcmHeight (t : ℕ) : ℕ :=
  (Finset.Icc 1 t).lcm (fun n ↦ n)

@[simp]
theorem lcmHeight_zero : lcmHeight 0 = 1 := by
  norm_num [lcmHeight]

@[simp]
theorem lcmHeight_one : lcmHeight 1 = 1 := by
  norm_num [lcmHeight]

/-- Executable pressure test for the through-`t` convention and upper
endpoint. -/
theorem lcmHeight_five_fixture : lcmHeight 5 = 60 := by
  decide

/-- `rₜ = rad(Hₜ)` using the canonical T6 squarefree kernel. -/
def lcmRadical (t : ℕ) : ℕ :=
  RadicalMobiusShadow.squarefreeKernel (lcmHeight t)

/-- `hₜ = Hₜ / rₜ`, the scale multiplying the radical shadow. -/
def lcmScale (t : ℕ) : ℕ :=
  lcmHeight t / lcmRadical t

/-- The prime support of `Hₜ` is exactly the set of primes at most `t`. -/
theorem prime_dvd_lcmHeight_iff
    {t ℓ : ℕ} (hℓ : ℓ.Prime) :
    ℓ ∣ lcmHeight t ↔ ℓ ≤ t := by
  constructor
  · intro hdiv
    have hprod : ℓ ∣ ∏ n ∈ Finset.Icc 1 t, n :=
      hdiv.trans (Finset.lcm_dvd_prod (Finset.Icc 1 t) (fun n ↦ n))
    obtain ⟨n, hn, hℓn⟩ :=
      (hℓ.prime.dvd_finset_prod_iff (fun n : ℕ ↦ n)).mp hprod
    have hnBounds := Finset.mem_Icc.mp hn
    exact (Nat.le_of_dvd (by omega) hℓn).trans hnBounds.2
  · intro hℓt
    have hmem : ℓ ∈ Finset.Icc 1 t :=
      Finset.mem_Icc.mpr ⟨hℓ.one_le, hℓt⟩
    simpa [lcmHeight] using
      (Finset.dvd_lcm (f := fun n : ℕ ↦ n) hmem)

theorem lcmHeight_pos (t : ℕ) : 0 < lcmHeight t := by
  apply Nat.pos_of_ne_zero
  rw [lcmHeight, Finset.lcm_ne_zero_iff]
  intro n hn
  have hnBounds := Finset.mem_Icc.mp hn
  omega

theorem lcmScale_dvd_lcmHeight (t : ℕ) :
    lcmScale t ∣ lcmHeight t := by
  simpa [lcmScale, lcmRadical] using
    (Nat.div_dvd_of_dvd
      (RadicalMobiusShadow.squarefreeKernel_dvd (lcmHeight t)))

theorem lcmScale_primeFactors_le (t : ℕ) :
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ lcmScale t → ℓ ≤ t := by
  intro ℓ hℓ hℓscale
  exact (prime_dvd_lcmHeight_iff hℓ).mp
    (hℓscale.trans (lcmScale_dvd_lcmHeight t))

theorem prime_dvd_lcmRadical_iff
    {t p : ℕ} (hp : p.Prime) :
    p ∣ lcmRadical t ↔ p ≤ t := by
  rw [lcmRadical,
    RadicalMobiusShadow.prime_dvd_squarefreeKernel_iff
      (lcmHeight_pos t).ne' hp,
    prime_dvd_lcmHeight_iff hp]

theorem lcmRadical_div_dvd_lcmHeight
    {t p : ℕ} (hp : p ∣ lcmRadical t) :
    lcmRadical t / p ∣ lcmHeight t := by
  exact (Nat.div_dvd_of_dvd hp).trans (by
    simpa [lcmRadical] using
      RadicalMobiusShadow.squarefreeKernel_dvd (lcmHeight t))

theorem lcmRadical_div_primeFactors_le
    {t p : ℕ} (hp : p ∣ lcmRadical t) :
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ lcmRadical t / p → ℓ ≤ t := by
  intro ℓ hℓ hℓdiv
  exact (prime_dvd_lcmHeight_iff hℓ).mp
    (hℓdiv.trans (lcmRadical_div_dvd_lcmHeight hp))

/-- Prime indices in the development's upper half `(t/2, t]`. -/
def upperHalfPrimes (t : ℕ) : Finset ℕ :=
  (Finset.Ioc (t / 2) t).filter Nat.Prime

/-- Executable pressure test for the strict lower and inclusive upper
boundaries of the upper-half prime family. -/
theorem upperHalfPrimes_five_fixture : upperHalfPrimes 5 = {3, 5} := by
  decide

/-! ## Instantiation at the repository's scaled Möbius shadow -/

theorem scaledMobiusShadow_upperHalf_survivorProduct_dvd_den
    (P : Finset ℕ) {t H : ℕ} (hH : 0 < H) (ht : 5 ≤ t)
    (hprime : ∀ p ∈ P, p.Prime)
    (hpr : ∀ p ∈ P, p ∣ RadicalMobiusShadow.squarefreeKernel H)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime →
      q ∣ RadicalMobiusShadow.squarefreeKernel H → q ≤ t) :
    let h := H / RadicalMobiusShadow.squarefreeKernel H
    let C := ∏ p ∈ P, RadicalMobiusShadow.mersenne p
    C / Nat.gcd C h ∣
      ((H : ℚ) * RadicalMobiusShadow.numericMobiusShadow H).den := by
  dsimp only
  rw [RadicalMobiusShadow.scaledMobiusShadow_eq_radicalNumerator H hH]
  have hmul :
      ((H / RadicalMobiusShadow.squarefreeKernel H : ℕ) : ℚ) *
          Rat.divInt
            (RadicalMobiusShadow.mobiusNumerator
              (RadicalMobiusShadow.squarefreeKernel H))
            (RadicalMobiusShadow.mersenne
              (RadicalMobiusShadow.squarefreeKernel H) : ℤ) =
        Rat.divInt
          (((H / RadicalMobiusShadow.squarefreeKernel H : ℕ) : ℤ) *
            RadicalMobiusShadow.mobiusNumerator
              (RadicalMobiusShadow.squarefreeKernel H))
          (RadicalMobiusShadow.mersenne
            (RadicalMobiusShadow.squarefreeKernel H) : ℤ) := by
    rw [Rat.natCast_eq_divInt, Rat.divInt_mul_divInt]
    simp
  rw [hmul]
  exact upperHalfChannel_survivorProduct_dvd_den P ht
    (RadicalMobiusShadow.squarefreeKernel_squarefree H)
    hprime hpr hupper hcut

theorem scaledMobiusShadow_upperHalf_product_dvd_den_of_scale_primeFactors_le
    (P : Finset ℕ) {t H : ℕ} (hH : 0 < H) (ht : 5 ≤ t)
    (hprime : ∀ p ∈ P, p.Prime)
    (hpr : ∀ p ∈ P, p ∣ RadicalMobiusShadow.squarefreeKernel H)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime →
      q ∣ RadicalMobiusShadow.squarefreeKernel H → q ≤ t)
    (hhcut : ∀ q : ℕ, q.Prime →
      q ∣ H / RadicalMobiusShadow.squarefreeKernel H → q ≤ t) :
    (∏ p ∈ P, RadicalMobiusShadow.mersenne p) ∣
      ((H : ℚ) * RadicalMobiusShadow.numericMobiusShadow H).den := by
  have hscale : Nat.Coprime
      (∏ p ∈ P, RadicalMobiusShadow.mersenne p)
      (H / RadicalMobiusShadow.squarefreeKernel H) := by
    apply Nat.Coprime.prod_left
    intro p hpP
    exact (coprime_mersenne_of_primeFactors_le
      (hprime p hpP) (by have := hupper p hpP; omega)
        (hupper p hpP) hhcut).symm
  simpa [hscale.gcd_eq_one] using
    (scaledMobiusShadow_upperHalf_survivorProduct_dvd_den P hH ht
      hprime hpr hupper hcut)

/-- Concrete paper-level T4: at `Hₜ = lcm(1, ..., t)`, the product of all
prime-index Mersenne channels with `t/2 < p ≤ t` survives in the reduced
denominator of the scaled numeric Möbius shadow. -/
theorem lcmHeight_upperHalf_product_dvd_den
    {t : ℕ} (ht : 5 ≤ t) :
    (∏ p ∈ upperHalfPrimes t, RadicalMobiusShadow.mersenne p) ∣
      ((lcmHeight t : ℚ) *
        RadicalMobiusShadow.numericMobiusShadow (lcmHeight t)).den := by
  apply scaledMobiusShadow_upperHalf_product_dvd_den_of_scale_primeFactors_le
    (upperHalfPrimes t) (lcmHeight_pos t) ht
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · intro p hp
    exact (prime_dvd_lcmRadical_iff (Finset.mem_filter.mp hp).2).mpr
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
  · intro p hp
    have hpLower := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
    omega
  · intro q hq hqrad
    exact (prime_dvd_lcmRadical_iff hq).mp hqrad
  · intro q hq hqscale
    exact lcmScale_primeFactors_le t q hq (by
      simpa [lcmScale, lcmRadical] using hqscale)

#print axioms prime_dvd_mersenne_gt_scale
#print axioms prime_dvd_mersenne_lower_bound
#print axioms coprime_mersenne_of_primeFactors_le
#print axioms isUnit_mod_mersenne_of_primeFactors_le
#print axioms upperHalfUnitTarget_isUnit_of_primeFactors_le
#print axioms upperHalfChannel_survivorProduct_dvd_den
#print axioms upperHalfChannel_product_dvd_den_of_scale_primeFactors_le
#print axioms scaledMobiusShadow_upperHalf_survivorProduct_dvd_den
#print axioms scaledMobiusShadow_upperHalf_product_dvd_den_of_scale_primeFactors_le
#print axioms prime_dvd_lcmHeight_iff
#print axioms lcmHeight_upperHalf_product_dvd_den
#print axioms lcmHeight_five_fixture
#print axioms upperHalfPrimes_five_fixture
#print axioms localCofactorValue_coprime_mersenne
#print axioms localNumeratorValue_two_coprime_mersenne
#print axioms localNumeratorValue_four_gcd
#print axioms mobiusNumerator_associated_oddJordanScalar
#print axioms scaledMobiusNumerator_gcd_eq_oddJordanScalar
#print axioms scaledMobiusNumerator_den_exact

end Erdos249257.MersenneShadowCyclotomicNoncollapse
