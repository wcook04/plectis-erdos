import Erdos249257.PrimePowerJumpDynamics
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Tactic

/-!
# Cyclic tensor algebra for the Möbius shadow

This file packages the prime-index subgroup sums in `ℤ[X] / (X^r - 1)`.
It is the finite algebraic owner for the local numerator factors, their
integral cofactors, and the scalar adjugate used by the base-two normal form.
-/

open scoped BigOperators Polynomial

namespace Erdos249257.CyclicTensorMobiusShadow

open RepunitMobiusNumerator
open CyclotomicProjectionOfShadow

/-- The defining relation of the cyclic polynomial algebra of order `r`. -/
noncomputable def cyclicModulus (r : ℕ) : ℤ[X] :=
  (Polynomial.X : ℤ[X]) ^ r - 1

/-- The sum of the order-`q` subgroup in the cyclic algebra of order `r`. -/
noncomputable def subgroupSum (r q : ℕ) : ℤ[X] :=
  spacedRepunit (r / q) q

/-- The prime-local factor occurring in the tensor product for the numerator. -/
noncomputable def localNumeratorFactor (r q : ℕ) : ℤ[X] :=
  Polynomial.C (q : ℤ) * subgroupSum r q - 1

/-- The integral cofactor of the prime-local numerator factor. -/
noncomputable def localCofactorFactor (r q : ℕ) : ℤ[X] :=
  Polynomial.C (q : ℤ) * subgroupSum r q -
    Polynomial.C ((q : ℤ) ^ 2 - 1)

/-- Product of all prime-local numerator factors. -/
noncomputable def numeratorFactorProduct (r : ℕ) : ℤ[X] :=
  ∏ q ∈ r.primeFactors, localNumeratorFactor r q

/-- Product of all integral prime-local cofactors. -/
noncomputable def cofactorProduct (r : ℕ) : ℤ[X] :=
  ∏ q ∈ r.primeFactors, localCofactorFactor r q

/-- The scalar contributed by the odd prime factors of `r`. -/
noncomputable def oddJordanScalar (r : ℕ) : ℤ :=
  ∏ q ∈ r.primeFactors.filter (fun q => q ≠ 2), ((q : ℤ) ^ 2 - 1)

/-- Base-two evaluation of a local numerator factor. -/
noncomputable def localNumeratorValue (r q : ℕ) : ℤ :=
  (localNumeratorFactor r q).eval 2

/-- Base-two evaluation of a local cofactor factor. -/
noncomputable def localCofactorValue (r q : ℕ) : ℤ :=
  (localCofactorFactor r q).eval 2

private theorem subgroupSum_mul_X_pow_sub_one
    {r q : ℕ} (hq : q ∣ r) :
    subgroupSum r q * ((Polynomial.X : ℤ[X]) ^ (r / q) - 1) =
      cyclicModulus r := by
  rw [subgroupSum, cyclicModulus]
  have hgeom := geom_sum_mul ((Polynomial.X : ℤ[X]) ^ (r / q)) q
  rw [← pow_mul, Nat.div_mul_cancel hq] at hgeom
  simpa [spacedRepunit, Polynomial.monomial_one_right_eq_X_pow,
    pow_mul] using hgeom

private theorem X_pow_sub_one_dvd_subgroupSum_sub_C
    (r q : ℕ) :
    (Polynomial.X : ℤ[X]) ^ (r / q) - 1 ∣
      subgroupSum r q - Polynomial.C (q : ℤ) := by
  classical
  let d := r / q
  have hterm (j : ℕ) :
      (Polynomial.X : ℤ[X]) ^ d - 1 ∣
        (Polynomial.X : ℤ[X]) ^ (d * j) - 1 := by
    simpa [pow_mul] using
      (sub_dvd_pow_sub_pow ((Polynomial.X : ℤ[X]) ^ d) 1 j)
  have hsum :
      (Polynomial.X : ℤ[X]) ^ d - 1 ∣
        ∑ j ∈ Finset.range q,
          ((Polynomial.X : ℤ[X]) ^ (d * j) - 1) := by
    exact Finset.dvd_sum fun j _ => hterm j
  simpa [subgroupSum, spacedRepunit, d,
    Polynomial.monomial_one_right_eq_X_pow, Finset.sum_sub_distrib] using hsum

/-- In the cyclic algebra, the subgroup sum satisfies `Σ_q² = q Σ_q`. -/
theorem cyclicModulus_dvd_subgroupSum_sq_sub_smul
    {r q : ℕ} (hq : q ∣ r) :
    cyclicModulus r ∣
      subgroupSum r q ^ 2 - Polynomial.C (q : ℤ) * subgroupSum r q := by
  obtain ⟨u, hu⟩ := X_pow_sub_one_dvd_subgroupSum_sub_C r q
  refine ⟨u, ?_⟩
  calc
    subgroupSum r q ^ 2 - Polynomial.C (q : ℤ) * subgroupSum r q =
        subgroupSum r q *
          (subgroupSum r q - Polynomial.C (q : ℤ)) := by ring
    _ = subgroupSum r q *
        (((Polynomial.X : ℤ[X]) ^ (r / q) - 1) * u) := by rw [hu]
    _ = cyclicModulus r * u := by
      rw [← subgroupSum_mul_X_pow_sub_one hq]
      ring

/-- The local numerator and cofactor multiply to the scalar `q² - 1`
modulo `X^r - 1`. -/
theorem cyclicModulus_dvd_localNumerator_mul_localCofactor_sub_scalar
    {r q : ℕ} (hq : q ∣ r) :
    cyclicModulus r ∣
      localNumeratorFactor r q * localCofactorFactor r q -
        Polynomial.C ((q : ℤ) ^ 2 - 1) := by
  have hidem := cyclicModulus_dvd_subgroupSum_sq_sub_smul hq
  obtain ⟨u, hu⟩ := hidem
  refine ⟨Polynomial.C ((q : ℤ) ^ 2) * u, ?_⟩
  calc
    localNumeratorFactor r q * localCofactorFactor r q -
        Polynomial.C ((q : ℤ) ^ 2 - 1) =
      Polynomial.C ((q : ℤ) ^ 2) *
        (subgroupSum r q ^ 2 -
          Polynomial.C (q : ℤ) * subgroupSum r q) := by
            simp only [localNumeratorFactor, localCofactorFactor, map_sub,
              map_pow, map_natCast, map_one]
            ring
    _ = Polynomial.C ((q : ℤ) ^ 2) * (cyclicModulus r * u) := by rw [hu]
    _ = cyclicModulus r * (Polynomial.C ((q : ℤ) ^ 2) * u) := by ring

private theorem dvd_finset_prod_sub_prod
    {ι : Type*} [DecidableEq ι] (m : ℤ[X]) (s : Finset ι)
    (f g : ι → ℤ[X])
    (hfg : ∀ i ∈ s, m ∣ f i - g i) :
    m ∣ (∏ i ∈ s, f i) - ∏ i ∈ s, g i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have haDvd := hfg a (Finset.mem_insert_self a s)
      have hsDvd := ih fun i hi => hfg i (Finset.mem_insert_of_mem hi)
      obtain ⟨u, hu⟩ := haDvd
      obtain ⟨v, hv⟩ := hsDvd
      refine ⟨f a * v + u * (∏ i ∈ s, g i), ?_⟩
      simp only [Finset.prod_insert ha]
      calc
        f a * (∏ i ∈ s, f i) - g a * ∏ i ∈ s, g i =
            f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) +
              (f a - g a) * ∏ i ∈ s, g i := by ring
        _ = f a * (m * v) + (m * u) * ∏ i ∈ s, g i := by rw [hu, hv]
        _ = m * (f a * v + u * ∏ i ∈ s, g i) := by ring

private theorem polynomial_dvd_sub {a b c : ℤ[X]}
    (hb : a ∣ b) (hc : a ∣ c) : a ∣ b - c := by
  obtain ⟨u, rfl⟩ := hb
  obtain ⟨v, rfl⟩ := hc
  exact ⟨u - v, by ring⟩

private theorem monic_dvd_of_map_rat_dvd {m d : ℤ[X]}
    (hm : m.Monic)
    (h : m.map (Int.castRingHom ℚ) ∣ d.map (Int.castRingHom ℚ)) :
    m ∣ d := by
  have hmapRem : (d %ₘ m).map (Int.castRingHom ℚ) = 0 := by
    rw [Polynomial.map_modByMonic (Int.castRingHom ℚ) hm]
    exact (Polynomial.modByMonic_eq_zero_iff_dvd
      (hm.map (Int.castRingHom ℚ))).2 h
  have hrem : d %ₘ m = 0 := by
    apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
    simpa using hmapRem
  exact (Polynomial.modByMonic_eq_zero_iff_dvd hm).1 hrem

/-- A fresh-prime expansion acts trivially on the squarefree Möbius numerator
in the cyclic algebra of the old order.  This is the algebraic transport
lemma used by prime-adjunction induction. -/
theorem cyclicModulus_dvd_mobiusNumeratorPolynomial_sub_expand
    {r p : ℕ} (hr : Squarefree r) (hp : p.Prime) (hpr : ¬ p ∣ r) :
    cyclicModulus r ∣
      mobiusNumeratorPolynomial r -
        Polynomial.expand ℤ p (mobiusNumeratorPolynomial r) := by
  classical
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr.ne_zero
  let D : ℤ[X] := mobiusNumeratorPolynomial r -
    Polynomial.expand ℤ p (mobiusNumeratorPolynomial r)
  have hfibre : ∀ m ∈ r.divisors, Polynomial.cyclotomic m ℤ ∣ D := by
    intro m hm
    have hmr : m ∣ r := Nat.dvd_of_mem_divisors hm
    have hpm : ¬ p ∣ m := fun h => hpr (h.trans hmr)
    let a : ℤ := ArithmeticFunction.moebius m * jordanTotientTwo (r / m)
    have hbase : Polynomial.cyclotomic m ℤ ∣
        mobiusNumeratorPolynomial r - Polynomial.C a :=
      cyclotomic_dvd_mobiusNumeratorPolynomial_sub hr hmr
    have hexpand : Polynomial.expand ℤ p (Polynomial.cyclotomic m ℤ) ∣
        Polynomial.expand ℤ p
          (mobiusNumeratorPolynomial r - Polynomial.C a) :=
      (Polynomial.expand ℤ p).map_dvd hbase
    have hfactor : Polynomial.cyclotomic m ℤ ∣
        Polynomial.expand ℤ p (Polynomial.cyclotomic m ℤ) := by
      rw [Polynomial.cyclotomic_expand_eq_cyclotomic_mul hp hpm ℤ]
      exact dvd_mul_left _ _
    have hnew : Polynomial.cyclotomic m ℤ ∣
        Polynomial.expand ℤ p (mobiusNumeratorPolynomial r) -
          Polynomial.C a :=
      hfactor.trans (by simpa [a] using hexpand)
    simpa [D, a] using polynomial_dvd_sub hbase hnew
  have hrat :
      (cyclicModulus r).map (Int.castRingHom ℚ) ∣
        D.map (Int.castRingHom ℚ) := by
    have hpair : ((r.divisors : Finset ℕ) : Set ℕ).Pairwise
        (fun m n => IsCoprime
          (Polynomial.cyclotomic m ℚ) (Polynomial.cyclotomic n ℚ)) := by
      intro m hm n hn hmn
      exact Polynomial.cyclotomic.isCoprime_rat hmn
    have hall : ∀ m ∈ r.divisors,
        Polynomial.cyclotomic m ℚ ∣ D.map (Int.castRingHom ℚ) := by
      intro m hm
      simpa using map_dvd (Polynomial.mapRingHom (Int.castRingHom ℚ)) (hfibre m hm)
    have hprod := Finset.prod_dvd_of_coprime hpair hall
    rw [Polynomial.prod_cyclotomic_eq_X_pow_sub_one hrpos ℚ] at hprod
    simpa [cyclicModulus] using hprod
  have hmonic : (cyclicModulus r).Monic := by
    simpa [cyclicModulus] using
      (Polynomial.monic_X_pow_sub_C (1 : ℤ) hr.ne_zero)
  exact monic_dvd_of_map_rat_dvd hmonic (by simpa [D] using hrat)

@[simp]
private theorem expand_cyclicModulus (r p : ℕ) :
    Polynomial.expand ℤ p (cyclicModulus r) = cyclicModulus (r * p) := by
  simp only [cyclicModulus, map_sub, map_pow, map_one, Polynomial.expand_X]
  rw [← pow_mul, Nat.mul_comm]

private theorem localNumeratorFactor_mul_prime
    {a p q : ℕ} (hqa : q ∣ a) :
    localNumeratorFactor (p * a) q =
      Polynomial.expand ℤ p (localNumeratorFactor a q) := by
  have hquot : (p * a) / q = (a / q) * p := by
    rw [Nat.mul_div_assoc p hqa, Nat.mul_comm]
  simp [localNumeratorFactor, subgroupSum, hquot,
    PrimePowerJumpDynamics.expand_spacedRepunit]

private theorem numeratorFactorProduct_mul_prime
    {a p : ℕ} (hp : p.Prime) (ha0 : a ≠ 0) (hpa : ¬ p ∣ a) :
    numeratorFactorProduct (p * a) =
      localNumeratorFactor (p * a) p *
        Polynomial.expand ℤ p (numeratorFactorProduct a) := by
  classical
  have hpnot : p ∉ a.primeFactors := by
    intro hmem
    exact hpa (Nat.dvd_of_mem_primeFactors hmem)
  rw [numeratorFactorProduct, Nat.primeFactors_mul hp.ne_zero ha0,
    hp.primeFactors]
  simp only [Finset.singleton_union, Finset.prod_insert hpnot]
  rw [numeratorFactorProduct, map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro q hq
  exact localNumeratorFactor_mul_prime
    (Nat.dvd_of_mem_primeFactors hq)

private theorem subgroupSum_mul_prime_at_prime
    {a p : ℕ} (hp : p.Prime) :
    subgroupSum (p * a) p = spacedRepunit a p := by
  simp [subgroupSum, hp.ne_zero]

private theorem subgroupSum_mul_cyclicModulus
    {a p : ℕ} (hp : p.Prime) :
    subgroupSum (p * a) p * cyclicModulus a = cyclicModulus (p * a) := by
  simpa [hp.ne_zero] using
    (subgroupSum_mul_X_pow_sub_one (r := p * a) (q := p)
      (dvd_mul_right p a))

/-- Prime-factor tensor factorisation of the existing Möbius numerator in
the cyclic algebra.  The polynomial on the left is the original T1 owner;
no parallel numerator definition is introduced. -/
theorem cyclicModulus_dvd_mobiusNumeratorPolynomial_sub_numeratorFactorProduct
    {r : ℕ} (hr : Squarefree r) :
    cyclicModulus r ∣
      mobiusNumeratorPolynomial r - numeratorFactorProduct r := by
  classical
  induction r using induction_on_primes with
  | zero => exact (hr.ne_zero rfl).elim
  | one =>
      simp [cyclicModulus, numeratorFactorProduct,
        mobiusNumeratorPolynomial, spacedRepunit]
  | prime_mul p a hp ih =>
      have ha0 : a ≠ 0 := by
        intro ha
        subst a
        exact hr.ne_zero (Nat.mul_zero p)
      have haSq : Squarefree a :=
        hr.squarefree_of_dvd (dvd_mul_left a p)
      have hcop : p.Coprime a := Nat.coprime_of_squarefree_mul hr
      have hpa : ¬ p ∣ a := (hp.coprime_iff_not_dvd).1 hcop
      have hIH := ih haSq
      have hInv :=
        cyclicModulus_dvd_mobiusNumeratorPolynomial_sub_expand haSq hp hpa
      have hExpandedRaw :=
        map_dvd (Polynomial.expand ℤ p) hIH
      have hExpanded : cyclicModulus (p * a) ∣
          Polynomial.expand ℤ p
            (mobiusNumeratorPolynomial a - numeratorFactorProduct a) := by
        simpa [Nat.mul_comm] using hExpandedRaw
      obtain ⟨u, hu⟩ := hInv
      obtain ⟨v, hv⟩ := hExpanded
      have hfirst : cyclicModulus (p * a) ∣
          Polynomial.C (p : ℤ) * subgroupSum (p * a) p *
            (mobiusNumeratorPolynomial a -
              Polynomial.expand ℤ p (mobiusNumeratorPolynomial a)) := by
        refine ⟨Polynomial.C (p : ℤ) * u, ?_⟩
        rw [hu, ← subgroupSum_mul_cyclicModulus hp]
        ring
      have hsecond : cyclicModulus (p * a) ∣
          Polynomial.C (p : ℤ) * subgroupSum (p * a) p *
            Polynomial.expand ℤ p
              (mobiusNumeratorPolynomial a - numeratorFactorProduct a) := by
        refine ⟨Polynomial.C (p : ℤ) * subgroupSum (p * a) p * v, ?_⟩
        rw [hv]
        ring
      have hthird : cyclicModulus (p * a) ∣
          Polynomial.expand ℤ p
            (mobiusNumeratorPolynomial a - numeratorFactorProduct a) :=
        ⟨v, hv⟩
      have htotal := (hfirst.add hsecond).sub hthird
      convert htotal using 1
      rw [PrimePowerJumpDynamics.mobiusNumeratorPolynomial_prime_mul hp hpa,
        numeratorFactorProduct_mul_prime hp ha0 hpa,
        subgroupSum_mul_prime_at_prime hp]
      simp only [map_sub, localNumeratorFactor, subgroupSum]
      simp only [Nat.mul_div_cancel_left a hp.pos]
      ring

/-- Multiplying all local adjugate identities gives the integral scalar
adjugate for the tensor product itself. -/
theorem cyclicModulus_dvd_numeratorFactorProduct_mul_cofactorProduct_sub_jordanTotientTwo
    {r : ℕ} (hr : Squarefree r) :
    cyclicModulus r ∣
      numeratorFactorProduct r * cofactorProduct r -
        Polynomial.C (jordanTotientTwo r) := by
  classical
  have hlocal : ∀ q ∈ r.primeFactors,
      cyclicModulus r ∣
        (localNumeratorFactor r q * localCofactorFactor r q) -
          Polynomial.C ((q : ℤ) ^ 2 - 1) := by
    intro q hq
    exact cyclicModulus_dvd_localNumerator_mul_localCofactor_sub_scalar
      (Nat.dvd_of_mem_primeFactors hq)
  have hprod := dvd_finset_prod_sub_prod (cyclicModulus r) r.primeFactors
    (fun q => localNumeratorFactor r q * localCofactorFactor r q)
    (fun q => Polynomial.C ((q : ℤ) ^ 2 - 1)) hlocal
  simpa [numeratorFactorProduct, cofactorProduct, Finset.prod_mul_distrib,
    ← map_prod, jordanTotientTwo_eq_prod_primeFactors hr] using hprod

/-- The cofactor product is an integral adjugate for the original Möbius
numerator polynomial, not merely for the auxiliary tensor product. -/
theorem cyclicModulus_dvd_mobiusNumeratorPolynomial_mul_cofactorProduct_sub_jordanTotientTwo
    {r : ℕ} (hr : Squarefree r) :
    cyclicModulus r ∣
      mobiusNumeratorPolynomial r * cofactorProduct r -
        Polynomial.C (jordanTotientTwo r) := by
  have hfactor :=
    cyclicModulus_dvd_mobiusNumeratorPolynomial_sub_numeratorFactorProduct hr
  have hadj :=
    cyclicModulus_dvd_numeratorFactorProduct_mul_cofactorProduct_sub_jordanTotientTwo hr
  have hmul : cyclicModulus r ∣
      (mobiusNumeratorPolynomial r - numeratorFactorProduct r) *
        cofactorProduct r := by
    exact dvd_mul_of_dvd_left hfactor _
  have htotal := hmul.add hadj
  convert htotal using 1
  ring

/-- Evaluation at `X = 2` gives the prime-factor product congruence modulo
the Mersenne denominator. -/
theorem mersenne_dvd_mobiusNumerator_sub_localNumeratorProduct
    {r : ℕ} (hr : Squarefree r) :
    (RadicalMobiusShadow.mersenne r : ℤ) ∣
      RadicalMobiusShadow.mobiusNumerator r -
        ∏ q ∈ r.primeFactors, localNumeratorValue r q := by
  have hpoly :=
    cyclicModulus_dvd_mobiusNumeratorPolynomial_sub_numeratorFactorProduct hr
  have heval := map_dvd (Polynomial.evalRingHom (R := ℤ) 2) hpoly
  have hpow : 1 ≤ 2 ^ r := one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))
  change (cyclicModulus r).eval 2 ∣
    (mobiusNumeratorPolynomial r - numeratorFactorProduct r).eval 2 at heval
  rw [Polynomial.eval_sub] at heval
  have hprod : (numeratorFactorProduct r).eval 2 =
      ∏ q ∈ r.primeFactors, localNumeratorValue r q := by
    simp [numeratorFactorProduct, localNumeratorValue, Polynomial.eval_prod]
  simpa [cyclicModulus, RadicalMobiusShadow.mersenne,
    Nat.cast_sub hpow,
    RepunitMobiusNumerator.mobiusNumeratorPolynomial_eval_two hr,
    hprod] using heval

#print axioms cyclicModulus_dvd_subgroupSum_sq_sub_smul
#print axioms cyclicModulus_dvd_mobiusNumeratorPolynomial_sub_expand
#print axioms cyclicModulus_dvd_mobiusNumeratorPolynomial_sub_numeratorFactorProduct
#print axioms cyclicModulus_dvd_mobiusNumeratorPolynomial_mul_cofactorProduct_sub_jordanTotientTwo
#print axioms mersenne_dvd_mobiusNumerator_sub_localNumeratorProduct

end Erdos249257.CyclicTensorMobiusShadow
