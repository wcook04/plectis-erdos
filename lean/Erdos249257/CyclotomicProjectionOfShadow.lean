import Erdos249257.RepunitMobiusNumerator
import Erdos249257.RationalDenominatorSurvival
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic

/-!
# Cyclotomic projection of the radical Möbius shadow

This file develops the first two cyclotomic projection layers for Erdős #249.  It projects the
divisor-spaced-repunit numerator onto integral cyclotomic fibres and proves
that the top fibre survives reduction of the unscaled rational shadow.

The theorem boundary is deliberately algebraic and universal on squarefree
exponents.  Finite fixtures are regression evidence only, and none of the
results below claims that Erdős #249 is solved.
-/

open scoped BigOperators ArithmeticFunction.Moebius Polynomial

namespace Erdos249257.CyclotomicProjectionOfShadow

/-- The second Jordan totient, as the integer-valued Dirichlet convolution
`μ * id²`. -/
noncomputable def jordanTotientTwo : ArithmeticFunction ℤ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℤ) *
    (ArithmeticFunction.pow 2 : ArithmeticFunction ℤ)

/-- Integer evaluation `Φ_m(2)`. -/
noncomputable def cyclotomicEval (m : ℕ) : ℤ :=
  (Polynomial.cyclotomic m ℤ).eval 2

/-- The unsigned cyclotomic channel modulus `|Φ_m(2)|`. -/
noncomputable def cyclotomicValue (m : ℕ) : ℕ :=
  (cyclotomicEval m).natAbs

@[simp]
theorem jordanTotientTwo_one : jordanTotientTwo 1 = 1 := by
  simp [jordanTotientTwo]

theorem jordanTotientTwo_eq_divisorSum {n : ℕ} (_hn : 0 < n) :
    jordanTotientTwo n =
      ∑ d ∈ n.divisors,
        ArithmeticFunction.moebius d * (((n / d : ℕ) : ℤ) ^ 2) := by
  rw [jordanTotientTwo, ArithmeticFunction.mul_apply]
  calc
    ∑ x ∈ n.divisorsAntidiagonal,
        ArithmeticFunction.moebius x.1 *
          (ArithmeticFunction.pow 2 : ArithmeticFunction ℤ) x.2 =
        ∑ d ∈ n.divisors,
          ArithmeticFunction.moebius d * (((n / d : ℕ) : ℤ) ^ 2) := by
            exact Nat.sum_divisorsAntidiagonal
              (fun d q ↦ ArithmeticFunction.moebius d * ((q : ℤ) ^ 2))

private theorem jordanTotientTwo_multiplicative :
    jordanTotientTwo.IsMultiplicative := by
  exact ArithmeticFunction.isMultiplicative_moebius.mul
    ArithmeticFunction.isMultiplicative_pow.natCast

theorem jordanTotientTwo_prime {p : ℕ} (hp : p.Prime) :
    jordanTotientTwo p = (p : ℤ) ^ 2 - 1 := by
  rw [jordanTotientTwo_eq_divisorSum hp.pos, hp.divisors]
  rw [Finset.sum_insert (by simpa using hp.ne_one.symm), Finset.sum_singleton]
  rw [ArithmeticFunction.moebius_apply_prime hp]
  norm_num [hp.ne_zero]
  ring

theorem jordanTotientTwo_eq_prod_primeFactors
    {n : ℕ} (hn : Squarefree n) :
    jordanTotientTwo n =
      ∏ p ∈ n.primeFactors, ((p : ℤ) ^ 2 - 1) := by
  rw [← jordanTotientTwo_multiplicative.prod_primeFactors hn]
  apply Finset.prod_congr rfl
  intro p hp
  exact jordanTotientTwo_prime (Nat.prime_of_mem_primeFactors hp)

/-- If a squarefree argument has prime support at most `t`, then the same is
true of the absolute second Jordan totient, once `t` contains the exceptional
factor `3` coming from `2² - 1`. -/
theorem jordanTotientTwo_natAbs_primeFactors_le
    {t n : ℕ} (ht : 3 ≤ t) (hnSq : Squarefree n)
    (hnSupp : ∀ q : ℕ, q.Prime → q ∣ n → q ≤ t) :
    ∀ ℓ : ℕ, ℓ.Prime →
      ℓ ∣ (jordanTotientTwo n).natAbs → ℓ ≤ t := by
  intro ℓ hℓ hℓj
  rw [jordanTotientTwo_eq_prod_primeFactors hnSq] at hℓj
  change ℓ ∣ Int.natAbsHom
    (∏ q ∈ n.primeFactors, ((q : ℤ) ^ 2 - 1)) at hℓj
  rw [map_prod] at hℓj
  obtain ⟨q, hqmem, hℓq⟩ :=
    (hℓ.prime.dvd_finset_prod_iff
      (fun q : ℕ ↦ (((q : ℤ) ^ 2 - 1).natAbs))).mp hℓj
  have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hqmem
  have hqLe : q ≤ t :=
    hnSupp q hqPrime (Nat.dvd_of_mem_primeFactors hqmem)
  have hqAbs : (((q : ℤ) ^ 2 - 1).natAbs) = q ^ 2 - 1 := by
    rw [← Int.natCast_pow, ← Int.natCast_one,
      Int.natAbs_natCast_sub_natCast_of_ge]
    exact one_le_pow₀ hqPrime.one_le
  rw [hqAbs] at hℓq
  have hfactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    simpa [mul_comm] using (sq_tsub_sq q 1)
  rw [hfactor] at hℓq
  rcases (hℓ.dvd_mul.mp hℓq) with hleft | hright
  · have hℓLe : ℓ ≤ q - 1 :=
      Nat.le_of_dvd (Nat.sub_pos_of_lt hqPrime.one_lt) hleft
    omega
  · by_cases hq2 : q = 2
    · subst q
      have hcases : ℓ = 1 ∨ ℓ = 3 :=
        (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp (by simpa using hright)
      rcases hcases with hℓ1 | hℓ3
      · exact (hℓ.ne_one hℓ1).elim
      · omega
    · have hqOdd : q % 2 = 1 :=
        hqPrime.eq_two_or_odd.resolve_left hq2
      have hqTwo : 2 ≤ q := hqPrime.two_le
      have hℓLeSucc : ℓ ≤ q + 1 :=
        Nat.le_of_dvd (by omega) hright
      have hℓLeQ : ℓ ≤ q := by
        by_contra hℓNotLe
        have hqLtℓ : q < ℓ := Nat.lt_of_not_ge hℓNotLe
        have hℓEq : ℓ = q + 1 := by omega
        have hℓNeTwo : ℓ ≠ 2 := by omega
        have hℓOdd : ℓ % 2 = 1 :=
          hℓ.eq_two_or_odd.resolve_left hℓNeTwo
        omega
      exact hℓLeQ.trans hqLe

private theorem spacedRepunit_eq_sum_X_pow (d q : ℕ) :
    RepunitMobiusNumerator.spacedRepunit d q =
      ∑ j ∈ Finset.range q, (Polynomial.X : ℤ[X]) ^ (d * j) := by
  simp [RepunitMobiusNumerator.spacedRepunit,
    Polynomial.monomial_one_right_eq_X_pow]

private theorem spacedRepunit_mul_X_pow_sub_one (d q : ℕ) :
    RepunitMobiusNumerator.spacedRepunit d q *
        ((Polynomial.X : ℤ[X]) ^ d - 1) =
      (Polynomial.X : ℤ[X]) ^ (d * q) - 1 := by
  rw [spacedRepunit_eq_sum_X_pow]
  simp_rw [pow_mul]
  exact geom_sum_mul ((Polynomial.X : ℤ[X]) ^ d) q

private theorem spacedRepunit_eq_prod_cyclotomic_sdiff
    {r d : ℕ} (hr : 0 < r) (hd : d ∣ r) :
    RepunitMobiusNumerator.spacedRepunit d (r / d) =
      ∏ e ∈ r.divisors \ d.divisors, Polynomial.cyclotomic e ℤ := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hr
  have hgeom := spacedRepunit_mul_X_pow_sub_one d (r / d)
  rw [Nat.mul_div_cancel' hd] at hgeom
  have hcycl :=
    Polynomial.X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd
      ℤ hd hr.ne'
  apply mul_left_cancel₀
      (by simpa using
        (Polynomial.X_pow_sub_C_ne_zero hdpos (1 : ℤ)))
  rw [mul_comm]
  exact hgeom.trans hcycl.symm

/-- A cyclotomic fibre absent from the block spacing divides the corresponding
spaced repunit.  This public wrapper is the geometric input used by the T5
new-prime fibre split. -/
theorem cyclotomic_dvd_spacedRepunit_of_not_dvd
    {r d m : ℕ} (hr : 0 < r) (hd : d ∣ r) (hm : m ∣ r)
    (hmd : ¬m ∣ d) :
    Polynomial.cyclotomic m ℤ ∣
      RepunitMobiusNumerator.spacedRepunit d (r / d) := by
  rw [spacedRepunit_eq_prod_cyclotomic_sdiff hr hd]
  apply Finset.dvd_prod_of_mem
  simp [Nat.mem_divisors, hm, hr.ne', hmd]

/-- On a cyclotomic fibre already present in the block spacing, the spaced
repunit is congruent to its number of blocks.  This is the old-fibre geometric
input for T5. -/
theorem cyclotomic_dvd_spacedRepunit_sub_C_of_dvd
    {r d m : ℕ} (hmd : m ∣ d) :
    Polynomial.cyclotomic m ℤ ∣
      RepunitMobiusNumerator.spacedRepunit d (r / d) -
        Polynomial.C (((r / d : ℕ) : ℤ)) := by
  rw [spacedRepunit_eq_sum_X_pow]
  have hconst :
      Polynomial.C (((r / d : ℕ) : ℤ)) =
        ∑ _j ∈ Finset.range (r / d), (1 : ℤ[X]) := by
          simp [Int.natCast_ediv]
          exact congrArg Polynomial.C (Int.natCast_div r d).symm
  rw [hconst]
  rw [← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro j hj
  have hmj : m ∣ d * j := hmd.trans (dvd_mul_right d j)
  exact (Polynomial.cyclotomic.dvd_X_pow_sub_one m ℤ).trans
    (dvd_pow_sub_one_of_dvd hmj)

private noncomputable def cyclotomicFibreConstant (r m : ℕ) : ℤ :=
  ∑ d ∈ r.divisors,
    if m ∣ d then
      ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ) ^ 2)
    else 0

private theorem cyclotomic_dvd_polynomial_sub_fibreConstant
    {r m : ℕ} (hr : 0 < r) (hm : m ∣ r) :
    Polynomial.cyclotomic m ℤ ∣
      RepunitMobiusNumerator.mobiusNumeratorPolynomial r -
        Polynomial.C (cyclotomicFibreConstant r m) := by
  classical
  rw [RepunitMobiusNumerator.mobiusNumeratorPolynomial,
    cyclotomicFibreConstant, map_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro d hd
  have hdr : d ∣ r := Nat.dvd_of_mem_divisors hd
  let a : ℤ := ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ))
  by_cases hmd : m ∣ d
  · rw [if_pos hmd]
    have h := cyclotomic_dvd_spacedRepunit_sub_C_of_dvd
      (r := r) hmd
    have hmul := dvd_mul_of_dvd_right h (Polynomial.C a)
    convert hmul using 1
    simp only [a, Polynomial.C_mul, map_pow]
    ring
  · simp only [if_neg hmd, map_zero, sub_zero]
    exact dvd_mul_of_dvd_right
      (cyclotomic_dvd_spacedRepunit_of_not_dvd hr hdr hm hmd)
      (Polynomial.C a)

private theorem cyclotomicFibreConstant_eq
    {r m : ℕ} (hr : Squarefree r) (hm : m ∣ r) :
    cyclotomicFibreConstant r m =
      ArithmeticFunction.moebius m * jordanTotientTwo (r / m) := by
  classical
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr.ne_zero
  have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hm hrpos
  let n := r / m
  have hmn : m * n = r := Nat.mul_div_cancel' hm
  have hsqmn : Squarefree (m * n) := by simpa [hmn] using hr
  have hcop : m.Coprime n := Nat.coprime_of_squarefree_mul hsqmn
  have hnpos : 0 < n := by
    exact Nat.div_pos (Nat.le_of_dvd hrpos hm) hmpos
  rw [cyclotomicFibreConstant, ← Finset.sum_filter]
  calc
    ∑ d ∈ {d ∈ r.divisors | m ∣ d},
        ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ) ^ 2) =
        ∑ e ∈ n.divisors,
          ArithmeticFunction.moebius (m * e) * (((n / e : ℕ) : ℤ) ^ 2) := by
            refine Finset.sum_bij'
              (fun d _hd ↦ d / m) (fun e _he ↦ m * e) ?_ ?_ ?_ ?_ ?_
            · intro d hd
              have hdr : d ∣ r := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
              have hmd : m ∣ d := (Finset.mem_filter.mp hd).2
              apply Nat.mem_divisors.mpr
              constructor
              · obtain ⟨k, hk⟩ := hdr
                refine ⟨k, ?_⟩
                apply Nat.mul_left_cancel hmpos
                calc
                  m * n = r := hmn
                  _ = d * k := hk
                  _ = (m * (d / m)) * k := by rw [Nat.mul_div_cancel' hmd]
                  _ = m * ((d / m) * k) := mul_assoc _ _ _
              · exact hnpos.ne'
            · intro e he
              have hen : e ∣ n := Nat.dvd_of_mem_divisors he
              apply Finset.mem_filter.mpr
              constructor
              · exact Nat.mem_divisors.mpr
                  ⟨by simpa [hmn] using Nat.mul_dvd_mul_left m hen, hr.ne_zero⟩
              · exact dvd_mul_right m e
            · intro d hd
              exact Nat.mul_div_cancel' (Finset.mem_filter.mp hd).2
            · intro e he
              exact Nat.mul_div_cancel_left e hmpos
            · intro d hd
              have hmd : m ∣ d := (Finset.mem_filter.mp hd).2
              change ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ) ^ 2) =
                ArithmeticFunction.moebius (m * (d / m)) *
                  (((n / (d / m) : ℕ) : ℤ) ^ 2)
              have hdEq : m * (d / m) = d := Nat.mul_div_cancel' hmd
              have hquot : r / d = n / (d / m) := by
                calc
                  r / d = (m * n) / (m * (d / m)) :=
                    congrArg₂ (fun x y : ℕ ↦ x / y) hmn.symm hdEq.symm
                  _ = n / (d / m) := Nat.mul_div_mul_left n (d / m) hmpos
              rw [hdEq, hquot]
    _ = ∑ e ∈ n.divisors,
          (ArithmeticFunction.moebius m * ArithmeticFunction.moebius e) *
            (((n / e : ℕ) : ℤ) ^ 2) := by
          apply Finset.sum_congr rfl
          intro e he
          have hen : e ∣ n := Nat.dvd_of_mem_divisors he
          rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
            (hcop.of_dvd_right hen)]
    _ = ArithmeticFunction.moebius m * jordanTotientTwo n := by
          rw [jordanTotientTwo_eq_divisorSum hnpos, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _he
          ring
    _ = ArithmeticFunction.moebius m * jordanTotientTwo (r / m) := rfl

/-- T2: the complete integral cyclotomic congruence. -/
theorem cyclotomic_dvd_mobiusNumeratorPolynomial_sub
    {r m : ℕ} (hr : Squarefree r) (hm : m ∣ r) :
    Polynomial.cyclotomic m ℤ ∣
      RepunitMobiusNumerator.mobiusNumeratorPolynomial r -
        Polynomial.C
          (ArithmeticFunction.moebius m * jordanTotientTwo (r / m)) := by
  rw [← cyclotomicFibreConstant_eq hr hm]
  exact cyclotomic_dvd_polynomial_sub_fibreConstant
    (Nat.pos_of_ne_zero hr.ne_zero) hm

/-- Evaluation form of T2, designed for T3 and T4. -/
theorem mobiusNumerator_mod_cyclotomicEval
    {r m : ℕ} (hr : Squarefree r) (hm : m ∣ r) :
    cyclotomicEval m ∣
      RadicalMobiusShadow.mobiusNumerator r -
        ArithmeticFunction.moebius m * jordanTotientTwo (r / m) := by
  have h := cyclotomic_dvd_mobiusNumeratorPolynomial_sub hr hm
  have heval := map_dvd (Polynomial.evalRingHom (R := ℤ) 2) h
  simpa [cyclotomicEval,
    RepunitMobiusNumerator.mobiusNumeratorPolynomial_eval_two hr] using heval

/-- Every cyclotomic channel divides its corresponding Mersenne value. -/
theorem cyclotomicValue_dvd_mersenne (m : ℕ) :
    cyclotomicValue m ∣ RadicalMobiusShadow.mersenne m := by
  have hpoly := Polynomial.cyclotomic.dvd_X_pow_sub_one m ℤ
  have heval := map_dvd (Polynomial.evalRingHom (R := ℤ) 2) hpoly
  have hpow : 1 ≤ (2 : ℕ) ^ m := one_le_pow₀ (by norm_num)
  have hint : cyclotomicEval m ∣
      (RadicalMobiusShadow.mersenne m : ℤ) := by
    simpa [cyclotomicEval, RadicalMobiusShadow.mersenne,
      Nat.cast_sub hpow] using heval
  simpa [cyclotomicValue] using Int.natAbs_dvd_natAbs.mpr hint

/-- Prime cyclotomic channels are exactly Mersenne channels. -/
theorem cyclotomicEval_prime {p : ℕ} (hp : p.Prime) :
    cyclotomicEval p = (RadicalMobiusShadow.mersenne p : ℤ) := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [cyclotomicEval, Polynomial.cyclotomic_prime]
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_pow,
    Polynomial.eval_X]
  have hgeom := geom_sum_mul (2 : ℤ) p
  have hpow : 1 ≤ (2 : ℕ) ^ p := one_le_pow₀ (by norm_num)
  simpa [RadicalMobiusShadow.mersenne,
    Nat.cast_sub hpow] using hgeom

@[simp]
theorem cyclotomicValue_prime {p : ℕ} (hp : p.Prime) :
    cyclotomicValue p = RadicalMobiusShadow.mersenne p := by
  rw [cyclotomicValue, cyclotomicEval_prime hp, Int.natAbs_natCast]

/-- T3: the top cyclotomic fibre cannot cancel from the numerator. -/
theorem mobiusNumerator_gcd_cyclotomicValue
    {r : ℕ} (hr : Squarefree r) :
    Nat.gcd
      (RadicalMobiusShadow.mobiusNumerator r).natAbs
      (cyclotomicValue r) = 1 := by
  have hdiv := mobiusNumerator_mod_cyclotomicEval hr (dvd_refl r)
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr.ne_zero
  simp only [Nat.div_self hrpos, jordanTotientTwo_one, mul_one] at hdiv
  obtain ⟨k, hk⟩ := hdiv
  have hmu : ArithmeticFunction.moebius r = 1 ∨
      ArithmeticFunction.moebius r = -1 :=
    ArithmeticFunction.moebius_ne_zero_iff_eq_or.mp
      (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hr)
  change Int.gcd (RadicalMobiusShadow.mobiusNumerator r)
    (cyclotomicEval r) = 1
  apply Nat.dvd_one.mp
  rw [Int.gcd_dvd_iff]
  rcases hmu with hmu | hmu
  · refine ⟨1, -k, ?_⟩
    rw [hmu] at hk
    calc
      (1 : ℤ) = RadicalMobiusShadow.mobiusNumerator r -
          (RadicalMobiusShadow.mobiusNumerator r - 1) := by ring
      _ = RadicalMobiusShadow.mobiusNumerator r - cyclotomicEval r * k := by
        rw [hk]
      _ = RadicalMobiusShadow.mobiusNumerator r * 1 +
          cyclotomicEval r * -k := by ring
  · refine ⟨-1, k, ?_⟩
    rw [hmu] at hk
    calc
      (1 : ℤ) = -RadicalMobiusShadow.mobiusNumerator r +
          (RadicalMobiusShadow.mobiusNumerator r + 1) := by ring
      _ = -RadicalMobiusShadow.mobiusNumerator r + cyclotomicEval r * k := by
        simpa only [sub_neg_eq_add] using congrArg
          (fun z : ℤ ↦ -RadicalMobiusShadow.mobiusNumerator r + z) hk
      _ = RadicalMobiusShadow.mobiusNumerator r * -1 +
          cyclotomicEval r * k := by ring

/-- The exact unscaled-denominator consequence of T3. -/
theorem cyclotomicValue_dvd_baseMobiusShadow_den
    {r : ℕ} (hr : Squarefree r) :
    cyclotomicValue r ∣ (RadicalMobiusShadow.baseMobiusShadow r).den := by
  simpa [RadicalMobiusShadow.baseMobiusShadow] using
    RationalDenominatorSurvival.divisor_dvd_divInt_den
      (a := RadicalMobiusShadow.mobiusNumerator r)
      (D := RadicalMobiusShadow.mersenne r)
      (m := cyclotomicValue r)
      (by
        simpa [RadicalMobiusShadow.mersenne] using
          Nat.sub_pos_of_lt (Nat.one_lt_two_pow hr.ne_zero))
      (cyclotomicValue_dvd_mersenne r)
      (by
        simpa [Nat.coprime_comm] using
          mobiusNumerator_gcd_cyclotomicValue hr)

private theorem eval_spacedRepunit_two {r d : ℕ}
    (hr : 0 < r) (hd : d ∣ r) :
    (RepunitMobiusNumerator.spacedRepunit d (r / d)).eval 2 =
      (((RadicalMobiusShadow.mersenne r /
          RadicalMobiusShadow.mersenne d : ℕ) : ℤ)) := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hr
  have htwo : 2 ≤ 2 ^ d := by
    have := Nat.one_lt_two_pow hdpos.ne'
    omega
  have hp : (2 ^ d) ^ (r / d) = 2 ^ r := by
    rw [← pow_mul, Nat.mul_div_cancel' hd]
  have hnat :
      ∑ j ∈ Finset.range (r / d), 2 ^ (d * j) =
        RadicalMobiusShadow.mersenne r /
          RadicalMobiusShadow.mersenne d := by
    simp_rw [pow_mul]
    rw [Nat.geomSum_eq htwo, hp]
    rfl
  rw [RepunitMobiusNumerator.spacedRepunit, Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_monomial, one_mul]
  exact_mod_cast hnat

/-- The geometric cofactor is congruent to `r / m` in the `m`-th channel.
This is the second algebraic bridge consumed by T4. -/
theorem mersenneQuotient_mod_cyclotomicEval
    {r m : ℕ} (hr : 0 < r) (hm : m ∣ r) :
    cyclotomicEval m ∣
      (((RadicalMobiusShadow.mersenne r /
          RadicalMobiusShadow.mersenne m : ℕ) : ℤ) -
        ((r / m : ℕ) : ℤ)) := by
  have hpoly := cyclotomic_dvd_spacedRepunit_sub_C_of_dvd
    (r := r) (d := m) (m := m) (dvd_refl m)
  have heval := map_dvd (Polynomial.evalRingHom (R := ℤ) 2) hpoly
  simpa [cyclotomicEval, eval_spacedRepunit_two hr hm] using heval

/-! ## Finite regression anchors

These are theorem-level elaboration anchors, not finite substitutes for T2 or
T3.  The larger generated matrix remains receipt evidence.
-/

private theorem squarefree_210 : Squarefree 210 := by
  have h6 : Squarefree (2 * 3) :=
    (Nat.squarefree_mul (by norm_num)).2
      ⟨Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩
  have h30 : Squarefree ((2 * 3) * 5) :=
    (Nat.squarefree_mul (by norm_num)).2
      ⟨h6, (by norm_num : Nat.Prime 5).squarefree⟩
  have h210 : Squarefree (((2 * 3) * 5) * 7) :=
    (Nat.squarefree_mul (by norm_num)).2
      ⟨h30, (by norm_num : Nat.Prime 7).squarefree⟩
  norm_num at h210 ⊢
  exact h210

private theorem squarefree_2310 : Squarefree 2310 := by
  have h : Squarefree (210 * 11) :=
    (Nat.squarefree_mul (by norm_num)).2
      ⟨squarefree_210, (by norm_num : Nat.Prime 11).squarefree⟩
  norm_num at h ⊢
  exact h

theorem t2_210_105_anchor :
    Polynomial.cyclotomic 105 ℤ ∣
      RepunitMobiusNumerator.mobiusNumeratorPolynomial 210 -
        Polynomial.C
          (ArithmeticFunction.moebius 105 * jordanTotientTwo (210 / 105)) := by
  exact cyclotomic_dvd_mobiusNumeratorPolynomial_sub squarefree_210 (by norm_num)

theorem t2_210_210_anchor :
    Polynomial.cyclotomic 210 ℤ ∣
      RepunitMobiusNumerator.mobiusNumeratorPolynomial 210 -
        Polynomial.C
          (ArithmeticFunction.moebius 210 * jordanTotientTwo (210 / 210)) := by
  exact cyclotomic_dvd_mobiusNumeratorPolynomial_sub squarefree_210 (by norm_num)

theorem t3_2310_anchor :
    Nat.gcd
      (RadicalMobiusShadow.mobiusNumerator 2310).natAbs
      (cyclotomicValue 2310) = 1 := by
  exact mobiusNumerator_gcd_cyclotomicValue squarefree_2310

#print axioms cyclotomic_dvd_mobiusNumeratorPolynomial_sub
#print axioms jordanTotientTwo_natAbs_primeFactors_le
#print axioms mobiusNumerator_mod_cyclotomicEval
#print axioms mobiusNumerator_gcd_cyclotomicValue
#print axioms cyclotomicValue_dvd_baseMobiusShadow_den
#print axioms mersenneQuotient_mod_cyclotomicEval

end Erdos249257.CyclotomicProjectionOfShadow
