import ErdosProblems.Erdos1049.SourceRootBlocksR13
import Mathlib

/-!
# Actual all-index Omega cancellation for the literal cleared B



At an ell-th primitive root only denominators with ell | j survive.
Their precise values need not be divided by an integer: the global block
identity is valid for an arbitrary function of the cutoff floor. This
avoids a spurious division at a root and also works in positive characteristic
in the finite-field stage. Descent to Z[X] uses a primitive complex root,
the cyclotomic minimal polynomial, coprimality over Q[X], and monic descent.
Distinct cyclotomic polynomials are NOT assumed comaximal over Z[X].
-/
namespace ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12 Finset
open scoped BigOperators

lemma finite_prefix_supported_on_multiples {R : Type*} [AddCommMonoid R]
    (g : ℕ → R) (ell J : ℕ) (hell : 0 < ell)
    (hzero : ∀ j ∈ Icc 1 J, ¬ ell ∣ j → g j = 0) :
    (∑ j ∈ Icc 1 J, g j) = ∑ b ∈ Icc 1 (J / ell), g (ell * b) := by
  classical
  have hfilter : (∑ j ∈ (Icc 1 J).filter (fun j => ell ∣ j), g j) =
      ∑ j ∈ Icc 1 J, g j := by
    apply sum_subset (filter_subset _ _)
    intro j hj hnot
    apply hzero j hj
    intro hdiv
    exact hnot (mem_filter.mpr ⟨hj, hdiv⟩)
  rw [← hfilter]
  symm
  refine sum_bij (fun b _ => ell * b) ?_ ?_ ?_ ?_
  · intro b hb
    obtain ⟨hb0, hbJ⟩ := mem_Icc.mp hb
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨by nlinarith, ?_⟩, dvd_mul_right _ _⟩
    have hm := (Nat.le_div_iff_mul_le hell).mp hbJ
    simpa only [Nat.mul_comm b ell] using hm
  · intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left hell hab
  · intro j hj
    obtain ⟨hjI, hdiv⟩ := mem_filter.mp hj
    obtain ⟨b, rfl⟩ := hdiv
    refine ⟨b, mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
    · have hj0 := (mem_Icc.mp hjI).1
      by_contra hb
      have : b = 0 := by omega
      simp [this] at hj0
    · apply (Nat.le_div_iff_mul_le hell).mpr
      simpa only [Nat.mul_comm b ell] using (mem_Icc.mp hjI).2
  · intro b hb
    rfl

section Field
variable {K : Type*} [Field K]

lemma root_power_ne_one_of_not_dvd (q : K) {ell j : ℕ} (hell : 0 < ell)
    (hroot : q ^ ell = 1)
    (hprimitive : ∀ a : ℕ, 0 < a → a < ell → q ^ a ≠ 1)
    (hdiv : ¬ ell ∣ j) : q ^ j ≠ 1 := by
  rw [root_power_reduce q hroot j]
  apply hprimitive _ _ (Nat.mod_lt _ hell)
  have hm : j % ell ≠ 0 := fun h => hdiv (Nat.dvd_of_mod_eq_zero h)
  omega

lemma sourceD_eval_zero_at_root (q : K) (n ell : ℕ) (hell : 0 < ell)
    (helln : ell ≤ 15 * n) (hroot : q ^ ell = 1) :
    (sourceD n).eval₂ (Int.castRingHom K) q = 0 := by
  have h := congrArg (Polynomial.eval₂ (Int.castRingHom K) q)
    (sourceDQuotient_factor n ell hell helln)
  simpa only [eval₂_mul, eval₂_sub, eval₂_pow, eval₂_X, eval₂_one,
    hroot, sub_self, zero_mul] using h.symm

lemma sourceDQuotient_eval_zero_of_not_dvd (q : K) (n ell j : ℕ)
    (hell : 0 < ell) (helln : ell ≤ 15 * n) (hroot : q ^ ell = 1)
    (hprimitive : ∀ a : ℕ, 0 < a → a < ell → q ^ a ≠ 1)
    (hj0 : 0 < j) (hjn : j ≤ 15 * n) (hdiv : ¬ ell ∣ j) :
    (sourceDQuotient n j).eval₂ (Int.castRingHom K) q = 0 := by
  have h := congrArg (Polynomial.eval₂ (Int.castRingHom K) q)
    (sourceDQuotient_factor n j hj0 hjn)
  simp only [eval₂_mul, eval₂_sub, eval₂_pow, eval₂_X, eval₂_one,
    sourceD_eval_zero_at_root q n ell hell helln hroot] at h
  exact (mul_eq_zero.mp h).resolve_left
    (sub_ne_zero.mpr (root_power_ne_one_of_not_dvd q hell hroot hprimitive hdiv))

lemma sourceShiftedASummand_eval_eq_of_dvd (q : K) (n ell s j : ℕ)
    (hroot : q ^ ell = 1) (hs : s ≤ 13 * n) (hj : j ≤ 14 * n)
    (hdiv : ell ∣ j) :
    (sourceShiftedASummand n s j).eval₂ (Int.castRingHom K) q =
      (sourceASummand n s).eval₂ (Int.castRingHom K) q := by
  have hp : q ^ j = 1 := by
    obtain ⟨b, rfl⟩ := hdiv
    rw [pow_mul, hroot, one_pow]
  have h := congrArg (Polynomial.eval₂ (Int.castRingHom K) q)
    (sourceShiftedASummand_factor n s j hs hj)
  simpa only [eval₂_mul, eval₂_pow, eval₂_X, pow_mul, hp, one_pow, one_mul] using h

noncomputable def sourcePolePrefix (q : K) (n ell L : ℕ) : K :=
  ∑ b ∈ Icc 1 L, (sourceDQuotient n (ell * b)).eval₂ (Int.castRingHom K) q

lemma sourceDQuotient_eval_prefix (q : K) (n ell J : ℕ)
    (hell : 0 < ell) (helln : ell ≤ 15 * n) (hroot : q ^ ell = 1)
    (hprimitive : ∀ a : ℕ, 0 < a → a < ell → q ^ a ≠ 1)
    (hJ : J ≤ 15 * n) :
    (∑ j ∈ Icc 1 J, (sourceDQuotient n j).eval₂ (Int.castRingHom K) q) =
      sourcePolePrefix q n ell (J / ell) := by
  apply finite_prefix_supported_on_multiples _ ell J hell
  intro j hj hdiv
  obtain ⟨hj0, hjJ⟩ := mem_Icc.mp hj
  exact sourceDQuotient_eval_zero_of_not_dvd q n ell j hell helln hroot hprimitive
    hj0 (hjJ.trans hJ) hdiv

/-- Actual cleared B, evaluated polynomially at the root. In particular, no
rational expression with a zero denominator is evaluated here. -/
theorem actual_cleared_B_root_prefix_identity (q : K) (n ell : ℕ)
    (hell : 0 < ell) (helln : ell ≤ 15 * n) (hroot : q ^ ell = 1)
    (hprimitive : ∀ a : ℕ, 0 < a → a < ell → q ^ a ≠ 1) :
    (sourceClearedB n).eval₂ (Int.castRingHom K) q =
      ∑ s ∈ range (13 * n + 1),
        (sourceASummand n s).eval₂ (Int.castRingHom K) q *
          (sourcePolePrefix q n ell ((2 * n + s) / ell) +
            sourcePolePrefix q n ell (14 * n / ell)) := by
  classical
  let f : ℤ[X] →+* K := Polynomial.eval₂RingHom (Int.castRingHom K) q
  change f (sourceClearedB n) = _
  unfold sourceClearedB
  rw [map_sum]
  apply sum_congr rfl
  intro s hs
  have hs' : s ≤ 13 * n := by have := mem_range.mp hs; omega
  have hshift : (∑ j ∈ Icc 1 (14 * n), f (sourceShiftedASummand n s j * sourceDQuotient n j)) =
      ∑ j ∈ Icc 1 (14 * n), f (sourceASummand n s * sourceDQuotient n j) := by
    apply sum_congr rfl
    intro j hj
    obtain ⟨hj0, hjn⟩ := mem_Icc.mp hj
    rw [map_mul, map_mul]
    by_cases hdiv : ell ∣ j
    · rw [show f (sourceShiftedASummand n s j) = f (sourceASummand n s) from
        sourceShiftedASummand_eval_eq_of_dvd q n ell s j hroot hs' hjn hdiv]
    · have hz : f (sourceDQuotient n j) = 0 :=
        sourceDQuotient_eval_zero_of_not_dvd q n ell j hell helln hroot hprimitive
          hj0 (by omega) hdiv
      rw [hz, mul_zero, mul_zero]
  rw [map_add, map_sum, map_sum, hshift]
  simp only [map_mul, ← mul_sum]
  rw [show (∑ j ∈ Icc 1 (2 * n + s), f (sourceDQuotient n j)) =
      sourcePolePrefix q n ell ((2 * n + s) / ell) from
        sourceDQuotient_eval_prefix q n ell (2 * n + s) hell helln hroot hprimitive (by omega),
    show (∑ j ∈ Icc 1 (14 * n), f (sourceDQuotient n j)) =
      sourcePolePrefix q n ell (14 * n / ell) from
        sourceDQuotient_eval_prefix q n ell (14 * n) hell helln hroot hprimitive (by omega)]
  exact (mul_add _ _ _).symm

/-- Complete root cancellation at every selected cyclotomic factor. -/
theorem actual_cleared_B_root_zero (q : K) (hq : q ≠ 0) (n ell : ℕ)
    (hell : 0 < ell) (helln : ell ≤ 15 * n) (hroot : q ^ ell = 1)
    (hprimitive : ∀ a : ℕ, 0 < a → a < ell → q ^ a ≠ 1)
    (hweight : sourceWeight n ell = 1) :
    (sourceClearedB n).eval₂ (Int.castRingHom K) q = 0 := by
  rcases sourceWeight_one_carry_cases n ell hweight with hfirst | ⟨hfirst, hsecond⟩
  · exact actual_cleared_B_first_carry_zero q hq n ell hell hroot hprimitive hfirst
  · rw [actual_cleared_B_root_prefix_identity q n ell hell helln hroot hprimitive]
    exact actual_source_second_carry_weighted_zero q hq n ell hell hroot hprimitive
      hfirst hsecond (fun L => sourcePolePrefix q n ell L + sourcePolePrefix q n ell (14 * n / ell))

end Field

/-- Individual integral divisibility, obtained from the actual polynomial
and a genuine primitive complex root, not from a divisibility assumption. -/
theorem actual_B_cyclotomic_dvd (n ell : ℕ) (hell : 0 < ell)
    (helln : ell ≤ 15 * n) (hweight : sourceWeight n ell = 1) :
    cyclotomic ell ℤ ∣ sourceBWithoutMonomial n := by
  let q : ℂ := Complex.exp (2 * Real.pi * Complex.I / ell)
  have hp : IsPrimitiveRoot q ell := Complex.isPrimitiveRoot_exp ell hell.ne'
  have hq : q ≠ 0 := by
    intro hz
    have hh := hp.pow_eq_one
    rw [hz, zero_pow hell.ne'] at hh
    exact zero_ne_one hh
  have hprimitive : ∀ a : ℕ, 0 < a → a < ell → q ^ a ≠ 1 := by
    intro a ha0 haell hpow
    have hdiv := hp.dvd_of_pow_eq_one a hpow
    have hle := Nat.le_of_dvd ha0 hdiv
    omega
  have hzero := actual_cleared_B_root_zero q hq n ell hell helln hp.pow_eq_one hprimitive hweight
  rw [actual_B_monomial_factor, eval₂_mul, eval₂_pow, eval₂_X] at hzero
  have hb : (sourceBWithoutMonomial n).eval₂ (Int.castRingHom ℂ) q = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ hq)
  rw [cyclotomic_eq_minpoly hp hell]
  apply minpoly.isIntegrallyClosed_dvd (hp.isIntegral hell)
  simpa only [aeval_def] using hb

lemma coprime_finset_product_right {R : Type*} [CommSemiring R]
    (a : R) (s : Finset ℕ) (f : ℕ → R)
    (h : ∀ i ∈ s, IsCoprime a (f i)) : IsCoprime a (∏ i ∈ s, f i) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty => intro h; simpa using (isCoprime_one_right : IsCoprime a 1)
  | @insert i s hi ih =>
      intro h
      rw [prod_insert hi]
      exact (h i (mem_insert_self _ _)).mul_right
        (ih (fun j hj => h j (mem_insert_of_mem hj)))

lemma pairwise_coprime_finset_product_dvd {R : Type*} [CommSemiring R]
    (s : Finset ℕ) (f : ℕ → R) (p : R)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (f i) (f j))
    (hdiv : ∀ i ∈ s, f i ∣ p) : (∏ i ∈ s, f i) ∣ p := by
  classical
  revert hpair hdiv
  induction s using Finset.induction_on with
  | empty => intro hpair hdiv; simp
  | @insert i s hi ih =>
      intro hpair hdiv
      rw [prod_insert hi]
      have hcop := coprime_finset_product_right (f i) s f (fun j hj =>
        hpair i (mem_insert_self _ _) j (mem_insert_of_mem hj)
          (fun hij => hi (by simpa only [hij] using hj)))
      apply hcop.mul_dvd (hdiv i (mem_insert_self _ _))
      apply ih
      · intro a ha b hb hab
        exact hpair a (mem_insert_of_mem ha) b (mem_insert_of_mem hb) hab
      · intro a ha
        exact hdiv a (mem_insert_of_mem ha)

/-- All selected factors divide simultaneously. The coprimality step is over
Q[X]; monicity then descends the divisibility to Z[X]. -/
theorem actual_Omega_divides_B_without_monomial (n : ℕ) :
    sourceOmega n ∣ sourceBWithoutMonomial n := by
  classical
  let f : ℤ →+* ℚ := Int.castRingHom ℚ
  apply (Polynomial.map_dvd_map f Int.cast_injective (sourceOmega_monic n)).mp
  have hOmega : (sourceOmega n).map f =
      ∏ ell ∈ Icc 1 (15 * n), (cyclotomic ell ℚ) ^ (sourceWeight n ell).toNat := by
    simp only [sourceOmega, Polynomial.map_prod, Polynomial.map_pow]
    apply prod_congr rfl
    intro ell hell
    dsimp only [f]
    rw [map_cyclotomic_int ell ℚ]
  rw [hOmega]
  apply pairwise_coprime_finset_product_dvd
  · intro i hi j hj hij
    rcases sourceWeight_zero_or_one n i with hwi | hwi
    · simpa [hwi] using
        (isCoprime_one_left : IsCoprime (1 : ℚ[X])
          ((cyclotomic j ℚ) ^ (sourceWeight n j).toNat))
    rcases sourceWeight_zero_or_one n j with hwj | hwj
    · simpa [hwj] using
        (isCoprime_one_right : IsCoprime
          ((cyclotomic i ℚ) ^ (sourceWeight n i).toNat) (1 : ℚ[X]))
    simpa [hwi, hwj] using (Polynomial.cyclotomic.isCoprime_rat hij)
  · intro ell hell
    rcases sourceWeight_zero_or_one n ell with hw | hw
    · simp [hw]
    simp only [hw, Int.toNat_one, pow_one]
    have h := actual_B_cyclotomic_dvd n ell (mem_Icc.mp hell).1 (mem_Icc.mp hell).2 hw
    obtain ⟨p, hp⟩ := h
    refine ⟨p.map f, ?_⟩
    rw [hp, Polynomial.map_mul, map_cyclotomic_int]

/-- The remainder in R13's canonical quotient is now proved zero, for every n. -/
theorem actual_Omega_remainder_zero (n : ℕ) : sourceOmegaRemainder n = 0 :=
  (actual_Omega_remainder_zero_iff n).mpr (actual_Omega_divides_B_without_monomial n)

theorem actual_B_polynomial_inclusion (n : ℕ) :
    sourceClearedB n = sourceOmega n * X ^ sourceM n * sourceV n :=
  (actual_B_inclusion_iff_remainder n).mpr (actual_Omega_remainder_zero n)

theorem actual_B_without_monomial_factor (n : ℕ) :
    sourceBWithoutMonomial n = sourceOmega n * sourceV n := by
  have h := actual_B_Omega_division n
  simpa only [actual_Omega_remainder_zero n, zero_add] using h.symm

theorem actual_V_nonzero (n : ℕ) (hn : 1 ≤ n) : sourceV n ≠ 0 := by
  intro hz
  apply actual_B_without_monomial_ne_zero n hn
  rw [actual_B_without_monomial_factor, hz, mul_zero]

theorem actual_V_degree_and_leadingCoeff (n : ℕ) (hn : 1 ≤ n) :
    (sourceV n).natDegree = (sourceU n).natDegree - 1 ∧
    (sourceV n).leadingCoeff = (-1 : ℤ) ^ (13 * n) := by
  refine ⟨actual_V_quotient_degree n hn, ?_⟩
  have h := congrArg Polynomial.leadingCoeff (actual_B_without_monomial_factor n)
  rw [leadingCoeff_mul, (sourceOmega_monic n).leadingCoeff, one_mul,
    (actual_B_without_monomial_degree_and_leadingCoeff n hn).2] at h
  exact h.symm

/-- Both literal polynomial inclusions, with the actual canonical U and V. -/
theorem actual_cancelled_polynomial_pair (n : ℕ) :
    sourceD n * sourceA n = sourceOmega n * X ^ sourceM n * sourceU n ∧
    sourceClearedB n = sourceOmega n * X ^ sourceM n * sourceV n :=
  ⟨actual_A_polynomial_inclusion n, actual_B_polynomial_inclusion n⟩

end ErdosProblems.Erdos1049.PaperR13
