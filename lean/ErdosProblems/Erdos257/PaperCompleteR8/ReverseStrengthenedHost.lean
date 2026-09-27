import ErdosProblems.Erdos257.PaperCompleteR8.DivisorCubeMoments
import ErdosProblems.Erdos257.PaperCompleteR8.PrimeHarmonicBlocks
import ErdosProblems.Erdos257.PaperCompleteR8.WeightedReturn
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib

/-!
# A constructed squarefree strengthened-cover host outside every old cover

This proof uses a different admissible row schedule from the historical note.
It avoids deleting an infinite reserved-prime set and does not need disjoint
rows. The finite harmonic supplier is used after deleting all primes <= q_j.
The factor (j+1) in S_j >= (j+1)*sqrt(q_j) is essential: S~sqrt(q) alone
would not make the old logarithmic-square obstruction unbounded.
The witness here is a squarefree divisor-cube host with rows supplied by
`exists_odd_prime_harmonic_block`; it is not the paper's printed
bounded-mass fresh-prime construction, and neither result stands in for the other.

-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257.PaperCompleteR7
open Erdos249257

def reverseScale (j : ℕ) : ℕ := (j + 2) * 2 ^ (j + 2)

/-- Arithmetic row data only: no analytic endpoint occurs among the fields. -/
structure ReverseRow (j : ℕ) where
  q : ℕ
  q_prime : Nat.Prime q
  q_large : reverseScale j ^ 2 ≤ q
  primes : Finset ℕ
  primes_large : ∀ p ∈ primes, Nat.Prime p ∧ q < p
  mass_lower : ((j + 1 : ℕ) : ℝ) * Real.sqrt q ≤ primeReciprocalMass primes
  mass_upper : primeReciprocalMass primes ≤ ((j + 1 : ℕ) : ℝ) * Real.sqrt q + 1

/-- Every row is supplied by Euclid's prime theorem and the checked finite
harmonic-block theorem. No cover or obstruction is supplied as a premise. -/
theorem exists_reverseRow (j : ℕ) : Nonempty (ReverseRow j) := by
  obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes (reverseScale j ^ 2)
  let R : ℝ := ((j + 1 : ℕ) : ℝ) * Real.sqrt q
  have hR : 0 ≤ R := mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  obtain ⟨P, hP, hlow, hupp⟩ := exists_odd_prime_harmonic_block (range (q + 1)) R hR
  refine ⟨⟨q, hprime, hq, P, ?_, hlow, hupp⟩⟩
  intro p hp
  have hn := ((hP p hp).2.2)
  have hnot : ¬ p < q + 1 := by simpa only [mem_range] using hn
  exact ⟨(hP p hp).1, by omega⟩

def reverseRow (j : ℕ) : ReverseRow j := Classical.choice (exists_reverseRow j)

theorem ReverseRow.scale_le_sqrt {j : ℕ} (R : ReverseRow j) :
    (reverseScale j : ℝ) ≤ Real.sqrt R.q := by
  have hq : (reverseScale j : ℝ) ^ 2 ≤ (R.q : ℝ) := by exact_mod_cast R.q_large
  have hs := Real.sq_sqrt (Nat.cast_nonneg R.q)
  have hnn := Real.sqrt_nonneg (R.q : ℝ)
  have hsc := Nat.cast_nonneg (α := ℝ) (reverseScale j)
  nlinarith

theorem reverseScale_ge_index (j : ℕ) : j + 2 ≤ reverseScale j := by
  have hp : 1 ≤ (2 : ℕ) ^ (j + 2) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold reverseScale
  nlinarith

theorem ReverseRow.q_gt_index {j : ℕ} (R : ReverseRow j) : j + 1 < R.q := by
  have hs := reverseScale_ge_index j
  have hq := R.q_large
  nlinarith

theorem ReverseRow.sqrt_ge_one {j : ℕ} (R : ReverseRow j) :
    1 ≤ Real.sqrt R.q := by
  have hi : (1 : ℝ) ≤ reverseScale j := by exact_mod_cast (by
    have := reverseScale_ge_index j; omega : 1 ≤ reverseScale j)
  exact hi.trans R.scale_le_sqrt

theorem ReverseRow.mass_ge_index {j : ℕ} (R : ReverseRow j) :
    ((j + 1 : ℕ) : ℝ) ≤ primeReciprocalMass R.primes := by
  have h := mul_le_mul_of_nonneg_left R.sqrt_ge_one (Nat.cast_nonneg (j + 1))
  have h' : ((j + 1 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * Real.sqrt R.q := by simpa using h
  exact h'.trans R.mass_lower

theorem ReverseRow.mass_pos {j : ℕ} (R : ReverseRow j) :
    0 < primeReciprocalMass R.primes := by
  have h0 : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos j
  exact h0.trans_le R.mass_ge_index

/-- The strengthened first-log cost is geometrically summable. -/
theorem ReverseRow.mass_ratio_bound {j : ℕ} (R : ReverseRow j) :
    primeReciprocalMass R.primes / (R.q : ℝ) ≤ 1 / (2 : ℝ) ^ (j + 2) := by
  have hq : (0 : ℝ) < R.q := by exact_mod_cast R.q_prime.pos
  have hp : (0 : ℝ) < (2 : ℝ) ^ (j + 2) := by positivity
  have hs := R.scale_le_sqrt
  have hsq := Real.sq_sqrt (Nat.cast_nonneg R.q)
  have hs1 := R.sqrt_ge_one
  have hupper : primeReciprocalMass R.primes ≤ ((j + 2 : ℕ) : ℝ) * Real.sqrt R.q := by
    have hu := R.mass_upper
    push_cast at hu ⊢
    nlinarith
  have hsc : (((j + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (j + 2)) ≤ Real.sqrt R.q := by
    simpa only [reverseScale, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hs
  have hm := mul_le_mul_of_nonneg_right hsc (Real.sqrt_nonneg (R.q : ℝ))
  have hu := mul_le_mul_of_nonneg_right hupper hp.le
  apply (div_le_div_iff₀ hq hp).mpr
  nlinarith only [hm, hu, hsq]

/-- The old second-log cost, in contrast, grows quadratically in j. -/
theorem ReverseRow.square_mass_ratio {j : ℕ} (R : ReverseRow j) :
    (((j + 1 : ℕ) : ℝ) ^ 2) ≤ (primeReciprocalMass R.primes) ^ 2 / (R.q : ℝ) := by
  have hq : (0 : ℝ) < R.q := by exact_mod_cast R.q_prime.pos
  have hlow := R.mass_lower
  have hs := Real.sqrt_nonneg (R.q : ℝ)
  have hj := Nat.cast_nonneg (α := ℝ) (j + 1)
  have hS := R.mass_pos.le
  have hsq := Real.sq_sqrt (Nat.cast_nonneg R.q)
  have h2 := mul_self_le_mul_self (mul_nonneg hj hs) hlow
  have h3 : (((j + 1 : ℕ) : ℝ) * Real.sqrt R.q) * (((j + 1 : ℕ) : ℝ) * Real.sqrt R.q) =
      ((j + 1 : ℕ) : ℝ) ^ 2 * R.q := by
    linear_combination (((j + 1 : ℕ) : ℝ) ^ 2) * hsq
  apply (le_div_iff₀ hq).mpr
  nlinarith [h2, h3]

def reverseExponent (j : ℕ) : ℝ := exponentFromIncrement
  (1 / primeReciprocalMass (reverseRow j).primes)

theorem reverseExponent_bounds (j : ℕ) : 0 < reverseExponent j ∧ reverseExponent j ≤ 1 := by
  apply exponentFromIncrement_bounds (one_div_pos.mpr (reverseRow j).mass_pos)
  apply (div_le_one (reverseRow j).mass_pos).mpr
  have h1 : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
  exact h1.trans (reverseRow j).mass_ge_index

def reverseFrame (j : ℕ) : FiniteCoverFrame :=
  cubeCoverFrame (reverseRow j).q (reverseRow j).primes (reverseExponent j)
    (reverseRow j).q_prime.pos (fun p hp => ((reverseRow j).primes_large p hp).1)
    (reverseExponent_bounds j).1 (reverseExponent_bounds j).2

def reverseHost : Set ℕ := {a | ∃ j, a ∈ (reverseFrame j).support}

def reverseCover : PositiveCoverData where
  frame := fun j => (reverseFrame j).support
  exponent := reverseExponent
  coefficient := fun j => (reverseFrame j).coefficient
  frame_positive := fun j => (reverseFrame j).positive
  exponent_bounds := reverseExponent_bounds
  coefficient_nonneg := fun j => (reverseFrame j).coefficient_nonneg
  column_summable := fun j => (reverseFrame j).column_summable
  majorises := fun j => (reverseFrame j).majorises

theorem reverseCover_host : reverseCover.host = reverseHost := rfl

theorem reverseCover_row_cost_bound (j : ℕ) : reverseCover.cost j ≤ Real.exp 1 / (reverseRow j).q := by
  have hS := (reverseRow j).mass_pos
  have h := cubeProductCost_le_exp (reverseRow j).q (reverseRow j).primes
    (1 / primeReciprocalMass (reverseRow j).primes) (one_div_nonneg.mpr hS.le)
  have he : (2 : ℝ) ^ reverseExponent j - 1 =
      1 / primeReciprocalMass (reverseRow j).primes := by
    rw [reverseExponent, two_rpow_exponentFromIncrement (one_div_pos.mpr hS)]
    ring
  change (reverseFrame j).cost ≤ _
  rw [reverseFrame, cubeCoverFrame_cost, he]
  simpa only [one_div_mul_cancel hS.ne'] using h

theorem reverse_geometric_factor_bound (j : ℕ) :
    (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * reverseExponent j) ≤ Real.exp 1 := by
  let S := primeReciprocalMass (reverseRow j).primes
  have hS : 0 < S := (reverseRow j).mass_pos
  have hidx : ((j + 1 : ℕ) : ℝ) ≤ S := (reverseRow j).mass_ge_index
  have hpow : (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * reverseExponent j) =
      (1 + 1 / S) ^ (j + 1) := by
    rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    rw [reverseExponent, two_rpow_exponentFromIncrement (one_div_pos.mpr hS)]
  rw [hpow]
  have hbase : 1 + 1 / S ≤ Real.exp (1 / S) := by
    simpa [add_comm] using Real.add_one_le_exp (1 / S)
  have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + 1 / S) hbase (j + 1)
  have he : Real.exp (1 / S) ^ (j + 1) = Real.exp (((j + 1 : ℕ) : ℝ) / S) := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using (Real.exp_nat_mul (1 / S) (j + 1)).symm
  exact h.trans (he.le.trans (Real.exp_le_exp.mpr ((div_le_one hS).mpr hidx)))

theorem reverse_strengthened_term_bound (j : ℕ) :
    reverseCover.cost j * (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * reverseExponent j) /
      ((2 : ℝ) ^ reverseExponent j - 1) ≤
      (Real.exp 1) ^ 2 / (2 : ℝ) ^ (j + 2) := by
  let S := primeReciprocalMass (reverseRow j).primes
  have hS : 0 < S := (reverseRow j).mass_pos
  have hq : (0 : ℝ) < (reverseRow j).q := by exact_mod_cast (reverseRow j).q_prime.pos
  have he : (2 : ℝ) ^ reverseExponent j - 1 = 1 / S := by
    rw [reverseExponent, two_rpow_exponentFromIncrement (one_div_pos.mpr hS)]
    ring
  have hmul := mul_le_mul (reverseCover_row_cost_bound j) (reverse_geometric_factor_bound j)
    (Real.rpow_nonneg (by norm_num) _) (div_nonneg (Real.exp_pos _).le hq.le)
  rw [he]
  have hdiv := div_le_div_of_nonneg_right hmul (one_div_nonneg.mpr hS.le)
  have hratio := mul_le_mul_of_nonneg_left (reverseRow j).mass_ratio_bound
    (sq_nonneg (Real.exp 1))
  have heq : (Real.exp 1 / ((reverseRow j).q : ℝ) * Real.exp 1) / (1 / S) =
      (Real.exp 1) ^ 2 * (S / ((reverseRow j).q : ℝ)) := by field_simp
  rw [heq] at hdiv
  exact hdiv.trans (by simpa only [mul_one_div] using hratio)

theorem reverseCover_strengthened : reverseCover.StrengthenedCostSummable := by
  have hs : Summable (fun j => (Real.exp 1) ^ 2 * coverThreshold (1 / 2) j) :=
    (summable_coverThreshold (1 / 2)).mul_left _
  apply Summable.of_nonneg_of_le _ _ hs
  · intro j
    exact div_nonneg (mul_nonneg (positiveCover_cost_nonneg reverseCover j)
      (Real.rpow_nonneg (by norm_num) _))
      (sub_pos.mpr (Real.one_lt_rpow (by norm_num) (reverseExponent_bounds j).1)).le
  · intro j
    have h := reverse_strengthened_term_bound j
    convert h using 1
    unfold coverThreshold
    rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
    ring

theorem reverseHost_has_strengthened_cover : HasStrengthenedPositiveCover reverseHost :=
  ⟨reverseCover, Set.Subset.refl _, reverseCover_strengthened⟩

theorem reverseHost_positive : 0 ∉ reverseHost := by
  rintro ⟨j, hj⟩
  exact (reverseFrame j).positive hj

theorem reverseHost_squarefree : ∀ a ∈ reverseHost, Squarefree a := by
  rintro a ⟨j, hj⟩
  let R := reverseRow j
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hj
  have hqP : R.q ∉ R.primes := by
    intro h
    exact (lt_irrefl R.q) (R.primes_large R.q h).2
  have hsq := squarefree_prime_product (insert R.q R.primes) (by
    intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · exact R.q_prime
    · exact (R.primes_large p hp).1)
  rw [Finset.prod_insert hqP] at hsq
  exact hsq.squarefree_of_dvd (Nat.mul_dvd_mul_left R.q (Nat.dvd_of_mem_divisors hd))

theorem reverseHost_infinite : reverseHost.Infinite := by
  intro hfinite
  obtain ⟨B, hB⟩ := hfinite.bddAbove
  have hqmem : (reverseRow B).q ∈ reverseHost := by
    refine ⟨B, ?_⟩
    exact factor_mem_divisorCube _ _ (fun p hp => ((reverseRow B).primes_large p hp).1)
  have hlarge := (reverseRow B).q_gt_index
  have hle := hB hqmem
  omega

theorem exists_large_square_multiple (c R : ℝ) (hc : 0 < c) (J : ℕ) :
    ∃ j : ℕ, J ≤ j ∧ R < c * (((j + 1 : ℕ) : ℝ) ^ 2) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (R / c)
  let j := max k J
  have hjk : (k : ℝ) ≤ j := by exact_mod_cast le_max_left k J
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hsq : (j : ℝ) ≤ (((j + 1 : ℕ) : ℝ) ^ 2) := by push_cast; nlinarith
  have hR : R < (k : ℝ) * c := (div_lt_iff₀ hc).mp hk
  have hm := mul_le_mul_of_nonneg_left (hjk.trans hsq) hc.le
  exact ⟨j, le_max_right _ _, by nlinarith⟩

theorem reverseHost_unbounded_old_moments :
    ∀ T : ℝ, ∃ F : Finset ℕ, (F : Set ℕ) ⊆ reverseHost ∧
      ∃ X : ℕ, 0 < X ∧ T < finiteLogSquareMean F X := by
  intro T
  let c := (Real.log 2) ^ 2 / 2
  have hc : 0 < c := div_pos (sq_pos_of_pos (Real.log_pos (by norm_num))) (by norm_num)
  obtain ⟨j, hj, hT⟩ := exists_large_square_multiple c T hc 0
  let R := reverseRow j
  have hP : ∀ p ∈ R.primes, Nat.Prime p := fun p hp => (R.primes_large p hp).1
  have h := cube_logSquare_mean_lower R.q R.primes R.q_prime.pos hP
  have hm := mul_le_mul_of_nonneg_left R.square_mass_ratio hc.le
  refine ⟨(reverseFrame j).support, (fun a ha => ⟨j, ha⟩),
    R.q * R.primes.prod id, Nat.mul_pos R.q_prime.pos (prime_product_pos _ hP), ?_⟩
  change T < finiteLogSquareMean (divisorCube R.q R.primes) _
  have hh : c * (((j + 1 : ℕ) : ℝ) ^ 2) ≤
      finiteLogSquareMean (divisorCube R.q R.primes) (R.q * R.primes.prod id) := by
    exact hm.trans (by convert h using 1 <;> dsimp [c] <;> ring)
  exact hT.trans_le hh

theorem reverseHost_no_old_cover : ¬ HasOldPositiveCover reverseHost :=
  no_old_cover_of_unbounded_logSquare_means reverseHost reverseHost_unbounded_old_moments

theorem reverse_row_reciprocal_lower (j : ℕ) :
    (((j + 1 : ℕ) : ℝ) ^ 2) / 4 ≤ ∑ a ∈ (reverseFrame j).support, (1 : ℝ) / a := by
  let R := reverseRow j
  have hP : ∀ p ∈ R.primes, Nat.Prime p := fun p hp => (R.primes_large p hp).1
  rw [show (reverseFrame j).support = divisorCube R.q R.primes from rfl,
    cube_reciprocal_sum R.q R.primes R.q_prime.pos hP]
  have h := cubeProductCost_quadratic_lower R.q R.primes 1 hP (by norm_num) le_rfl
  have hratio := div_le_div_of_nonneg_right R.square_mass_ratio (by norm_num : (0 : ℝ) ≤ 4)
  exact hratio.trans (by convert h using 1 <;> ring)

theorem reverseHost_reciprocal_not_summable :
    ¬ Summable (Set.indicator reverseHost (fun a : ℕ => (1 : ℝ) / a)) := by
  intro hs
  let T := ∑' a : ℕ, Set.indicator reverseHost (fun a => (1 : ℝ) / a) a
  obtain ⟨j, hj, hT⟩ := exists_large_square_multiple (1 / 4) T (by norm_num) 0
  have hb := hs.sum_le_tsum (reverseFrame j).support (fun a ha =>
    Set.indicator_nonneg (fun a _ => one_div_nonneg.mpr (Nat.cast_nonneg a)) a)
  have heq : (∑ a ∈ (reverseFrame j).support,
      Set.indicator reverseHost (fun a => (1 : ℝ) / a) a) =
      ∑ a ∈ (reverseFrame j).support, (1 : ℝ) / a := by
    apply Finset.sum_congr rfl
    intro a ha
    exact Set.indicator_of_mem (show a ∈ reverseHost from ⟨j, ha⟩) _
  rw [heq] at hb
  have hl := reverse_row_reciprocal_lower j
  dsimp [T] at hT
  nlinarith

/-- A finite set of smaller primes is absent from every factor of a row. -/
theorem no_smaller_prime_divides_cube {j : ℕ} (R : ReverseRow j)
    (p a : ℕ) (hp : Nat.Prime p) (hpq : p < R.q) (ha : a ∈ divisorCube R.q R.primes) :
    ¬ p ∣ a := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ha
  intro hpa
  rcases hp.dvd_mul.mp hpa with hpq' | hpd
  · have heq := (Nat.prime_dvd_prime_iff_eq hp R.q_prime).mp hpq'
    omega
  · have hpM := hpd.trans (Nat.dvd_of_mem_divisors hd)
    have hP : ∀ r ∈ R.primes, Nat.Prime r := fun r hr => (R.primes_large r hr).1
    have hmem : p ∈ (R.primes.prod id).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpM, (prime_product_pos _ hP).ne'⟩
    change p ∈ (∏ r ∈ R.primes, r).primeFactors at hmem
    rw [Nat.primeFactors_prod hP] at hmem
    have hlarge := (R.primes_large p hmem).2
    omega

theorem reverse_row_primePart_one (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (j : ℕ) (hj : P.sup id ≤ j) (a : ℕ) (ha : a ∈ (reverseFrame j).support) :
    primeSetPart P a = 1 := by
  unfold primeSetPart
  apply Finset.prod_eq_one
  intro p hp
  have hpj : p ≤ j := (Finset.le_sup hp).trans hj
  have hpq : p < (reverseRow j).q := by have := (reverseRow j).q_gt_index; omega
  have hnd := no_smaller_prime_divides_cube (reverseRow j) p a (hP p hp) hpq ha
  rw [Nat.factorization_eq_zero_of_not_dvd hnd, pow_zero]

theorem reverse_row_weighted_sum (b : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (j : ℕ) (hj : P.sup id ≤ j) :
    (∑ a ∈ (reverseFrame j).support, primeWeightedTerm b P a) =
      (∑ a ∈ (reverseFrame j).support, (1 : ℝ) / a) / ((b : ℝ) - 1) := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  unfold primeWeightedTerm
  rw [reverse_row_primePart_one P hP j hj a ha]
  simp only [Nat.cast_one, pow_one]
  rw [div_div]

/-- All finite-prime weighted tests fail at every integer base, including
P empty. The official FinitePrimeWeighted predicate requires P nonempty. -/
theorem reverseHost_no_weighted_sum (b : ℕ) (hb : 2 ≤ b)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    ¬ Summable (Set.indicator reverseHost (primeWeightedTerm b P)) := by
  intro hs
  let T := ∑' a, Set.indicator reverseHost (primeWeightedTerm b P) a
  have hbR : 0 < (b : ℝ) - 1 := by
    have hbc : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  let c := 1 / (4 * ((b : ℝ) - 1))
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨j, hj, hT⟩ := exists_large_square_multiple c T hc (P.sup id)
  have hbnd := hs.sum_le_tsum (reverseFrame j).support (fun a ha =>
    Set.indicator_nonneg (fun a _ => primeWeightedTerm_nonneg b hb P a) a)
  have heq : (∑ a ∈ (reverseFrame j).support, Set.indicator reverseHost (primeWeightedTerm b P) a) =
      ∑ a ∈ (reverseFrame j).support, primeWeightedTerm b P a := by
    apply Finset.sum_congr rfl
    intro a ha
    exact Set.indicator_of_mem (show a ∈ reverseHost from ⟨j, ha⟩) _
  rw [heq, reverse_row_weighted_sum b P hP j hj] at hbnd
  have hlo := div_le_div_of_nonneg_right (reverse_row_reciprocal_lower j) hbR.le
  have hh : c * (((j + 1 : ℕ) : ℝ) ^ 2) ≤ T := by
    have hcj : c * (((j + 1 : ℕ) : ℝ) ^ 2) = (((j + 1 : ℕ) : ℝ) ^ 2) / 4 / ((b : ℝ) - 1) := by
      have hb1 : (b : ℝ) - 1 ≠ 0 := hbR.ne'
      dsimp only [c]
      field_simp
      try ring
    rw [hcj]
    exact hlo.trans hbnd
  exact (not_lt_of_ge hh) hT

theorem reverseHost_not_finitePrimeWeighted (b : ℕ) (hb : 2 ≤ b) :
    ¬ FinitePrimeWeighted b reverseHost := by
  rintro ⟨P, hPn, hP, hs⟩
  exact reverseHost_no_weighted_sum b hb P hP hs

/-- Complete reverse host, composed through the checked hereditary consumer. -/
theorem exists_strengthened_not_old_or_weighted_host :
    ∃ A : Set ℕ, A.Infinite ∧ 0 ∉ A ∧ (∀ a ∈ A, Squarefree a) ∧
      HasStrengthenedPositiveCover A ∧ ¬ HasOldPositiveCover A ∧
      (¬ Summable (Set.indicator A (fun a : ℕ => (1 : ℝ) / a))) ∧
      (∀ b : ℕ, 2 ≤ b → ¬ FinitePrimeWeighted b A) ∧
      (∀ B : Set ℕ, B ⊆ A → B.Infinite → ∀ b : ℕ, 2 ≤ b →
        Irrational (erdosSupportSeries b B)) := by
  refine ⟨reverseHost, reverseHost_infinite, reverseHost_positive, reverseHost_squarefree,
    reverseHost_has_strengthened_cover, reverseHost_no_old_cover,
    reverseHost_reciprocal_not_summable, reverseHost_not_finitePrimeWeighted, ?_⟩
  intro B hB hInf b hb
  exact strengthenedPositiveCoverClaim reverseCover reverseCover_strengthened B hB hInf b hb

end ErdosProblems.Erdos257.PaperCompleteR8
end
