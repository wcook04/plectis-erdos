import ErdosProblems.Erdos269.PaperCompleteR20.WeightedShiftArithmetic

/-!
# Weighted shifts of the literal series

Finite linear combinations of shifted digits retain the original value
with an integer prefix correction. All sums below converge absolutely.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR20

open PaperR7
open scoped BigOperators

noncomputable def shiftTerm (a : ℕ) : ℝ :=
  (dyadicOrderedBlockDigit235 a : ℝ) / (shiftHeight (a + 1) : ℝ)

theorem shiftTerm_eq_half_shell (a : ℕ) : shiftTerm a = dyadicShellMassR235 a / 2 := by
  have hp : (shiftHeight (a + 1) : ℝ) ≠ 0 := (threePrimeHeight235_cast_pos _).ne'
  have hd := half_threePrimeHeight_mul_dyadicShellMassR235 a
  unfold shiftTerm
  apply (div_eq_div_iff hp (by norm_num : (2 : ℝ) ≠ 0)).2
  nlinarith only [hd]

theorem hasSum_shiftTerm : HasSum shiftTerm (paperSeries235 / 2) := by
  have hs := summable_dyadicShellMassR235.hasSum.div_const (2 : ℝ)
  have hv : (∑' a : ℕ, dyadicShellMassR235 a) = paperSeries235 := by
    simpa only [dyadicShellTsumTailR235, Nat.zero_add] using paperSeries235_eq_shellTsum.symm
  rw [hv] at hs
  exact hs.congr_fun shiftTerm_eq_half_shell

theorem weighted_shift_term (a t : ℕ) :
    shiftGamma a t * (dyadicOrderedBlockDigit235 (a + t) : ℝ) /
        (shiftHeight (a + 1) : ℝ) = (shiftHeight t : ℝ) * shiftTerm (a + t) := by
  have hp : (shiftHeight (a + 1) : ℝ) ≠ 0 := (threePrimeHeight235_cast_pos _).ne'
  have ht : (shiftHeight (a + t + 1) : ℝ) ≠ 0 := (threePrimeHeight235_cast_pos _).ne'
  unfold shiftGamma shiftTerm
  field_simp

theorem hasSum_one_weighted_shift (t : ℕ) :
    HasSum (fun a : ℕ => shiftGamma a t * (dyadicOrderedBlockDigit235 (a + t) : ℝ) /
      (shiftHeight (a + 1) : ℝ))
      ((shiftHeight t : ℝ) * (paperSeries235 / 2) - shiftedPrefix t) := by
  have hs := ((hasSum_nat_add_iff' t).2 hasSum_shiftTerm).mul_left (shiftHeight t : ℝ)
  have he : (shiftHeight t : ℝ) *
      (paperSeries235 / 2 - ∑ k ∈ Finset.range t, shiftTerm k) =
      (shiftHeight t : ℝ) * (paperSeries235 / 2) - shiftedPrefix t := by
    simp only [shiftedPrefix, shiftTerm, mul_sub]
  rw [he] at hs
  exact hs.congr_fun (fun a => weighted_shift_term a t)

def shiftedLeading (c : ℕ → ℤ) (σ r : ℕ) : ℤ :=
  15 * ∑ j ∈ Finset.range (σ + 1), c j * (shiftHeight (j * r) : ℤ)

noncomputable def shiftedCorrection (c : ℕ → ℤ) (σ r : ℕ) : ℝ :=
  15 * ∑ j ∈ Finset.range (σ + 1), (c j : ℝ) * shiftedPrefix (j * r)

theorem shiftedCorrection_integral (c : ℕ → ℤ) (σ r : ℕ) :
    ∃ z : ℤ, shiftedCorrection c σ r = (z : ℝ) := by
  choose z hz using shiftedPrefix_integral
  refine ⟨15 * ∑ j ∈ Finset.range (σ + 1), c j * z (j * r), ?_⟩
  unfold shiftedCorrection
  push_cast
  simp only [hz]

theorem hasSum_weighted_shift_identity (c : ℕ → ℤ) (σ r : ℕ) :
    HasSum (fun a : ℕ => shiftedNumerator c σ r a / (shiftHeight (a + 1) : ℝ))
      ((shiftedLeading c σ r : ℝ) * (paperSeries235 / 2) - shiftedCorrection c σ r) := by
  have hs := (hasSum_sum (s := Finset.range (σ + 1))
    (fun j _ => (hasSum_one_weighted_shift (j * r)).mul_left (c j : ℝ))).mul_left (15 : ℝ)
  convert hs using 1
  · funext a
    simp only [shiftedNumerator, Finset.sum_div, mul_div_assoc, Finset.mul_sum, mul_assoc]
  · simp only [shiftedLeading, shiftedCorrection, Int.cast_mul, Int.cast_ofNat,
      Int.cast_sum, Int.cast_natCast, mul_sub, Finset.sum_sub_distrib,
      Finset.sum_mul, mul_assoc]

theorem weighted_shift_identity_absolute (c : ℕ → ℤ) (σ r : ℕ) :
    Summable (fun a : ℕ => |shiftedNumerator c σ r a / (shiftHeight (a + 1) : ℝ)|) := by
  simpa only [Real.norm_eq_abs] using (hasSum_weighted_shift_identity c σ r).summable.norm

noncomputable def shiftedQuadraticConstant (c : ℕ → ℤ) (σ : ℕ) : ℝ :=
  225 * ∑ j ∈ Finset.range (σ + 1), |(c j : ℝ)| * (max 1 j : ℝ) ^ 2

theorem shifted_index_le (a j r : ℕ) :
    a + j * r + 1 ≤ max 1 j * (a + r + 1) := by
  have h1 : 1 ≤ max 1 j := le_max_left _ _
  have hj : j ≤ max 1 j := le_max_right _ _
  nlinarith

theorem one_shift_quadratic_bound (c : ℤ) (a j r : ℕ) :
    |(c : ℝ) * shiftGamma a (j * r) * (dyadicOrderedBlockDigit235 (a + j * r) : ℝ)| ≤
      15 * |(c : ℝ)| * (max 1 j : ℝ) ^ 2 * ((a + r + 1 : ℕ) : ℝ) ^ 2 := by
  obtain ⟨hg0, hg1⟩ := shiftGamma_bounds a (j * r)
  have hm0 : (0 : ℝ) ≤ dyadicOrderedBlockDigit235 (a + j * r) := Nat.cast_nonneg _
  have hmu : (dyadicOrderedBlockDigit235 (a + j * r) : ℝ) ≤
      15 * ((a + j * r + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast dyadicOrderedBlockDigit235_le_quadratic (a + j * r)
  have hindex : ((a + j * r + 1 : ℕ) : ℝ) ≤
      (max 1 j : ℝ) * ((a + r + 1 : ℕ) : ℝ) := by
    exact_mod_cast shifted_index_le a j r
  have hsq : (((a + j * r + 1 : ℕ) : ℝ)) ^ 2 ≤
      ((max 1 j : ℝ) * ((a + r + 1 : ℕ) : ℝ)) ^ 2 := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hindex 2
  rw [abs_mul, abs_mul, abs_of_pos hg0, abs_of_nonneg hm0]
  calc
    |(c : ℝ)| * shiftGamma a (j * r) * (dyadicOrderedBlockDigit235 (a + j * r) : ℝ)
        ≤ |(c : ℝ)| * (dyadicOrderedBlockDigit235 (a + j * r) : ℝ) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg1 (abs_nonneg _)) hm0
    _ ≤ |(c : ℝ)| * (15 * ((a + j * r + 1 : ℕ) : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hmu (abs_nonneg _)
    _ ≤ |(c : ℝ)| * (15 * ((max 1 j : ℝ) * ((a + r + 1 : ℕ) : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (by norm_num)) (abs_nonneg _)
    _ = _ := by ring

theorem shiftedNumerator_quadratic_bound (c : ℕ → ℤ) (σ r a : ℕ) :
    |shiftedNumerator c σ r a| ≤
      shiftedQuadraticConstant c σ * ((a + r + 1 : ℕ) : ℝ) ^ 2 := by
  unfold shiftedNumerator
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 15)]
  calc
    15 * |∑ j ∈ Finset.range (σ + 1), (c j : ℝ) * shiftGamma a (j * r) *
        (dyadicOrderedBlockDigit235 (a + j * r) : ℝ)|
      ≤ 15 * ∑ j ∈ Finset.range (σ + 1),
        |(c j : ℝ) * shiftGamma a (j * r) * (dyadicOrderedBlockDigit235 (a + j * r) : ℝ)| := by
          gcongr
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ 15 * ∑ j ∈ Finset.range (σ + 1),
        15 * |(c j : ℝ)| * (max 1 j : ℝ) ^ 2 * ((a + r + 1 : ℕ) : ℝ) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Finset.sum_le_sum (fun j _ => one_shift_quadratic_bound (c j) a j r)
    _ = 15 * (15 * (∑ j ∈ Finset.range (σ + 1),
        |(c j : ℝ)| * (max 1 j : ℝ) ^ 2) * ((a + r + 1 : ℕ) : ℝ) ^ 2) := by
      congr 1
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = shiftedQuadraticConstant c σ * ((a + r + 1 : ℕ) : ℝ) ^ 2 := by
      unfold shiftedQuadraticConstant
      ring

theorem shiftHeight_ratio_le_binary {m n : ℕ} (h : m ≤ n) :
    (shiftHeight m : ℝ) / (shiftHeight n : ℝ) ≤ 1 / (2 : ℝ) ^ (n - m) := by
  have hp : (0 : ℝ) < (shiftHeight m : ℝ) := threePrimeHeight235_cast_pos _
  have hW : (0 : ℝ) < (actualWindowProduct m (n - m) : ℝ) := by
    exact_mod_cast actualWindowProduct_pos m (n - m)
  have hpow : (2 : ℝ) ^ (n - m) ≤ (actualWindowProduct m (n - m) : ℝ) := by
    have hZ : (2 : ℤ) ^ (n - m) ≤ (actualWindowProduct m (n - m) : ℤ) := by
      rw [← actualWindowBase_eq_product]
      exact two_pow_le_windowBase235 m (n - m)
    exact_mod_cast hZ
  have he : (shiftHeight n : ℝ) =
      (shiftHeight m : ℝ) * (actualWindowProduct m (n - m) : ℝ) := by
    exact_mod_cast (show shiftHeight n = shiftHeight m * actualWindowProduct m (n - m) by
      simpa only [Nat.add_sub_of_le h] using height_windowProduct m (n - m))
  rw [he]
  calc
    (shiftHeight m : ℝ) / ((shiftHeight m : ℝ) * (actualWindowProduct m (n - m) : ℝ))
        = 1 / (actualWindowProduct m (n - m) : ℝ) := by field_simp
    _ ≤ 1 / (2 : ℝ) ^ (n - m) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow

/-- The printed sufficient condition for the leading coefficient to be nonzero. -/
theorem shiftedLeading_ne_zero (c : ℕ → ℤ) (σ r J : ℕ)
    (hJ : J ≤ σ)
    (hmax : ∀ j, J < j → j ≤ σ → c j = 0)
    (hmargin : (∑ j ∈ Finset.range J, |(c j : ℝ)| / (2 : ℝ) ^ ((J - j) * r)) < |(c J : ℝ)|) :
    shiftedLeading c σ r ≠ 0 := by
  intro hz
  have hsum : (∑ j ∈ Finset.range (σ + 1), (c j : ℝ) * (shiftHeight (j * r) : ℝ)) = 0 := by
    have he : (shiftedLeading c σ r : ℝ) = 0 := by rw [hz]; norm_num
    simp only [shiftedLeading, Int.cast_mul, Int.cast_ofNat, Int.cast_sum, Int.cast_natCast] at he
    linarith
  have htrunc : (∑ j ∈ Finset.range (J + 1), (c j : ℝ) * (shiftHeight (j * r) : ℝ)) =
      ∑ j ∈ Finset.range (σ + 1), (c j : ℝ) * (shiftHeight (j * r) : ℝ) := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j hj hj'
    have hjs : j ≤ σ := by have := Finset.mem_range.mp hj; omega
    have hJj : J < j := by
      have hn : ¬ j < J + 1 := by simpa only [Finset.mem_range] using hj'
      omega
    simp [hmax j hJj hjs]
  rw [← htrunc, Finset.sum_range_succ] at hsum
  have hp : (0 : ℝ) < (shiftHeight (J * r) : ℝ) := threePrimeHeight235_cast_pos _
  have hnormalized :
      (∑ j ∈ Finset.range J, (c j : ℝ) * (shiftHeight (j * r) : ℝ) /
        (shiftHeight (J * r) : ℝ)) = -(c J : ℝ) := by
    rw [← Finset.sum_div]
    apply (div_eq_iff hp.ne').2
    linarith
  have hbound : |(c J : ℝ)| ≤
      ∑ j ∈ Finset.range J, |(c j : ℝ)| / (2 : ℝ) ^ ((J - j) * r) := by
    calc
      |(c J : ℝ)| = |∑ j ∈ Finset.range J,
          (c j : ℝ) * (shiftHeight (j * r) : ℝ) / (shiftHeight (J * r) : ℝ)| := by
        rw [hnormalized, abs_neg]
      _ ≤ ∑ j ∈ Finset.range J,
          |(c j : ℝ) * (shiftHeight (j * r) : ℝ) / (shiftHeight (J * r) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        have hjJ : j ≤ J := by have := Finset.mem_range.mp hj; omega
        have hratio := shiftHeight_ratio_le_binary (Nat.mul_le_mul_right r hjJ)
        rw [← Nat.sub_mul] at hratio
        have hjp : (0 : ℝ) < (shiftHeight (j * r) : ℝ) := threePrimeHeight235_cast_pos _
        rw [abs_div, abs_mul, abs_of_pos hjp, abs_of_pos hp, mul_div_assoc]
        simpa only [← mul_div_assoc, mul_one] using
          mul_le_mul_of_nonneg_left hratio (abs_nonneg (c j : ℝ))
  exact (not_lt_of_ge hbound) hmargin

/-- Every clause of the weighted-shift identity, retaining its explicit constant
and the largest-coefficient nonvanishing condition. -/
theorem weighted_shift_whole (c : ℕ → ℤ) (σ r : ℕ) :
    (∀ a t, shiftGamma a t = 1 ∨ shiftGamma a t = 1 / 3 ∨
      shiftGamma a t = 1 / 5 ∨ shiftGamma a t = 1 / 15) ∧
    (∀ a, ∃ z : ℤ, shiftedNumerator c σ r a = (z : ℝ)) ∧
    (∃ z : ℤ, shiftedCorrection c σ r = (z : ℝ)) ∧
    HasSum (fun a : ℕ => shiftedNumerator c σ r a / (shiftHeight (a + 1) : ℝ))
      ((shiftedLeading c σ r : ℝ) * (paperSeries235 / 2) - shiftedCorrection c σ r) ∧
    Summable (fun a : ℕ => |shiftedNumerator c σ r a / (shiftHeight (a + 1) : ℝ)|) ∧
    (∀ a, |shiftedNumerator c σ r a| ≤
      shiftedQuadraticConstant c σ * ((a + r + 1 : ℕ) : ℝ) ^ 2) ∧
    (∀ J : ℕ, J ≤ σ → (∀ j, J < j → j ≤ σ → c j = 0) →
      (∑ j ∈ Finset.range J, |(c j : ℝ)| / (2 : ℝ) ^ ((J - j) * r)) < |(c J : ℝ)| →
      shiftedLeading c σ r ≠ 0) := by
  exact ⟨shiftGamma_four_values, shiftedNumerator_integral c σ r,
    shiftedCorrection_integral c σ r, hasSum_weighted_shift_identity c σ r,
    weighted_shift_identity_absolute c σ r, shiftedNumerator_quadratic_bound c σ r,
    shiftedLeading_ne_zero c σ r⟩

#print axioms weighted_shift_whole

#print axioms hasSum_weighted_shift_identity
#print axioms weighted_shift_identity_absolute
#print axioms shiftedNumerator_quadratic_bound

end ErdosProblems.Erdos269.PaperCompleteR20
