import ErdosProblems.Erdos269.PaperR8RankMajorant

/-!
# Direct fixed-base recoding of the actual series

The coefficient is the literal termwise rescaling of the actual ordered
digit. Base 30 retains integrality; base 8 retains the quadratic bound and
has denominators supported on 3 and 5. No echoing hypothesis is asserted.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR20

open PaperR7 PaperR8
open scoped BigOperators

noncomputable def recodedCoefficient (q a : ℕ) : ℝ :=
  (dyadicOrderedBlockDigit235 a : ℝ) * (q : ℝ) ^ (a + 1) /
    (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ)

theorem dyadic_height_dvd_thirty_pow (n : ℕ) :
    threePrimeHeight 2 3 5 (2 ^ n) ∣ 30 ^ n := by
  have h := sorted_height_profile (pow_ne_zero n (by decide : (2 : ℕ) ≠ 0))
  rw [Nat.log_pow (by decide : 1 < (2 : ℕ))] at h
  have hd := Nat.mul_dvd_mul
    (Nat.mul_dvd_mul (dvd_refl (2 ^ n)) (pow_dvd_pow 3 h.2))
    (pow_dvd_pow 5 (h.1.trans h.2))
  simpa only [threePrimeHeight, Nat.log_pow (by decide : 1 < (2 : ℕ)),
    ← mul_pow, show (2 : ℕ) * 3 * 5 = 30 from rfl] using hd

theorem dyadic_height_le_eight_pow (n : ℕ) :
    threePrimeHeight 2 3 5 (2 ^ n) ≤ 8 ^ n := by
  have h := threePrimeHeight_le_cube 2 3 5 (2 ^ n)
    (pow_ne_zero n (by decide : (2 : ℕ) ≠ 0))
  have hp : (2 ^ n : ℕ) ^ 3 = 8 ^ n := by
    rw [← pow_mul, Nat.mul_comm n 3, pow_mul]
    norm_num
  rwa [hp] at h

/-- The termwise divisibility condition is exactly divisibility of the base by 30. -/
theorem all_dyadic_heights_dvd_base_powers_iff (q : ℕ) :
    (∀ n : ℕ, 1 ≤ n → threePrimeHeight 2 3 5 (2 ^ n) ∣ q ^ n) ↔ 30 ∣ q := by
  constructor
  · intro h
    have hheight : threePrimeHeight 2 3 5 (2 ^ 3) = 120 := by decide +kernel
    have hh : 120 ∣ q ^ 3 := by simpa only [hheight] using h 3 (by decide)
    have h2 : 2 ∣ q := Nat.prime_two.dvd_of_dvd_pow
      ((by decide : 2 ∣ 120).trans hh)
    have h3 : 3 ∣ q := Nat.prime_three.dvd_of_dvd_pow
      ((by decide : 3 ∣ 120).trans hh)
    have h5 : 5 ∣ q := Nat.prime_five.dvd_of_dvd_pow
      ((by decide : 5 ∣ 120).trans hh)
    have h6 : 6 ∣ q := (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h2 h3
    exact (by decide : Nat.Coprime 6 5).mul_dvd_of_dvd_of_dvd h6 h5
  · intro h n _
    exact (dyadic_height_dvd_thirty_pow n).trans (pow_dvd_pow_of_dvd h n)

theorem recodedCoefficient_pos {q : ℕ} (hq : 0 < q) (a : ℕ) :
    0 < recodedCoefficient q a := by
  have hm : (0 : ℝ) < dyadicOrderedBlockDigit235 a := by exact_mod_cast orderedDigit235_pos a
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  exact div_pos (mul_pos hm (pow_pos hqR _)) (threePrimeHeight235_cast_pos _)

theorem recodedCoefficient_integral {q : ℕ} (hq : 0 < q) (h30 : 30 ∣ q) (a : ℕ) :
    ∃ z : ℕ, 0 < z ∧ recodedCoefficient q a = (z : ℝ) := by
  obtain ⟨k, hk⟩ := (all_dyadic_heights_dvd_base_powers_iff q).2 h30 (a + 1) (by omega)
  have hp : (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) ≠ 0 :=
    (threePrimeHeight235_cast_pos _).ne'
  have hkR : (q : ℝ) ^ (a + 1) =
      (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) * (k : ℝ) := by exact_mod_cast hk
  have he : recodedCoefficient q a = ((dyadicOrderedBlockDigit235 a * k : ℕ) : ℝ) := by
    unfold recodedCoefficient
    rw [hkR]
    push_cast
    field_simp
  refine ⟨dyadicOrderedBlockDigit235 a * k, ?_, he⟩
  have hz := recodedCoefficient_pos hq a
  rw [he] at hz
  exact_mod_cast hz

theorem recodedCoefficient_lower {q : ℕ} (_hq : 0 < q) (a : ℕ) :
    ((q : ℝ) / 8) ^ (a + 1) ≤ recodedCoefficient q a := by
  have hp := threePrimeHeight235_cast_pos (2 ^ (a + 1))
  have hu : (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) ≤ (8 : ℝ) ^ (a + 1) := by
    exact_mod_cast dyadic_height_le_eight_pow (a + 1)
  have hm : (1 : ℝ) ≤ dyadicOrderedBlockDigit235 a := by
    exact_mod_cast orderedDigit235_pos a
  have hqpow : (0 : ℝ) ≤ (q : ℝ) ^ (a + 1) := pow_nonneg (Nat.cast_nonneg _) _
  rw [div_pow]
  apply (div_le_div_of_nonneg_left hqpow hp hu).trans
  apply div_le_div_of_nonneg_right _ hp.le
  nlinarith [mul_nonneg (sub_nonneg.mpr hm) hqpow]

theorem base_eight_coefficient_upper (a : ℕ) :
    recodedCoefficient 8 a < 225 * ((a + 1 : ℕ) : ℝ) ^ 2 := by
  have hp := threePrimeHeight235_cast_pos (2 ^ (a + 1))
  have hl := eight_pow_lt_fifteen_dyadic_height (a + 1)
  have hratio : (8 : ℝ) ^ (a + 1) /
      (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) < 15 :=
    (div_lt_iff₀ hp).2 hl
  have hm : (0 : ℝ) < dyadicOrderedBlockDigit235 a := by exact_mod_cast orderedDigit235_pos a
  have hmu : (dyadicOrderedBlockDigit235 a : ℝ) ≤ 15 * ((a + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast dyadicOrderedBlockDigit235_le_quadratic a
  have hh := mul_lt_mul_of_pos_left hratio hm
  unfold recodedCoefficient
  norm_num only [Nat.cast_ofNat]
  rw [mul_div_assoc]
  nlinarith only [hh, hmu]

/-- A fixed power of 15 clears each base-eight coefficient. -/
theorem base_eight_coefficient_in_localization (a : ℕ) :
    ∃ z : ℕ, recodedCoefficient 8 a = (z : ℝ) / (15 : ℝ) ^ (a + 1) := by
  obtain ⟨z, _, hz⟩ := recodedCoefficient_integral (q := 120) (by decide) (by decide) a
  refine ⟨z, ?_⟩
  rw [← hz]
  unfold recodedCoefficient
  have hp : (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) ≠ 0 :=
    (threePrimeHeight235_cast_pos _).ne'
  norm_num only [Nat.cast_ofNat]
  rw [show (120 : ℝ) = 8 * 15 by norm_num, mul_pow]
  field_simp
  <;> ring

theorem recoded_term_eq_half_shell {q : ℕ} (hq : 0 < q) (a : ℕ) :
    recodedCoefficient q a / (q : ℝ) ^ (a + 1) = dyadicShellMassR235 a / 2 := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hpow : (q : ℝ) ^ (a + 1) ≠ 0 := pow_ne_zero _ hqR
  have hp : (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) ≠ 0 :=
    (threePrimeHeight235_cast_pos _).ne'
  have hd := half_threePrimeHeight_mul_dyadicShellMassR235 a
  calc
    recodedCoefficient q a / (q : ℝ) ^ (a + 1) =
        (dyadicOrderedBlockDigit235 a : ℝ) /
          (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) := by
      unfold recodedCoefficient
      field_simp
    _ = dyadicShellMassR235 a / 2 := by
      apply (div_eq_div_iff hp (by norm_num : (2 : ℝ) ≠ 0)).2
      nlinarith only [hd]

theorem hasSum_recoded_actual_value {q : ℕ} (hq : 0 < q) :
    HasSum (fun a : ℕ => recodedCoefficient q a / (q : ℝ) ^ (a + 1))
      (paperSeries235 / 2) := by
  have hs := summable_dyadicShellMassR235.hasSum.div_const (2 : ℝ)
  have hv : (∑' a : ℕ, dyadicShellMassR235 a) = paperSeries235 := by
    simpa only [dyadicShellTsumTailR235, Nat.zero_add] using paperSeries235_eq_shellTsum.symm
  rw [hv] at hs
  exact hs.congr_fun (fun a => recoded_term_eq_half_shell hq a)

theorem recoded_actual_value_absolute {q : ℕ} (hq : 0 < q) :
    Summable (fun a : ℕ => |recodedCoefficient q a / (q : ℝ) ^ (a + 1)|) := by
  simpa only [Real.norm_eq_abs] using (hasSum_recoded_actual_value hq).summable.norm

/-- The complete direct-recoding proposition with its original two bases. -/
theorem fixed_base_recoding_whole :
    (HasSum (fun a : ℕ => recodedCoefficient 30 a / (30 : ℝ) ^ (a + 1)) (paperSeries235 / 2)) ∧
    (Summable (fun a : ℕ => |recodedCoefficient 30 a / (30 : ℝ) ^ (a + 1)|)) ∧
    (HasSum (fun a : ℕ => recodedCoefficient 8 a / (8 : ℝ) ^ (a + 1)) (paperSeries235 / 2)) ∧
    (Summable (fun a : ℕ => |recodedCoefficient 8 a / (8 : ℝ) ^ (a + 1)|)) ∧
    (∀ a : ℕ, (∃ z : ℕ, 0 < z ∧ recodedCoefficient 30 a = (z : ℝ)) ∧
      (15 / 4 : ℝ) ^ (a + 1) ≤ recodedCoefficient 30 a) ∧
    (∀ a : ℕ, (∃ z : ℕ, recodedCoefficient 8 a = (z : ℝ) / (15 : ℝ) ^ (a + 1)) ∧
      0 < recodedCoefficient 8 a ∧ recodedCoefficient 8 a < 225 * ((a + 1 : ℕ) : ℝ) ^ 2) ∧
    (∀ q : ℕ, 2 ≤ q →
      ((∀ n : ℕ, 1 ≤ n → threePrimeHeight 2 3 5 (2 ^ n) ∣ q ^ n) ↔ 30 ∣ q) ∧
      ∀ a : ℕ, ((q : ℝ) / 8) ^ (a + 1) ≤ recodedCoefficient q a) := by
  refine ⟨hasSum_recoded_actual_value (by decide), recoded_actual_value_absolute (by decide),
    hasSum_recoded_actual_value (by decide), recoded_actual_value_absolute (by decide),
    ?_, ?_, ?_⟩
  · intro a
    refine ⟨recodedCoefficient_integral (by decide) (by decide) a, ?_⟩
    have h := recodedCoefficient_lower (q := 30) (by decide) a
    norm_num only [Nat.cast_ofNat, show (30 / 8 : ℝ) = 15 / 4 by norm_num] at h
    exact h
  · intro a
    exact ⟨base_eight_coefficient_in_localization a,
      recodedCoefficient_pos (by decide) a, base_eight_coefficient_upper a⟩
  · intro q hq
    exact ⟨all_dyadic_heights_dvd_base_powers_iff q,
      fun a => recodedCoefficient_lower (by omega) a⟩

#print axioms fixed_base_recoding_whole

end ErdosProblems.Erdos269.PaperCompleteR20
