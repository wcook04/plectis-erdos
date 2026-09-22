import ErdosProblems.Erdos269.PaperR7WindowResults

/-!
# Exact arithmetic of the paper's weighted shifts

The ratio is defined from the actual dyadic heights. Integer logarithms
prove its four-element alphabet without numerical logarithms. The factor
15 clears both the shifted coefficients and the finite prefix correction.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR20

open PaperR7
open scoped BigOperators

abbrev shiftHeight (n : ℕ) : ℕ := threePrimeHeight 2 3 5 (2 ^ n)

noncomputable def shiftGamma (a t : ℕ) : ℝ :=
  (shiftHeight t : ℝ) * (shiftHeight (a + 1) : ℝ) / (shiftHeight (a + t + 1) : ℝ)

theorem natLog_dyadic_add_cases {b : ℕ} (hb : 1 < b) (m n : ℕ) :
    Nat.log b (2 ^ (m + n)) = Nat.log b (2 ^ m) + Nat.log b (2 ^ n) ∨
    Nat.log b (2 ^ (m + n)) = Nat.log b (2 ^ m) + Nat.log b (2 ^ n) + 1 := by
  have hm : (2 : ℕ) ^ m ≠ 0 := by positivity
  have hn : (2 : ℕ) ^ n ≠ 0 := by positivity
  have hmn : (2 : ℕ) ^ (m + n) ≠ 0 := by positivity
  have hlo : Nat.log b (2 ^ m) + Nat.log b (2 ^ n) ≤ Nat.log b (2 ^ (m + n)) := by
    apply Nat.le_log_of_pow_le hb
    simpa only [pow_add] using Nat.mul_le_mul (Nat.pow_log_le_self b hm) (Nat.pow_log_le_self b hn)
  have hup : Nat.log b (2 ^ (m + n)) < Nat.log b (2 ^ m) + Nat.log b (2 ^ n) + 2 := by
    apply Nat.log_lt_of_lt_pow hmn
    have h := Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_pow_succ_log_self hb (2 ^ m))
      (Nat.lt_pow_succ_log_self hb (2 ^ n))
    simpa only [← pow_add, Nat.succ_eq_add_one,
      show Nat.log b (2 ^ m) + 1 + (Nat.log b (2 ^ n) + 1) =
        Nat.log b (2 ^ m) + Nat.log b (2 ^ n) + 2 by omega] using h
  omega

theorem shiftHeight_add_factor (m n : ℕ) :
    ∃ d : ℕ, (d = 1 ∨ d = 3 ∨ d = 5 ∨ d = 15) ∧
      shiftHeight (m + n) = d * (shiftHeight m * shiftHeight n) := by
  rcases natLog_dyadic_add_cases (by decide : 1 < (3 : ℕ)) m n with h3 | h3 <;>
    rcases natLog_dyadic_add_cases (by decide : 1 < (5 : ℕ)) m n with h5 | h5
  · refine ⟨1, Or.inl rfl, ?_⟩
    simp only [shiftHeight, threePrimeHeight, Nat.log_pow (by decide : 1 < (2 : ℕ))]
    rw [h3, h5]
    simp only [pow_add, pow_one]
    ring
  · refine ⟨5, Or.inr (Or.inr (Or.inl rfl)), ?_⟩
    simp only [shiftHeight, threePrimeHeight, Nat.log_pow (by decide : 1 < (2 : ℕ))]
    rw [h3, h5]
    simp only [pow_add, pow_one]
    ring
  · refine ⟨3, Or.inr (Or.inl rfl), ?_⟩
    simp only [shiftHeight, threePrimeHeight, Nat.log_pow (by decide : 1 < (2 : ℕ))]
    rw [h3, h5]
    simp only [pow_add, pow_one]
    ring
  · refine ⟨15, Or.inr (Or.inr (Or.inr rfl)), ?_⟩
    simp only [shiftHeight, threePrimeHeight, Nat.log_pow (by decide : 1 < (2 : ℕ))]
    rw [h3, h5]
    simp only [pow_add, pow_one]
    ring

theorem shiftGamma_four_values (a t : ℕ) :
    shiftGamma a t = 1 ∨ shiftGamma a t = 1 / 3 ∨
      shiftGamma a t = 1 / 5 ∨ shiftGamma a t = 1 / 15 := by
  obtain ⟨d, hd, hh⟩ := shiftHeight_add_factor t (a + 1)
  have ht : (shiftHeight t : ℝ) ≠ 0 := (threePrimeHeight235_cast_pos _).ne'
  have ha : (shiftHeight (a + 1) : ℝ) ≠ 0 := (threePrimeHeight235_cast_pos _).ne'
  have hd0 : (d : ℝ) ≠ 0 := by
    rcases hd with rfl | rfl | rfl | rfl <;> norm_num
  have hhR : (shiftHeight (a + t + 1) : ℝ) = (d : ℝ) *
      ((shiftHeight t : ℝ) * (shiftHeight (a + 1) : ℝ)) := by
    exact_mod_cast (show shiftHeight (a + t + 1) = d * (shiftHeight t * shiftHeight (a + 1)) by
      simpa only [show t + (a + 1) = a + t + 1 by omega] using hh)
  have he : shiftGamma a t = 1 / (d : ℝ) := by
    unfold shiftGamma
    rw [hhR]
    field_simp
  rcases hd with rfl | rfl | rfl | rfl <;> simp_all

theorem shiftGamma_bounds (a t : ℕ) : 0 < shiftGamma a t ∧ shiftGamma a t ≤ 1 := by
  rcases shiftGamma_four_values a t with h | h | h | h <;> rw [h] <;> norm_num

theorem fifteen_shiftGamma_integral (a t : ℕ) :
    ∃ z : ℤ, 15 * shiftGamma a t = (z : ℝ) := by
  rcases shiftGamma_four_values a t with h | h | h | h
  · exact ⟨15, by rw [h]; norm_num⟩
  · exact ⟨5, by rw [h]; norm_num⟩
  · exact ⟨3, by rw [h]; norm_num⟩
  · exact ⟨1, by rw [h]; norm_num⟩

noncomputable def shiftedNumerator (c : ℕ → ℤ) (σ r a : ℕ) : ℝ :=
  15 * ∑ j ∈ Finset.range (σ + 1), (c j : ℝ) * shiftGamma a (j * r) *
    (dyadicOrderedBlockDigit235 (a + j * r) : ℝ)

theorem shiftedNumerator_integral (c : ℕ → ℤ) (σ r a : ℕ) :
    ∃ z : ℤ, shiftedNumerator c σ r a = (z : ℝ) := by
  choose z hz using fifteen_shiftGamma_integral a
  refine ⟨∑ j ∈ Finset.range (σ + 1), c j * z (j * r) *
    (dyadicOrderedBlockDigit235 (a + j * r) : ℤ), ?_⟩
  unfold shiftedNumerator
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← hz (j * r)]
  ring

theorem shiftHeight_dvd_of_le {m n : ℕ} (h : m ≤ n) : shiftHeight m ∣ shiftHeight n := by
  refine ⟨actualWindowProduct m (n - m), ?_⟩
  simpa only [Nat.add_sub_of_le h] using height_windowProduct m (n - m)

noncomputable def shiftedPrefix (t : ℕ) : ℝ :=
  (shiftHeight t : ℝ) * ∑ k ∈ Finset.range t,
    (dyadicOrderedBlockDigit235 k : ℝ) / (shiftHeight (k + 1) : ℝ)

theorem shiftedPrefix_integral (t : ℕ) : ∃ z : ℤ, shiftedPrefix t = (z : ℝ) := by
  have hterm : ∀ k ∈ Finset.range t, ∃ z : ℤ,
      (shiftHeight t : ℝ) * ((dyadicOrderedBlockDigit235 k : ℝ) /
        (shiftHeight (k + 1) : ℝ)) = (z : ℝ) := by
    intro k hk
    obtain ⟨z, hz⟩ := shiftHeight_dvd_of_le (by have := Finset.mem_range.mp hk; omega : k + 1 ≤ t)
    refine ⟨(z : ℤ) * dyadicOrderedBlockDigit235 k, ?_⟩
    have hp : (shiftHeight (k + 1) : ℝ) ≠ 0 := (threePrimeHeight235_cast_pos _).ne'
    rw [hz]
    push_cast
    field_simp
  classical
  choose z hz using hterm
  refine ⟨∑ k ∈ (Finset.range t).attach, z k.val k.property, ?_⟩
  unfold shiftedPrefix
  rw [Finset.mul_sum, ← Finset.sum_attach]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  exact hz k.val k.property

#print axioms shiftGamma_four_values
#print axioms shiftedNumerator_integral
#print axioms shiftedPrefix_integral

end ErdosProblems.Erdos269.PaperCompleteR20
