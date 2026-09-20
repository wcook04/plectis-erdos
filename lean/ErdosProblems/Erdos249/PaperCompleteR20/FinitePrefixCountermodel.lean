import ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates

namespace ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel
open Erdos249257
open scoped BigOperators

def gamma (B P n : ℕ) : ℕ :=
  if n ≤ B then Nat.totient n else if P ∣ n then n - 1 else n

def correction (B n : ℕ) : ℕ := if n ≤ B then n - Nat.totient n else 0

noncomputable def multipleTerm (P n : ℕ) : ℝ :=
  if 0 < n ∧ P ∣ n then 1 / (2 : ℝ) ^ n else 0

theorem gamma_le (B P n : ℕ) : gamma B P n ≤ n := by
  unfold gamma
  split
  · exact Nat.totient_le n
  · split <;> omega

theorem gamma_prefix (B P n : ℕ) (hn : n ≤ B) : gamma B P n = Nat.totient n := by
  simp [gamma, hn]

theorem discrepancy_prefix (B P h N L : ℕ) (hB : N + h + L ≤ B) :
    GenericTailCertificates.discrepancy (gamma B P) h N L =
      GenericTailCertificates.discrepancy Nat.totient h N L := by
  unfold GenericTailCertificates.discrepancy
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [gamma_prefix B P _ (by omega), gamma_prefix B P _ (by omega)]

theorem gamma_term (B P n : ℕ) (hBP : B < P) :
    (gamma B P n : ℝ) / 2 ^ n =
      (n : ℝ) / 2 ^ n - (correction B n : ℝ) / 2 ^ n - multipleTerm P n := by
  by_cases hn : n ≤ B
  · have hnot : ¬ (0 < n ∧ P ∣ n) := by
      rintro ⟨hp, hd⟩
      have := Nat.le_of_dvd hp hd
      omega
    simp only [gamma, correction, if_pos hn, multipleTerm, if_neg hnot, sub_zero]
    rw [Nat.cast_sub (Nat.totient_le n)]
    ring
  · have hnpos : 0 < n := by omega
    by_cases hd : P ∣ n
    · simp only [gamma, correction, if_neg hn, if_pos hd, Nat.cast_zero,
        zero_div, sub_zero, multipleTerm, if_pos (show 0 < n ∧ P ∣ n from ⟨hnpos, hd⟩)]
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      push_cast
      ring
    · simp [gamma, correction, hn, multipleTerm, hd]

theorem tsum_multiple (P : ℕ) (hP : 0 < P) :
    ∑' n, multipleTerm P n = 1 / ((2 : ℝ) ^ P - 1) := by
  have hi : Function.Injective (fun k : ℕ => P * (k + 1)) := by
    intro i j hh
    have := Nat.eq_of_mul_eq_mul_left hP hh
    omega
  have hsupp : Function.support (multipleTerm P) ⊆ Set.range (fun k : ℕ => P * (k + 1)) := by
    intro n hn
    have hn' : multipleTerm P n ≠ 0 := hn
    by_cases hh : 0 < n ∧ P ∣ n
    · obtain ⟨hnpos, k, hk⟩ := hh
      have hkpos : 0 < k := by nlinarith
      exact ⟨k - 1, by dsimp only; rw [Nat.sub_add_cancel (by omega)]; exact hk.symm⟩
    · exact False.elim (hn' (by simp [multipleTerm, hh]))
  rw [← hi.tsum_eq hsupp]
  have hterm : ∀ k : ℕ, multipleTerm P (P * (k + 1)) =
      ((1 : ℝ) / 2 ^ P) ^ (k + 1) := by
    intro k
    rw [multipleTerm, if_pos ⟨Nat.mul_pos hP (by omega), dvd_mul_right _ _⟩]
    rw [div_pow, one_pow, pow_mul]
  simp_rw [hterm]
  have hp : (1 : ℝ) < 2 ^ P := one_lt_pow₀ (by norm_num) hP.ne'
  have hr0 : (0 : ℝ) ≤ 1 / 2 ^ P := by positivity
  have hr1 : (1 : ℝ) / 2 ^ P < 1 := (div_lt_one (by positivity)).mpr hp
  have hh : ∑' k : ℕ, ((1 : ℝ) / 2 ^ P) ^ (k + 1) =
      (1 / 2 ^ P) * (1 / (1 - 1 / 2 ^ P)) := by
    simp_rw [pow_succ']
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    simp [one_div]
  rw [hh]
  field_simp

theorem correction_le (B n : ℕ) : correction B n ≤ n := by
  unfold correction
  split <;> omega

private theorem summable_bounded (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) :
    Summable (fun n : ℕ => (c n : ℝ) / 2 ^ n) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1
      (r := (1 / 2 : ℝ)) (by norm_num)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  rw [div_pow, one_pow, mul_one_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc n) (by positivity)

private theorem summable_multiple (P : ℕ) : Summable (multipleTerm P) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num))
  · unfold multipleTerm
    split <;> positivity
  · unfold multipleTerm
    split
    · simp [div_pow, one_pow]
    · positivity

theorem exact_series (B P : ℕ) (hBP : B < P) :
    binaryCoeffSeries (gamma B P) = 2 -
      (∑ n ∈ Finset.range (B + 1), ((n - Nat.totient n : ℕ) : ℝ) / 2 ^ n) -
      1 / ((2 : ℝ) ^ P - 1) := by
  have hsId : Summable (fun n : ℕ => (n : ℝ) / 2 ^ n) :=
    summable_bounded (fun n => n) (fun n => le_rfl)
  have hsC := summable_bounded (correction B) (correction_le B)
  have hsM := summable_multiple P
  have hId : (∑' n : ℕ, (n : ℝ) / 2 ^ n) = 2 := by
    simp_rw [div_eq_mul_inv, ← inv_pow]
    rw [tsum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(2 : ℝ)⁻¹‖ < 1)]
    norm_num
  have hC : (∑' n : ℕ, (correction B n : ℝ) / 2 ^ n) =
      ∑ n ∈ Finset.range (B + 1), ((n - Nat.totient n : ℕ) : ℝ) / 2 ^ n := by
    rw [tsum_eq_sum (s := Finset.range (B + 1)) (fun n hn => by
      have hh : ¬ n ≤ B := by simpa using hn
      simp [correction, hh])]
    apply Finset.sum_congr rfl
    intro n hn
    have hh : n ≤ B := by simpa using hn
    simp [correction, hh]
  have hfull : (∑' n : ℕ, (gamma B P n : ℝ) / 2 ^ n) = 2 -
      (∑ n ∈ Finset.range (B + 1), ((n - Nat.totient n : ℕ) : ℝ) / 2 ^ n) -
      1 / ((2 : ℝ) ^ P - 1) := by
    simp_rw [gamma_term B P _ hBP]
    rw [(hsId.sub hsC).tsum_sub hsM, hsId.tsum_sub hsC, hId, hC, tsum_multiple P (by omega)]
  have hsplit := (summable_bounded (gamma B P) (gamma_le B P)).sum_add_tsum_nat_add 1
  simpa [binaryCoeffSeries, Finset.sum_range_one, gamma] using hsplit.trans hfull

end ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.gamma_le
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.gamma_prefix
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.discrepancy_prefix
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.exact_series
