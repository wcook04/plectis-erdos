import Erdos249257.TotientTailPeriodKiller

/-! The two inputs to the worked example in `prop:D9-inv`: the ordinary dyadic
prefix `Φ_N / 2^N` of `S` has denominator dividing `2^N`, and its tail is at
most `(N+2)·2^{-N}`.

Here `Φ_N = totientPrefix N` and `R_N = totientTail N`. -/
namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.TotientTailPeriodKiller

/-- The ordinary dyadic prefix has denominator dividing `2^N`. -/
theorem dyadic_prefix_den_dvd (N : ℕ) :
    (((totientPrefix N : ℤ) : ℚ) / (((2 : ℤ) ^ N : ℤ) : ℚ)).den ∣ 2 ^ N := by
  have h := Rat.den_dvd (totientPrefix N : ℤ) ((2 : ℤ) ^ N)
  rw [Rat.divInt_eq_div] at h
  exact_mod_cast h

/-- The local tail is at most `N + 2`: only `φ(n) ≤ n` against a
geometric-linear majorant. -/
theorem totientTail_le_add_two (N : ℕ) :
    totientTail N ≤ (N : ℝ) + 2 := by
  have h := tail_after_le N 0
  simpa [totientTail] using h

/-- Hence the tail of the ordinary dyadic prefix is at most `(N+2)·2^{-N}`. -/
theorem dyadic_prefix_tail_le (N : ℕ) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
        - (totientPrefix N : ℝ) / (2 : ℝ) ^ N
      ≤ ((N : ℝ) + 2) / (2 : ℝ) ^ N := by
  have h := two_pow_mul_totient_series_eq N
  have htail := totientTail_le_add_two N
  have h2 : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have hinv : (0 : ℝ) ≤ ((2 : ℝ) ^ N)⁻¹ := by positivity
  have hexp : (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
      = ((totientPrefix N : ℝ) + totientTail N) * ((2 : ℝ) ^ N)⁻¹ := by
    rw [← h]
    field_simp
  have hS : (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
      - (totientPrefix N : ℝ) / (2 : ℝ) ^ N
      = totientTail N * ((2 : ℝ) ^ N)⁻¹ := by
    rw [hexp, div_eq_mul_inv]
    ring
  rw [hS, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right htail hinv

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.dyadic_prefix_den_dvd
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.totientTail_le_add_two
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.dyadic_prefix_tail_le
