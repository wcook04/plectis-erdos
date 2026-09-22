import Erdos249257.TotientTailPeriodKiller

/-! The exact denominator-specific period in long-paper `catalogue:cert:a9`.
The displayed rational representation need not be reduced. This proves its
specified preperiod and Euler period, rather than just existence of some period. -/

namespace ErdosProblems.Erdos249.PaperCompleteR20

open Erdos249257.TotientTailPeriodKiller
open scoped BigOperators

/-- A displayed denominator gives the exact tail-integrality range. -/
theorem tail_diff_int_of_displayed_denominator
    (a : ℤ) (c v h N : ℕ) (hv : 0 < v) (hN : c ≤ N)
    (hdiv : v ∣ 2 ^ h - 1)
    (hS : (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) =
      (a : ℝ) / ((2 : ℝ) ^ c * (v : ℝ))) :
    totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ) := by
  obtain ⟨k, hk⟩ := hdiv
  have hv0 : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  have hpow : (2 : ℝ) ^ N = 2 ^ c * 2 ^ (N - c) := by
    rw [← pow_add, Nat.add_sub_of_le hN]
  have hm : (2 : ℝ) ^ h - 1 = (v : ℝ) * (k : ℝ) := by
    have hge : 1 ≤ (2 : ℕ) ^ h := Nat.one_le_pow _ _ (by norm_num)
    have hh := congrArg (fun n : ℕ => (n : ℝ)) hk
    simpa only [Nat.cast_sub hge, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
      Nat.cast_mul] using hh
  have hscale : (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) *
      ((a : ℝ) / ((2 : ℝ) ^ c * (v : ℝ))) =
      (a : ℝ) * 2 ^ (N - c) * (k : ℝ) := by
    rw [hpow, hm]
    field_simp [hv0]
    <;> ring
  have h1 := two_pow_mul_totient_series_eq (N + h)
  have h2 := two_pow_mul_totient_series_eq N
  rw [hS, pow_add] at h1
  rw [hS] at h2
  refine ⟨a * 2 ^ (N - c) * (k : ℤ) +
    (totientPrefix N : ℤ) - (totientPrefix (N + h) : ℤ), ?_⟩
  push_cast
  nlinarith [hscale]

/-- The complete paper assertion: h = φ(v) is positive, and every N ≥ c works. -/
theorem specified_euler_tail_period
    (a : ℤ) (c v : ℕ) (hv : 0 < v) (hodd : Odd v)
    (hS : (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) =
      (a : ℝ) / ((2 : ℝ) ^ c * (v : ℝ))) :
    0 < Nat.totient v ∧ ∀ N : ℕ, c ≤ N →
      totientTail (N + Nat.totient v) - totientTail N ∈
        Set.range ((↑) : ℤ → ℝ) := by
  refine ⟨Nat.totient_pos.mpr hv, fun N hN => ?_⟩
  apply tail_diff_int_of_displayed_denominator a c v (Nat.totient v) N hv hN _ hS
  have heuler := Nat.ModEq.pow_totient hodd.coprime_two_left
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp heuler.symm

#print axioms tail_diff_int_of_displayed_denominator
#print axioms specified_euler_tail_period

end ErdosProblems.Erdos249.PaperCompleteR20
