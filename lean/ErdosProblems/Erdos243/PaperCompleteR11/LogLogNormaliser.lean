import ErdosProblems.Erdos243.PaperCompleteR11.CanonicalGrowthBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exact base-two log-log normalisation


The cut-off is exactly `max 4 x`, as in the paper. The tower identities
are exact, including the normalisation constant: no change of logarithm
base is absorbed into an unspecified asymptotic constant.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

/-- An integer height which the paper's normaliser sends to its index. -/
def binaryTower (n : ℕ) : ℕ := 2 ^ (2 ^ n)

/-- An elementary exponent estimate, including the index zero. -/
theorem index_succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      omega

/-- Monotonicity in a natural exponent, proved without an asymptotic API. -/
theorem two_pow_mono {n m : ℕ} (h : n ≤ m) : 2 ^ n ≤ 2 ^ m :=
  Nat.pow_le_pow_right (by norm_num) h

theorem binaryTower_pos (n : ℕ) : 0 < binaryTower n := by
  unfold binaryTower
  positivity

theorem binaryTower_mono {n m : ℕ} (h : n ≤ m) : binaryTower n ≤ binaryTower m :=
  two_pow_mono (two_pow_mono h)

theorem binaryTower_succ (n : ℕ) : binaryTower (n + 1) = binaryTower n ^ 2 :=
  doublePower_succ 2 n

/-- A very coarse lower bound, useful for the finite width term. -/
theorem index_le_binaryTower (n : ℕ) : n ≤ binaryTower n := by
  have h₁ := index_succ_le_two_pow n
  have h₂ := index_succ_le_two_pow (2 ^ n)
  unfold binaryTower
  omega

/-- The exact real-valued normaliser from the inclusive boundary. -/
noncomputable def recordLogLog (x : ℝ) : ℝ :=
  Real.log (Real.log (max 4 x) / Real.log 2) / Real.log 2

theorem log_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)

/-- The argument of the outer logarithm is at least two. -/
theorem inner_logLog_ge_two (x : ℝ) :
    2 ≤ Real.log (max 4 x) / Real.log 2 := by
  apply (le_div_iff₀ log_two_pos).2
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (le_max_left 4 x)
  have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have hh := Real.log_pow (2 : ℝ) 2
    norm_num at hh
    exact hh
  linarith

/-- Monotonicity is global because the cut-off is part of the definition. -/
theorem recordLogLog_mono : Monotone recordLogLog := by
  intro x y hxy
  have hx : 0 < max (4 : ℝ) x := lt_of_lt_of_le (by norm_num) (le_max_left 4 x)
  have hinner : Real.log (max 4 x) / Real.log 2 ≤
      Real.log (max 4 y) / Real.log 2 :=
    div_le_div_of_nonneg_right (Real.log_le_log hx (max_le_max le_rfl hxy))
      log_two_pos.le
  have hpos : 0 < Real.log (max 4 x) / Real.log 2 := by
    have hh := inner_logLog_ge_two x
    linarith
  exact div_le_div_of_nonneg_right (Real.log_le_log hpos hinner) log_two_pos.le

/-- The normaliser is positive even below the cut-off, where it is one. -/
theorem one_le_recordLogLog (x : ℝ) : 1 ≤ recordLogLog x := by
  unfold recordLogLog
  apply (le_div_iff₀ log_two_pos).2
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (inner_logLog_ge_two x)
  simpa only [one_mul] using h

/-- Exact evaluation on the integer double-exponential grid. -/
theorem recordLogLog_binaryTower (n : ℕ) (hn : 1 ≤ n) :
    recordLogLog (binaryTower n : ℝ) = (n : ℝ) := by
  have hfourN : 4 ≤ binaryTower n := by
    have h := binaryTower_mono hn
    norm_num [binaryTower] at h
    exact h
  have hfour : (4 : ℝ) ≤ (binaryTower n : ℝ) := by exact_mod_cast hfourN
  have ht : (binaryTower n : ℝ) = (2 : ℝ) ^ (2 ^ n) := by
    simp only [binaryTower, Nat.cast_pow, Nat.cast_ofNat]
  have hl : Real.log (2 : ℝ) ≠ 0 := log_two_pos.ne'
  unfold recordLogLog
  rw [max_eq_right hfour, ht, Real.log_pow, mul_div_cancel_right₀ _ hl]
  have hpow : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by push_cast; rfl
  rw [hpow, Real.log_pow, mul_div_cancel_right₀ _ hl]

theorem recordLogLog_four : recordLogLog 4 = 1 := by
  simpa [binaryTower] using recordLogLog_binaryTower 1 le_rfl

/-- The tower budget gives an exact index bound, with coefficient one. -/
theorem recordLogLog_le_of_le_binaryTower {x : ℝ} {n : ℕ}
    (hn : 1 ≤ n) (hx : x ≤ (binaryTower n : ℝ)) :
    recordLogLog x ≤ (n : ℝ) := by
  exact (recordLogLog_mono hx).trans_eq (recordLogLog_binaryTower n hn)

/-- A bound at the unscaled height transfers monotonically to a larger
height. This lemma does not assert that fixed scaling disappears exactly. -/
theorem recordLogLog_nat_mul_mono (g : ℕ) {x y : ℕ} (hxy : x ≤ y) :
    recordLogLog (g * x : ℕ) ≤ recordLogLog (g * y : ℕ) := by
  apply recordLogLog_mono
  exact_mod_cast Nat.mul_le_mul_left g hxy

end ErdosProblems.Erdos243.PaperCompleteR11
