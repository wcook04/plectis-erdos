import Mathlib

/-!
# Erdős 1041: the uniform radius `4/3` threshold of the disk-family coefficient

First clause of the long-record corollary labelled
`res:critical-value-thresholds` (`paper/reasoning-parts/erdos1041/core.tex`,
line 1534): the paper's inequality (6),
`(S/(n-1))^(2/n) * log((S^2+S+p)/(S^2-S+p)) < 2` with `p = w₀(1-w₀)`, holds for
every degree `n ≥ 3`, every centre `w₀ ∈ [0,1]`, and every radius
`4/3 ≤ S ≤ 2`.

This file does **not** cover the corollary's second clause, which transports
that inequality through the unformalised analytic Theorem
`res:critical-value-separation` (line 1341) to a root-to-root connector of
length below `2` inside `{|f| < 1}`.

The proof is transported from
`ErdosProblems/Erdos1041/DiskFamilyCriticalValueSeparation.lean` in the
read-only tree `/Users/willcook/.codex/worktrees/plectis-palomar-math-01a0bb15`,
which is absent from this tree.
-/

noncomputable section

namespace ErdosProblems.Erdos1041.PaperCompleteR21

/-- The left side of the paper's inequality (6):
`(S/(n-1))^(2/n) * log((S^2 + S + p)/(S^2 - S + p))`. -/
def separationCoefficient (n : ℕ) (S p : ℝ) : ℝ :=
  (S / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ)) *
    Real.log ((S ^ 2 + S + p) / (S ^ 2 - S + p))

private theorem seven_lt_exp_two : (7 : ℝ) < Real.exp 2 := by
  have h := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  rw [h2]
  nlinarith [h, Real.exp_pos 1]

private theorem log_seven_lt_two : Real.log 7 < 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  exact seven_lt_exp_two

/-- For `S > 1` and `p ≥ 0` the centre parameter only lowers the logarithmic
ratio: `(S^2+S+p)/(S^2-S+p) ≤ (S+1)/(S-1)`. -/
theorem separation_ratio_le_branch_ratio {S p : ℝ} (hS : 1 < S) (hp : 0 ≤ p) :
    (S ^ 2 + S + p) / (S ^ 2 - S + p) ≤ (S + 1) / (S - 1) := by
  have hden1 : 0 < S ^ 2 - S + p := by nlinarith
  have hden2 : 0 < S - 1 := by linarith
  rw [div_le_div_iff₀ hden1 hden2]
  nlinarith

/-- The branch-centred ratio is at most `7` once `S ≥ 4/3`. -/
theorem branch_ratio_le_seven {S : ℝ} (hS : 4 / 3 ≤ S) :
    (S + 1) / (S - 1) ≤ 7 := by
  have hden : 0 < S - 1 := by linarith
  rw [div_le_iff₀ hden]
  linarith

/-- The logarithmic factor is nonnegative in the admissible range. -/
theorem separation_log_nonneg {S p : ℝ} (hS : 1 < S) (hp : 0 ≤ p) :
    0 ≤ Real.log ((S ^ 2 + S + p) / (S ^ 2 - S + p)) := by
  apply Real.log_nonneg
  have hden : 0 < S ^ 2 - S + p := by nlinarith
  rw [le_div_iff₀ hden]
  linarith

/-- The radial factor `(S/(n-1))^(2/n)` lies in `(0, 1]` whenever
`0 < S ≤ n - 1`. -/
theorem separation_rpow_mem {n : ℕ} {S : ℝ} (hS0 : 0 < S)
    (hSn : S ≤ (n : ℝ) - 1) :
    0 < (S / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ)) ∧
      (S / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ)) ≤ 1 := by
  have hn1 : 0 < (n : ℝ) - 1 := lt_of_lt_of_le hS0 hSn
  have hbase0 : 0 < S / ((n : ℝ) - 1) := div_pos hS0 hn1
  have hbase1 : S / ((n : ℝ) - 1) ≤ 1 := by
    rw [div_le_one hn1]; exact hSn
  have hexp : (0 : ℝ) ≤ (2 : ℝ) / (n : ℝ) := by positivity
  exact ⟨Real.rpow_pos_of_pos hbase0 _, Real.rpow_le_one hbase0.le hbase1 hexp⟩

/-- General-`p` form of the threshold. -/
theorem separationCoefficient_lt_two {n : ℕ} (hn : 3 ≤ n) {S p : ℝ}
    (hS : 4 / 3 ≤ S) (hS2 : S ≤ 2) (hp0 : 0 ≤ p) :
    separationCoefficient n S p < 2 := by
  have hS1 : 1 < S := by linarith
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hSn : S ≤ (n : ℝ) - 1 := by linarith
  obtain ⟨hr0, hr1⟩ := separation_rpow_mem (by linarith) hSn
  have hlog0 := separation_log_nonneg hS1 hp0
  have hratio_pos : 0 < (S ^ 2 + S + p) / (S ^ 2 - S + p) := by
    have hden : 0 < S ^ 2 - S + p := by nlinarith
    exact div_pos (by nlinarith) hden
  have hlog7 : Real.log ((S ^ 2 + S + p) / (S ^ 2 - S + p)) ≤ Real.log 7 :=
    Real.log_le_log hratio_pos
      (le_trans (separation_ratio_le_branch_ratio hS1 hp0)
        (branch_ratio_le_seven hS))
  unfold separationCoefficient
  calc
    (S / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ)) *
        Real.log ((S ^ 2 + S + p) / (S ^ 2 - S + p))
        ≤ 1 * Real.log ((S ^ 2 + S + p) / (S ^ 2 - S + p)) :=
      mul_le_mul_of_nonneg_right hr1 hlog0
    _ = Real.log ((S ^ 2 + S + p) / (S ^ 2 - S + p)) := one_mul _
    _ ≤ Real.log 7 := hlog7
    _ < 2 := log_seven_lt_two

/-- **First clause of `res:critical-value-thresholds`.**  The paper's
inequality (6) holds for every degree `n ≥ 3`, every centre `w₀ ∈ [0,1]`, and
every radius `4/3 ≤ S ≤ 2`, with `p = w₀(1 - w₀)`. -/
theorem separationCoefficient_lt_two_of_uniform_radius {n : ℕ} (hn : 3 ≤ n)
    {w₀ S : ℝ} (hw₀ : 0 ≤ w₀) (hw₁ : w₀ ≤ 1) (hS : 4 / 3 ≤ S) (hS2 : S ≤ 2) :
    separationCoefficient n S (w₀ * (1 - w₀)) < 2 :=
  separationCoefficient_lt_two hn hS hS2 (mul_nonneg hw₀ (by linarith))

#print axioms separation_ratio_le_branch_ratio
#print axioms branch_ratio_le_seven
#print axioms separation_log_nonneg
#print axioms separation_rpow_mem
#print axioms separationCoefficient_lt_two
#print axioms separationCoefficient_lt_two_of_uniform_radius

end ErdosProblems.Erdos1041.PaperCompleteR21
