import Mathlib.Tactic

/-!
# Erdős #1041: exact kernel for the block-L1 sextic rescue

The companion note gives a strict finite connector for the same sextic that
refutes pointwise component-block L1 contraction. This module checks the
Bernstein signs, tail endpoint/monotonicity kernel, and metric budget.
-/

namespace ErdosProblems.Erdos1041.TiedNewtonFaceBlockL1RationalRescue

noncomputable section

def s3 : ℝ := Real.sqrt 3
def epsilon : ℝ := -(5997001 / 1000000000)
def radius : ℝ := 5 / 4

theorem s3_pos : 0 < s3 := by
  dsimp [s3]
  positivity

theorem s3_sq : s3 ^ 2 = 3 := by
  dsimp [s3]
  norm_num

theorem s3_gt_threeHalves : 3 / 2 < s3 := by
  have hs := s3_sq
  have hn : 0 ≤ s3 := le_of_lt s3_pos
  nlinarith

theorem s3_lt_sevenFourths : s3 < 7 / 4 := by
  have hs := s3_sq
  have hn : 0 ≤ s3 := le_of_lt s3_pos
  nlinarith

def u0 : ℝ := -187661814643 / 32768000000000
def u1 : ℝ := -6859138399 / 1024000000000
def u2 : ℝ := -293067436173 / 2048000000000
def u3 : ℝ := -70121042439 / 64000000000
def u4 : ℝ := -413998038003 / 128000000000
def u5 : ℝ := -24568909879 / 4000000000
def u6 : ℝ := -68065554133 / 8000000000

theorem armU_controls_neg :
    u0 < 0 ∧ u1 < 0 ∧ u2 < 0 ∧ u3 < 0 ∧ u4 < 0 ∧ u5 < 0 ∧ u6 < 0 := by
  norm_num [u0, u1, u2, u3, u4, u5, u6]

def v0 : ℝ := -187661814643 / 32768000000000
def v1 : ℝ := -(-185279460616 + 213778321875 * s3) / 16384000000000
def v2 : ℝ := (-5348002137971 + 2805682500000 * s3) / 4096000000000
def v3 : ℝ := (-110490573689 + 51300000000 * s3) / 64000000000
def v4 : ℝ := -19 * (-2876378401 + 6806250000 * s3) / 256000000000
def v5 : ℝ := -(-3256816936 + 41080078125 * s3) / 64000000000
def v6 : ℝ := -11815554133 / 8000000000

theorem armV_controls_neg :
    v0 < 0 ∧ v1 < 0 ∧ v2 < 0 ∧ v3 < 0 ∧ v4 < 0 ∧ v5 < 0 ∧ v6 < 0 := by
  have hl := s3_gt_threeHalves
  have hu := s3_lt_sevenFourths
  constructor
  · norm_num [v0]
  constructor
  · dsimp [v1]
    norm_num
    nlinarith
  constructor
  · dsimp [v2]
    nlinarith
  constructor
  · dsimp [v3]
    nlinarith
  constructor
  · dsimp [v4]
    norm_num
    nlinarith
  constructor
  · dsimp [v5]
    norm_num
    nlinarith
  · norm_num [v6]

def tailV (r : ℝ) : ℝ := -r ^ 6 + (3 / 2) * r ^ 2 + epsilon

theorem tailV_at_radius_neg : tailV radius < 0 := by
  norm_num [tailV, radius, epsilon]

/-- Once r^4 >= 3/2, the selected tail is no larger than its negative
constant term. The ordinary proof obtains this hypothesis from r>=5/4. -/
theorem tailV_neg_of_fourthPower
    {r : ℝ} (hr4 : 3 / 2 ≤ r ^ 4) :
    tailV r < 0 := by
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  have hmul := mul_le_mul_of_nonneg_left hr4 hr2
  have heps : epsilon < 0 := by norm_num [epsilon]
  dsimp [tailV]
  ring_nf at hmul ⊢
  nlinarith

def distUSq : ℝ := (5 / 4 - 7 / 10) ^ 2 + (57 / 80) ^ 2
def distVSq : ℝ :=
  (5 / 8 - 7 / 10) ^ 2 + (5 * s3 / 8 - 57 / 80) ^ 2

theorem distUSq_value : distUSq = 1037 / 1280 := by
  norm_num [distUSq]

theorem distVSq_value :
    distVSq = 2157 / 1280 - 57 * s3 / 64 := by
  dsimp [distVSq]
  nlinarith [s3_sq]

theorem distUSq_lt_one : distUSq < 1 := by
  rw [distUSq_value]
  norm_num

theorem distVSq_lt_one : distVSq < 1 := by
  rw [distVSq_value]
  nlinarith [s3_gt_threeHalves]

theorem connector_length_lt_two_mul_radius :
    Real.sqrt distUSq + Real.sqrt distVSq < 2 * radius := by
  have hu0 : 0 ≤ distUSq := by
    dsimp [distUSq]
    positivity
  have hv0 : 0 ≤ distVSq := by
    dsimp [distVSq]
    positivity
  have hu : Real.sqrt distUSq < 1 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
    simpa using distUSq_lt_one
  have hv : Real.sqrt distVSq < 1 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
    simpa using distVSq_lt_one
  dsimp [radius]
  linarith

end

end ErdosProblems.Erdos1041.TiedNewtonFaceBlockL1RationalRescue
