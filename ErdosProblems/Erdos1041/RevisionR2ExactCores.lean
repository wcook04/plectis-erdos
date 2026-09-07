import Mathlib.Tactic

/-!
# Erdős #1041: exact rational cores from the 2026-09-06 revision return

These declarations kernel-check only finite rational identities used by the
ordinary refutations in `ExactObstructionsR2.md`.  They do not prove Rouché,
winding, Riemann–Hurwitz, or any parent-problem statement.

The Type B `S = 3/2` cube is recorded solely to compare it with the already
landed disk-family threshold `S = 4/3`, which is strictly smaller.
-/

namespace ErdosProblems.Erdos1041.RevisionR2ExactCores

theorem sepOr_rouche_margin : (39 : ℚ) / 50 < 1 := by norm_num

theorem sepOr_muSq_gt_thirteen_twentyfifths :
    (9 : ℚ) / 16 + 1 / 250000 > (13 / 25) ^ 2 := by norm_num

theorem sepOr_muSq_gt_three_fourths :
    (9 : ℚ) / 16 + 1 / 250000 > (3 / 4) ^ 2 := by norm_num

theorem sepOr_reciprocal_from_three_fourths :
    (1 : ℚ) / 250 / (3 / 4) = 2 / 375 := by norm_num

theorem sepOr_separation_lt_two : (2 : ℚ) / 375 < 2 := by norm_num

theorem sepOr_squared_ratio_lt_four :
    ((1 : ℚ) / 250) ^ 2 < 4 * (9 / 16 + 1 / 250000) := by norm_num

theorem oneLobe_separating_circle : (6 : ℚ) / 5 - (4 / 5) ^ 8 > 1 := by
  norm_num

theorem oneLobe_inner_disc : (15 : ℚ) / 16 + (5 / 8) ^ 8 < 1 := by norm_num

theorem oneLobe_inner_eighth_power : ((5 : ℚ) / 8) ^ 8 < 1 / 16 := by
  norm_num

theorem oneLobe_critical_value_outside : 3 * 21 ^ 7 > 16 ^ 8 := by
  norm_num

/-- `√2 < 3/2` after squaring positive quantities, used to compare the
proposed gamma constant with `5π/4`. -/
theorem oneLobe_two_lt_nine_fourths : (2 : ℚ) < 9 / 4 := by norm_num

theorem arity_rouche : (3 : ℚ) / 400 + 3 / 32 < 1 := by norm_num

theorem arity_unique_first_modulus : (187 : ℚ) / 2000 < 47 / 500 := by
  norm_num

theorem arity_second_inside_double :
    (47 : ℚ) / 500 < 2 * (187 / 2000) := by norm_num

theorem arity_mu_lt_half : (187 : ℚ) / 2000 < 1 / 2 := by norm_num

theorem paper_constant_factor_lt_seventy_one_tenths :
    (66517563 : ℚ) / 9392500 < 71 / 10 := by norm_num

theorem typeB_constant_factor_lt_seventy_one_tenths :
    (465613191 : ℚ) / 65747500 < 71 / 10 := by norm_num

theorem unit_scale_lt_five_point_seven :
    (15668813 : ℚ) / 2755116 < 57 / 10 := by norm_num

theorem typeB_three_halves_cube :
    (3 : ℚ) / 2 * (5 / 6) ^ 3 = 125 / 144 := by norm_num

theorem typeB_three_halves_cube_lt_one : (125 : ℚ) / 144 < 1 := by
  norm_num

/-- The already-landed disk-family uniform radius is strictly smaller than
Type B's proposed all-degree cutoff `3/2`. -/
theorem diskFamily_four_thirds_lt_three_halves : (4 : ℚ) / 3 < 3 / 2 := by
  norm_num

/-- `log(S/(S-1)) - artanh(1/S) = (1/2) log(S^2/(S^2-1))` is positive at
`S = 3/2` because `9/5 > 1`. -/
theorem artanh_gap_ratio_at_three_halves : (9 : ℚ) / 5 > 1 := by norm_num

end ErdosProblems.Erdos1041.RevisionR2ExactCores
