/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos1041.CriticalTwoRootProximity

namespace Erdos249257.ExternalVerification1041CriticalGeometry

open Finset

theorem criticalGeometricMean_twoRootProximity
    {n : ℕ} (hn : 2 ≤ n) (z : Fin n → ℂ) (c : ℂ)
    (hne : ∀ k, c - z k ≠ 0)
    (hcrit : ∑ k, (c - z k)⁻¹ = 0)
    {r : ℝ} (hr : 0 < r) (hrn : r ^ n = ∏ k, ‖c - z k‖) :
    ∃ i j : Fin n, i ≠ j ∧ ‖c - z i‖ + ‖c - z j‖ ≤ 2 * r := by
  exact ErdosProblems.Erdos1041.exists_two_roots_dist_sum_le_two_mul_geomMean
    hn z c hne hcrit hr hrn

theorem criticalDiskInverseBalance_twoRootProximity
    {N t δ e : ℝ}
    (hN : 2 ≤ N) (ht1 : t < 1)
    (hδ : 0 < δ) (hδe : δ ≤ e) (hδ1 : δ ≤ 1)
    (hemax : e ≤ 1 + t) (hbal : e ≤ (N - 1) * δ)
    (hstar : N ≤ (1 - t ^ 2) * (1 / δ ^ 2 + (N - 1) / e ^ 2)) :
    δ + e ≤ 2 := by
  exact ErdosProblems.Erdos1041.two_add_le_two_of_disk_inverse_balance
    hN ht1 hδ hδe hδ1 hemax hbal hstar

theorem criticalDiskInverseBalance_twoRootProximity_strict
    {N t δ e : ℝ}
    (hN : 2 ≤ N) (ht1 : t < 1)
    (hδ : 0 < δ) (hδe : δ ≤ e) (hδ1 : δ ≤ 1)
    (hemax : e < 1 + t) (hbal : e ≤ (N - 1) * δ)
    (hstar : N ≤ (1 - t ^ 2) * (1 / δ ^ 2 + (N - 1) / e ^ 2)) :
    δ + e < 2 := by
  exact ErdosProblems.Erdos1041.two_add_lt_two_of_disk_inverse_balance_of_strict_diameter
    hN ht1 hδ hδe hδ1 hemax hbal hstar

theorem nearestSpoke_unique_nearest_spoke_escapes :
    (1 : ℝ) <
      (900099 / 902000 : ℝ) * (1 - 1 / 10) *
        (((1 / 10 : ℝ) * (900099 / 902000)) ^ 2 + (999 / 1000) ^ 2) *
        (((1 / 10 : ℝ) * (900099 / 902000)) ^ 2 +
          (1 / 10) * (999 / 1000) ^ 2 + (999 / 1000) ^ 2) := by
  exact ErdosProblems.Erdos1041.nearestSpoke_unique_nearest_spoke_escapes

noncomputable def allStraightRadius : ℂ := (99 : ℂ) / 100

noncomputable def allStraightOmega : ℂ :=
  (-1 : ℂ) / 2 + ((Real.sqrt 3 : ℂ) / 2) * Complex.I

noncomputable def allStraightRoot : Fin 3 → ℂ
  | 0 => allStraightRadius
  | 1 => allStraightRadius * allStraightOmega
  | 2 => allStraightRadius * allStraightOmega ^ 2

noncomputable def allStraightCubic (z : ℂ) : ℂ :=
  z ^ 3 - allStraightRadius ^ 3

private theorem allStraightOmega_quadratic :
    allStraightOmega ^ 2 + allStraightOmega + 1 = 0 := by
  have hsqrt : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  apply Complex.ext <;>
    norm_num [allStraightOmega, pow_two, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im] <;> nlinarith

private theorem allStraightOmega_cube : allStraightOmega ^ 3 = 1 := by
  apply sub_eq_zero.mp
  calc allStraightOmega ^ 3 - 1 =
        (allStraightOmega - 1) *
          (allStraightOmega ^ 2 + allStraightOmega + 1) := by ring
    _ = 0 := by rw [allStraightOmega_quadratic, mul_zero]

private theorem allStraight_midpoint_value_of_unit
    (u : ℂ) (hu : u ^ 3 = 1) :
    allStraightCubic (-(allStraightRadius * u) / 2) =
      -(9 / 8 : ℂ) * allStraightRadius ^ 3 := by
  unfold allStraightCubic
  rw [div_pow, neg_pow, mul_pow, hu]
  ring

private theorem allStraight_pair_zero_one :
    allStraightCubic ((allStraightRoot 0 + allStraightRoot 1) / 2) =
      -(9 / 8 : ℂ) * allStraightRadius ^ 3 := by
  rw [show (allStraightRoot 0 + allStraightRoot 1) / 2 =
      -(allStraightRadius * allStraightOmega ^ 2) / 2 by
        simp only [allStraightRoot]
        linear_combination (allStraightRadius / 2) * allStraightOmega_quadratic]
  apply allStraight_midpoint_value_of_unit
  rw [show (allStraightOmega ^ 2) ^ 3 =
    (allStraightOmega ^ 3) ^ 2 by ring]
  rw [allStraightOmega_cube]
  norm_num

private theorem allStraight_pair_zero_two :
    allStraightCubic ((allStraightRoot 0 + allStraightRoot 2) / 2) =
      -(9 / 8 : ℂ) * allStraightRadius ^ 3 := by
  rw [show (allStraightRoot 0 + allStraightRoot 2) / 2 =
      -(allStraightRadius * allStraightOmega) / 2 by
        simp only [allStraightRoot]
        linear_combination (allStraightRadius / 2) * allStraightOmega_quadratic]
  exact allStraight_midpoint_value_of_unit allStraightOmega allStraightOmega_cube

private theorem allStraight_pair_one_two :
    allStraightCubic ((allStraightRoot 1 + allStraightRoot 2) / 2) =
      -(9 / 8 : ℂ) * allStraightRadius ^ 3 := by
  rw [show (allStraightRoot 1 + allStraightRoot 2) / 2 =
      -(allStraightRadius * 1) / 2 by
        simp only [allStraightRoot]
        linear_combination (allStraightRadius / 2) * allStraightOmega_quadratic]
  exact allStraight_midpoint_value_of_unit 1 (by norm_num)

private theorem allStraight_pair_midpoint_value
    (i j : Fin 3) (hij : i ≠ j) :
    allStraightCubic ((allStraightRoot i + allStraightRoot j) / 2) =
      -(9 / 8 : ℂ) * allStraightRadius ^ 3 := by
  fin_cases i <;> fin_cases j <;> simp_all
  · simpa only [neg_mul] using allStraight_pair_zero_one
  · simpa only [neg_mul] using allStraight_pair_zero_two
  · convert allStraight_pair_zero_one using 1 <;> ring
  · simpa only [neg_mul] using allStraight_pair_one_two
  · convert allStraight_pair_zero_two using 1 <;> ring
  · convert allStraight_pair_one_two using 1 <;> ring

theorem allStraightCubic_every_pair_midpoint_escapes :
    ∀ i j : Fin 3, i ≠ j →
      1 < ‖allStraightCubic ((allStraightRoot i + allStraightRoot j) / 2)‖ := by
  intro i j hij
  rw [allStraight_pair_midpoint_value i j hij, norm_mul, norm_neg]
  norm_num [allStraightRadius, norm_pow]

end Erdos249257.ExternalVerification1041CriticalGeometry
