/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Round-six proposed algebraic/inequality components. UNCOMPILED in the review
session: neither Lean nor Lake was available. These declarations do not assert
holomorphic square-root existence, path integration, or the complete connector
or cusp theorem. The complete ordinary proof is in report/research_report.tex.
-/
import Mathlib

namespace ErdosProblems.Erdos1041.BlaschkeSectorConnector

/-- The circle is the exact equality set of the quadratic quotient's moduli. -/
theorem quadratic_normsq_defect (x y b : ℝ) :
    (x ^ 2 + y ^ 2) * ((x + b) ^ 2 + y ^ 2) -
        ((1 + b * x) ^ 2 + (b * y) ^ 2) =
      (x ^ 2 + y ^ 2 - 1) * (x ^ 2 + y ^ 2 + 1 + 2 * b * x) := by
  ring

/-- The second factor is strictly positive for |b| < 1. -/
theorem circle_factor_pos (x y b : ℝ) (hb : b ^ 2 < 1) :
    0 < x ^ 2 + y ^ 2 + 1 + 2 * b * x := by
  nlinarith [sq_nonneg (x + b), sq_nonneg y]

/-- A quotient modulus at most one forces the point into the closed disc. -/
theorem inside_of_quadratic_modulus
    (x y b : ℝ) (hb : b ^ 2 < 1)
    (h : (x ^ 2 + y ^ 2) * ((x + b) ^ 2 + y ^ 2) ≤
      (1 + b * x) ^ 2 + (b * y) ^ 2) :
    x ^ 2 + y ^ 2 ≤ 1 := by
  have hp := circle_factor_pos x y b hb
  have hd := quadratic_normsq_defect x y b
  have hn : (x ^ 2 + y ^ 2 - 1) *
      (x ^ 2 + y ^ 2 + 1 + 2 * b * x) ≤ 0 := by
    linarith
  by_contra hc
  have hpos : 0 < x ^ 2 + y ^ 2 - 1 := by linarith
  exact (not_lt_of_ge hn) (mul_pos hpos hp)

/-- A supplied square root of the discriminant solves the low-degree inverse
relation. The analytic selection of that root is a separate ordinary step. -/
theorem quadratic_pullback (p b s : ℂ)
    (hs : s ^ 2 = p ^ 2 + (b ^ 2 / 4) * (p ^ 2 - 1) ^ 2) :
    ((b / 2) * (p ^ 2 - 1) - s) *
      (((b / 2) * (p ^ 2 - 1) - s) + b) =
    p ^ 2 * (1 + b * ((b / 2) * (p ^ 2 - 1) - s)) := by
  linear_combination hs

/-- Keeping the quadratic relation before taking norms retains cancellation
at both endpoints of the sector path. -/
theorem power_pullback (z p b : ℂ) (N : ℕ)
    (h : z * (z + b) = p ^ 2 * (1 + b * z)) :
    (z * (z + b)) ^ N - (1 + b * z) ^ N =
      (1 + b * z) ^ N * (p ^ (2 * N) - 1) := by
  rw [h, mul_pow, ← pow_mul]
  ring

/-- Pointwise amplitude estimate used on all three pieces of the path. -/
theorem amplitude_normsq_bound (x y b u : ℝ)
    (hb : 0 ≤ b) (hbu : b ≤ u / 10)
    (hz : x ^ 2 + y ^ 2 ≤ 1) (hx : x ≤ -(49 / 100 : ℝ) * u) :
    (1 + b * x) ^ 2 + (b * y) ^ 2 ≤ 1 - (22 / 25 : ℝ) * b * u := by
  have h1 := mul_le_mul_of_nonneg_left hx (show 0 ≤ 2 * b by positivity)
  have h2 := mul_le_mul_of_nonneg_left hz (sq_nonneg b)
  have h3 := mul_le_mul_of_nonneg_left hbu hb
  nlinarith

/-- Scalar consolidation after the derivative has been integrated. -/
theorem uniform_length_saving (L q t e : ℝ)
    (ht : 0 ≤ t) (hq : q ≤ (22 / 21 : ℝ))
    (he : e ≤ (311 / 1050 : ℝ) * t)
    (hL : L ≤ 2 - (2 - q) * t + e) :
    L ≤ 2 - (689 / 1050 : ℝ) * t := by
  have hqt := mul_le_mul_of_nonneg_right hq ht
  nlinarith

/-- Strict target length once the inner radius is positive. -/
theorem below_two_of_saving (L t : ℝ) (ht : 0 < t)
    (hL : L ≤ 2 - (689 / 1050 : ℝ) * t) : L < 2 := by
  nlinarith

/-- Reverse triangle inequality for the exterior radial barriers. -/
theorem outside_of_error_bound (u v : ℂ) (s t : ℝ)
    (hu : ‖u‖ = 1 + s) (hv : ‖v‖ ≤ t) (hst : t < s) :
    1 < ‖u + v‖ := by
  have htri : ‖u‖ ≤ ‖u + v‖ + ‖v‖ := by
    calc
      ‖u‖ = ‖(u + v) - v‖ := by congr 1; ring
      _ ≤ ‖u + v‖ + ‖v‖ := norm_sub_le (u + v) v
  linarith

/-- The rational radius used for the finite degree-24 connector. -/
theorem degree24_radius_power : (13 / 15 : ℝ) ^ 23 < 1 / 25 := by
  norm_num

/-- Exact evaluation of the three-piece length majorant. -/
theorem degree24_length_evaluation :
    2 - (2 - (11 / 42 : ℝ)) * (13 / 15) +
      (1 / 120) * (1 - (1 - (11 / 42)) * (13 / 15) ^ 2) +
      3 * (1 / 120) ^ 2 *
        (2 * ((13 / 15)⁻¹ - 1) + (11 / 42) / (13 / 15)) =
      (58672129 / 117936000 : ℝ) := by
  norm_num

theorem degree24_length_lt_half :
    (58672129 / 117936000 : ℝ) < 1 / 2 := by
  norm_num

theorem degree24_level_evaluation :
    (1 + (1 / 10 : ℝ) * (13 / 15) / 25)⁻¹ = 3750 / 3763 := by
  norm_num

/-- This scalar comparison is the only extra numerical ingredient in the
registered 13/25 theorem's degree-uniform 5/2 scaling corollary. -/
theorem scale_base_lt_five_fourths_cube :
    (25 / 13 : ℝ) < (5 / 4) ^ 3 := by
  norm_num

#print axioms quadratic_pullback
#print axioms amplitude_normsq_bound
#print axioms degree24_length_lt_half

end ErdosProblems.Erdos1041.BlaschkeSectorConnector
