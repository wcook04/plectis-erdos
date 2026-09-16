import ErdosProblems.Erdos1049.RationalBaseContour
import ErdosProblems.Erdos1049.QuadraticMeasureR10

/-!
# Exact constants for the power-uniform 31/4 bound

Finite rational sums bound the actual infinite trigamma
constant from below. These are unconditional parameter theorems, not an
assertion that the analytic source-form supplier has been formalised.
-/
namespace ErdosProblems.Erdos1049.PaperR10
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Sixteen positive terms on each of the thirteen intervals suffice. -/
theorem zudilinJ_sixteen_lower : (779418 : ℝ) / 10000 < zudilinJ := by
  have h1 := sum_le_trigammaSeries_sub
    (u := (1 / 14)) (v := (1 / 12)) (by norm_num) (by norm_num) 16
  have c1 : (5202337678 : ℝ) / 100000000 <
      ∑ k ∈ Finset.range 16,
        (1 / ((k : ℝ) + (1 / 14)) ^ 2 - 1 / ((k : ℝ) + (1 / 12)) ^ 2) := by
    norm_num [Finset.sum_range_succ]
  have b1 : (5202337678 : ℝ) / 100000000 < zudilinJTerm (1 / 14) (1 / 12) :=
    c1.trans_le h1
  have h2 := sum_le_trigammaSeries_sub
    (u := (1 / 7)) (v := (1 / 6)) (by norm_num) (by norm_num) 16
  have c2 : (1303886129 : ℝ) / 100000000 <
      ∑ k ∈ Finset.range 16,
        (1 / ((k : ℝ) + (1 / 7)) ^ 2 - 1 / ((k : ℝ) + (1 / 6)) ^ 2) := by
    norm_num [Finset.sum_range_succ]
  have b2 : (1303886129 : ℝ) / 100000000 < zudilinJTerm (1 / 7) (1 / 6) :=
    c2.trans_le h2
  have h3 := sum_le_trigammaSeries_sub
    (u := (3 / 14)) (v := (1 / 4)) (by norm_num) (by norm_num) 16
  have c3 : (582689310 : ℝ) / 100000000 <
      ∑ k ∈ Finset.range 16,
        (1 / ((k : ℝ) + (3 / 14)) ^ 2 - 1 / ((k : ℝ) + (1 / 4)) ^ 2) := by
    norm_num [Finset.sum_range_succ]
  have b3 : (582689310 : ℝ) / 100000000 < zudilinJTerm (3 / 14) (1 / 4) :=
    c3.trans_le h3
  have h4 := sum_le_trigammaSeries_sub
    (u := (2 / 7)) (v := (1 / 3)) (by norm_num) (by norm_num) 16
  have c4 : (330583528 : ℝ) / 100000000 <
      ∑ k ∈ Finset.range 16,
        (1 / ((k : ℝ) + (2 / 7)) ^ 2 - 1 / ((k : ℝ) + (1 / 3)) ^ 2) := by
    norm_num [Finset.sum_range_succ]
  have b4 : (330583528 : ℝ) / 100000000 < zudilinJTerm (2 / 7) (1 / 3) :=
    c4.trans_le h4
  have h5 := sum_le_trigammaSeries_sub
    (u := (5 / 14)) (v := (2 / 5)) (by norm_num) (by norm_num) 16
  have c5 : (163395902 : ℝ) / 100000000 <
      ∑ k ∈ Finset.range 16,
        (1 / ((k : ℝ) + (5 / 14)) ^ 2 - 1 / ((k : ℝ) + (2 / 5)) ^ 2) := by
    norm_num [Finset.sum_range_succ]
  have b5 : (163395902 : ℝ) / 100000000 < zudilinJTerm (5 / 14) (2 / 5) :=
    c5.trans_le h5
  have h6 := sum_le_trigammaSeries_sub
    (u := (3 / 7)) (v := (7 / 15)) (by norm_num) (by norm_num) 16
  have c6 : (88704481 : ℝ) / 100000000 <
      ∑ k ∈ Finset.range 16,
        (1 / ((k : ℝ) + (3 / 7)) ^ 2 - 1 / ((k : ℝ) + (7 / 15)) ^ 2) := by
    norm_num [Finset.sum_range_succ]
  have b6 : (88704481 : ℝ) / 100000000 < zudilinJTerm (3 / 7) (7 / 15) :=
    c6.trans_le h6
  have h7 := sum_le_trigammaSeries_sub
    (u := (1 / 2)) (v := (8 / 15)) (by norm_num) (by norm_num) 16
  have c7 : (51110980 : ℝ) / 100000000 <
      ∑ k ∈ Finset.range 16,
        (1 / ((k : ℝ) + (1 / 2)) ^ 2 - 1 / ((k : ℝ) + (8 / 15)) ^ 2) := by
    norm_num [Finset.sum_range_succ]
  have b7 : (51110980 : ℝ) / 100000000 < zudilinJTerm (1 / 2) (8 / 15) :=
    c7.trans_le h7
  have h8 := sum_le_trigammaSeries_sub
    (u := (4 / 7)) (v := (3 / 5)) (by norm_num) (by norm_num) 16
  have c8 : (30517746 : ℝ) / 100000000 <
      ∑ k ∈ Finset.range 16,
        (1 / ((k : ℝ) + (4 / 7)) ^ 2 - 1 / ((k : ℝ) + (3 / 5)) ^ 2) := by
    norm_num [Finset.sum_range_succ]
  have b8 : (30517746 : ℝ) / 100000000 < zudilinJTerm (4 / 7) (3 / 5) :=
    c8.trans_le h8
  have h9 := sum_le_trigammaSeries_sub
    (u := (9 / 14)) (v := (2 / 3)) (by norm_num) (by norm_num) 16
  have c9 : (18505297 : ℝ) / 100000000 <
      ∑ k ∈ Finset.range 16,
        (1 / ((k : ℝ) + (9 / 14)) ^ 2 - 1 / ((k : ℝ) + (2 / 3)) ^ 2) := by
    norm_num [Finset.sum_range_succ]
  have b9 : (18505297 : ℝ) / 100000000 < zudilinJTerm (9 / 14) (2 / 3) :=
    c9.trans_le h9
  have h10 := sum_le_trigammaSeries_sub
    (u := (5 / 7)) (v := (11 / 15)) (by norm_num) (by norm_num) 16
  have c10 : (11153720 : ℝ) / 100000000 <
      ∑ k ∈ Finset.range 16,
        (1 / ((k : ℝ) + (5 / 7)) ^ 2 - 1 / ((k : ℝ) + (11 / 15)) ^ 2) := by
    norm_num [Finset.sum_range_succ]
  have b10 : (11153720 : ℝ) / 100000000 < zudilinJTerm (5 / 7) (11 / 15) :=
    c10.trans_le h10
  have h11 := sum_le_trigammaSeries_sub
    (u := (11 / 14)) (v := (4 / 5)) (by norm_num) (by norm_num) 16
  have c11 : (6483917 : ℝ) / 100000000 <
      ∑ k ∈ Finset.range 16,
        (1 / ((k : ℝ) + (11 / 14)) ^ 2 - 1 / ((k : ℝ) + (4 / 5)) ^ 2) := by
    norm_num [Finset.sum_range_succ]
  have b11 : (6483917 : ℝ) / 100000000 < zudilinJTerm (11 / 14) (4 / 5) :=
    c11.trans_le h11
  have h12 := sum_le_trigammaSeries_sub
    (u := (6 / 7)) (v := (13 / 15)) (by norm_num) (by norm_num) 16
  have c12 : (3430313 : ℝ) / 100000000 <
      ∑ k ∈ Finset.range 16,
        (1 / ((k : ℝ) + (6 / 7)) ^ 2 - 1 / ((k : ℝ) + (13 / 15)) ^ 2) := by
    norm_num [Finset.sum_range_succ]
  have b12 : (3430313 : ℝ) / 100000000 < zudilinJTerm (6 / 7) (13 / 15) :=
    c12.trans_le h12
  have h13 := sum_le_trigammaSeries_sub
    (u := (13 / 14)) (v := (14 / 15)) (by norm_num) (by norm_num) 16
  have c13 : (1388390 : ℝ) / 100000000 <
      ∑ k ∈ Finset.range 16,
        (1 / ((k : ℝ) + (13 / 14)) ^ 2 - 1 / ((k : ℝ) + (14 / 15)) ^ 2) := by
    norm_num [Finset.sum_range_succ]
  have b13 : (1388390 : ℝ) / 100000000 < zudilinJTerm (13 / 14) (14 / 15) :=
    c13.trans_le h13
  unfold zudilinJ
  linarith only [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13]

/-- A deliberately rounded lower contour, adequate for the strict 301 bound. -/
theorem zudilinContour_gt_40568 : (40568 : ℝ) / 100000 < zudilinContour := by
  have hJ := zudilinJ_sixteen_lower
  have hpi : (314159 : ℝ) / 100000 < Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have hpi2 : ((314159 : ℝ) / 100000) ^ 2 < Real.pi ^ 2 := by
    nlinarith [Real.pi_pos]
  have hc : 3 / Real.pi ^ 2 < 3 / ((314159 : ℝ) / 100000) ^ 2 :=
    div_lt_div_of_pos_left (by norm_num) (by norm_num) hpi2
  have hp : 3 / Real.pi ^ 2 * (225 - zudilinJ) <
      3 / ((314159 : ℝ) / 100000) ^ 2 * (225 - 779418 / 10000) := by
    calc
      _ ≤ 3 / Real.pi ^ 2 * (225 - 779418 / 10000) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ < _ := mul_lt_mul_of_pos_right hc (by norm_num)
  unfold zudilinContour
  apply (lt_div_iff₀ zudilinC1_pos).mpr
  unfold zudilinC0 zudilinC1
  norm_num at hp ⊢
  linarith

/-- Exact integer certificate; no floating-point logarithm is used. -/
theorem thirtyoneFour_power_certificate_2217 :
    (4 : ℕ) ^ 2217 < 31 ^ 895 := by decide

theorem thirtyoneFour_ratio_lt_895_2217 :
    Real.log 4 / Real.log 31 < (895 : ℝ) / 2217 := by
  have hpows : (4 : ℝ) ^ 2217 < (31 : ℝ) ^ 895 := by
    exact_mod_cast thirtyoneFour_power_certificate_2217
  have hlogs := Real.strictMonoOn_log
    (Set.mem_Ioi.mpr (by positivity : (0 : ℝ) < 4 ^ 2217))
    (Set.mem_Ioi.mpr (by positivity : (0 : ℝ) < 31 ^ 895)) hpows
  rw [Real.log_pow, Real.log_pow] at hlogs
  norm_num at hlogs
  apply (div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 31))).mpr
  nlinarith

/-- A smaller exact certificate implies the literal seven-place bound in the paper. -/
theorem thirtyoneFour_power_certificate_8058 :
    (4 : ℕ) ^ 8058 < 31 ^ 3253 := by decide

theorem thirtyoneFour_ratio_lt_2018491_5000000 :
    Real.log 4 / Real.log 31 < (2018491 : ℝ) / 5000000 := by
  have hpows : (4 : ℝ) ^ 8058 < (31 : ℝ) ^ 3253 := by
    exact_mod_cast thirtyoneFour_power_certificate_8058
  have hlogs := Real.strictMonoOn_log
    (Set.mem_Ioi.mpr (by positivity : (0 : ℝ) < 4 ^ 8058))
    (Set.mem_Ioi.mpr (by positivity : (0 : ℝ) < 31 ^ 3253)) hpows
  rw [Real.log_pow, Real.log_pow] at hlogs
  norm_num at hlogs
  have hratio : Real.log 4 / Real.log 31 < (3253 : ℝ) / 8058 := by
    apply (div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 31))).mpr
    nlinarith
  exact hratio.trans (by norm_num)

/-- The paper's exact rounded quotient, rather than just its 301 corollary. -/
theorem quotient_lt_paper_fraction {t z : ℝ}
    (ht : t < (2018491 : ℝ) / 5000000)
    (hz : (40568 : ℝ) / 100000 < z) :
    (1 - t) / (z - t) < (2981509 : ℝ) / 9909 := by
  have hden : 0 < z - t := by linarith
  apply (div_lt_iff₀ hden).mpr
  linarith

/-- The quotient appearing in the paper; this definition makes no assertion
about the irrationality exponent of a Lambert value. -/
noncomputable def rationalBaseMeasureBound (a b : ℕ) : ℝ :=
  (1 - Real.log b / Real.log a) /
    (zudilinContour - Real.log b / Real.log a)

/-- Algebraic comparison keeps strict inequalities at the rounded boundaries. -/
theorem quotient_lt_301 {t z : ℝ}
    (ht : t < (895 : ℝ) / 2217)
    (hz : (40568 : ℝ) / 100000 < z) :
    (1 - t) / (z - t) < 301 := by
  have hden : 0 < z - t := by linarith
  apply (div_lt_iff₀ hden).mpr
  linarith

theorem thirtyoneFour_measureBound_lt_301 : rationalBaseMeasureBound 31 4 < 301 :=
  quotient_lt_301 thirtyoneFour_ratio_lt_895_2217 zudilinContour_gt_40568

theorem thirtyoneFour_measureBound_lt_paper_fraction :
    rationalBaseMeasureBound 31 4 < (2981509 : ℝ) / 9909 :=
  quotient_lt_paper_fraction thirtyoneFour_ratio_lt_2018491_5000000
    zudilinContour_gt_40568

theorem paper_fraction_lt_301 : (2981509 : ℝ) / 9909 < 301 := by norm_num

/-- Common positive powers do not alter the logarithmic parameter. -/
theorem rationalBaseMeasureBound_pow (a b r : ℕ) (hr : 0 < r) :
    rationalBaseMeasureBound (a ^ r) (b ^ r) = rationalBaseMeasureBound a b := by
  unfold rationalBaseMeasureBound
  rw [Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow]
  rw [mul_div_mul_left _ _ (by exact_mod_cast hr.ne')]

theorem thirtyoneFour_power_measureBound_lt_301 (r : ℕ) (hr : 0 < r) :
    rationalBaseMeasureBound (31 ^ r) (4 ^ r) < 301 := by
  rw [rationalBaseMeasureBound_pow 31 4 r hr]
  exact thirtyoneFour_measureBound_lt_301

/-- The exact analytic-rate quotient reduces to the displayed contour formula. -/
theorem rate_quotient_eq_contour (a b : ℕ)
    (ha : 0 < Real.log (a : ℝ))
    (hτ : 0 < zudilinC0 * Real.log a - zudilinC1 * Real.log b) :
    1 + ((zudilinC1 - zudilinC0) * Real.log a) /
        (zudilinC0 * Real.log a - zudilinC1 * Real.log b) =
      rationalBaseMeasureBound a b := by
  unfold rationalBaseMeasureBound zudilinContour
  have hC1 := zudilinC1_pos.ne'
  have hden : zudilinC0 / zudilinC1 - Real.log b / Real.log a ≠ 0 := by
    intro h
    have hh : zudilinC0 * Real.log a - zudilinC1 * Real.log b = 0 := by
      field_simp [hC1, ha.ne'] at h
      nlinarith
    exact hτ.ne' hh
  field_simp [hC1, ha.ne', hτ.ne', hden]
  <;> ring

/-- Common powers multiply both rates by the same positive integer. -/
theorem rate_ratio_scale (α τ : ℝ) (r : ℕ) (hr : 0 < r) :
    1 + ((r : ℝ) * α) / ((r : ℝ) * τ) = 1 + α / τ := by
  rw [mul_div_mul_left _ _ (by exact_mod_cast hr.ne')]

end ErdosProblems.Erdos1049.PaperR10
