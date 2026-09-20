import ErdosProblems.Erdos1049.PaperR17.SourceConsumers

/-!
# Erdős #1049: the rational-base threshold in its paper form

Paper restatements of

* `res:rational-base-threshold` / `long1049:res:region` (the rational-base
  region, stated with the paper's hypothesis `b^μ < a` and with the paper's
  "equivalently" `b^μ < a ↔ log b / log a < θ*` proved, not assumed);
* `long1049:res:31over4` (the base `31/4`, its powers, and the two displayed
  chains `1/2 - 1/π² < log 4 / log 31 < 81/200 < θ*` and `4^μ < 31 < 4^{μ_BV}`
  with `μ_BV = 2π²/(π²-2)`);
* `cor:rational-base-measure` / `long1049:cor:rational-base-measure`
  (the irrationality measure uniform over powers).

Nothing here assumes an external theorem: the supplier comes from
`PaperR17.SourceConsumers`, which is itself proved in the tree.

The truncated decimal displays printed in those environments
(`θ* = 0.40568302138406054…`, `μ = 2.4649786835749750…`,
`log 4 / log 31 = 0.4036981731641997…`, `4^μ = 30.483515…`,
`4^{μ_BV} = 32.369642…`, `μ_BV = 2.508284761994…`,
`1/2 - 1/π² = 0.3986788163576622…`) are NOT proved here; only the bracketing
inequalities below are.
-/

namespace ErdosProblems.Erdos1049.PaperCompleteR21

open ErdosProblems.Erdos1049
open ErdosProblems.Erdos1049.PaperR7
open ErdosProblems.Erdos1049.PaperR10
open ErdosProblems.Erdos1049.PaperR11

/-! ## A real-power comparison used twice -/

/-- For `x, y > 0` with `log y > 0` and `c > 0`: `x^c < y ↔ log x / log y < 1/c`. -/
theorem rpow_lt_iff_log_ratio {x y c : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hlogy : 0 < Real.log y) (hc : 0 < c) :
    x ^ c < y ↔ Real.log x / Real.log y < 1 / c := by
  rw [div_lt_iff₀ hlogy, one_div, inv_mul_eq_div, lt_div_iff₀ hc]
  constructor
  · intro h
    have h0 : Real.exp (Real.log x * c) < Real.exp (Real.log y) := by
      rw [Real.exp_log hy]
      rwa [Real.rpow_def_of_pos hx] at h
    exact Real.exp_lt_exp.mp h0
  · intro h
    have h0 : Real.exp (Real.log x * c) < Real.exp (Real.log y) := Real.exp_lt_exp.mpr h
    rw [Real.exp_log hy] at h0
    rwa [Real.rpow_def_of_pos hx]

/-- The companion strict inequality in the other direction. -/
theorem lt_rpow_iff_log_ratio {x y c : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hlogy : 0 < Real.log y) (hc : 0 < c) :
    y < x ^ c ↔ 1 / c < Real.log x / Real.log y := by
  rw [lt_div_iff₀ hlogy, one_div, inv_mul_eq_div, div_lt_iff₀ hc]
  constructor
  · intro h
    have h0 : Real.exp (Real.log y) < Real.exp (Real.log x * c) := by
      rw [Real.exp_log hy]
      rwa [Real.rpow_def_of_pos hx] at h
    exact Real.exp_lt_exp.mp h0
  · intro h
    have h0 : Real.exp (Real.log y) < Real.exp (Real.log x * c) := Real.exp_lt_exp.mpr h
    rw [Real.exp_log hy] at h0
    rwa [Real.rpow_def_of_pos hx]

/-! ## The constants `θ*` and `μ` -/

/-- `μ = C₁/C₀`, the reciprocal of the contour `θ* = C₀/C₁`. -/
noncomputable def zudilinMu : ℝ := zudilinC1 / zudilinC0

theorem zudilinC0_pos : 0 < zudilinC0 := lt_trans (by norm_num) zudilinC0_gt

theorem zudilinContour_pos : 0 < zudilinContour :=
  div_pos zudilinC0_pos zudilinC1_pos

theorem zudilinMu_pos : 0 < zudilinMu := div_pos zudilinC1_pos zudilinC0_pos

/-- `θ*` and `μ` are reciprocal constants, as the paper states. -/
theorem zudilinContour_eq_inv_mu : zudilinContour = 1 / zudilinMu := by
  unfold zudilinMu zudilinContour
  rw [one_div, inv_div]

theorem zudilinMu_mul_zudilinContour : zudilinMu * zudilinContour = 1 := by
  have h0 := zudilinC0_pos.ne'
  have h1 := zudilinC1_pos.ne'
  unfold zudilinMu zudilinContour
  field_simp

/-! ## The rational-base region -/

/-- The paper's "equivalently": for integers `a > b ≥ 1`,
`b^μ < a ↔ log b / log a < θ*`, with `b^μ` the real power. -/
theorem zudilin_rpow_lt_iff_contourRegion (a b : ℕ) (hb : 0 < b) (hab : b < a) :
    ((b : ℝ) ^ zudilinMu < (a : ℝ)) ↔ ZudilinContourRegion a b := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have ha2 : 1 < a := by omega
  have haR : (0 : ℝ) < a := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one ha2.le)
  have hloga : 0 < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast ha2)
  rw [rpow_lt_iff_log_ratio hbR haR hloga zudilinMu_pos, ← zudilinContour_eq_inv_mu]
  exact Iff.rfl

/-- **`res:rational-base-threshold` / `long1049:res:region`.**
For coprime integers `a > b ≥ 1` with `b^μ < a`, equivalently
`log b / log a < θ*`, the value `F(a/b) = ∑_{m≥1} ((a/b)^m - 1)⁻¹` is
irrational.  Coprimality is carried to match the paper; it is not used. -/
theorem rational_base_threshold (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (_hcop : Nat.Coprime a b) (h : (b : ℝ) ^ zudilinMu < (a : ℝ)) :
    Irrational (paperLambert ((a : ℝ) / b)) :=
  PaperR17.rational_base_region a b hb hab
    ((zudilin_rpow_lt_iff_contourRegion a b hb hab).mp h)

/-- The same conclusion from the displayed logarithmic form of the hypothesis. -/
theorem rational_base_threshold_log (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (_hcop : Nat.Coprime a b)
    (h : Real.log (b : ℝ) / Real.log (a : ℝ) < zudilinContour) :
    Irrational (paperLambert ((a : ℝ) / b)) :=
  PaperR17.rational_base_region a b hb hab h

/-! ## The base `31/4` -/

/-- **`long1049:res:31over4`, first clause.** -/
theorem thirtyoneFour_irrational : Irrational (paperLambert ((31 : ℝ) / 4)) :=
  PaperR17.thirtyone_four

/-- **`long1049:res:31over4`, second clause: every positive integer power.** -/
theorem thirtyoneFour_pow_irrational (r : ℕ) (hr : 0 < r) :
    Irrational (paperLambert (((31 : ℝ) / 4) ^ r)) :=
  PaperR17.thirtyone_four_powers r hr

/-- **The displayed chain `1/2 - 1/π² < log 4 / log 31 < 81/200 < θ*`.** -/
theorem thirtyoneFour_ratio_chain :
    1 / 2 - 1 / Real.pi ^ 2 < Real.log 4 / Real.log 31 ∧
      Real.log 4 / Real.log 31 < (81 : ℝ) / 200 ∧
      (81 : ℝ) / 200 < zudilinContour :=
  ⟨bundschuhVaananenMargin_lt_twoFifths.trans twoFifths_lt_thirtyoneFour_log_ratio,
   thirtyoneFour_log_ratio_lt_eightyOne_twoHundredths,
   eightyOne_twoHundredths_lt_zudilinContour⟩

/-- `μ_BV = 2π²/(π² - 2)`, the Bundschuh–Väänänen exponent. -/
noncomputable def bvMu : ℝ := 2 * Real.pi ^ 2 / (Real.pi ^ 2 - 2)

theorem pi_sq_pos : (0 : ℝ) < Real.pi ^ 2 := pow_pos Real.pi_pos 2

theorem pi_sq_sub_two_pos : (0 : ℝ) < Real.pi ^ 2 - 2 := by
  have h : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  nlinarith [Real.pi_pos]

/-- `1/μ_BV = 1/2 - 1/π²`: the Bundschuh–Väänänen exponent and the displayed
Bundschuh–Väänänen region cutoff are reciprocal. -/
theorem inv_bvMu_eq : 1 / bvMu = 1 / 2 - 1 / Real.pi ^ 2 := by
  have h := pi_sq_sub_two_pos.ne'
  have hpi := pi_sq_pos.ne'
  unfold bvMu
  rw [one_div, inv_div]
  field_simp

theorem bvMu_pos : 0 < bvMu := by
  have h := pi_sq_sub_two_pos
  have hpi := pi_sq_pos
  unfold bvMu
  positivity

/-- **The displayed chain `4^μ < 31 < 4^{μ_BV}`.**  The left inequality places
`31/4` inside the region of the rational-base theorem, the right one places it
outside the Bundschuh–Väänänen region. -/
theorem thirtyoneFour_between_rpow :
    (4 : ℝ) ^ zudilinMu < 31 ∧ (31 : ℝ) < (4 : ℝ) ^ bvMu := by
  have hlog31 : 0 < Real.log (31 : ℝ) := Real.log_pos (by norm_num)
  constructor
  · rw [rpow_lt_iff_log_ratio (by norm_num : (0:ℝ) < 4) (by norm_num : (0:ℝ) < 31)
      hlog31 zudilinMu_pos, ← zudilinContour_eq_inv_mu]
    exact thirtyoneFour_ratio_chain.2.1.trans thirtyoneFour_ratio_chain.2.2
  · rw [lt_rpow_iff_log_ratio (by norm_num : (0:ℝ) < 4) (by norm_num : (0:ℝ) < 31)
      hlog31 bvMu_pos, inv_bvMu_eq]
    exact thirtyoneFour_ratio_chain.1

/-- **`31/4` is outside the Bundschuh–Väänänen region and inside the contour
region.** -/
theorem thirtyoneFour_outside_bv_inside_contour :
    ¬ BundschuhVaananenHeightRegion 31 4 ∧ ZudilinContourRegion 31 4 :=
  ⟨thirtyoneFour_outside_bundschuhVaananenHeightRegion,
   thirtyoneFour_mem_zudilinContourRegion⟩

/-! ## The irrationality measure, uniform over powers -/

/-- **`cor:rational-base-measure` / `long1049:cor:rational-base-measure`.**
For coprime `a > b ≥ 1` with `θ = log b / log a < θ*` and every integer
`r ≥ 1`, the irrationality exponent of `F((a/b)^r)` — by definition the
supremum of the exponents `ν` for which `|ξ - p/q| < q^{-ν}` has infinitely
many reduced rational solutions — is at most `(1 - θ)/(θ* - θ)`. -/
theorem rational_base_measure_uniform (a b r : ℕ) (hb : 0 < b) (hab : b < a)
    (_hcop : Nat.Coprime a b) (hr : 0 < r)
    (hθ : Real.log (b : ℝ) / Real.log (a : ℝ) < zudilinContour) :
    irrationalityExponent (paperLambert (((a : ℝ) / b) ^ r)) ≤
      (1 - Real.log (b : ℝ) / Real.log (a : ℝ)) /
        (zudilinContour - Real.log (b : ℝ) / Real.log (a : ℝ)) := by
  have h := PaperR17.rational_base_power_measure a b r hb hab hr hθ
  unfold rationalBaseMeasureBound at h
  exact h

/-- The displayed special case: `μ_irr(F((31/4)^r)) < 301` for every `r ≥ 1`. -/
theorem thirtyoneFour_power_measure_lt_301 (r : ℕ) (hr : 0 < r) :
    irrationalityExponent (paperLambert (((31 : ℝ) / 4) ^ r)) < 301 :=
  PaperR17.thirtyone_four_power_measure_lt_301 r hr

end ErdosProblems.Erdos1049.PaperCompleteR21

#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.rpow_lt_iff_log_ratio
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.lt_rpow_iff_log_ratio
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.zudilinContour_eq_inv_mu
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.zudilinMu_mul_zudilinContour
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.zudilin_rpow_lt_iff_contourRegion
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.rational_base_threshold
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.rational_base_threshold_log
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_irrational
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_pow_irrational
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_ratio_chain
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.inv_bvMu_eq
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_between_rpow
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_outside_bv_inside_contour
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.rational_base_measure_uniform
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_power_measure_lt_301
