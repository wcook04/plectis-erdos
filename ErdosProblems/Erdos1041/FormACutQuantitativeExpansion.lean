import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic

/-!
# Erdős #1041: quantitative near-Fekete expansion kernels

This module formalizes four load-bearing pieces of the explicit remainder
estimate used by `FormACutQuantitativeExpansion.md`:

* the exact algebraic factorization of one perturbed root factor;
* the sharp real-part consequence of Mathlib's complex logarithm tail bound;
* the convenient `‖w‖ ≤ 1/2` finite aggregation bound;
* absorption of an absolute error by a strict negative model margin.

The root-of-unity Fourier reindexing is kept in the accompanying ordinary proof;
the statements below are the analytic and order kernels it consumes.
-/

open scoped BigOperators

namespace ErdosProblems.Erdos1041.FormACutQuantitativeExpansion

/-- One factor in the perturbed-root product. Here `a*b=1`; in the application
`a=omega^k` and `b=omega^(-k)`. -/
theorem perturbedFactor_identity {a b e z : ℂ}
    (hab : a * b = 1) (hden : 1 - z * b ≠ 0) :
    z - a * (1 + e) = (z - a) * (1 + e / (1 - z * b)) := by
  have hza : z - a = -a * (1 - z * b) := by
    calc
      z - a = z * (a * b) - a := by rw [hab]; ring
      _ = -a * (1 - z * b) := by ring
  calc
    z - a * (1 + e) = (z - a) - a * e := by ring
    _ = (-a * (1 - z * b)) - a * e := by rw [hza]
    _ = (-a * (1 - z * b)) * (1 + e / (1 - z * b)) := by
      field_simp [hden]
      <;> ring
    _ = (z - a) * (1 + e / (1 - z * b)) := by rw [← hza]

/-- The sharp scalar logarithmic error used for every perturbed root factor. -/
theorem log_norm_one_add_linear_error {w : ℂ} (hw : ‖w‖ < 1) :
    |Real.log ‖1 + w‖ - w.re| ≤ ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ / 2 := by
  calc
    |Real.log ‖1 + w‖ - w.re| = |(Complex.log (1 + w) - w).re| := by
      simp [Complex.log_re]
    _ ≤ ‖Complex.log (1 + w) - w‖ := Complex.abs_re_le_norm _
    _ ≤ ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ / 2 :=
      Complex.norm_log_one_add_sub_self_le hw

/-- On the half-radius collar the sharp logarithmic error is at most `‖w‖²`. -/
theorem log_norm_one_add_linear_error_le_sq {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    |Real.log ‖1 + w‖ - w.re| ≤ ‖w‖ ^ 2 := by
  have hlt : ‖w‖ < 1 := lt_of_le_of_lt hw (by norm_num)
  have hpos : 0 < 1 - ‖w‖ := sub_pos.mpr hlt
  have hinv : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hpos (by norm_num)]
    linarith
  calc
    |Real.log ‖1 + w‖ - w.re|
        ≤ ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ / 2 := log_norm_one_add_linear_error hlt
    _ ≤ ‖w‖ ^ 2 * 2 / 2 := by gcongr
    _ = ‖w‖ ^ 2 := by ring

/-- Finite aggregation of pointwise logarithmic errors. -/
theorem sum_abs_error_le_card_mul_sq {ι : Type*} (s : Finset ι)
    (err : ι → ℝ) {a : ℝ}
    (herr : ∀ i ∈ s, |err i| ≤ a ^ 2) :
    |∑ i ∈ s, err i| ≤ (s.card : ℝ) * a ^ 2 := by
  calc
    |∑ i ∈ s, err i| ≤ ∑ i ∈ s, |err i| := Finset.abs_sum_le_sum_abs err s
    _ ≤ ∑ _i ∈ s, a ^ 2 := Finset.sum_le_sum fun i hi ↦ herr i hi
    _ = (s.card : ℝ) * a ^ 2 := by simp

/-- Combining the one-factor estimates when every factor has norm at most
`a ≤ 1/2`. -/
theorem sum_log_norm_error_le_card_mul_sq {ι : Type*} (s : Finset ι)
    (w : ι → ℂ) {a : ℝ} (ha : 0 ≤ a) (ha_half : a ≤ 1 / 2)
    (hw : ∀ i ∈ s, ‖w i‖ ≤ a) :
    |∑ i ∈ s, (Real.log ‖1 + w i‖ - (w i).re)| ≤
      (s.card : ℝ) * a ^ 2 := by
  apply sum_abs_error_le_card_mul_sq s
      (fun i ↦ Real.log ‖1 + w i‖ - (w i).re)
  intro i hi
  have hwi : ‖w i‖ ≤ 1 / 2 := (hw i hi).trans ha_half
  exact (log_norm_one_add_linear_error_le_sq hwi).trans
    ((sq_le_sq₀ (norm_nonneg (w i)) ha).2 (hw i hi))

/-- The baseline `log|1-z| = -Re z + error` with its sharp error. -/
theorem baseline_log_error {z : ℂ} (hz : ‖z‖ < 1) :
    |Real.log ‖1 - z‖ + z.re| ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := by
  simpa [norm_neg, sub_eq_add_neg] using
    (log_norm_one_add_linear_error (w := -z) (by simpa using hz))

/-- An absolute remainder bound plus a strict model margin gives strict
negativity of the actual logarithm. -/
theorem strict_negative_of_abs_sub_le {actual model budget : ℝ}
    (herror : |actual - model| ≤ budget) (hmargin : model + budget < 0) :
    actual < 0 := by
  have hup : actual - model ≤ budget := (le_abs_self (actual - model)).trans herror
  linarith

/-! ## The origin-anchored improvement -/

/-- The nonlinear part of `Log(1+w)` after subtracting its linear term. -/
noncomputable def logRemainder (w : ℂ) : ℂ := Complex.log (1 + w) - w

/-- The derivative of the nonlinear logarithmic remainder on the unit ball. -/
theorem hasDerivAt_logRemainder {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt logRemainder (-w * (1 + w)⁻¹) w := by
  have h := Complex.hasDerivAt_log_sub_logTaylor 1
    (Complex.mem_slitPlane_of_norm_lt_one hw)
  simpa [logRemainder, Complex.logTaylor_succ, Complex.logTaylor_zero] using h

/-- On the closed ball of radius `a<1`, the nonlinear logarithmic remainder is
`a/(1-a)`-Lipschitz. This is what improves an unanchored `O(eta^2)` error to the
origin-anchored `O(eta^2*|z|)` error. -/
theorem norm_logRemainder_sub_le {v w : ℂ} {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hv : ‖v‖ ≤ a) (hw : ‖w‖ ≤ a) :
    ‖logRemainder w - logRemainder v‖ ≤
      (a * (1 - a)⁻¹) * ‖w - v‖ := by
  let s : Set ℂ := Metric.closedBall 0 a
  have hvs : v ∈ s := by
    simpa [s, Metric.mem_closedBall, dist_zero_right] using hv
  have hws : w ∈ s := by
    simpa [s, Metric.mem_closedBall, dist_zero_right] using hw
  refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := s) (f := logRemainder) (f' := fun x : ℂ ↦ -x * (1 + x)⁻¹)
    ?_ ?_ (convex_closedBall 0 a) hvs hws
  · intro x hx
    have hxa : ‖x‖ ≤ a := by
      simpa [s, Metric.mem_closedBall, dist_zero_right] using hx
    exact (hasDerivAt_logRemainder (hxa.trans_lt ha1)).hasDerivWithinAt
  · intro x hx
    have hxa : ‖x‖ ≤ a := by
      simpa [s, Metric.mem_closedBall, dist_zero_right] using hx
    have hx1 : ‖x‖ < 1 := hxa.trans_lt ha1
    have hinvx : ‖(1 + x)⁻¹‖ ≤ (1 - ‖x‖)⁻¹ :=
      by simpa using
        (Complex.norm_one_add_mul_inv_le (t := 1) ⟨zero_le_one, le_rfl⟩ hx1)
    have hinva : (1 - ‖x‖)⁻¹ ≤ (1 - a)⁻¹ := by
      exact inv_anti₀ (sub_pos.mpr ha1) (by linarith)
    rw [norm_mul, norm_neg]
    calc
      ‖x‖ * ‖(1 + x)⁻¹‖ ≤ a * ‖(1 + x)⁻¹‖ :=
        mul_le_mul_of_nonneg_right hxa (norm_nonneg _)
      _ ≤ a * (1 - ‖x‖)⁻¹ := mul_le_mul_of_nonneg_left hinvx ha0
      _ ≤ a * (1 - a)⁻¹ := mul_le_mul_of_nonneg_left hinva ha0

/-- Real-part form of the anchored nonlinear logarithm estimate. -/
theorem anchored_log_error_sub_le {v w : ℂ} {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hv : ‖v‖ ≤ a) (hw : ‖w‖ ≤ a) :
    |(Real.log ‖1 + w‖ - w.re) - (Real.log ‖1 + v‖ - v.re)| ≤
      (a * (1 - a)⁻¹) * ‖w - v‖ := by
  calc
    |(Real.log ‖1 + w‖ - w.re) - (Real.log ‖1 + v‖ - v.re)|
        = |(logRemainder w - logRemainder v).re| := by
          simp [logRemainder, Complex.log_re]
    _ ≤ ‖logRemainder w - logRemainder v‖ := Complex.abs_re_le_norm _
    _ ≤ (a * (1 - a)⁻¹) * ‖w - v‖ :=
      norm_logRemainder_sub_le ha0 ha1 hv hw

/-- Finite geometric resummation, the algebra behind replacing the infinite
Fourier tail by one degree-`n` numerator over `1-z^n`. -/
theorem finite_geometric_quotient {u : ℂ} (n : ℕ) (hden : 1 - u ≠ 0) :
    (1 - u ^ n) / (1 - u) = ∑ j ∈ Finset.range n, u ^ j := by
  apply (div_eq_iff hden).2
  exact (geom_sum_mul_neg u n).symm

/-- A perturbation that keeps `1+e` in the closed unit disk has radial deficit
at least half its squared size. -/
theorem norm_sq_le_neg_two_re_of_norm_one_add_le_one {e : ℂ}
    (he : ‖1 + e‖ ≤ 1) : ‖e‖ ^ 2 ≤ -2 * e.re := by
  have hs : ‖1 + e‖ ^ 2 ≤ (1 : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg (1 + e)) zero_le_one).2 he
  rw [Complex.sq_norm] at hs ⊢
  simp [Complex.normSq_apply] at hs ⊢
  nlinarith

/-- Summed radial deficit controls the full quadratic perturbation energy. -/
theorem sum_norm_sq_div_two_le_radialDeficit {ι : Type*} (s : Finset ι)
    (e : ι → ℂ) (he : ∀ i ∈ s, ‖1 + e i‖ ≤ 1) :
    (∑ i ∈ s, ‖e i‖ ^ 2) / 2 ≤ -(∑ i ∈ s, (e i).re) := by
  have hsum : (∑ i ∈ s, ‖e i‖ ^ 2) ≤ ∑ i ∈ s, (-2 * (e i).re) :=
    Finset.sum_le_sum fun i hi ↦ norm_sq_le_neg_two_re_of_norm_one_add_le_one (he i hi)
  rw [← Finset.mul_sum] at hsum
  linarith

end ErdosProblems.Erdos1041.FormACutQuantitativeExpansion
