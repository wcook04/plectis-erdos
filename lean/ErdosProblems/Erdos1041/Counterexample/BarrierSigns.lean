import ErdosProblems.Erdos1041.Counterexample.BarrierGraphs
/-! External source: ani, erdosproblems.com forum thread 1041, 7 Sept 2026.
Explicit separating barriers replacing the Riemann-Hurwitz step of Lemma 2.1, at `s = 10⁻⁶`. -/

noncomputable section
namespace Erdos1041.Counterexample.S7Proof

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def centre : ℂ := ((823247 / 1000000 : ℝ) : ℂ) * Complex.I

theorem near_coordinates (w : ℂ) (hw : ‖w - centre‖ < 1 / 1000) :
    3 < xi w ∧ xi w < 4 ∧ 3 < eta w ∧ eta w < 5 := by
  have hx := (Complex.abs_re_le_norm (w - centre)).trans_lt hw
  have hy := (Complex.abs_im_le_norm (w - centre)).trans_lt hw
  norm_num [centre, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im] at hx hy
  obtain ⟨hx0, hx1⟩ := abs_lt.mp hx
  obtain ⟨hy0, hy1⟩ := abs_lt.mp hy
  unfold xi eta
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem G1_negative_near (w : ℂ) (hw : ‖w - centre‖ < 1 / 1000) : G1 w < 0 := by
  obtain ⟨hx0, hx1, he0, he1⟩ := near_coordinates w hw
  have hp : l1_23 (xi w) ≤ phi1 (xi w) := by
    unfold phi1
    exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hl : 9 < l1_23 (xi w) := by unfold l1_23; linarith
  unfold G1
  linarith

theorem G2_negative_near (w : ℂ) (hw : ‖w - centre‖ < 1 / 1000) : G2 w < 0 := by
  obtain ⟨hx0, hx1, he0, he1⟩ := near_coordinates w hw
  have hp : l2_12 (xi w) ≤ phi2 (xi w) := by
    unfold phi2
    exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hl : 16 < l2_12 (xi w) := by unfold l2_12; linarith
  unfold G2
  linarith

/-- Only coarse Taylor brackets are required; no algebraic minimal polynomial
or floating-point approximation to a trigonometric value is used. -/
theorem trig_small (x : ℝ) (hlo : 3 / 14 ≤ x) (hhi : x ≤ 1 / 4) :
    1 / 5 ≤ Real.sin x ∧ Real.sin x ≤ 1 / 4 ∧
      31 / 32 ≤ Real.cos x ∧ Real.cos x ≤ 1 := by
  have hx : 0 < x := by linarith
  have hx1 : x ≤ 1 := by linarith
  have hs := Real.sin_gt_sub_cube hx hx1
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have h2 := pow_le_pow_left₀ hx.le hhi 2
  have h3 := pow_le_pow_left₀ hx.le hhi 3
  norm_num at h2 h3
  exact ⟨by linarith, (Real.sin_le hx.le).trans hhi,
    by linarith, Real.cos_le_one x⟩

theorem trig_medium (x : ℝ) (hlo : 3 / 7 ≤ x) (hhi : x ≤ 1 / 2) :
    1 / 3 ≤ Real.sin x ∧ Real.sin x ≤ 1 / 2 ∧
      7 / 8 ≤ Real.cos x ∧ Real.cos x ≤ 1 := by
  have hx : 0 < x := by linarith
  have hx1 : x ≤ 1 := by linarith
  have hs := Real.sin_gt_sub_cube hx hx1
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have h2 := pow_le_pow_left₀ hx.le hhi 2
  have h3 := pow_le_pow_left₀ hx.le hhi 3
  norm_num at h2 h3
  exact ⟨by linarith, (Real.sin_le hx.le).trans hhi,
    by linarith, Real.cos_le_one x⟩

theorem trig_large (x : ℝ) (hlo : 6 / 7 ≤ x) (hhi : x ≤ 1) :
    1 / 2 ≤ Real.sin x ∧ 1 / 2 ≤ Real.cos x := by
  have hx : 0 < x := by linarith
  have hs := Real.sin_gt_sub_cube hx hhi
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have h2 : x ^ 2 ≤ 1 := by nlinarith
  have h3 : x ^ 3 ≤ 1 := by nlinarith
  exact ⟨by linarith, by linarith⟩

theorem pi_coarse : (3 : ℝ) < Real.pi ∧ Real.pi < 7 / 2 := by
  exact ⟨Real.pi_gt_three, by linarith [Real.pi_lt_d2]⟩

theorem u_form (j : ℕ) :
    u j = Complex.exp ((((2 * Real.pi * (j : ℝ) / 7 : ℝ) : ℂ)) * Complex.I) := by
  unfold u
  congr 1
  push_cast
  <;> ring

theorem u_re (j : ℕ) : (u j).re = Real.cos (2 * Real.pi * (j : ℝ) / 7) := by
  rw [u_form]
  exact Complex.exp_ofReal_mul_I_re _

theorem u_im (j : ℕ) : (u j).im = Real.sin (2 * Real.pi * (j : ℝ) / 7) := by
  rw [u_form]
  exact Complex.exp_ofReal_mul_I_im _

theorem norm_u (j : ℕ) : ‖u j‖ = 1 := by
  rw [u_form]
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

theorem u2_re : (u 2).re = -Real.sin (Real.pi / 14) := by
  rw [u_re]
  have h : 2 * Real.pi * (2 : ℝ) / 7 = Real.pi / 2 + Real.pi / 14 := by ring
  norm_num only
  rw [h]
  simp [Real.cos_add]

theorem u2_im : (u 2).im = Real.cos (Real.pi / 14) := by
  rw [u_im]
  have h : 2 * Real.pi * (2 : ℝ) / 7 = Real.pi / 2 + Real.pi / 14 := by ring
  norm_num only
  rw [h]
  simp [Real.sin_add]

theorem u4_re : (u 4).re = -Real.cos (Real.pi / 7) := by
  rw [u_re]
  have h : 2 * Real.pi * (4 : ℝ) / 7 = Real.pi + Real.pi / 7 := by ring
  norm_num only
  rw [h]
  simp [Real.cos_add]

theorem u4_im : (u 4).im = -Real.sin (Real.pi / 7) := by
  rw [u_im]
  have h : 2 * Real.pi * (4 : ℝ) / 7 = Real.pi + Real.pi / 7 := by ring
  norm_num only
  rw [h]
  simp [Real.sin_add]

theorem u5_re : (u 5).re = -Real.sin (Real.pi / 14) := by
  rw [u_re]
  have h : 2 * Real.pi * (5 : ℝ) / 7 = Real.pi + (Real.pi / 2 - Real.pi / 14) := by ring
  norm_num only
  rw [h]
  simp [Real.cos_add, Real.cos_sub]

theorem u5_im : (u 5).im = -Real.cos (Real.pi / 14) := by
  rw [u_im]
  have h : 2 * Real.pi * (5 : ℝ) / 7 = Real.pi + (Real.pi / 2 - Real.pi / 14) := by ring
  norm_num only
  rw [h]
  simp [Real.sin_add, Real.sin_sub]

theorem centre1_margin (j : ℕ) (hj : j = 0 ∨ j = 1 ∨ j = 2) :
    3 / 2 ≤ eta (u j) - (1 / 4 : ℝ) * |xi (u j)| := by
  rcases hj with rfl | rfl | rfl
  · norm_num [eta, xi, u]
  · obtain ⟨hp0, hp1⟩ := pi_coarse
    obtain ⟨hs, hc⟩ := trig_large (2 * Real.pi / 7) (by linarith) (by linarith)
    have he : 9 / 2 ≤ eta (u 1) := by
      unfold eta
      rw [u_re, u_im]
      norm_num only [mul_one]
      linarith
    have hx := abs_xi_le (u 1)
    rw [norm_u] at hx
    linarith
  · obtain ⟨hp0, hp1⟩ := pi_coarse
    obtain ⟨hs0, hs1, hc0, hc1⟩ := trig_small (Real.pi / 14) (by linarith) (by linarith)
    have he : 123 / 32 ≤ eta (u 2) := by
      unfold eta
      rw [u2_re, u2_im]
      linarith
    have hx := abs_xi_le (u 2)
    rw [norm_u] at hx
    linarith

theorem centre2_margin (j : ℕ) (hj : j = 4 ∨ j = 5) :
    2 ≤ -eta (u j) - |xi (u j)| := by
  rcases hj with rfl | rfl
  · obtain ⟨hp0, hp1⟩ := pi_coarse
    obtain ⟨hs0, hs1, hc0, hc1⟩ := trig_medium (Real.pi / 7) (by linarith) (by linarith)
    have hx : 0 ≤ xi (u 4) := by
      unfold xi
      rw [u4_re, u4_im]
      linarith
    rw [abs_of_nonneg hx]
    unfold eta xi
    rw [u4_re, u4_im]
    linarith
  · obtain ⟨hp0, hp1⟩ := pi_coarse
    obtain ⟨hs0, hs1, hc0, hc1⟩ := trig_small (Real.pi / 14) (by linarith) (by linarith)
    have hx : xi (u 5) ≤ 0 := by
      unfold xi
      rw [u5_re, u5_im]
      linarith
    rw [abs_of_nonpos hx]
    unfold eta xi
    rw [u5_re, u5_im]
    linarith

theorem disk_coordinate_errors (R : ℝ) (hR : 0 < R) (v w : ℂ)
    (hd : ‖w - (R : ℂ) * v‖ < R / 10) :
    |xi w - R * xi v| < 9 * R / 10 ∧
      |eta w - R * eta v| < 9 * R / 10 ∧
      |xi w| < R * |xi v| + 9 * R / 10 := by
  have hx0 := abs_xi_le (w - (R : ℂ) * v)
  have he0 := abs_eta_le (w - (R : ℂ) * v)
  rw [xi_sub, xi_real_mul] at hx0
  rw [eta_sub, eta_real_mul] at he0
  have hx : |xi w - R * xi v| < 9 * R / 10 := by linarith
  have he : |eta w - R * eta v| < 9 * R / 10 := by linarith
  have hh : |xi w| ≤ |xi w - R * xi v| + |R * xi v| := by
    calc
      |xi w| = |(xi w - R * xi v) + R * xi v| := by congr 1; ring
      _ ≤ |xi w - R * xi v| + |R * xi v| := abs_add_le _ _
  rw [abs_mul, abs_of_pos hR] at hh
  exact ⟨hx, he, by linarith⟩

theorem G1_positive_disk (R : ℝ) (hR : 100 ≤ R) (v w : ℂ)
    (hc : 3 / 2 ≤ eta v - (1 / 4 : ℝ) * |xi v|)
    (hd : ‖w - (R : ℂ) * v‖ < R / 10) : 0 < G1 w := by
  have hR0 : 0 < R := by linarith
  obtain ⟨hx, he, ha⟩ := disk_coordinate_errors R hR0 v w hd
  obtain ⟨he0, he1⟩ := abs_lt.mp he
  have hp := phi1_upper (xi w)
  have hcR := mul_le_mul_of_nonneg_left hc hR0.le
  unfold G1
  nlinarith

theorem G2_positive_disk (R : ℝ) (hR : 100 ≤ R) (v w : ℂ)
    (hc : 2 ≤ -eta v - |xi v|)
    (hd : ‖w - (R : ℂ) * v‖ < R / 10) : 0 < G2 w := by
  have hR0 : 0 < R := by linarith
  obtain ⟨hx, he, ha⟩ := disk_coordinate_errors R hR0 v w hd
  obtain ⟨he0, he1⟩ := abs_lt.mp he
  have hp := phi2_upper (xi w)
  have hcR := mul_le_mul_of_nonneg_left hc hR0.le
  unfold G2
  nlinarith

end Erdos1041.Counterexample.S7Proof
