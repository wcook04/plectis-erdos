import ErdosProblems.Erdos68.PaperCompleteAsymptotics

/-!
# The sharp 16/9 radius constant

Long-record label res:radius-constant. Hypotheses are eventual, exactly as on
paper. The proof uses the actual optimised factorial segment, proves its
square-subsequence limiting scale, and rules out every subcritical radius.
It does not replace 16/9 by the already compiled finite 3/2 bound.

STATUS: uncompiled end-to-end proof candidate; no new axioms or placeholders.
-/
namespace ErdosProblems.Erdos68.PaperComplete

open Filter
open scoped Topology

lemma twice_square_tendsto_atTop :
    Tendsto (fun t : ℕ => 2 * t ^ 2) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [eventually_ge_atTop (B + 1)] with t ht
  have ht1 : 1 ≤ t := by omega
  nlinarith

lemma square_log_scale {t : ℕ} (ht : 2 ≤ t) :
    (((2 * t ^ 2 : ℕ) : ℝ) * Real.sqrt ((2 * t ^ 2 : ℕ) : ℝ) *
        Real.log ((2 * t ^ 2 : ℕ) : ℝ)) /
      ((t : ℝ) ^ 3 * Real.log (t : ℝ)) =
    2 * Real.sqrt 2 * (Real.log 2 * (Real.log (t : ℝ))⁻¹ + 2) := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hlog : Real.log (t : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < t by omega))).ne'
  push_cast
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq htpos.le,
    Real.log_mul (by norm_num) (pow_ne_zero _ htpos.ne'), Real.log_pow]
  field_simp [htpos.ne', hlog]
  ring

noncomputable def squareBlockNormalised (t : ℕ) : ℝ :=
  blockLogLower (2 * t ^ 2) (optimalWindow (2 * t ^ 2)) /
    ((t : ℝ) ^ 3 * Real.log (t : ℝ))

lemma square_block_lower_tendsto :
    Tendsto squareBlockNormalised atTop (𝓝 ((16 : ℝ) / 3)) := by
  have hscale : Tendsto
      (fun t : ℕ => 2 * Real.sqrt 2 *
        (Real.log 2 * (Real.log (t : ℝ))⁻¹ + 2)) atTop
      (𝓝 (4 * Real.sqrt 2)) := by
    convert (tendsto_const_nhds.mul
      ((tendsto_const_nhds.mul inv_log_nat_tendsto_zero).add tendsto_const_nhds)) using 1 <;>
      ring_nf
  have hproduct := (optimised_lower_tendsto.comp twice_square_tendsto_atTop).mul hscale
  have hlimit : (2 * Real.sqrt 2 / 3) * (4 * Real.sqrt 2) = (16 : ℝ) / 3 := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  rw [hlimit] at hproduct
  apply hproduct.congr'
  filter_upwards [eventually_ge_atTop 2] with t ht
  rw [← square_log_scale ht]
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hn : (0 : ℝ) < ((2 * t ^ 2 : ℕ) : ℝ) := by positivity
  have hs : Real.sqrt ((2 * t ^ 2 : ℕ) : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  have hlog : Real.log ((2 * t ^ 2 : ℕ) : ℝ) ≠ 0 := by
    apply (Real.log_pos _).ne'
    have : 1 < 2 * t ^ 2 := by nlinarith
    exact_mod_cast this
  have hlt : Real.log (t : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < t by omega))).ne'
  dsimp [optimisedLogLower, squareBlockNormalised, Function.comp_def]
  field_simp [hn.ne', hs, hlog, htpos.ne', hlt]

lemma subcritical_upper_tendsto (c : ℝ) :
    Tendsto (fun t : ℕ => c * (Real.log c * (Real.log (t : ℝ))⁻¹ + 3))
      atTop (𝓝 (3 * c)) := by
  convert (tendsto_const_nhds.mul
    ((tendsto_const_nhds.mul inv_log_nat_tendsto_zero).add tendsto_const_nhds)) using 1 <;>
    ring_nf

lemma x_log_x_mono {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    x * Real.log x ≤ y * Real.log y := by
  have hxpos : 0 < x := by linarith
  have hypos : 0 < y := lt_of_lt_of_le hxpos hxy
  have hlog : Real.log x ≤ Real.log y := Real.log_le_log hxpos hxy
  exact mul_le_mul hxy hlog (Real.log_nonneg hx) hypos.le

lemma subcritical_log_normalisation {c : ℝ} (hc : 0 < c) {t : ℕ} (ht : 2 ≤ t) :
    (c * (t : ℝ) ^ 3 * Real.log (c * (t : ℝ) ^ 3)) /
      ((t : ℝ) ^ 3 * Real.log (t : ℝ)) =
    c * (Real.log c * (Real.log (t : ℝ))⁻¹ + 3) := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hl : Real.log (t : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < t by omega))).ne'
  rw [Real.log_mul hc.ne' (pow_ne_zero _ htpos.ne'), Real.log_pow]
  field_simp [htpos.ne', hl]
  ring

/-- Whole res:radius-constant, in the exact epsilon/eventual form of liminf.
No boundedness or regularity condition on M or R is added. -/
theorem asymptotic_radius_constant (M R : ℕ → ℕ)
    (hH : ∀ᶠ t : ℕ in atTop,
      0 < M t ∧ _root_.Erdos68.channelLCM (2 * t ^ 2) ∣ M t ∧
      M t < (R t + 1).factorial - 1) :
    LowerLimitAtLeast (fun t : ℕ => ((R t + 1 : ℕ) : ℝ) / (t : ℝ) ^ 3)
      ((16 : ℝ) / 9) := by
  intro a ha
  by_cases ha0 : a ≤ 0
  · filter_upwards [eventually_ge_atTop 1] with t ht
    have hp : (0 : ℝ) < ((R t + 1 : ℕ) : ℝ) / (t : ℝ) ^ 3 := by
      have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
      positivity
    exact lt_of_le_of_lt ha0 hp
  · have apos : 0 < a := lt_of_not_ge ha0
    let c : ℝ := (a + 16 / 9) / 2
    have hc : 0 < c := by dsimp [c]; linarith
    have hac : a < c := by dsimp [c]; linarith
    have hct : 3 * c < (16 : ℝ) / 3 := by dsimp [c]; linarith
    have hdiff := square_block_lower_tendsto.sub (subcritical_upper_tendsto c)
    have hgood : ∀ᶠ t : ℕ in atTop,
        c * (Real.log c * (Real.log (t : ℝ))⁻¹ + 3) < squareBlockNormalised t := by
      have hz := hdiff.eventually (Ioi_mem_nhds (show (0 : ℝ) < 16 / 3 - 3 * c by linarith))
      filter_upwards [hz] with t ht
      linarith
    filter_upwards [hH, hgood, eventually_ge_atTop 3] with t hHt hgt ht
    have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
    have htlog : 0 < Real.log (t : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < t by omega))
    have hden : 0 < (t : ℝ) ^ 3 * Real.log (t : ℝ) := by positivity
    have hN : 3 ≤ 2 * t ^ 2 := by nlinarith
    have hb := blockLogLower_lt_radius (optimalWindow_lt hN) hHt.1 hHt.2.1 hHt.2.2
    have hsub : c < ((R t + 1 : ℕ) : ℝ) / (t : ℝ) ^ 3 := by
      by_contra hn
      have hrle : ((R t + 1 : ℕ) : ℝ) ≤ c * (t : ℝ) ^ 3 :=
        (div_le_iff₀ (pow_pos htpos 3)).mp (le_of_not_gt hn)
      have hm := x_log_x_mono
        (show (1 : ℝ) ≤ ((R t + 1 : ℕ) : ℝ) by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _))
        hrle
      have hratio : squareBlockNormalised t <
          c * (Real.log c * (Real.log (t : ℝ))⁻¹ + 3) := by
        rw [← subcritical_log_normalisation hc (by omega : 2 ≤ t)]
        exact (div_lt_div_of_pos_right hb hden).trans_le
          (div_le_div_of_nonneg_right hm hden.le)
      exact (not_lt_of_ge hgt.le) hratio
    exact hac.trans hsub

end ErdosProblems.Erdos68.PaperComplete
