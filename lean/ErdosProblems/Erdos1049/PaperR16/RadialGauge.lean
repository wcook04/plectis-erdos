import ErdosProblems.Erdos1049.PaperR16.LambertBasic

/-!
# The logarithmic radial normalisation

Candidate source; all new Lean checks UNRUN. The filter is genuinely one-sided.
No primitive-root limit or equation-to-row supplier is a hypothesis here.
-/

noncomputable section
open scoped BigOperators
open Filter Topology

namespace ErdosProblems.Erdos1049.PaperR16

abbrev radial : Filter ℝ := 𝓝[<] (1 : ℝ)

/-- `(1-r)/log(1/(1-r))`, written without an unnecessary logarithmic division. -/
def radialGauge (r : ℝ) : ℝ := (1 - r) / logMass r

lemma radial_eventually_unit : ∀ᶠ r : ℝ in radial, 0 < r ∧ r < 1 := by
  have hp : ∀ᶠ r : ℝ in radial, 0 < r :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num))
  filter_upwards [hp, self_mem_nhdsWithin] with r hr hs
  exact ⟨hr, hs⟩

lemma radial_id : Tendsto (fun r : ℝ => r) radial (𝓝 (1 : ℝ)) :=
  tendsto_id'.mpr nhdsWithin_le_nhds

lemma radial_one_sub :
    Tendsto (fun r : ℝ => 1 - r) radial (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) radial (𝓝 1)).sub radial_id
  · filter_upwards [radial_eventually_unit] with r hr
    exact sub_pos.mpr hr.2

lemma logMass_tendsto_atTop : Tendsto logMass radial atTop := by
  exact tendsto_neg_atBot_atTop.comp
    (Real.tendsto_log_nhdsGT_zero.comp radial_one_sub)

lemma logMass_inv_tendsto_zero :
    Tendsto (fun r : ℝ => (logMass r)⁻¹) radial (𝓝 (0 : ℝ)) :=
  tendsto_inv_atTop_zero.comp logMass_tendsto_atTop

lemma radialGauge_pos {r : ℝ} (hr : 0 < r ∧ r < 1) : 0 < radialGauge r :=
  div_pos (sub_pos.mpr hr.2) (logMass_pos hr)

lemma unit_power_mem {r : ℝ} (hr : 0 < r ∧ r < 1) {m : ℕ} (hm : 0 < m) :
    0 < r ^ m ∧ r ^ m < 1 :=
  ⟨pow_pos hr.1 m, unit_pow_lt_one hr.1.le hr.2 hm⟩

lemma power_tendsto_radial (m : ℕ) (hm : 0 < m) :
    Tendsto (fun r : ℝ => r ^ m) radial radial := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using radial_id.pow m
  · filter_upwards [radial_eventually_unit] with r hr
    exact (unit_power_mem hr hm).2

/-- A complete real radial limit, obtained from the quantitative series estimate. -/
theorem lambert_real_radial :
    Tendsto (fun r : ℝ => radialGauge r * lambert r) radial (𝓝 (1 : ℝ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    ?_ logMass_inv_tendsto_zero
  filter_upwards [radial_eventually_unit] with r hr
  have ha := logMass_pos hr
  have hb := lambert_log_error_bounds r hr
  have he : radialGauge r * lambert r - 1 =
      ((1 - r) * lambert r - logMass r) / logMass r := by
    dsimp [radialGauge]
    field_simp [ne_of_gt ha] <;> ring
  rw [he, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hb.1 ha.le)]
  calc
    ((1 - r) * lambert r - logMass r) / logMass r ≤ 1 / logMass r :=
      (div_le_div_iff_of_pos_right ha).2 hb.2
    _ = (logMass r)⁻¹ := one_div _

theorem lambert_complex_radial_at_one :
    Tendsto (fun r : ℝ => (radialGauge r : ℂ) * lambert (r : ℂ))
      radial (𝓝 (1 : ℂ)) := by
  have h := (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp lambert_real_radial
  change Tendsto (fun r : ℝ => ((radialGauge r * lambert (K := ℝ) r : ℝ) : ℂ))
    radial (𝓝 (1 : ℂ)) at h
  simpa only [Function.comp_apply, Complex.ofReal_mul, Complex.ofReal_one,
    lambert_ofReal] using h

lemma geometricBlock_tendsto (m : ℕ) :
    Tendsto (geometricBlock m) radial (𝓝 (m : ℝ)) := by
  have hc : Continuous (geometricBlock m) := by
    unfold geometricBlock
    fun_prop
  simpa [geometricBlock] using (hc.tendsto 1).mono_left nhdsWithin_le_nhds

lemma logMass_pow (m : ℕ) (hm : 0 < m) (r : ℝ) (hr : 0 < r ∧ r < 1) :
    logMass (r ^ m) = logMass r - Real.log (geometricBlock m r) := by
  have hg := geometricBlock_pos hr.1 hm
  simp only [logMass]
  rw [← geometricBlock_identity m r,
    Real.log_mul (show 1 - r ≠ 0 by linarith [hr.2]) (ne_of_gt hg)]
  ring

/-- Exact composition normalisation before taking any limit. -/
lemma radialGauge_div_pow (m : ℕ) (hm : 0 < m)
    (r : ℝ) (hr : 0 < r ∧ r < 1) :
    radialGauge r / radialGauge (r ^ m) =
      (geometricBlock m r)⁻¹ *
        (1 - Real.log (geometricBlock m r) / logMass r) := by
  have hg := geometricBlock_pos hr.1 hm
  have ha := logMass_pos hr
  have ham := logMass_pos (unit_power_mem hr hm)
  have hdiff : logMass r - Real.log (geometricBlock m r) ≠ 0 := by
    rw [← logMass_pow m hm r hr]
    exact ne_of_gt ham
  simp only [radialGauge]
  rw [logMass_pow m hm r hr, ← geometricBlock_identity m r]
  field_simp [ne_of_gt ha, ne_of_gt hg, hdiff,
    show 1 - r ≠ 0 by linarith [hr.2]] <;> ring

/-- The essential `1/m` composition factor. -/
theorem radialGauge_div_pow_tendsto (m : ℕ) (hm : 0 < m) :
    Tendsto (fun r : ℝ => radialGauge r / radialGauge (r ^ m))
      radial (𝓝 ((m : ℝ)⁻¹)) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hg := geometricBlock_tendsto m
  have hlog : Tendsto (fun r : ℝ => Real.log (geometricBlock m r))
      radial (𝓝 (Real.log (m : ℝ))) :=
    (Real.continuousAt_log hmR).tendsto.comp hg
  have hsmall : Tendsto
      (fun r : ℝ => Real.log (geometricBlock m r) / logMass r)
      radial (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero] using hlog.mul logMass_inv_tendsto_zero
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) radial (𝓝 (1 : ℝ)) :=
    tendsto_const_nhds
  have hout := (hg.inv₀ hmR).mul (hone.sub hsmall)
  have he : (fun r : ℝ => radialGauge r / radialGauge (r ^ m)) =ᶠ[radial]
      (fun r : ℝ => (geometricBlock m r)⁻¹ *
        (1 - Real.log (geometricBlock m r) / logMass r)) := by
    filter_upwards [radial_eventually_unit] with r hr
    exact radialGauge_div_pow m hm r hr
  apply (tendsto_congr' he).2
  simpa only [sub_zero, mul_one] using hout

/-- An `O((1-r)⁻¹)` complex remainder disappears under the logarithmic gauge. -/
theorem radialGauge_mul_remainder_tendsto_zero (E : ℝ → ℂ) (C : ℝ)
    (hbound : ∀ᶠ r : ℝ in radial, ‖E r‖ ≤ C / (1 - r)) :
    Tendsto (fun r : ℝ => (radialGauge r : ℂ) * E r) radial (𝓝 (0 : ℂ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  have hmajor : Tendsto (fun r : ℝ => C * (logMass r)⁻¹) radial (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => C) radial (𝓝 C)).mul
        logMass_inv_tendsto_zero
  refine squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hmajor
  filter_upwards [hbound, radial_eventually_unit] with r hb hr
  have hg := radialGauge_pos hr
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg]
  calc
    radialGauge r * ‖E r‖ ≤ radialGauge r * (C / (1 - r)) :=
      mul_le_mul_of_nonneg_left hb hg.le
    _ = C * (logMass r)⁻¹ := by
      dsimp [radialGauge]
      field_simp [ne_of_gt (logMass_pos hr), show 1 - r ≠ 0 by linarith [hr.2]] <;> ring

end ErdosProblems.Erdos1049.PaperR16
