import Mathlib

/-!
# Erdős 1041: the relation between two merger-scale integrals

Paper-form restatement of the short-paper theorem labelled `res:orlicz-currency`
(`paper/1041/erdos-1041-lemniscate-newton-flow.tex`, line 1436): the substitution
identity (O1), monotonicity and strict convexity of `Φ` on `(0, ∞)`, the
sublinearity (O2), its consequence (O3), and the resulting non-existence of a
positive universal linear lower bound.

The paper writes "At `t = 0` the integrand is understood by its continuous
limiting value `0`".  That convention is realised here by Lean's own
conventions: `Real.sinh 0 = 0`, hence `coth 0 = 0`, `Real.log 0 = 0` and
`1 / 0 = 0`, so `orliczKernel 0 = 0`.  `orliczKernel_continuous` proves that
this is indeed the continuous extension, so the definition below transcribes
the paper's improper integral.
-/

set_option autoImplicit false

noncomputable section

namespace ErdosProblems.Erdos1041.PaperCompleteR21

open Set Filter MeasureTheory
open scoped Topology

/-- `coth t = cosh t / sinh t`. -/
def coth (t : ℝ) : ℝ := Real.cosh t / Real.sinh t

/-- The integrand `1 / log (coth t)` of the paper's `Φ`, carrying the paper's
continuous limiting value `0` at `t = 0`. -/
def orliczKernel (t : ℝ) : ℝ := 1 / Real.log (coth t)

/-- `Φ(x) = ∫_0^x dt / log (coth t)`. -/
def Phi (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, orliczKernel t

/-- `I_k(r) = ∫_r^1 dq / (q * log ((1 + q ^ (2/k)) / (1 - q ^ (2/k))))`. -/
def mergerIntegral (k : ℕ) (r : ℝ) : ℝ :=
  ∫ q in r..(1 : ℝ),
    1 / (q * Real.log ((1 + q ^ ((2 : ℝ) / k)) / (1 - q ^ ((2 : ℝ) / k))))

theorem Phi_def (x : ℝ) : Phi x = ∫ t in (0 : ℝ)..x, orliczKernel t := rfl

theorem mergerIntegral_def (k : ℕ) (r : ℝ) :
    mergerIntegral k r = ∫ q in r..(1 : ℝ),
      1 / (q * Real.log ((1 + q ^ ((2 : ℝ) / k)) / (1 - q ^ ((2 : ℝ) / k)))) := rfl

/-! ### Elementary properties of the kernel -/

theorem sinh_ne_zero {t : ℝ} (ht : t ≠ 0) : Real.sinh t ≠ 0 := by
  rcases ht.lt_or_gt with h | h
  · exact ne_of_lt (Real.sinh_neg_iff.mpr h)
  · exact ne_of_gt (Real.sinh_pos_iff.mpr h)

theorem coth_zero : coth 0 = 0 := by simp [coth]

theorem coth_pos {t : ℝ} (ht : 0 < t) : 0 < coth t :=
  div_pos (Real.cosh_pos t) (Real.sinh_pos_iff.mpr ht)

theorem one_lt_abs_coth {t : ℝ} (ht : t ≠ 0) : 1 < |coth t| := by
  have hs : Real.sinh t ≠ 0 := sinh_ne_zero ht
  have hsa : 0 < |Real.sinh t| := abs_pos.mpr hs
  have hc : 0 < Real.cosh t := Real.cosh_pos t
  have key : |Real.sinh t| < Real.cosh t := by
    have h1 : Real.cosh t ^ 2 - Real.sinh t ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq t
    nlinarith [sq_abs (Real.sinh t), abs_nonneg (Real.sinh t)]
  rw [coth, abs_div, abs_of_pos hc, lt_div_iff₀ hsa, one_mul]
  exact key

theorem log_coth_pos {t : ℝ} (ht : t ≠ 0) : 0 < Real.log (coth t) := by
  rw [← Real.log_abs]
  exact Real.log_pos (one_lt_abs_coth ht)

theorem orliczKernel_zero : orliczKernel 0 = 0 := by
  simp [orliczKernel, coth_zero]

theorem orliczKernel_pos {t : ℝ} (ht : t ≠ 0) : 0 < orliczKernel t :=
  one_div_pos.mpr (log_coth_pos ht)

theorem orliczKernel_nonneg (t : ℝ) : 0 ≤ orliczKernel t := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [orliczKernel_zero]
  · exact (orliczKernel_pos ht).le

theorem coth_anti {s t : ℝ} (hs : 0 < s) (hst : s < t) : coth t < coth s := by
  have hss : 0 < Real.sinh s := Real.sinh_pos_iff.mpr hs
  have hts : 0 < Real.sinh t := Real.sinh_pos_iff.mpr (hs.trans hst)
  have key : 0 < Real.sinh (t - s) := Real.sinh_pos_iff.mpr (by linarith)
  rw [Real.sinh_sub] at key
  have hid : coth s - coth t
      = (Real.sinh t * Real.cosh s - Real.cosh t * Real.sinh s)
        / (Real.sinh s * Real.sinh t) := by
    rw [coth, coth]
    field_simp
  have hpos : 0 < coth s - coth t := by
    rw [hid]
    exact div_pos key (mul_pos hss hts)
  linarith

theorem orliczKernel_strictMonoOn : StrictMonoOn orliczKernel (Ici (0 : ℝ)) := by
  intro s hs t _ht hst
  have hs0 : (0 : ℝ) ≤ s := hs
  have ht0 : (0 : ℝ) < t := lt_of_le_of_lt hs0 hst
  rcases eq_or_lt_of_le hs0 with h0 | h0
  · rw [← h0, orliczKernel_zero]
    exact orliczKernel_pos ht0.ne'
  · have hct : (0 : ℝ) < coth t := coth_pos ht0
    have hlt : Real.log (coth t) < Real.log (coth s) :=
      Real.log_lt_log hct (coth_anti h0 hst)
    have hpt : 0 < Real.log (coth t) := log_coth_pos ht0.ne'
    simpa only [orliczKernel] using one_div_lt_one_div_of_lt hpt hlt

theorem orliczKernel_continuous : Continuous orliczKernel := by
  rw [continuous_iff_continuousAt]
  intro t
  rcases eq_or_ne t 0 with rfl | ht
  · rw [continuousAt_iff_punctured_nhds, orliczKernel_zero]
    have hsinh : Tendsto (fun s : ℝ => |Real.sinh s|) (𝓝[≠] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have hc : Continuous fun s : ℝ => |Real.sinh s| := Real.continuous_sinh.abs
        have h2 := hc.tendsto (0 : ℝ)
        simp only [Real.sinh_zero, abs_zero] at h2
        exact h2.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact abs_pos.mpr (sinh_ne_zero hs)
    have hinv : Tendsto (fun s : ℝ => |Real.sinh s|⁻¹) (𝓝[≠] (0 : ℝ)) atTop :=
      tendsto_inv_nhdsGT_zero.comp hsinh
    have habs : Tendsto (fun s : ℝ => |coth s|) (𝓝[≠] (0 : ℝ)) atTop := by
      refine tendsto_atTop_mono' _ ?_ hinv
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hsa : 0 < |Real.sinh s| := abs_pos.mpr (sinh_ne_zero hs)
      have hval : |coth s| = Real.cosh s / |Real.sinh s| := by
        rw [coth, abs_div, abs_of_pos (Real.cosh_pos s)]
      have hstep : |Real.sinh s|⁻¹ * |Real.sinh s|
          ≤ (Real.cosh s / |Real.sinh s|) * |Real.sinh s| := by
        rw [inv_mul_cancel₀ hsa.ne', div_mul_cancel₀ _ hsa.ne']
        exact Real.one_le_cosh s
      rw [hval]
      exact le_of_mul_le_mul_right hstep hsa
    have hlog : Tendsto (fun s : ℝ => Real.log (coth s)) (𝓝[≠] (0 : ℝ)) atTop := by
      have hcomp := Real.tendsto_log_atTop.comp habs
      simpa only [Function.comp_def, Real.log_abs] using hcomp
    have hres : Tendsto (fun s : ℝ => (Real.log (coth s))⁻¹) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
      hlog.inv_tendsto_atTop
    have heq : (fun s : ℝ => (Real.log (coth s))⁻¹) = orliczKernel := by
      funext s
      rw [orliczKernel, one_div]
    rwa [heq] at hres
  · have hs : Real.sinh t ≠ 0 := sinh_ne_zero ht
    have hct : coth t ≠ 0 := div_ne_zero (Real.cosh_pos t).ne' hs
    have hlog : Real.log (coth t) ≠ 0 := (log_coth_pos ht).ne'
    have hcoth : ContinuousAt coth t :=
      ContinuousAt.div Real.continuous_cosh.continuousAt Real.continuous_sinh.continuousAt hs
    have hlc : ContinuousAt (fun s => Real.log (coth s)) t :=
      (Real.continuousAt_log hct).comp hcoth
    exact ContinuousAt.div continuousAt_const hlc hlog

/-- The paper's endpoint convention, as an assertion: the integrand has
continuous limiting value `0` at `t = 0`, and that is the value it takes. -/
theorem orliczKernel_tendsto_zero : Tendsto orliczKernel (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have h := orliczKernel_continuous.continuousAt (x := (0 : ℝ))
  rwa [continuousAt_iff_punctured_nhds, orliczKernel_zero] at h

/-! ### The primitive `Φ` -/

theorem orliczKernel_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable orliczKernel volume a b :=
  orliczKernel_continuous.intervalIntegrable a b

theorem phi_zero : Phi 0 = 0 := by simp [Phi_def]

theorem phi_hasDerivAt (x : ℝ) : HasDerivAt Phi (orliczKernel x) x :=
  (orliczKernel_continuous.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem deriv_phi : deriv Phi = orliczKernel :=
  funext fun x => (phi_hasDerivAt x).deriv

theorem phi_continuous : Continuous Phi :=
  continuous_iff_continuousAt.mpr fun x => (phi_hasDerivAt x).continuousAt

theorem phi_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Phi x :=
  intervalIntegral.integral_nonneg hx fun u _ => orliczKernel_nonneg u

theorem phi_le {x : ℝ} (hx : 0 ≤ x) : Phi x ≤ x * orliczKernel x := by
  have key : Phi x ≤ ∫ _t in (0 : ℝ)..x, orliczKernel x := by
    apply intervalIntegral.integral_mono_on hx (orliczKernel_intervalIntegrable 0 x)
      intervalIntegrable_const
    intro t ht
    exact orliczKernel_strictMonoOn.monotoneOn ht.1 hx ht.2
  rw [intervalIntegral.integral_const] at key
  simpa using key

theorem phi_strictMonoOn : StrictMonoOn Phi (Ici (0 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) phi_continuous.continuousOn
  intro y hy
  rw [interior_Ici] at hy
  rw [deriv_phi]
  exact orliczKernel_pos (ne_of_gt hy)

theorem phi_strictConvexOn : StrictConvexOn ℝ (Ioi (0 : ℝ)) Phi := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ioi 0) phi_continuous.continuousOn
  rw [interior_Ioi, deriv_phi]
  exact orliczKernel_strictMonoOn.mono Ioi_subset_Ici_self

/-- Paper formula (O2): `Φ(x)/x → 0` as `x ↓ 0`. -/
theorem phi_div_tendsto_zero :
    Tendsto (fun x => Phi x / x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hk : Tendsto orliczKernel (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := orliczKernel_continuous.continuousAt (x := (0 : ℝ))
    rw [ContinuousAt, orliczKernel_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hk ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact div_nonneg (phi_nonneg (le_of_lt hy)) (le_of_lt hy)
  · filter_upwards [self_mem_nhdsWithin] with y hy
    rw [div_le_iff₀ hy]
    have h := phi_le (le_of_lt hy)
    linarith [h, mul_comm y (orliczKernel y)]

/-! ### The substitution `q = e^{-kt}` -/

private theorem exp_substitution (K : ℝ) (hK : 0 < K) (x : ℝ) (_hx : 0 ≤ x)
    (g h : ℝ → ℝ)
    (hgh : ∀ t ∈ Ioc (0 : ℝ) x,
      K * Real.exp (-(K * t)) * g (Real.exp (-(K * t))) = h t) :
    ∫ q in Ico (Real.exp (-(K * x))) (1 : ℝ), g q = ∫ t in Ioc (0 : ℝ) x, h t := by
  have hKne : K ≠ 0 := hK.ne'
  have hderiv : ∀ t ∈ Ioc (0 : ℝ) x,
      HasDerivWithinAt (fun s : ℝ => Real.exp (-(K * s)))
        ((fun s : ℝ => Real.exp (-(K * s)) * (-K)) t) (Ioc (0 : ℝ) x) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => -(K * s)) (-K) t := by
      simpa using ((hasDerivAt_id t).const_mul K).neg
    exact h1.exp.hasDerivWithinAt
  have hinj : InjOn (fun s : ℝ => Real.exp (-(K * s))) (Ioc (0 : ℝ) x) := by
    intro a _ b _ hab
    have h := Real.exp_eq_exp.mp hab
    have h2 : K * a = K * b := by linarith
    exact mul_left_cancel₀ hKne h2
  have himg : (fun s : ℝ => Real.exp (-(K * s))) '' (Ioc (0 : ℝ) x)
      = Ico (Real.exp (-(K * x))) (1 : ℝ) := by
    ext y
    constructor
    · rintro ⟨t, ⟨ht0, htx⟩, rfl⟩
      refine ⟨Real.exp_le_exp.mpr (by nlinarith), ?_⟩
      have hlt : Real.exp (-(K * t)) < Real.exp 0 := Real.exp_lt_exp.mpr (by nlinarith)
      simpa using hlt
    · rintro ⟨hy1, hy2⟩
      have hy0 : 0 < y := lt_of_lt_of_le (Real.exp_pos _) hy1
      refine ⟨-Real.log y / K, ⟨div_pos (by simpa using Real.log_neg hy0 hy2) hK, ?_⟩, ?_⟩
      · have hlog : Real.log (Real.exp (-(K * x))) ≤ Real.log y :=
          (Real.log_le_log_iff (Real.exp_pos _) hy0).mpr hy1
        rw [Real.log_exp] at hlog
        rw [div_le_iff₀ hK]
        linarith
      · have hcancel : -(K * (-Real.log y / K)) = Real.log y := by field_simp
        simp only
        rw [hcancel]
        exact Real.exp_log hy0
  have hmain := integral_image_eq_integral_abs_deriv_smul
    (f := fun s : ℝ => Real.exp (-(K * s)))
    (f' := fun s : ℝ => Real.exp (-(K * s)) * (-K))
    measurableSet_Ioc hderiv hinj g
  rw [himg] at hmain
  rw [hmain]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  have habs : |Real.exp (-(K * t)) * (-K)| = K * Real.exp (-(K * t)) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_neg, abs_of_pos hK]
    ring
  simp only [smul_eq_mul, habs]
  exact hgh t ht

/-- Paper formula (O1): the substitution identity `I_k(r) = k Φ(k⁻¹ log(1/r))`. -/
theorem mergerIntegral_eq_mul_phi {k : ℕ} (hk : 1 ≤ k) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) :
    mergerIntegral k r = k * Phi (Real.log (1 / r) / k) := by
  have hK : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hKne : (k : ℝ) ≠ 0 := hK.ne'
  have hlogr : Real.log (1 / r) = -Real.log r := by rw [one_div, Real.log_inv]
  have hnp : Real.log r ≤ 0 := Real.log_nonpos hr0.le hr1
  have hx0 : 0 ≤ Real.log (1 / r) / (k : ℝ) := by
    rw [hlogr]
    exact div_nonneg (by linarith) hK.le
  have hrx : Real.exp (-((k : ℝ) * (Real.log (1 / r) / (k : ℝ)))) = r := by
    rw [show (k : ℝ) * (Real.log (1 / r) / (k : ℝ)) = Real.log (1 / r) by field_simp,
      hlogr, neg_neg, Real.exp_log hr0]
  have hcongr : ∀ t ∈ Ioc (0 : ℝ) (Real.log (1 / r) / (k : ℝ)),
      (k : ℝ) * Real.exp (-((k : ℝ) * t)) *
        (1 / (Real.exp (-((k : ℝ) * t)) *
          Real.log ((1 + Real.exp (-((k : ℝ) * t)) ^ ((2 : ℝ) / (k : ℝ)))
            / (1 - Real.exp (-((k : ℝ) * t)) ^ ((2 : ℝ) / (k : ℝ))))))
        = (k : ℝ) * orliczKernel t := by
    intro t ht
    have ht0 : t ≠ 0 := ht.1.ne'
    have hu : (0 : ℝ) < Real.exp (-((k : ℝ) * t)) := Real.exp_pos _
    have hune : Real.exp (-((k : ℝ) * t)) ≠ 0 := hu.ne'
    have hk2 : (k : ℝ) * ((2 : ℝ) / (k : ℝ)) = 2 := by field_simp
    have hexpo : -((k : ℝ) * t) * ((2 : ℝ) / (k : ℝ)) = -t + -t := by
      linear_combination (-t) * hk2
    have hpow : Real.exp (-((k : ℝ) * t)) ^ ((2 : ℝ) / (k : ℝ))
        = Real.exp (-t) * Real.exp (-t) := by
      rw [Real.rpow_def_of_pos hu, Real.log_exp, hexpo, Real.exp_add]
    have hd2 : 1 - Real.exp (-t) * Real.exp (-t) ≠ 0 := by
      intro hcon
      have h1 : Real.exp (-t + -t) = 1 := by rw [Real.exp_add]; linarith
      rw [Real.exp_eq_one_iff] at h1
      exact ht0 (by linarith)
    have hden : Real.exp t - Real.exp (-t) ≠ 0 := by
      intro hcon
      have h1 : Real.exp t = Real.exp (-t) := by linarith
      have h2 : t = -t := Real.exp_eq_exp.mp h1
      exact ht0 (by linarith)
    have hcoth : coth t = (Real.exp t + Real.exp (-t)) / (Real.exp t - Real.exp (-t)) := by
      have h2 : (Real.exp t - Real.exp (-t)) / 2 ≠ 0 := div_ne_zero hden two_ne_zero
      rw [coth, Real.cosh_eq, Real.sinh_eq, div_eq_div_iff h2 hden]
      ring
    have hEE : Real.exp t * Real.exp (-t) = 1 := by
      rw [← Real.exp_add]; simp
    have hkey : (1 + Real.exp (-t) * Real.exp (-t)) / (1 - Real.exp (-t) * Real.exp (-t))
        = coth t := by
      rw [hcoth, div_eq_div_iff hd2 hden]
      linear_combination (2 * Real.exp (-t)) * hEE
    have hl : Real.log (coth t) ≠ 0 := (log_coth_pos ht0).ne'
    rw [hpow, hkey, orliczKernel]
    field_simp
  have hsub := exp_substitution (k : ℝ) hK (Real.log (1 / r) / (k : ℝ)) hx0
    (fun q => 1 / (q * Real.log ((1 + q ^ ((2 : ℝ) / (k : ℝ)))
      / (1 - q ^ ((2 : ℝ) / (k : ℝ))))))
    (fun t => (k : ℝ) * orliczKernel t) hcongr
  rw [hrx] at hsub
  rw [mergerIntegral_def, intervalIntegral.integral_of_le hr1,
    integral_Ioc_eq_integral_Ioo, ← integral_Ico_eq_integral_Ioo, hsub,
    integral_const_mul, Phi_def, intervalIntegral.integral_of_le hx0]

/-- Paper formula (O3): for every `k ≥ 1` and every `c > 0` some `0 < r < 1`
satisfies `I_k(r) < c k⁻¹ log(1/r)`. -/
theorem exists_mergerIntegral_lt {k : ℕ} (hk : 1 ≤ k) {c : ℝ} (hc : 0 < c) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ mergerIntegral k r < c * (Real.log (1 / r) / k) := by
  have hK : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hKne : (k : ℝ) ≠ 0 := hK.ne'
  have hcK : 0 < c / (k : ℝ) := div_pos hc hK
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), Phi x / x < c / (k : ℝ) :=
    phi_div_tendsto_zero (Iio_mem_nhds hcK)
  obtain ⟨x, hxlt, hx0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hxpos : (0 : ℝ) < x := hx0
  refine ⟨Real.exp (-((k : ℝ) * x)), Real.exp_pos _, ?_, ?_⟩
  · have hlt : Real.exp (-((k : ℝ) * x)) < Real.exp 0 :=
      Real.exp_lt_exp.mpr (by nlinarith)
    simpa using hlt
  · have hlog : Real.log (1 / Real.exp (-((k : ℝ) * x))) = (k : ℝ) * x := by
      rw [one_div, ← Real.exp_neg, Real.log_exp, neg_neg]
    rw [mergerIntegral_eq_mul_phi hk (Real.exp_pos _)
      (by
        have hlt : Real.exp (-((k : ℝ) * x)) < Real.exp 0 :=
          Real.exp_lt_exp.mpr (by nlinarith)
        simp only [Real.exp_zero] at hlt
        exact hlt.le), hlog]
    rw [show (k : ℝ) * x / (k : ℝ) = x by field_simp]
    have hstep : Phi x < c / (k : ℝ) * x := (div_lt_iff₀ hxpos).mp hxlt
    have h2 : (k : ℝ) * Phi x < (k : ℝ) * (c / (k : ℝ) * x) :=
      mul_lt_mul_of_pos_left hstep hK
    rwa [show (k : ℝ) * (c / (k : ℝ) * x) = c * x by field_simp] at h2

/-- The whole short-paper theorem `res:orlicz-currency`:
the endpoint convention as a limit identity; the substitution identity (O1);
`Φ` increasing (both in the strict and the weak reading) and strictly convex on
`(0, ∞)`; the sublinearity (O2); its consequence (O3); and the non-existence of
a positive universal constant bounding `I_k(r)` below by that constant times
`k⁻¹ log(1/r)`. -/
theorem orlicz_currency :
    (Tendsto orliczKernel (𝓝[≠] (0 : ℝ)) (𝓝 0) ∧ orliczKernel 0 = 0) ∧
      (∀ k : ℕ, 1 ≤ k → ∀ r : ℝ, 0 < r → r ≤ 1 →
        mergerIntegral k r = k * Phi (Real.log (1 / r) / k)) ∧
      StrictMonoOn Phi (Ioi (0 : ℝ)) ∧
      MonotoneOn Phi (Ioi (0 : ℝ)) ∧
      StrictConvexOn ℝ (Ioi (0 : ℝ)) Phi ∧
      Tendsto (fun x => Phi x / x) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      (∀ k : ℕ, 1 ≤ k → ∀ c : ℝ, 0 < c → ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        mergerIntegral k r < c * (Real.log (1 / r) / k)) ∧
      ¬ ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k → ∀ r : ℝ, 0 < r → r < 1 →
        c * (Real.log (1 / r) / k) ≤ mergerIntegral k r := by
  refine ⟨⟨orliczKernel_tendsto_zero, orliczKernel_zero⟩,
    fun k hk r hr0 hr1 => mergerIntegral_eq_mul_phi hk hr0 hr1,
    phi_strictMonoOn.mono Ioi_subset_Ici_self,
    (phi_strictMonoOn.mono Ioi_subset_Ici_self).monotoneOn, phi_strictConvexOn,
    phi_div_tendsto_zero,
    fun k hk c hc => exists_mergerIntegral_lt hk hc, ?_⟩
  rintro ⟨c, hc, hcall⟩
  obtain ⟨r, hr0, hr1, hlt⟩ := exists_mergerIntegral_lt (k := 1) le_rfl hc
  exact absurd (hcall 1 le_rfl r hr0 hr1) (not_le.mpr hlt)

#print axioms orliczKernel_continuous
#print axioms orliczKernel_tendsto_zero
#print axioms mergerIntegral_eq_mul_phi
#print axioms phi_strictMonoOn
#print axioms phi_strictConvexOn
#print axioms phi_div_tendsto_zero
#print axioms exists_mergerIntegral_lt
#print axioms orlicz_currency

end ErdosProblems.Erdos1041.PaperCompleteR21
