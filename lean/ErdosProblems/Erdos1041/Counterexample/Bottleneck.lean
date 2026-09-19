import Mathlib
import ErdosProblems.Erdos1041.Counterexample.Components

/-! External source: ani, erdosproblems.com forum thread 1041, 7 Sept 2026.
Formalisation of Lemma 2.3 and Corollary 2.4 from `ani_degree7_counterexample.tex`. -/

/-!
This module owns slice S3 and declares `s3_bottleneck_length` at the interface
name and statement, with no `sorry`.

The route departs from the Type B return, which stopped at two topological
hypotheses.  The covering hypothesis is `s3_bottleneck_isCoveringMap`.  The
connectedness hypothesis is replaced by the sharper
`bottleneck_slit_preimage_near`: the holomorphic square root of `𝒜/â` supplies
the paper's quadratic coordinate `ψ`, its two branches `ψ = ±η` give two
preimages of each slit point next to `cc`, `hzeros` makes the covering
two-sheeted, and a third preimage anywhere in the component would produce a
third preimage of a nearby point of the slit disc.  So every slit preimage in
the component is one of the two local branches, hence inside the disk-criterion
radius.  Neither Rouché's theorem nor the argument principle is used; see
`bottleneck_ball_subset_image` and `bottleneck_sublevel_isPreconnected`.
-/

noncomputable section

open Topology

namespace Erdos1041.Counterexample

/-! ### Two `ℝ`-on-`ℂ` scalar-action instances

`StarConvex ℝ (0 : ℂ)` elaborates its `SMul ℝ ℂ` to `Algebra.toSMul` (through
`NormedAlgebra ℝ ℂ`), and for that particular instance path Mathlib v4.29.1 does
not resolve `ContinuousSMul ℝ ℂ` or `NormSMulClass ℝ ℂ` by typeclass search.
Both are true and are proved here from `Complex.real_smul`, which rewrites the
action to multiplication by the real coercion.  They are `private`: nothing
outside this file needs them. -/

private instance instContinuousSMulRealComplex : ContinuousSMul ℝ ℂ where
  continuous_smul := by
    have hfun : (fun p : ℝ × ℂ => p.1 • p.2) = fun p : ℝ × ℂ => (p.1 : ℂ) * p.2 := by
      funext p
      exact Complex.real_smul
    rw [hfun]
    exact (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd

private instance instNormSMulClassRealComplex : NormSMulClass ℝ ℂ where
  norm_smul r z := by
    rw [show r • z = (r : ℂ) * z from Complex.real_smul, norm_mul]
    simp

/-- The displacement parametrisation of the paper's radial slit. -/
def bottleneckSlit (v : ℂ) : Set ℂ :=
  {w | ∃ t : ℝ, 0 ≤ t ∧ t < 1 - ‖v‖ ∧
    w = v + (t : ℂ) * (v / (‖v‖ : ℂ))}

/-- The displacement parametrisation agrees with the radius parametrisation. -/
theorem bottleneckSlit_iff (v w : ℂ) (hv : v ≠ 0) :
    w ∈ bottleneckSlit v ↔
      ∃ r : ℝ, ‖v‖ ≤ r ∧ r < 1 ∧
        w = (r : ℂ) * (v / (‖v‖ : ℂ)) := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hnC : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  have hbase : (‖v‖ : ℂ) * (v / (‖v‖ : ℂ)) = v := by
    rw [mul_comm, div_mul_cancel₀ _ hnC]
  constructor
  · rintro ⟨t, ht, ht', hw⟩
    refine ⟨‖v‖ + t, by linarith, by linarith, ?_⟩
    rw [hw, Complex.ofReal_add, add_mul, hbase]
  · rintro ⟨r, hr, hr', hw⟩
    refine ⟨r - ‖v‖, sub_nonneg.mpr hr, by linarith, ?_⟩
    rw [hw, Complex.ofReal_sub, sub_mul, hbase]
    ring

/-- The initial point belongs to the slit when it lies in the unit disc. -/
theorem bottleneckSlit_self (v : ℂ) (hv : ‖v‖ < 1) :
    v ∈ bottleneckSlit v := by
  refine ⟨0, le_rfl, by linarith, ?_⟩
  simp

/-- Zero is not on the slit associated with a nonzero critical value. -/
theorem zero_not_mem_bottleneckSlit (v : ℂ) (hv : v ≠ 0) :
    (0 : ℂ) ∉ bottleneckSlit v := by
  intro hzero
  obtain ⟨r, hr, -, heq⟩ := (bottleneckSlit_iff v 0 hv).mp hzero
  have hrpos : 0 < r := (norm_pos_iff.mpr hv).trans_le hr
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hrpos)
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hnC : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  exact (mul_ne_zero hrC (div_ne_zero hv hnC)) heq.symm

/-- The distance along the slit is strictly smaller than its remaining radius. -/
theorem bottleneckSlit_norm_sub_lt (v w : ℂ) (hv : v ≠ 0)
    (hw : w ∈ bottleneckSlit v) : ‖w - v‖ < 1 - ‖v‖ := by
  obtain ⟨t, ht, ht', rfl⟩ := hw
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hunit : ‖v / (‖v‖ : ℂ)‖ = 1 := by
    simp [hn]
  calc
    ‖v + (t : ℂ) * (v / (‖v‖ : ℂ)) - v‖ = |t| := by
      simp [div_self hn]
    _ = t := abs_of_nonneg ht
    _ < 1 - ‖v‖ := ht'

/-- A critical point makes the translated numerator divisible by `X^2`. -/
theorem bottleneck_shiftQuad_factorisation (p : Polynomial ℂ) (cc : ℂ)
    (hcrit : (Polynomial.derivative p).IsRoot cc) :
    p.comp (Polynomial.X + Polynomial.C cc) - Polynomial.C (p.eval cc) =
      Polynomial.X ^ 2 * shiftQuad p cc := by
  let q : Polynomial ℂ :=
    p.comp (Polynomial.X + Polynomial.C cc) - Polynomial.C (p.eval cc)
  have hq0 : q.coeff 0 = 0 := by
    simp [q, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp]
  have hqd : (Polynomial.derivative q).eval 0 = 0 := by
    have hc : (Polynomial.derivative p).eval cc = 0 := hcrit
    simpa [q, Polynomial.derivative_comp, Polynomial.derivative_X_add_C,
      Polynomial.eval_comp] using hc
  have hq1 : q.coeff 1 = 0 := by
    have hdc : (Polynomial.derivative q).coeff 0 = 0 := by
      simpa only [Polynomial.coeff_zero_eq_eval_zero] using hqd
    simpa [Polynomial.coeff_derivative] using hdc
  have hdiv : (Polynomial.X : Polynomial ℂ) ^ 2 ∣ q := by
    apply Polynomial.X_pow_dvd_iff.mpr
    intro d hd
    have hd' : d = 0 ∨ d = 1 := by omega
    rcases hd' with rfl | rfl
    · exact hq0
    · exact hq1
  have hmod : q %ₘ (Polynomial.X ^ 2) = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X.pow 2)).mpr hdiv
  have hidentity := Polynomial.modByMonic_add_div q (Polynomial.X ^ 2)
  rw [hmod, zero_add] at hidentity
  change q = Polynomial.X ^ 2 * (q /ₘ (Polynomial.X ^ 2))
  exact hidentity.symm

/-- Evaluation of the translated quadratic factor, including at zero. -/
theorem bottleneck_eval_shiftQuad (p : Polynomial ℂ) (cc : ℂ)
    (hcrit : (Polynomial.derivative p).IsRoot cc) (z : ℂ) :
    p.eval (cc + z) = p.eval cc + z ^ 2 * (shiftQuad p cc).eval z := by
  have heval : p.eval (cc + z) - p.eval cc =
      z ^ 2 * (shiftQuad p cc).eval z := by
    simpa only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_pow, add_comm z cc] using
      congrArg (fun q : Polynomial ℂ => q.eval z)
        (bottleneck_shiftQuad_factorisation p cc hcrit)
  exact (sub_eq_iff_eq_add.mp heval).trans (add_comm _ _)

/-- The relative quarter-disc estimate implies a lower bound for the coefficient. -/
theorem bottleneck_coefficient_norm_lower (A a : ℂ) (ha : a ≠ 0)
    (hA : ‖A / a - 1‖ ≤ 1 / 4) : (3 / 4 : ℝ) * ‖a‖ ≤ ‖A‖ := by
  have hone : A / a - (A / a - 1) = 1 := by ring
  have htri := norm_sub_le (A / a) (A / a - 1)
  rw [hone, norm_one] at htri
  have hlower : (3 / 4 : ℝ) ≤ ‖A / a‖ := by linarith
  calc
    (3 / 4 : ℝ) * ‖a‖ ≤ ‖A / a‖ * ‖a‖ :=
      mul_le_mul_of_nonneg_right hlower (norm_nonneg a)
    _ = ‖A‖ := by rw [← norm_mul, div_mul_cancel₀ _ ha]

/-- The disk criterion gives a quadratic lower bound without an inverse chart. -/
theorem bottleneck_quadratic_norm_lower (p : Polynomial ℂ) (cc : ℂ)
    (hcrit : (Polynomial.derivative p).IsRoot cc)
    (aHat : ℂ) (haHat : aHat ≠ 0) (h : ℝ)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h →
      ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (z : ℂ) (hz : ‖z‖ ≤ h) :
    (3 / 4 : ℝ) * ‖aHat‖ * ‖z‖ ^ 2 ≤ ‖p.eval (cc + z) - p.eval cc‖ := by
  have hA := bottleneck_coefficient_norm_lower
    ((shiftQuad p cc).eval z) aHat haHat (hdisk z hz)
  have heq : p.eval (cc + z) - p.eval cc =
      z ^ 2 * (shiftQuad p cc).eval z := by
    rw [bottleneck_eval_shiftQuad p cc hcrit z]
    ring
  rw [heq, norm_mul, norm_pow]
  nlinarith [mul_le_mul_of_nonneg_right hA (sq_nonneg ‖z‖)]

/-- The numerical implication used to obtain the paper's radius. -/
theorem bottleneck_radius_of_quadratic_bound (δ A x : ℝ)
    (hδ : 0 < δ) (hA : 0 < A) (hx : 0 ≤ x)
    (hbound : (3 / 4 : ℝ) * A * x ^ 2 < δ) :
    x < 4 / 3 * Real.sqrt (δ / A) := by
  have hsnonneg := Real.sqrt_nonneg (δ / A)
  have hsq : A * (Real.sqrt (δ / A)) ^ 2 = δ := by
    rw [Real.sq_sqrt (div_nonneg hδ.le hA.le), mul_comm,
      div_mul_cancel₀ _ (ne_of_gt hA)]
  by_contra hnot
  have hge : 4 / 3 * Real.sqrt (δ / A) ≤ x := le_of_not_gt hnot
  have hsum : 0 ≤ x + 4 / 3 * Real.sqrt (δ / A) := by positivity
  have hprod := mul_nonneg (sub_nonneg.mpr hge) hsum
  have hprodA := mul_nonneg hA.le hprod
  nlinarith

/-- Localisation of a slit preimage that is already in the comparison disc. -/
theorem bottleneck_local_slit_norm_lt (p : Polynomial ℂ) (cc : ℂ)
    (hcrit : (Polynomial.derivative p).IsRoot cc) (hv : p.eval cc ≠ 0)
    (aHat : ℂ) (haHat : aHat ≠ 0) (h : ℝ)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h →
      ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (δ : ℝ) (hδ : δ = 1 - ‖p.eval cc‖) (hδpos : 0 < δ)
    (z : ℂ) (hz : ‖z - cc‖ ≤ h)
    (hslit : p.eval z ∈ bottleneckSlit (p.eval cc)) :
    ‖z - cc‖ < 4 / 3 * Real.sqrt (δ / ‖aHat‖) := by
  have hlocal := bottleneck_quadratic_norm_lower
    p cc hcrit aHat haHat h hdisk (z - cc) hz
  have hc : cc + (z - cc) = z := by ring
  rw [hc] at hlocal
  have hdisplacement := bottleneckSlit_norm_sub_lt (p.eval cc) (p.eval z) hv hslit
  rw [← hδ] at hdisplacement
  exact bottleneck_radius_of_quadratic_bound δ ‖aHat‖ ‖z - cc‖
    hδpos (norm_pos_iff.mpr haHat) (norm_nonneg _)
    (lt_of_le_of_lt hlocal hdisplacement)

/-- No slit preimage can lie on the boundary of the comparison disc. -/
theorem bottleneck_sphere_excludes_slit (p : Polynomial ℂ) (cc : ℂ)
    (hcrit : (Polynomial.derivative p).IsRoot cc) (hv : p.eval cc ≠ 0)
    (aHat : ℂ) (haHat : aHat ≠ 0) (h : ℝ)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h →
      ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (δ : ℝ) (hδ : δ = 1 - ‖p.eval cc‖)
    (hδsmall : δ < ‖aHat‖ * h ^ 2 / 4)
    (z : ℂ) (hz : ‖z - cc‖ = h) :
    p.eval z ∉ bottleneckSlit (p.eval cc) := by
  intro hslit
  have hlocal := bottleneck_quadratic_norm_lower
    p cc hcrit aHat haHat h hdisk (z - cc) hz.le
  have hc : cc + (z - cc) = z := by ring
  rw [hc, hz] at hlocal
  have hdisplacement := bottleneckSlit_norm_sub_lt (p.eval cc) (p.eval z) hv hslit
  rw [← hδ] at hdisplacement
  have hnonneg : 0 ≤ ‖aHat‖ * h ^ 2 := mul_nonneg (norm_nonneg _) (sq_nonneg _)
  nlinarith

/-- A preconnected set containing the centre cannot cross an excluded sphere. -/
theorem bottleneck_disc_capture (S : Set ℂ) (hS : IsPreconnected S)
    (cc : ℂ) (hcc : cc ∈ S) (h : ℝ) (hh : 0 < h)
    (havoid : ∀ z ∈ S, ‖z - cc‖ ≠ h) :
    ∀ z ∈ S, ‖z - cc‖ < h := by
  intro z hz
  by_contra hnot
  have hupper : h ≤ ‖z - cc‖ := le_of_not_gt hnot
  have hcont : ContinuousOn (fun w : ℂ => ‖w - cc‖) S :=
    (continuous_id.sub continuous_const).norm.continuousOn
  have hbetween : h ∈ Set.Icc ‖cc - cc‖ ‖z - cc‖ :=
    ⟨by simpa using hh.le, hupper⟩
  obtain ⟨w, hw, heq⟩ := hS.intermediate_value hcc hz hcont hbetween
  exact havoid w hw heq

/-- L1 follows from preconnectedness of the entire slit preimage in the component. -/
theorem bottleneck_localisation_of_preconnected
    (p : Polynomial ℂ) (cc : ℂ) (hcc : cc ∈ Omega p)
    (hcrit : (Polynomial.derivative p).IsRoot cc) (hv : p.eval cc ≠ 0)
    (aHat : ℂ) (haHat : aHat ≠ 0) (h : ℝ) (hh : 0 < h)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h →
      ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (δ : ℝ) (hδ : δ = 1 - ‖p.eval cc‖) (hδpos : 0 < δ)
    (hδsmall : δ < ‖aHat‖ * h ^ 2 / 4)
    (hpre : IsPreconnected (connectedComponentIn (Omega p) cc ∩
      (fun z => p.eval z) ⁻¹' bottleneckSlit (p.eval cc))) :
    connectedComponentIn (Omega p) cc ∩
      (fun z => p.eval z) ⁻¹' bottleneckSlit (p.eval cc) ⊆
        Metric.ball cc (4 / 3 * Real.sqrt (δ / ‖aHat‖)) := by
  let S := connectedComponentIn (Omega p) cc ∩
    (fun z => p.eval z) ⁻¹' bottleneckSlit (p.eval cc)
  have hcS : cc ∈ S :=
    ⟨mem_connectedComponentIn hcc, bottleneckSlit_self (p.eval cc) hcc⟩
  have hcapture : ∀ z ∈ S, ‖z - cc‖ < h :=
    bottleneck_disc_capture S hpre cc hcS h hh (by
      intro z hz heq
      exact bottleneck_sphere_excludes_slit p cc hcrit hv aHat haHat h
        hdisk δ hδ hδsmall z heq hz.2)
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm]
  exact bottleneck_local_slit_norm_lt p cc hcrit hv aHat haHat h hdisk
    δ hδ hδpos z (hcapture z hz).le hz.2

/-- The two endpoint distances through an intermediate point are bounded by variation. -/
theorem bottleneck_length_via_point (γ : ℝ → ℂ) (b₁ b₂ cc : ℂ)
    (hγ0 : γ 0 = b₁) (hγ1 : γ 1 = b₂)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ENNReal.ofReal (‖b₁ - cc‖ + ‖b₂ - cc‖ - 2 * ‖γ τ - cc‖) ≤ pathLength γ := by
  have hleft : ENNReal.ofReal ‖b₁ - γ τ‖ ≤ eVariationOn γ (Set.Icc 0 τ) := by
    simpa only [edist_dist, dist_eq_norm, hγ0] using
      eVariationOn.edist_le γ (show (0 : ℝ) ∈ Set.Icc 0 τ from ⟨le_rfl, hτ.1⟩)
        (show τ ∈ Set.Icc 0 τ from ⟨hτ.1, le_rfl⟩)
  have hright : ENNReal.ofReal ‖b₂ - γ τ‖ ≤ eVariationOn γ (Set.Icc τ 1) := by
    simpa only [edist_dist, dist_eq_norm, hγ1] using
      eVariationOn.edist_le γ (show (1 : ℝ) ∈ Set.Icc τ 1 from ⟨hτ.2, le_rfl⟩)
        (show τ ∈ Set.Icc τ 1 from ⟨le_rfl, hτ.2⟩)
  have hsplit : eVariationOn γ (Set.Icc 0 τ) + eVariationOn γ (Set.Icc τ 1) =
      pathLength γ := by
    simpa only [Set.univ_inter, pathLength] using
      eVariationOn.Icc_add_Icc γ (s := Set.univ) hτ.1 hτ.2 (Set.mem_univ τ)
  have hsum : ENNReal.ofReal (‖b₁ - γ τ‖ + ‖b₂ - γ τ‖) ≤ pathLength γ := by
    rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact (add_le_add hleft hright).trans_eq hsplit
  have htri₁ := norm_add_le (b₁ - γ τ) (γ τ - cc)
  have htri₂ := norm_add_le (b₂ - γ τ) (γ τ - cc)
  have heq₁ : b₁ - γ τ + (γ τ - cc) = b₁ - cc := by ring
  have heq₂ : b₂ - γ τ + (γ τ - cc) = b₂ - cc := by ring
  rw [heq₁] at htri₁
  rw [heq₂] at htri₂
  exact (ENNReal.ofReal_le_ofReal (by linarith)).trans hsum

/-- The numerical finish, with no rectifiability or continuity assumption. -/
theorem bottleneck_length_of_near_point (γ : ℝ → ℂ) (b₁ b₂ cc : ℂ)
    (hγ0 : γ 0 = b₁) (hγ1 : γ 1 = b₂) (δ : ℝ) (aHat : ℂ)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hnear : ‖γ τ - cc‖ < 4 / 3 * Real.sqrt (δ / ‖aHat‖)) :
    ENNReal.ofReal (‖b₁ - cc‖ + ‖b₂ - cc‖ -
      8 / 3 * Real.sqrt (δ / ‖aHat‖)) ≤ pathLength γ := by
  exact (ENNReal.ofReal_le_ofReal (by linarith)).trans
    (bottleneck_length_via_point γ b₁ b₂ cc hγ0 hγ1 τ hτ)

/-- The target numerical conclusion follows from a slit hit in the comparison disc. -/
theorem bottleneck_length_of_disk_hit (p : Polynomial ℂ) (cc : ℂ)
    (hcrit : (Polynomial.derivative p).IsRoot cc) (hv : p.eval cc ≠ 0)
    (b₁ b₂ : ℂ) (aHat : ℂ) (haHat : aHat ≠ 0) (h : ℝ)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h →
      ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (δ : ℝ) (hδ : δ = 1 - ‖p.eval cc‖) (hδpos : 0 < δ)
    (γ : ℝ → ℂ) (hγ0 : γ 0 = b₁) (hγ1 : γ 1 = b₂)
    (hhit : ∃ τ ∈ Set.Icc (0 : ℝ) 1, ‖γ τ - cc‖ ≤ h ∧
      p.eval (γ τ) ∈ bottleneckSlit (p.eval cc)) :
    ENNReal.ofReal (‖b₁ - cc‖ + ‖b₂ - cc‖ -
      8 / 3 * Real.sqrt (δ / ‖aHat‖)) ≤ pathLength γ := by
  obtain ⟨τ, hτ, hdisc, hslit⟩ := hhit
  exact bottleneck_length_of_near_point γ b₁ b₂ cc hγ0 hγ1 δ aHat τ hτ
    (bottleneck_local_slit_norm_lt p cc hcrit hv aHat haHat h hdisk
      δ hδ hδpos (γ τ) hdisc hslit)

/-- A covering over a simply connected base is injective along a preconnected image. -/
theorem bottleneck_covering_fibre_eq_on_preconnected
    {E B T : Type*} [TopologicalSpace E] [T2Space E]
    [TopologicalSpace B] [TopologicalSpace T]
    [SimplyConnectedSpace B] [LocPathConnectedSpace B]
    (π : E → B) (hπ : IsCoveringMap π)
    (S : Set T) (hS : IsPreconnected S) (g : T → E) (hg : ContinuousOn g S)
    (a b : T) (ha : a ∈ S) (hb : b ∈ S) (hab : π (g a) = π (g b)) :
    g a = g b := by
  obtain ⟨σ, ⟨hσa, hσπ⟩, -⟩ :=
    hπ.existsUnique_continuousMap_lifts (ContinuousMap.id B) (π (g a)) (g a) rfl
  have hsection (y : B) : π (σ y) = y := congrFun hσπ y
  have hsecond : ContinuousOn (fun t => σ (π (g t))) S :=
    σ.continuous.comp_continuousOn (hπ.continuous.comp_continuousOn hg)
  have heq : S.EqOn g (fun t => σ (π (g t))) :=
    (T2Space.isSeparatedMap π).eqOn_of_comp_eqOn
      hπ.isLocalHomeomorph.isLocallyInjective hS hg hsecond
      (fun t _ => (hsection (π (g t))).symm) ha hσa.symm
  calc
    g a = σ (π (g a)) := hσa.symm
    _ = σ (π (g b)) := congrArg σ hab
    _ = g b := (heq hb).symm

/-- The slit disc, as a subtype suitable for covering-space lifting. -/
def bottleneckSlitBase (v : ℂ) : Set ℂ :=
  {w | ‖w‖ < 1 ∧ w ∉ bottleneckSlit v}

/-- A closed-ray description of slit membership inside the open disc. -/
theorem bottleneckSlit_iff_norm (v w : ℂ) (hv : v ≠ 0) :
    w ∈ bottleneckSlit v ↔
      ‖v‖ ≤ ‖w‖ ∧ ‖w‖ < 1 ∧
        w = (‖w‖ : ℂ) * (v / (‖v‖ : ℂ)) := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hunit : ‖v / (‖v‖ : ℂ)‖ = 1 := by simp [hn]
  rw [bottleneckSlit_iff v w hv]
  constructor
  · rintro ⟨r, hr, hrone, hw⟩
    have hrnonneg : 0 ≤ r := (norm_nonneg v).trans hr
    have hwNorm : ‖w‖ = r := by
      rw [hw]
      simp [abs_of_nonneg hrnonneg, div_self hn]
    exact ⟨hwNorm.symm ▸ hr, hwNorm.symm ▸ hrone, hwNorm.symm ▸ hw⟩
  · rintro ⟨hr, hrone, hw⟩
    exact ⟨‖w‖, hr, hrone, hw⟩

/-- The slit disc is open; the slit is relatively closed in the unit disc. -/
theorem bottleneckSlitBase_isOpen (v : ℂ) (hv : v ≠ 0) :
    IsOpen (bottleneckSlitBase v) := by
  let K : Set ℂ := {w | ‖v‖ ≤ ‖w‖ ∧
    w = (‖w‖ : ℂ) * (v / (‖v‖ : ℂ))}
  have hK : IsClosed K :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_eq continuous_id (by fun_prop))
  have heq : bottleneckSlitBase v = {w : ℂ | ‖w‖ < 1} ∩ Kᶜ := by
    ext w
    change (‖w‖ < 1 ∧ w ∉ bottleneckSlit v) ↔
      ‖w‖ < 1 ∧ ¬(‖v‖ ≤ ‖w‖ ∧ w = (‖w‖ : ℂ) * (v / (‖v‖ : ℂ)))
    rw [bottleneckSlit_iff_norm v w hv]
    tauto
  rw [heq]
  exact (isOpen_lt continuous_norm continuous_const).inter hK.isOpen_compl

/-- Shrinking a point towards zero cannot introduce an intersection with the slit. -/
theorem bottleneckSlitBase_starConvex (v : ℂ) (hv : v ≠ 0) :
    StarConvex ℝ (0 : ℂ) (bottleneckSlitBase v) := by
  intro w hw a b ha hb hab
  have hbone : b ≤ 1 := by linarith
  have hnorm : ‖b • w‖ = b * ‖w‖ := by
    rw [norm_smul, Real.norm_of_nonneg hb]
  have hnormle : ‖b • w‖ ≤ ‖w‖ := by
    rw [hnorm]
    nlinarith [mul_le_mul_of_nonneg_right hbone (norm_nonneg w)]
  have hbw : b • w ∈ bottleneckSlitBase v := by
    refine ⟨hnormle.trans_lt hw.1, ?_⟩
    intro hslit
    have hbzero : b ≠ 0 := by
      intro hz
      subst b
      exact zero_not_mem_bottleneckSlit v hv (by simpa using hslit)
    have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hbzero
    have hsmul (z : ℂ) : b • z = (b : ℂ) * z := Complex.real_smul
    obtain ⟨hlower, -, hdir⟩ := (bottleneckSlit_iff_norm v (b • w) hv).mp hslit
    have hwdir : w = (‖w‖ : ℂ) * (v / (‖v‖ : ℂ)) := by
      apply mul_left_cancel₀ hbC
      calc
        (b : ℂ) * w = b • w := (hsmul w).symm
        _ = (‖b • w‖ : ℂ) * (v / (‖v‖ : ℂ)) := hdir
        _ = (b : ℂ) * ((‖w‖ : ℂ) * (v / (‖v‖ : ℂ))) := by
          rw [hnorm, Complex.ofReal_mul]
          ring
    exact hw.2 ((bottleneckSlit_iff_norm v w hv).mpr
      ⟨hlower.trans hnormle, hw.1, hwdir⟩)
  have hcollapse : a • (0 : ℂ) + b • w = b • w := by
    rw [show a • (0 : ℂ) = (a : ℂ) * 0 from Complex.real_smul, mul_zero, zero_add]
  rw [hcollapse]
  exact hbw

/-- Simple connectedness of the slit disc, derived from its explicit star-convexity. -/
theorem bottleneckSlitBase_simplyConnected (v : ℂ) (hv : v ≠ 0) :
    SimplyConnectedSpace (bottleneckSlitBase v) := by
  have hzero : (0 : ℂ) ∈ bottleneckSlitBase v :=
    ⟨by simp, zero_not_mem_bottleneckSlit v hv⟩
  letI : ContractibleSpace (bottleneckSlitBase v) :=
    (bottleneckSlitBase_starConvex v hv).contractibleSpace ⟨0, hzero⟩
  infer_instance

/-- Local path connectedness follows from openness in the complex plane. -/
theorem bottleneckSlitBase_locPathConnected (v : ℂ) (hv : v ≠ 0) :
    LocPathConnectedSpace (bottleneckSlitBase v) :=
  (bottleneckSlitBase_isOpen v hv).locPathConnectedSpace

/-- The component with the slit preimage removed. -/
def bottleneckSlitDomain (p : Polynomial ℂ) (cc : ℂ) : Set ℂ :=
  {z | z ∈ connectedComponentIn (Omega p) cc ∧
    p.eval z ∉ bottleneckSlit (p.eval cc)}

/-- The polynomial restriction used for L2. -/
def bottleneckSlitProjection (p : Polynomial ℂ) (cc : ℂ) :
    bottleneckSlitDomain p cc → bottleneckSlitBase (p.eval cc) :=
  fun z => ⟨p.eval z, ⟨connectedComponentIn_subset (Omega p) cc z.2.1, z.2.2⟩⟩

/-- A zero together with a nonzero value rules out a constant polynomial. -/
theorem bottleneck_natDegree_pos (p : Polynomial ℂ) (cc b : ℂ)
    (hv : p.eval cc ≠ 0) (hr : p.IsRoot b) : 0 < p.natDegree := by
  by_contra hnot
  have hdeg : p.natDegree = 0 := by omega
  have hpC := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have heq : p.eval cc = p.eval b := by
    rw [hpC]
    simp only [Polynomial.eval_C]
  exact hv (heq.trans hr)

/-- Zeros in the distinguished component are regular when the critical value is nonzero. -/
theorem bottleneck_root_regular (p : Polynomial ℂ) (cc b : ℂ)
    (hv : p.eval cc ≠ 0)
    (huniq : ∀ c' ∈ connectedComponentIn (Omega p) cc,
      (Polynomial.derivative p).IsRoot c' → c' = cc)
    (hb : b ∈ connectedComponentIn (Omega p) cc) (hr : p.IsRoot b) :
    (Polynomial.derivative p).eval b ≠ 0 := by
  intro hzero
  have heq : b = cc := huniq b hb hzero
  exact hv (heq ▸ hr)

/-- The polynomial derivative does not vanish on the slit-complement domain. -/
theorem bottleneck_regular_on_slitDomain (p : Polynomial ℂ) (cc : ℂ)
    (hcc : cc ∈ Omega p)
    (huniq : ∀ c' ∈ connectedComponentIn (Omega p) cc,
      (Polynomial.derivative p).IsRoot c' → c' = cc)
    (z : bottleneckSlitDomain p cc) :
    (Polynomial.derivative p).eval (z : ℂ) ≠ 0 := by
  intro hzero
  have heq : (z : ℂ) = cc := huniq z z.2.1 hzero
  apply z.2.2
  rw [heq]
  exact bottleneckSlit_self (p.eval cc) hcc

/-- L2, conditional only on the covering construction. -/
theorem bottleneck_path_meets_slit_of_covering
    (p : Polynomial ℂ) (cc : ℂ) (hv : p.eval cc ≠ 0)
    (hcover : IsCoveringMap (bottleneckSlitProjection p cc))
    (b₁ b₂ : ℂ) (hne : b₁ ≠ b₂) (hr₁ : p.IsRoot b₁) (hr₂ : p.IsRoot b₂)
    (γ : ℝ → ℂ) (hcont : ContinuousOn γ (Set.Icc 0 1))
    (hγ0 : γ 0 = b₁) (hγ1 : γ 1 = b₂)
    (hγmem : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      γ τ ∈ connectedComponentIn (Omega p) cc) :
    ∃ τ ∈ Set.Icc (0 : ℝ) 1, γ τ ∈ connectedComponentIn (Omega p) cc ∩
      (fun z => p.eval z) ⁻¹' bottleneckSlit (p.eval cc) := by
  letI : SimplyConnectedSpace (bottleneckSlitBase (p.eval cc)) :=
    bottleneckSlitBase_simplyConnected (p.eval cc) hv
  letI : LocPathConnectedSpace (bottleneckSlitBase (p.eval cc)) :=
    bottleneckSlitBase_locPathConnected (p.eval cc) hv
  by_contra hno
  have havoid (t : Set.Icc (0 : ℝ) 1) :
      p.eval (γ t) ∉ bottleneckSlit (p.eval cc) := by
    intro ht
    exact hno ⟨t, t.2, hγmem t t.2, ht⟩
  let g : Set.Icc (0 : ℝ) 1 → bottleneckSlitDomain p cc :=
    fun t => ⟨γ t, ⟨hγmem t t.2, havoid t⟩⟩
  have hg : Continuous g :=
    (continuousOn_iff_continuous_restrict.mp hcont).subtype_mk _
  let t₀ : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  let t₁ : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  letI : PreconnectedSpace (Set.Icc (0 : ℝ) 1) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  have hbase : bottleneckSlitProjection p cc (g t₀) =
      bottleneckSlitProjection p cc (g t₁) := by
    apply Subtype.ext
    change p.eval (γ 0) = p.eval (γ 1)
    rw [hγ0, hγ1]
    exact (show p.eval b₁ = 0 from hr₁).trans (show p.eval b₂ = 0 from hr₂).symm
  have heq := bottleneck_covering_fibre_eq_on_preconnected
    (bottleneckSlitProjection p cc) hcover Set.univ isPreconnected_univ
    g hg.continuousOn t₀ t₁ (Set.mem_univ _) (Set.mem_univ _) hbase
  have hend : γ 0 = γ 1 := congrArg Subtype.val heq
  exact hne (hγ0.symm.trans (hend.trans hγ1))

/-- Explicit composition of the topological and numerical reductions. -/
theorem bottleneck_length_of_slit_topology
    (p : Polynomial ℂ) (cc : ℂ) (hcc : cc ∈ Omega p)
    (hcrit : (Polynomial.derivative p).IsRoot cc) (hv : p.eval cc ≠ 0)
    (b₁ b₂ : ℂ) (aHat : ℂ) (haHat : aHat ≠ 0) (h : ℝ) (hh : 0 < h)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h →
      ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (δ : ℝ) (hδ : δ = 1 - ‖p.eval cc‖) (hδpos : 0 < δ)
    (hδsmall : δ < ‖aHat‖ * h ^ 2 / 4)
    (γ : ℝ → ℂ) (hγ0 : γ 0 = b₁) (hγ1 : γ 1 = b₂)
    (hpre : IsPreconnected (connectedComponentIn (Omega p) cc ∩
      (fun z => p.eval z) ⁻¹' bottleneckSlit (p.eval cc)))
    (hmeets : ∃ τ ∈ Set.Icc (0 : ℝ) 1, γ τ ∈ connectedComponentIn (Omega p) cc ∩
      (fun z => p.eval z) ⁻¹' bottleneckSlit (p.eval cc)) :
    ENNReal.ofReal (‖b₁ - cc‖ + ‖b₂ - cc‖ -
      8 / 3 * Real.sqrt (δ / ‖aHat‖)) ≤ pathLength γ := by
  obtain ⟨τ, hτ, hz⟩ := hmeets
  have hlocal := bottleneck_localisation_of_preconnected p cc hcc hcrit hv
    aHat haHat h hh hdisk δ hδ hδpos hδsmall hpre hz
  rw [Metric.mem_ball, dist_eq_norm] at hlocal
  exact bottleneck_length_of_near_point γ b₁ b₂ cc hγ0 hγ1 δ aHat τ hτ hlocal

/-- The full numerical conclusion with the two unresolved topological inputs explicit. -/
theorem bottleneck_length_of_covering_and_preconnected
    (p : Polynomial ℂ) (cc : ℂ) (hcc : cc ∈ Omega p)
    (hcrit : (Polynomial.derivative p).IsRoot cc) (hv : p.eval cc ≠ 0)
    (b₁ b₂ : ℂ) (hne : b₁ ≠ b₂) (hr₁ : p.IsRoot b₁) (hr₂ : p.IsRoot b₂)
    (aHat : ℂ) (haHat : aHat ≠ 0) (h : ℝ) (hh : 0 < h)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h →
      ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (δ : ℝ) (hδ : δ = 1 - ‖p.eval cc‖) (hδpos : 0 < δ)
    (hδsmall : δ < ‖aHat‖ * h ^ 2 / 4)
    (γ : ℝ → ℂ) (hcont : ContinuousOn γ (Set.Icc 0 1))
    (hγ0 : γ 0 = b₁) (hγ1 : γ 1 = b₂)
    (hγmem : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      γ τ ∈ connectedComponentIn (Omega p) cc)
    (hcover : IsCoveringMap (bottleneckSlitProjection p cc))
    (hpre : IsPreconnected (connectedComponentIn (Omega p) cc ∩
      (fun z => p.eval z) ⁻¹' bottleneckSlit (p.eval cc))) :
    ENNReal.ofReal (‖b₁ - cc‖ + ‖b₂ - cc‖ -
      8 / 3 * Real.sqrt (δ / ‖aHat‖)) ≤ pathLength γ := by
  exact bottleneck_length_of_slit_topology p cc hcc hcrit hv b₁ b₂ aHat haHat h hh
    hdisk δ hδ hδpos hδsmall γ hγ0 hγ1 hpre
    (bottleneck_path_meets_slit_of_covering p cc hv hcover b₁ b₂ hne hr₁ hr₂
      γ hcont hγ0 hγ1 hγmem)

section Probe
end Probe

/-! ## Two complex-analysis tools

Mathlib v4.29.1 has neither Rouché's theorem nor the argument principle, and
`DiffContOnCl.ball_subset_image_closedBall` loses a factor of two that the
constants of Corollary 2.4 cannot afford.  Both tools are proved here instead
from the open mapping theorem and the maximum modulus principle. -/

/-- If `‖f z - f c‖ ≥ ε` on the sphere of radius `r` about `c`, then the image of
the *open* ball under `f` contains the whole ball of radius `ε` about `f c` — no
factor of two lost.  The image of the closed ball is compact, the image of the
open ball is open, and they differ only inside the image of the sphere, which
misses `ball (f c) ε`; connectedness of that ball then forces it into the image
of the open ball. -/
theorem bottleneck_ball_subset_image (f : ℂ → ℂ) (c : ℂ) (r ε : ℝ) (hr : 0 < r)
    (hcont : ContinuousOn f (Metric.closedBall c r))
    (himg : IsOpen (f '' Metric.ball c r))
    (hsphere : ∀ z ∈ Metric.sphere c r, ε ≤ ‖f z - f c‖) :
    Metric.ball (f c) ε ⊆ f '' Metric.ball c r := by
  have hclosed : IsClosed (f '' Metric.closedBall c r) :=
    ((isCompact_closedBall c r).image_of_continuousOn hcont).isClosed
  -- inside `ball (f c) ε` the two images agree
  have himage : ∀ y ∈ Metric.ball (f c) ε,
      y ∈ f '' Metric.closedBall c r → y ∈ f '' Metric.ball c r := by
    rintro y hy ⟨z, hz, rfl⟩
    refine ⟨z, ?_, rfl⟩
    rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hz) with hlt | heq
    · exact Metric.mem_ball.mpr hlt
    · exfalso
      have hzs : z ∈ Metric.sphere c r := Metric.mem_sphere.mpr heq
      rw [Metric.mem_ball, dist_eq_norm] at hy
      exact absurd (hsphere z hzs) (not_le.mpr hy)
  intro w hw
  by_contra hwnot
  have hεpos : 0 < ε := lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp hw)
  have hconn : IsPreconnected (Metric.ball (f c) ε) :=
    (convex_ball (f c) ε).isPreconnected
  have hcover : Metric.ball (f c) ε ⊆
      (f '' Metric.ball c r) ∪ (f '' Metric.closedBall c r)ᶜ := by
    intro y hy
    by_cases hy' : y ∈ f '' Metric.closedBall c r
    · exact Or.inl (himage y hy hy')
    · exact Or.inr hy'
  have h1 : (Metric.ball (f c) ε ∩ f '' Metric.ball c r).Nonempty :=
    ⟨f c, Metric.mem_ball_self hεpos, ⟨c, Metric.mem_ball_self hr, rfl⟩⟩
  have h2 : (Metric.ball (f c) ε ∩ (f '' Metric.closedBall c r)ᶜ).Nonempty :=
    ⟨w, hw, fun hmem => hwnot (himage w hw hmem)⟩
  obtain ⟨y, -, hy1, hy2⟩ :=
    hconn _ _ himg hclosed.isOpen_compl hcover h1 h2
  exact hy2 (Set.image_mono Metric.ball_subset_closedBall hy1)

/-- A component-free minimum-modulus argument.  If `f` is holomorphic on an open
set `V` and vanishes there only at `c`, then each sublevel set `‖f‖ < m` whose
closure stays inside `V` is preconnected: a piece not containing `c` would have
`f` nonvanishing on its closure, and the maximum modulus principle applied to
`f⁻¹` would put the minimum of `‖f‖` on its frontier, where `‖f‖ ≥ m`. -/
theorem bottleneck_sublevel_isPreconnected (f : ℂ → ℂ) (V : Set ℂ) (hV : IsOpen V)
    (hdiff : DifferentiableOn ℂ f V) (c : ℂ) (hc : c ∈ V) (m : ℝ) (hm : ‖f c‖ < m)
    (hzero : ∀ z ∈ V, f z = 0 → z = c)
    (hbdd : Bornology.IsBounded {z | z ∈ V ∧ ‖f z‖ < m})
    (hcl : closure {z | z ∈ V ∧ ‖f z‖ < m} ⊆ V) :
    IsPreconnected {z | z ∈ V ∧ ‖f z‖ < m} := by
  set Y : Set ℂ := {z | z ∈ V ∧ ‖f z‖ < m} with hYdef
  have hfcont : ContinuousOn f V := hdiff.continuousOn
  have hYopen : IsOpen Y :=
    hfcont.isOpen_inter_preimage hV (isOpen_lt continuous_norm continuous_const)
  have hcY : c ∈ Y := ⟨hc, hm⟩
  have key : ∀ u v : Set ℂ, IsOpen u → IsOpen v → Y ⊆ u ∪ v → c ∈ u →
      Y ∩ (u ∩ v) = ∅ → (Y ∩ v).Nonempty → False := by
    intro u v hu hv hsub hcu hempty hne
    have hmeet : ∀ x : ℂ, x ∈ Y → x ∈ u → x ∈ v → False := by
      intro x hxY hxu hxv
      exact Set.eq_empty_iff_forall_notMem.mp hempty x ⟨hxY, hxu, hxv⟩
    set Y₁ : Set ℂ := Y ∩ v with hY₁def
    have hY₁open : IsOpen Y₁ := hYopen.inter hv
    have hY₁sub : Y₁ ⊆ Y := Set.inter_subset_left
    have hclY₁ : ∀ w, w ∈ closure Y₁ → w ∈ Y → w ∈ Y₁ := by
      intro w hwc hwY
      by_contra hwn
      have hwu : u ∈ nhds w := by
        rcases hsub hwY with hwu | hwv
        · exact hu.mem_nhds hwu
        · exact absurd ⟨hwY, hwv⟩ hwn
      obtain ⟨x, hxu, hxY, hxv⟩ := mem_closure_iff_nhds.mp hwc u hwu
      exact hmeet x hxY hxu hxv
    have hcnot : c ∉ closure Y₁ := by
      intro hcc
      obtain ⟨x, hxu, hxY, hxv⟩ := mem_closure_iff_nhds.mp hcc u (hu.mem_nhds hcu)
      exact hmeet x hxY hxu hxv
    have hclsub : closure Y₁ ⊆ V :=
      (closure_mono hY₁sub).trans hcl
    have hfne : ∀ w ∈ closure Y₁, f w ≠ 0 := by
      intro w hw hw0
      exact hcnot ((hzero w (hclsub hw) hw0) ▸ hw)
    have hdc : DiffContOnCl ℂ (fun w => (f w)⁻¹) Y₁ := by
      refine ⟨(hdiff.mono (fun z hz => (hY₁sub hz).1)).inv
        (fun w hw => hfne w (subset_closure hw)), ?_⟩
      exact (hfcont.mono hclsub).inv₀ hfne
    obtain ⟨z, hzf, hzmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm
      (hbdd.subset hY₁sub) hne hdc
    rw [hY₁open.frontier_eq] at hzf
    obtain ⟨hzcl, hznotY₁⟩ := hzf
    have hzV : z ∈ V := hclsub hzcl
    have hzm : m ≤ ‖f z‖ := by
      by_contra hlt
      exact hznotY₁ (hclY₁ z hzcl ⟨hzV, lt_of_not_ge hlt⟩)
    obtain ⟨x, hxY, hxv⟩ := hne
    have hxcl : x ∈ closure Y₁ := subset_closure ⟨hxY, hxv⟩
    have hmax : ‖(f x)⁻¹‖ ≤ ‖(f z)⁻¹‖ := hzmax hxcl
    rw [norm_inv, norm_inv] at hmax
    have hxpos : 0 < ‖f x‖ := norm_pos_iff.mpr (hfne x hxcl)
    have hzpos : 0 < ‖f z‖ := norm_pos_iff.mpr (hfne z hzcl)
    have : ‖f z‖ ≤ ‖f x‖ := (inv_le_inv₀ hxpos hzpos).mp hmax
    exact absurd hxY.2 (not_lt.mpr (hzm.trans this))
  intro u v hu hv hsub h1 h2
  by_contra hcon
  have hempty : Y ∩ (u ∩ v) = ∅ := Set.not_nonempty_iff_eq_empty.mp hcon
  rcases hsub hcY with hcu | hcv
  · exact absurd (key u v hu hv hsub hcu hempty h2) not_false
  · refine absurd (key v u hv hu (fun z hz => (hsub hz).symm) hcv ?_ h1) not_false
    rw [Set.inter_comm u v] at hempty
    exact hempty

/-! ## The quadratic coordinate `ψ` of Corollary 2.4

The paper's inverse quadratic coordinate `χ` is built from the holomorphic
square root of `𝒜(z)/â`, which exists because the disk criterion `hdisk` puts
that quotient in `closedBall 1 (1/4)`, well inside `Complex.slitPlane`. -/

/-- The normalised quadratic factor `𝒜(z)/â`. -/
def bottleneckQuot (p : Polynomial ℂ) (cc aHat z : ℂ) : ℂ :=
  (shiftQuad p cc).eval z / aHat

/-- The paper's quadratic coordinate `ψ(z) = z √(𝒜(z)/â)`.  It satisfies
`p (cc + z) - p cc = â ψ(z)²`, and on the disk-criterion radius it is comparable
to `z`, so it separates the two branches of `p` at the critical point. -/
def bottleneckPsi (p : Polynomial ℂ) (cc aHat z : ℂ) : ℂ :=
  z * Complex.sqrt (bottleneckQuot p cc aHat z)

/-- The open set on which `ψ` is holomorphic. -/
def bottleneckPsiDomain (p : Polynomial ℂ) (cc aHat : ℂ) : Set ℂ :=
  bottleneckQuot p cc aHat ⁻¹' Complex.slitPlane

theorem bottleneckQuot_continuous (p : Polynomial ℂ) (cc aHat : ℂ) :
    Continuous (bottleneckQuot p cc aHat) :=
  (Polynomial.continuous _).div_const aHat

theorem bottleneckPsiDomain_isOpen (p : Polynomial ℂ) (cc aHat : ℂ) :
    IsOpen (bottleneckPsiDomain p cc aHat) :=
  Complex.isOpen_slitPlane.preimage (bottleneckQuot_continuous p cc aHat)

theorem bottleneck_sqrt_sq (w : ℂ) : Complex.sqrt w ^ 2 = w := by
  have := Complex.cpow_nat_inv_pow w (n := 2) (by norm_num)
  simpa [Complex.sqrt] using this

/-- The disk criterion bounds the normalised quadratic factor between `3/4` and
`5/4` in modulus. -/
theorem bottleneck_quot_norm_bounds (p : Polynomial ℂ) (cc aHat : ℂ) (h : ℝ)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (z : ℂ) (hz : ‖z‖ ≤ h) :
    3 / 4 ≤ ‖bottleneckQuot p cc aHat z‖ ∧ ‖bottleneckQuot p cc aHat z‖ ≤ 5 / 4 := by
  have hd : ‖bottleneckQuot p cc aHat z - 1‖ ≤ 1 / 4 := hdisk z hz
  have h1 : ‖bottleneckQuot p cc aHat z‖ - 1 ≤ ‖bottleneckQuot p cc aHat z - 1‖ := by
    simpa using norm_sub_norm_le (bottleneckQuot p cc aHat z) (1 : ℂ)
  have h2 : 1 - ‖bottleneckQuot p cc aHat z‖ ≤ ‖bottleneckQuot p cc aHat z - 1‖ := by
    have hx := norm_sub_norm_le (1 : ℂ) (bottleneckQuot p cc aHat z)
    rw [norm_sub_rev] at hx
    simpa using hx
  exact ⟨by linarith, by linarith⟩

/-- The normalised quadratic factor stays in the slit plane, so it has a
holomorphic square root. -/
theorem bottleneck_quot_mem_slitPlane (p : Polynomial ℂ) (cc aHat : ℂ) (h : ℝ)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (z : ℂ) (hz : ‖z‖ ≤ h) :
    bottleneckQuot p cc aHat z ∈ Complex.slitPlane := by
  have hd : ‖bottleneckQuot p cc aHat z - 1‖ ≤ 1 / 4 := hdisk z hz
  have hre : |(bottleneckQuot p cc aHat z - 1).re| ≤ ‖bottleneckQuot p cc aHat z - 1‖ :=
    Complex.abs_re_le_norm _
  have hsub : (bottleneckQuot p cc aHat z - 1).re = (bottleneckQuot p cc aHat z).re - 1 := by
    simp
  rw [hsub] at hre
  have hbounds := abs_le.mp hre
  exact Or.inl (by linarith [hbounds.1])

theorem bottleneck_closedBall_subset_psiDomain (p : Polynomial ℂ) (cc aHat : ℂ) (h : ℝ)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4) :
    Metric.closedBall (0 : ℂ) h ⊆ bottleneckPsiDomain p cc aHat := by
  intro z hz
  exact bottleneck_quot_mem_slitPlane p cc aHat h hdisk z
    (by simpa [Metric.mem_closedBall, dist_zero_right] using hz)

/-- Paper (2.6): the exact quadratic normal form of `p` at the critical point. -/
theorem bottleneck_psi_sq (p : Polynomial ℂ) (cc : ℂ)
    (hcrit : (Polynomial.derivative p).IsRoot cc) (aHat : ℂ) (haHat : aHat ≠ 0) (z : ℂ) :
    p.eval (cc + z) - p.eval cc = aHat * bottleneckPsi p cc aHat z ^ 2 := by
  have hsq : Complex.sqrt (bottleneckQuot p cc aHat z) ^ 2 = bottleneckQuot p cc aHat z :=
    bottleneck_sqrt_sq _
  rw [bottleneck_eval_shiftQuad p cc hcrit z]
  unfold bottleneckPsi
  rw [mul_pow, hsq]
  unfold bottleneckQuot
  field_simp
  ring

theorem bottleneck_sqrt_norm_bounds (p : Polynomial ℂ) (cc aHat : ℂ) (h : ℝ)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (z : ℂ) (hz : ‖z‖ ≤ h) :
    4 / 5 ≤ ‖Complex.sqrt (bottleneckQuot p cc aHat z)‖ ∧
      ‖Complex.sqrt (bottleneckQuot p cc aHat z)‖ ≤ 9 / 8 := by
  obtain ⟨hlo, hhi⟩ := bottleneck_quot_norm_bounds p cc aHat h hdisk z hz
  have hsq : ‖Complex.sqrt (bottleneckQuot p cc aHat z)‖ ^ 2 =
      ‖bottleneckQuot p cc aHat z‖ := by
    rw [← norm_pow, bottleneck_sqrt_sq]
  have hnn : 0 ≤ ‖Complex.sqrt (bottleneckQuot p cc aHat z)‖ := norm_nonneg _
  constructor
  · nlinarith
  · nlinarith

theorem bottleneck_psi_norm_lower (p : Polynomial ℂ) (cc aHat : ℂ) (h : ℝ)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (z : ℂ) (hz : ‖z‖ ≤ h) : 4 / 5 * ‖z‖ ≤ ‖bottleneckPsi p cc aHat z‖ := by
  have hb := (bottleneck_sqrt_norm_bounds p cc aHat h hdisk z hz).1
  have hnorm : ‖bottleneckPsi p cc aHat z‖ =
      ‖z‖ * ‖Complex.sqrt (bottleneckQuot p cc aHat z)‖ := by
    unfold bottleneckPsi; rw [norm_mul]
  rw [hnorm]
  nlinarith [norm_nonneg z]

theorem bottleneck_psi_differentiableOn (p : Polynomial ℂ) (cc aHat : ℂ) :
    DifferentiableOn ℂ (bottleneckPsi p cc aHat) (bottleneckPsiDomain p cc aHat) := by
  intro z hz
  refine DifferentiableAt.differentiableWithinAt ?_
  have hq : DifferentiableAt ℂ (bottleneckQuot p cc aHat) z :=
    (((Polynomial.differentiable _).div_const aHat)).differentiableAt
  have h2 : DifferentiableAt ℂ (fun w => Complex.sqrt (bottleneckQuot p cc aHat w)) z :=
    (Complex.differentiableAt_sqrt hz).comp z hq
  have hid : DifferentiableAt ℂ (fun w : ℂ => w) z := differentiableAt_id
  exact hid.mul h2

/-- No factor of two lost: `ψ` maps the open `h`-disc onto a set containing the
disc of radius `(4/5) h`. -/
theorem bottleneck_psi_image (p : Polynomial ℂ) (cc aHat : ℂ) (h : ℝ) (hh : 0 < h)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4) :
    Metric.ball (0 : ℂ) (4 / 5 * h) ⊆ bottleneckPsi p cc aHat '' Metric.ball 0 h := by
  have hsub := bottleneck_closedBall_subset_psiDomain p cc aHat h hdisk
  have hdiffOn := bottleneck_psi_differentiableOn p cc aHat
  have hcont : ContinuousOn (bottleneckPsi p cc aHat) (Metric.closedBall 0 h) :=
    hdiffOn.continuousOn.mono hsub
  have hzero : bottleneckPsi p cc aHat 0 = 0 := by simp [bottleneckPsi]
  have hAn : AnalyticOnNhd ℂ (bottleneckPsi p cc aHat) (Metric.ball (0 : ℂ) h) := by
    have hall := hdiffOn.analyticOnNhd (bottleneckPsiDomain_isOpen p cc aHat)
    exact fun x hx => hall x (hsub (Metric.ball_subset_closedBall hx))
  -- `ψ` is not constant on the disc: it vanishes only at the origin
  have hz₁norm : ‖((h / 2 : ℝ) : ℂ)‖ = h / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (show (0 : ℝ) < h / 2 by linarith)]
  have hz₁ : ((h / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) h := by
    rw [Metric.mem_ball, dist_zero_right, hz₁norm]
    linarith
  have himg : IsOpen (bottleneckPsi p cc aHat '' Metric.ball 0 h) := by
    rcases hAn.is_constant_or_isOpen (convex_ball (0 : ℂ) h).isPreconnected with ⟨w, hw⟩ | hopen
    · exfalso
      have h0 : bottleneckPsi p cc aHat 0 = w := hw 0 (Metric.mem_ball_self hh)
      have h1 : bottleneckPsi p cc aHat ((h / 2 : ℝ) : ℂ) = w := hw _ hz₁
      have hlow := bottleneck_psi_norm_lower p cc aHat h hdisk ((h / 2 : ℝ) : ℂ)
        (by rw [hz₁norm]; linarith)
      rw [hz₁norm, h1, ← h0, hzero] at hlow
      simp at hlow
      linarith
    · exact hopen _ (subset_refl _) Metric.isOpen_ball
  have hsphere : ∀ z ∈ Metric.sphere (0 : ℂ) h,
      4 / 5 * h ≤ ‖bottleneckPsi p cc aHat z - bottleneckPsi p cc aHat 0‖ := by
    intro z hz
    have hzn : ‖z‖ = h := by simpa [Metric.mem_sphere, dist_zero_right] using hz
    rw [hzero, sub_zero]
    have hlow := bottleneck_psi_norm_lower p cc aHat h hdisk z (le_of_eq hzn)
    rwa [hzn] at hlow
  have hmain := bottleneck_ball_subset_image (bottleneckPsi p cc aHat) 0 h (4 / 5 * h)
    hh hcont himg hsphere
  rwa [hzero] at hmain

/-- The two branches: every small value `η` and its negative are attained by `ψ`
inside the `h`-disc, giving two distinct preimages of `p cc + â η²` under `p`. -/
theorem bottleneck_two_preimages (p : Polynomial ℂ) (cc aHat : ℂ) (h : ℝ) (hh : 0 < h)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (η : ℂ) (hη : ‖η‖ < 4 / 5 * h) :
    ∃ zp ∈ Metric.ball (0 : ℂ) h, ∃ zm ∈ Metric.ball (0 : ℂ) h,
      bottleneckPsi p cc aHat zp = η ∧ bottleneckPsi p cc aHat zm = -η := by
  have himg := bottleneck_psi_image p cc aHat h hh hdisk
  obtain ⟨zp, hzp, hvp⟩ := himg (by simpa [Metric.mem_ball, dist_zero_right] using hη)
  obtain ⟨zm, hzm, hvm⟩ :=
    himg (show -η ∈ Metric.ball (0 : ℂ) (4 / 5 * h) by
      simpa [Metric.mem_ball, dist_zero_right] using hη)
  exact ⟨zp, hzp, zm, hzm, hvp, hvm⟩

/-! ## The two local preimages lie in the distinguished component

Both preimages produced by `bottleneck_two_preimages` sit inside the sublevel
set `‖ψ‖ < s`, on which `‖p - p cc‖ = ‖â‖ ‖ψ‖² < δ`, so that sublevel set lies
inside the lemniscate.  It is preconnected by the minimum-modulus tool, and it
contains `0`; so its translate by `cc` is a preconnected subset of `Ω(p)`
through `cc`, hence inside the component. -/

/-- The sublevel set of `‖ψ‖` that joins the two local preimages to `cc`. -/
def bottleneckNear (p : Polynomial ℂ) (cc aHat : ℂ) (h s : ℝ) : Set ℂ :=
  {z | z ∈ Metric.ball (0 : ℂ) h ∧ ‖bottleneckPsi p cc aHat z‖ < s}

theorem bottleneckNear_isPreconnected (p : Polynomial ℂ) (cc aHat : ℂ) (h s : ℝ)
    (hh : 0 < h) (hs : 0 < s) (hsh : 5 / 4 * s < h)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4) :
    IsPreconnected (bottleneckNear p cc aHat h s) := by
  have hballsub : Metric.ball (0 : ℂ) h ⊆ bottleneckPsiDomain p cc aHat :=
    Metric.ball_subset_closedBall.trans
      (bottleneck_closedBall_subset_psiDomain p cc aHat h hdisk)
  have hdiff : DifferentiableOn ℂ (bottleneckPsi p cc aHat) (Metric.ball (0 : ℂ) h) :=
    (bottleneck_psi_differentiableOn p cc aHat).mono hballsub
  have hlow : ∀ z ∈ Metric.ball (0 : ℂ) h, 4 / 5 * ‖z‖ ≤ ‖bottleneckPsi p cc aHat z‖ := by
    intro z hz
    exact bottleneck_psi_norm_lower p cc aHat h hdisk z
      (le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hz))
  have hsub : bottleneckNear p cc aHat h s ⊆ Metric.closedBall (0 : ℂ) (5 / 4 * s) := by
    intro z hz
    have h1 := hlow z hz.1
    have h2 := hz.2
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  unfold bottleneckNear
  refine bottleneck_sublevel_isPreconnected (bottleneckPsi p cc aHat)
    (Metric.ball (0 : ℂ) h) Metric.isOpen_ball hdiff 0 (Metric.mem_ball_self hh) s ?_ ?_ ?_ ?_
  · simpa [bottleneckPsi] using hs
  · intro z hz hz0
    have hl := hlow z hz
    rw [hz0, norm_zero] at hl
    exact norm_le_zero_iff.mp (by linarith [norm_nonneg z])
  · exact Metric.isBounded_closedBall.subset hsub
  · exact (closure_minimal hsub Metric.isClosed_closedBall).trans
      (Metric.closedBall_subset_ball hsh)

theorem bottleneckNear_shift_subset (p : Polynomial ℂ) (cc aHat : ℂ)
    (hcrit : (Polynomial.derivative p).IsRoot cc) (haHat : aHat ≠ 0)
    (h s δ : ℝ) (hh : 0 < h) (hs : 0 < s) (hsh : 5 / 4 * s < h)
    (hsδ : ‖aHat‖ * s ^ 2 ≤ δ) (hδ : δ = 1 - ‖p.eval cc‖)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4) :
    (fun z => cc + z) '' bottleneckNear p cc aHat h s ⊆
      connectedComponentIn (Omega p) cc := by
  have hpre := bottleneckNear_isPreconnected p cc aHat h s hh hs hsh hdisk
  have himgpre : IsPreconnected ((fun z => cc + z) '' bottleneckNear p cc aHat h s) :=
    hpre.image _ (by fun_prop)
  have hmem : cc ∈ (fun z => cc + z) '' bottleneckNear p cc aHat h s :=
    ⟨0, ⟨Metric.mem_ball_self hh, by simpa [bottleneckPsi] using hs⟩, by simp⟩
  refine himgpre.subset_connectedComponentIn hmem ?_
  rintro _ ⟨z, hz, rfl⟩
  have hval : p.eval (cc + z) - p.eval cc = aHat * bottleneckPsi p cc aHat z ^ 2 :=
    bottleneck_psi_sq p cc hcrit aHat haHat z
  have hnorm : ‖p.eval (cc + z) - p.eval cc‖ = ‖aHat‖ * ‖bottleneckPsi p cc aHat z‖ ^ 2 := by
    rw [hval, norm_mul, norm_pow]
  have htri : ‖p.eval (cc + z)‖ ≤ ‖p.eval cc‖ + ‖p.eval (cc + z) - p.eval cc‖ := by
    simpa using norm_add_le (p.eval cc) (p.eval (cc + z) - p.eval cc)
  have hpos : 0 < ‖aHat‖ := norm_pos_iff.mpr haHat
  have hlt : ‖aHat‖ * ‖bottleneckPsi p cc aHat z‖ ^ 2 < δ := by
    have h1 := hz.2
    have hnn := norm_nonneg (bottleneckPsi p cc aHat z)
    have hsq : ‖bottleneckPsi p cc aHat z‖ ^ 2 < s ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr h1)
        (show (0 : ℝ) < s + ‖bottleneckPsi p cc aHat z‖ by linarith)]
    have := mul_lt_mul_of_pos_left hsq hpos
    linarith
  show ‖p.eval (cc + z)‖ < 1
  rw [hnorm] at htri
  linarith

/-! ## The covering hypothesis, discharged

`hcover` in `bottleneck_length_of_covering_and_preconnected` is the statement
that `p` restricted to the slit complement inside the distinguished component is
a covering map over the slit disc.  `PROOF.md` §2 gives the argument: the
restriction is proper (a polynomial is a proper map, the component is relatively
closed in the lemniscate) and a local homeomorphism (`huniq` puts the only
critical point at `cc`, whose value `p cc` is removed with the slit), and a
proper local homeomorphism out of a Hausdorff space is a covering map, which is
slice S2's `s2_isCoveringMap_of_isProperMap_of_isLocalHomeomorph`. -/

/-- The slit-complement domain sits inside the preimage of the slit disc. -/
theorem bottleneckSlitDomain_subset (p : Polynomial ℂ) (cc : ℂ) :
    bottleneckSlitDomain p cc ⊆
      (fun z => p.eval z) ⁻¹' bottleneckSlitBase (p.eval cc) := by
  rintro z ⟨hU, hJ⟩
  exact ⟨connectedComponentIn_subset (Omega p) cc hU, hJ⟩

/-- The slit-complement domain is exactly the part of that preimage lying in the
distinguished component. -/
theorem bottleneckSlitDomain_eq (p : Polynomial ℂ) (cc : ℂ) :
    bottleneckSlitDomain p cc =
      connectedComponentIn (Omega p) cc ∩
        (fun z => p.eval z) ⁻¹' bottleneckSlitBase (p.eval cc) := by
  ext z
  constructor
  · rintro ⟨hU, hJ⟩
    exact ⟨hU, connectedComponentIn_subset (Omega p) cc hU, hJ⟩
  · rintro ⟨hU, -, hJ⟩
    exact ⟨hU, hJ⟩

/-- The slit-complement domain is open. -/
theorem bottleneckSlitDomain_isOpen (p : Polynomial ℂ) (cc : ℂ)
    (hv : p.eval cc ≠ 0) : IsOpen (bottleneckSlitDomain p cc) := by
  have hOopen : IsOpen (Omega p) :=
    isOpen_lt p.continuous.norm continuous_const
  rw [bottleneckSlitDomain_eq]
  exact hOopen.connectedComponentIn.inter
    ((bottleneckSlitBase_isOpen (p.eval cc) hv).preimage p.continuous)

/-- The inclusion of the slit-complement domain into the preimage of the slit
disc is a closed embedding: the component is relatively closed in the
lemniscate, and the preimage of the slit disc is contained in the lemniscate. -/
theorem bottleneck_isClosedEmbedding_slitDomain (p : Polynomial ℂ) (cc : ℂ)
    (hcc : cc ∈ Omega p) :
    IsClosedEmbedding (Set.inclusion (bottleneckSlitDomain_subset p cc)) := by
  refine ⟨IsEmbedding.inclusion (bottleneckSlitDomain_subset p cc), ?_⟩
  have hcomp : Continuous (fun x :
      ((fun z => p.eval z) ⁻¹' bottleneckSlitBase (p.eval cc)) =>
        (⟨(x : ℂ), x.2.1⟩ : Omega p)) :=
    continuous_subtype_val.subtype_mk _
  have hUclosed : IsClosed
      {y : Omega p | (y : ℂ) ∈ connectedComponentIn (Omega p) cc} := by
    have := (s2_isClosedEmbedding_componentIn_inclusion hcc).isClosed_range
    rwa [Set.range_inclusion] at this
  have hset : Set.range (Set.inclusion (bottleneckSlitDomain_subset p cc)) =
      (fun x : ((fun z => p.eval z) ⁻¹' bottleneckSlitBase (p.eval cc)) =>
        (⟨(x : ℂ), x.2.1⟩ : Omega p)) ⁻¹'
        {y : Omega p | (y : ℂ) ∈ connectedComponentIn (Omega p) cc} := by
    rw [Set.range_inclusion]
    ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2.2⟩⟩
  rw [hset]
  exact hUclosed.preimage hcomp

/-- The restriction of `p` to the slit complement is a proper map. -/
theorem bottleneck_isProperMap_projection (p : Polynomial ℂ) (cc : ℂ)
    (hcc : cc ∈ Omega p) (hdeg : 0 < p.natDegree) :
    IsProperMap (bottleneckSlitProjection p cc) := by
  have hpdegree : 0 < p.degree := by
    apply lt_of_not_ge
    intro hle
    exact (not_le_of_gt hdeg) (Polynomial.natDegree_le_of_degree_le hle)
  have hglobal : IsProperMap p.eval := p.isProperMap_eval hpdegree
  exact (hglobal.restrictPreimage (bottleneckSlitBase (p.eval cc))).comp
    (bottleneck_isClosedEmbedding_slitDomain p cc hcc).isProperMap

/-- The restriction of `p` to the slit complement is a local homeomorphism:
`huniq` confines the critical points of `p` in the component to `cc`, and `cc`
itself is removed because its value lies on the slit. -/
theorem bottleneck_isLocalHomeomorph_projection (p : Polynomial ℂ) (cc : ℂ)
    (hcc : cc ∈ Omega p) (hv : p.eval cc ≠ 0)
    (huniq : ∀ c' ∈ connectedComponentIn (Omega p) cc,
      (Polynomial.derivative p).IsRoot c' → c' = cc) :
    IsLocalHomeomorph (bottleneckSlitProjection p cc) := by
  have hderiv : ∀ u ∈ bottleneckSlitDomain p cc,
      (Polynomial.derivative p).eval u ≠ 0 := by
    intro u hu
    exact bottleneck_regular_on_slitDomain p cc hcc huniq ⟨u, hu⟩
  have hpLocal : IsLocalHomeomorphOn p.eval (bottleneckSlitDomain p cc) := by
    intro u hu
    have hd := (p.hasStrictDerivAt u).hasStrictFDerivAt_equiv (hderiv u hu)
    exact ⟨hd.toOpenPartialHomeomorph p.eval,
      hd.mem_toOpenPartialHomeomorph_source, rfl⟩
  have hDomInc : IsLocalHomeomorph
      (Subtype.val : bottleneckSlitDomain p cc → ℂ) :=
    (bottleneckSlitDomain_isOpen p cc hv).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hscalar : IsLocalHomeomorph
      (fun z : bottleneckSlitDomain p cc => p.eval (z : ℂ)) :=
    isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
      (hpLocal.comp hDomInc.isLocalHomeomorphOn (fun z _ => z.property))
  have hBaseInc : IsLocalHomeomorph
      (Subtype.val : bottleneckSlitBase (p.eval cc) → ℂ) :=
    (bottleneckSlitBase_isOpen (p.eval cc) hv).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hcont : Continuous (bottleneckSlitProjection p cc) :=
    (p.continuous.comp continuous_subtype_val).subtype_mk _
  exact hscalar.of_comp hBaseInc hcont

/-- The covering hypothesis of Lemma 2.3, discharged from the hypotheses of
`s3_bottleneck_length`. -/
theorem s3_bottleneck_isCoveringMap (p : Polynomial ℂ) (cc : ℂ)
    (hcc : cc ∈ Omega p) (hv : p.eval cc ≠ 0) (hdeg : 0 < p.natDegree)
    (huniq : ∀ c' ∈ connectedComponentIn (Omega p) cc,
      (Polynomial.derivative p).IsRoot c' → c' = cc) :
    IsCoveringMap (bottleneckSlitProjection p cc) :=
  s2_isCoveringMap_of_isProperMap_of_isLocalHomeomorph
    (bottleneck_isProperMap_projection p cc hcc hdeg)
    (bottleneck_isLocalHomeomorph_projection p cc hcc hv huniq)

/-! ## The fibres over the slit have at most two points

`hzeros` pins the fibre of the covering over `0` to `{b₁, b₂}`, so the covering
over the simply connected slit disc has exactly two sheets: the sections through
`b₁` and through `b₂`.  Points of the slit itself are limits of the slit disc,
so a third preimage there would produce a third preimage of a nearby point of
the slit disc through its inverse chart. -/

/-- Exactly two sheets: any three points of the slit complement with the same
image contain a repetition. -/
theorem bottleneck_fibre_le_two (p : Polynomial ℂ) (cc : ℂ) (hv : p.eval cc ≠ 0)
    (hcover : IsCoveringMap (bottleneckSlitProjection p cc))
    (b₁ b₂ : ℂ)
    (hb₁ : b₁ ∈ connectedComponentIn (Omega p) cc)
    (hb₂ : b₂ ∈ connectedComponentIn (Omega p) cc)
    (hr₁ : p.IsRoot b₁) (hr₂ : p.IsRoot b₂)
    (hzeros : ∀ w ∈ connectedComponentIn (Omega p) cc, p.IsRoot w → w = b₁ ∨ w = b₂)
    (e₁ e₂ e₃ : bottleneckSlitDomain p cc)
    (h12 : bottleneckSlitProjection p cc e₁ = bottleneckSlitProjection p cc e₂)
    (h13 : bottleneckSlitProjection p cc e₁ = bottleneckSlitProjection p cc e₃) :
    e₁ = e₂ ∨ e₁ = e₃ ∨ e₂ = e₃ := by
  letI : SimplyConnectedSpace (bottleneckSlitBase (p.eval cc)) :=
    bottleneckSlitBase_simplyConnected (p.eval cc) hv
  letI : LocPathConnectedSpace (bottleneckSlitBase (p.eval cc)) :=
    bottleneckSlitBase_locPathConnected (p.eval cc) hv
  have hzeroBase : (0 : ℂ) ∈ bottleneckSlitBase (p.eval cc) :=
    ⟨by simp, zero_not_mem_bottleneckSlit (p.eval cc) hv⟩
  have hslit₁ : p.eval b₁ ∉ bottleneckSlit (p.eval cc) := by
    rw [show p.eval b₁ = 0 from hr₁]
    exact zero_not_mem_bottleneckSlit (p.eval cc) hv
  have hslit₂ : p.eval b₂ ∉ bottleneckSlit (p.eval cc) := by
    rw [show p.eval b₂ = 0 from hr₂]
    exact zero_not_mem_bottleneckSlit (p.eval cc) hv
  have hB₁ : b₁ ∈ bottleneckSlitDomain p cc := ⟨hb₁, hslit₁⟩
  have hB₂ : b₂ ∈ bottleneckSlitDomain p cc := ⟨hb₂, hslit₂⟩
  have hπB₁ : bottleneckSlitProjection p cc ⟨b₁, hB₁⟩ = ⟨0, hzeroBase⟩ :=
    Subtype.ext (show p.eval b₁ = 0 from hr₁)
  have hπB₂ : bottleneckSlitProjection p cc ⟨b₂, hB₂⟩ = ⟨0, hzeroBase⟩ :=
    Subtype.ext (show p.eval b₂ = 0 from hr₂)
  obtain ⟨σ₁, ⟨hσ₁0, hσ₁π⟩, hσ₁u⟩ := hcover.existsUnique_continuousMap_lifts
    (ContinuousMap.id (bottleneckSlitBase (p.eval cc))) ⟨0, hzeroBase⟩ ⟨b₁, hB₁⟩ hπB₁
  obtain ⟨σ₂, ⟨hσ₂0, hσ₂π⟩, hσ₂u⟩ := hcover.existsUnique_continuousMap_lifts
    (ContinuousMap.id (bottleneckSlitBase (p.eval cc))) ⟨0, hzeroBase⟩ ⟨b₂, hB₂⟩ hπB₂
  have key : ∀ e : bottleneckSlitDomain p cc,
      e = σ₁ (bottleneckSlitProjection p cc e) ∨
      e = σ₂ (bottleneckSlitProjection p cc e) := by
    intro e
    obtain ⟨σ, ⟨hσ0, hσπ⟩, -⟩ := hcover.existsUnique_continuousMap_lifts
      (ContinuousMap.id (bottleneckSlitBase (p.eval cc)))
      (bottleneckSlitProjection p cc e) e rfl
    have hsec : bottleneckSlitProjection p cc (σ ⟨0, hzeroBase⟩) = ⟨0, hzeroBase⟩ :=
      congrFun hσπ ⟨0, hzeroBase⟩
    have hroot : p.IsRoot ((σ ⟨0, hzeroBase⟩ : bottleneckSlitDomain p cc) : ℂ) :=
      congrArg Subtype.val hsec
    have hmem : ((σ ⟨0, hzeroBase⟩ : bottleneckSlitDomain p cc) : ℂ) ∈
        connectedComponentIn (Omega p) cc := (σ ⟨0, hzeroBase⟩).2.1
    rcases hzeros _ hmem hroot with hb | hb
    · exact Or.inl (by rw [← hσ₁u σ ⟨Subtype.ext hb, hσπ⟩]; exact hσ0.symm)
    · exact Or.inr (by rw [← hσ₂u σ ⟨Subtype.ext hb, hσπ⟩]; exact hσ0.symm)
  have h23 : bottleneckSlitProjection p cc e₂ = bottleneckSlitProjection p cc e₃ :=
    h12.symm.trans h13
  have same : ∀ (σ : ContinuousMap (bottleneckSlitBase (p.eval cc))
        (bottleneckSlitDomain p cc)) (a b : bottleneckSlitDomain p cc),
      a = σ (bottleneckSlitProjection p cc a) →
      b = σ (bottleneckSlitProjection p cc b) →
      bottleneckSlitProjection p cc a = bottleneckSlitProjection p cc b → a = b := by
    intro σ a b ha hb hab
    rw [ha, hb, hab]
  rcases key e₁ with k1 | k1 <;> rcases key e₂ with k2 | k2 <;> rcases key e₃ with k3 | k3
  · exact Or.inl (same σ₁ e₁ e₂ k1 k2 h12)
  · exact Or.inl (same σ₁ e₁ e₂ k1 k2 h12)
  · exact Or.inr (Or.inl (same σ₁ e₁ e₃ k1 k3 h13))
  · exact Or.inr (Or.inr (same σ₂ e₂ e₃ k2 k3 h23))
  · exact Or.inr (Or.inr (same σ₁ e₂ e₃ k2 k3 h23))
  · exact Or.inr (Or.inl (same σ₂ e₁ e₃ k1 k3 h13))
  · exact Or.inl (same σ₂ e₁ e₂ k1 k2 h12)
  · exact Or.inl (same σ₂ e₁ e₂ k1 k2 h12)

/-- Every point of the slit is a limit of the slit disc: perturb it by a small
imaginary multiple of the slit direction. -/
theorem bottleneckSlit_mem_closure_base (v : ℂ) (hv : v ≠ 0) (ξ : ℂ)
    (hξ : ξ ∈ bottleneckSlit v) : ξ ∈ closure (bottleneckSlitBase v) := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hunit : ‖v / (‖v‖ : ℂ)‖ = 1 := by simp [hn]
  obtain ⟨r, hr, hrone, hxi⟩ := (bottleneckSlit_iff v ξ hv).mp hξ
  have hrnonneg : 0 ≤ r := (norm_nonneg v).trans hr
  have hu0 : v / (‖v‖ : ℂ) ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hunit
    norm_num at hunit
  rw [Metric.mem_closure_iff]
  intro ε hε
  set τ : ℝ := min (ε / 2) ((1 - r) / 2) with hτdef
  have hτpos : 0 < τ := lt_min (by linarith) (by linarith)
  have hτε : τ ≤ ε / 2 := min_le_left _ _
  have hτr : τ ≤ (1 - r) / 2 := min_le_right _ _
  refine ⟨(((r : ℂ) + (τ : ℂ) * Complex.I) * (v / (‖v‖ : ℂ))), ⟨?_, ?_⟩, ?_⟩
  · -- inside the unit disc
    have hbound : ‖(r : ℂ) + (τ : ℂ) * Complex.I‖ ≤ r + τ := by
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrnonneg, norm_mul,
        Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hτpos.le]
    rw [norm_mul, hunit, mul_one]
    linarith
  · -- off the slit
    intro hmem
    obtain ⟨ρ, -, -, hρ⟩ := (bottleneckSlit_iff v _ hv).mp hmem
    have hcancel : (r : ℂ) + (τ : ℂ) * Complex.I = (ρ : ℂ) :=
      mul_right_cancel₀ hu0 hρ
    have him := congrArg Complex.im hcancel
    simp at him
    exact absurd him hτpos.ne'
  · -- close to `ξ`
    have hdiff : ξ - ((r : ℂ) + (τ : ℂ) * Complex.I) * (v / (‖v‖ : ℂ)) =
        (-(τ : ℂ) * Complex.I) * (v / (‖v‖ : ℂ)) := by
      rw [hxi]; ring
    rw [dist_eq_norm, hdiff, norm_mul, hunit, mul_one, norm_mul, Complex.norm_I,
      mul_one, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτpos.le]
    linarith

/-- A point of the slit has at most two preimages in the distinguished
component. -/
theorem bottleneck_no_three_preimages (p : Polynomial ℂ) (cc : ℂ) (hv : p.eval cc ≠ 0)
    (hcover : IsCoveringMap (bottleneckSlitProjection p cc))
    (b₁ b₂ : ℂ)
    (hb₁ : b₁ ∈ connectedComponentIn (Omega p) cc)
    (hb₂ : b₂ ∈ connectedComponentIn (Omega p) cc)
    (hr₁ : p.IsRoot b₁) (hr₂ : p.IsRoot b₂)
    (hzeros : ∀ w ∈ connectedComponentIn (Omega p) cc, p.IsRoot w → w = b₁ ∨ w = b₂)
    (huniq : ∀ c' ∈ connectedComponentIn (Omega p) cc,
      (Polynomial.derivative p).IsRoot c' → c' = cc)
    (ξ : ℂ) (hξ : ξ ∈ bottleneckSlit (p.eval cc)) (hξv : ξ ≠ p.eval cc)
    (w₁ w₂ w₃ : ℂ)
    (hw₁ : w₁ ∈ connectedComponentIn (Omega p) cc)
    (hw₂ : w₂ ∈ connectedComponentIn (Omega p) cc)
    (hw₃ : w₃ ∈ connectedComponentIn (Omega p) cc)
    (hp₁ : p.eval w₁ = ξ) (hp₂ : p.eval w₂ = ξ) (hp₃ : p.eval w₃ = ξ)
    (n12 : w₁ ≠ w₂) (n13 : w₁ ≠ w₃) (n23 : w₂ ≠ w₃) : False := by
  have hOopen : IsOpen (Omega p) := isOpen_lt p.continuous.norm continuous_const
  have hUopen : IsOpen (connectedComponentIn (Omega p) cc) := hOopen.connectedComponentIn
  have hreg : ∀ w ∈ connectedComponentIn (Omega p) cc, p.eval w = ξ →
      (Polynomial.derivative p).eval w ≠ 0 := by
    intro w hw hpw hzero
    rw [huniq w hw hzero] at hpw
    exact hξv hpw.symm
  have hloc : ∀ w : ℂ, (Polynomial.derivative p).eval w ≠ 0 →
      ∃ e : OpenPartialHomeomorph ℂ ℂ, w ∈ e.source ∧ p.eval = ⇑e := by
    intro w hw
    have hd := (p.hasStrictDerivAt w).hasStrictFDerivAt_equiv hw
    exact ⟨hd.toOpenPartialHomeomorph p.eval, hd.mem_toOpenPartialHomeomorph_source, rfl⟩
  obtain ⟨c₁, hc₁, he₁⟩ := hloc w₁ (hreg w₁ hw₁ hp₁)
  obtain ⟨c₂, hc₂, he₂⟩ := hloc w₂ (hreg w₂ hw₂ hp₂)
  obtain ⟨c₃, hc₃, he₃⟩ := hloc w₃ (hreg w₃ hw₃ hp₃)
  have d12 : 0 < dist w₁ w₂ := dist_pos.mpr n12
  have d13 : 0 < dist w₁ w₃ := dist_pos.mpr n13
  have d23 : 0 < dist w₂ w₃ := dist_pos.mpr n23
  set r : ℝ := min (dist w₁ w₂) (min (dist w₁ w₃) (dist w₂ w₃)) / 3 with hrdef
  have hrpos : 0 < r := by
    have := lt_min d12 (lt_min d13 d23)
    simp only [hrdef]
    linarith
  have hr12 : 3 * r ≤ dist w₁ w₂ := by
    simp only [hrdef]
    have := min_le_left (dist w₁ w₂) (min (dist w₁ w₃) (dist w₂ w₃))
    linarith
  have hr13 : 3 * r ≤ dist w₁ w₃ := by
    simp only [hrdef]
    have h1 := min_le_right (dist w₁ w₂) (min (dist w₁ w₃) (dist w₂ w₃))
    have h2 := min_le_left (dist w₁ w₃) (dist w₂ w₃)
    linarith
  have hr23 : 3 * r ≤ dist w₂ w₃ := by
    simp only [hrdef]
    have h1 := min_le_right (dist w₁ w₂) (min (dist w₁ w₃) (dist w₂ w₃))
    have h2 := min_le_right (dist w₁ w₃) (dist w₂ w₃)
    linarith
  -- the three separated inverse charts
  set V₁ : Set ℂ := c₁.source ∩ connectedComponentIn (Omega p) cc ∩ Metric.ball w₁ r with hV₁
  set V₂ : Set ℂ := c₂.source ∩ connectedComponentIn (Omega p) cc ∩ Metric.ball w₂ r with hV₂
  set V₃ : Set ℂ := c₃.source ∩ connectedComponentIn (Omega p) cc ∩ Metric.ball w₃ r with hV₃
  have hV₁open : IsOpen V₁ := (c₁.open_source.inter hUopen).inter Metric.isOpen_ball
  have hV₂open : IsOpen V₂ := (c₂.open_source.inter hUopen).inter Metric.isOpen_ball
  have hV₃open : IsOpen V₃ := (c₃.open_source.inter hUopen).inter Metric.isOpen_ball
  have hw₁V : w₁ ∈ V₁ := ⟨⟨hc₁, hw₁⟩, Metric.mem_ball_self hrpos⟩
  have hw₂V : w₂ ∈ V₂ := ⟨⟨hc₂, hw₂⟩, Metric.mem_ball_self hrpos⟩
  have hw₃V : w₃ ∈ V₃ := ⟨⟨hc₃, hw₃⟩, Metric.mem_ball_self hrpos⟩
  have himg₁ : IsOpen (c₁ '' V₁) :=
    c₁.isOpen_image_of_subset_source hV₁open (fun x hx => hx.1.1)
  have himg₂ : IsOpen (c₂ '' V₂) :=
    c₂.isOpen_image_of_subset_source hV₂open (fun x hx => hx.1.1)
  have himg₃ : IsOpen (c₃ '' V₃) :=
    c₃.isOpen_image_of_subset_source hV₃open (fun x hx => hx.1.1)
  have hξ₁ : ξ ∈ c₁ '' V₁ := ⟨w₁, hw₁V, (congrFun he₁ w₁).symm.trans hp₁⟩
  have hξ₂ : ξ ∈ c₂ '' V₂ := ⟨w₂, hw₂V, (congrFun he₂ w₂).symm.trans hp₂⟩
  have hξ₃ : ξ ∈ c₃ '' V₃ := ⟨w₃, hw₃V, (congrFun he₃ w₃).symm.trans hp₃⟩
  have hTopen : IsOpen ((c₁ '' V₁) ∩ (c₂ '' V₂) ∩ (c₃ '' V₃)) :=
    (himg₁.inter himg₂).inter himg₃
  have hξT : ξ ∈ (c₁ '' V₁) ∩ (c₂ '' V₂) ∩ (c₃ '' V₃) := ⟨⟨hξ₁, hξ₂⟩, hξ₃⟩
  obtain ⟨ξ', ⟨⟨hξ'₁, hξ'₂⟩, hξ'₃⟩, hξ'base⟩ :=
    mem_closure_iff.mp (bottleneckSlit_mem_closure_base (p.eval cc) hv ξ hξ) _ hTopen hξT
  obtain ⟨y₁, hy₁V, hy₁⟩ := hξ'₁
  obtain ⟨y₂, hy₂V, hy₂⟩ := hξ'₂
  obtain ⟨y₃, hy₃V, hy₃⟩ := hξ'₃
  have hpy₁ : p.eval y₁ = ξ' := (congrFun he₁ y₁).trans hy₁
  have hpy₂ : p.eval y₂ = ξ' := (congrFun he₂ y₂).trans hy₂
  have hpy₃ : p.eval y₃ = ξ' := (congrFun he₃ y₃).trans hy₃
  have hdom : ∀ y : ℂ, y ∈ connectedComponentIn (Omega p) cc → p.eval y = ξ' →
      y ∈ bottleneckSlitDomain p cc := by
    intro y hy hpy
    exact ⟨hy, by rw [hpy]; exact hξ'base.2⟩
  have hD₁ := hdom y₁ hy₁V.1.2 hpy₁
  have hD₂ := hdom y₂ hy₂V.1.2 hpy₂
  have hD₃ := hdom y₃ hy₃V.1.2 hpy₃
  have hproj₁₂ : bottleneckSlitProjection p cc ⟨y₁, hD₁⟩ =
      bottleneckSlitProjection p cc ⟨y₂, hD₂⟩ := Subtype.ext (hpy₁.trans hpy₂.symm)
  have hproj₁₃ : bottleneckSlitProjection p cc ⟨y₁, hD₁⟩ =
      bottleneckSlitProjection p cc ⟨y₃, hD₃⟩ := Subtype.ext (hpy₁.trans hpy₃.symm)
  -- the three lifts are distinct because the charts were separated
  have hsep : ∀ (a b u v : ℂ) (ra : ℝ), 3 * ra ≤ dist u v →
      a ∈ Metric.ball u ra → b ∈ Metric.ball v ra → 0 < ra → a ≠ b := by
    intro a b u v ra hd ha hb hra hab
    subst hab
    have h1 : dist u a < ra := by
      rw [dist_comm]
      exact Metric.mem_ball.mp ha
    have h2 : dist a v < ra := Metric.mem_ball.mp hb
    have := dist_triangle u a v
    linarith
  have n₁₂ : y₁ ≠ y₂ := hsep y₁ y₂ w₁ w₂ r hr12 hy₁V.2 hy₂V.2 hrpos
  have n₁₃ : y₁ ≠ y₃ := hsep y₁ y₃ w₁ w₃ r hr13 hy₁V.2 hy₃V.2 hrpos
  have n₂₃ : y₂ ≠ y₃ := hsep y₂ y₃ w₂ w₃ r hr23 hy₂V.2 hy₃V.2 hrpos
  rcases bottleneck_fibre_le_two p cc hv hcover b₁ b₂ hb₁ hb₂ hr₁ hr₂ hzeros
    ⟨y₁, hD₁⟩ ⟨y₂, hD₂⟩ ⟨y₃, hD₃⟩ hproj₁₂ hproj₁₃ with hq | hq | hq
  · exact n₁₂ (congrArg Subtype.val hq)
  · exact n₁₃ (congrArg Subtype.val hq)
  · exact n₂₃ (congrArg Subtype.val hq)

/-- The two branches of `ψ` over a value `η ≠ 0` give two distinct preimages of
`p cc + â η²` inside the component, both within `(5/4)‖η‖` of `cc`. -/
theorem bottleneck_two_local_preimages (p : Polynomial ℂ) (cc : ℂ)
    (hcrit : (Polynomial.derivative p).IsRoot cc)
    (aHat : ℂ) (haHat : aHat ≠ 0) (h s δ : ℝ) (hh : 0 < h) (hs : 0 < s)
    (hsh : 5 / 4 * s < h) (hsδ : ‖aHat‖ * s ^ 2 ≤ δ) (hδ : δ = 1 - ‖p.eval cc‖)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (η : ℂ) (hη : η ≠ 0) (hηs : ‖η‖ < s) :
    ∃ x₁ ∈ connectedComponentIn (Omega p) cc, ∃ x₂ ∈ connectedComponentIn (Omega p) cc,
      x₁ ≠ x₂ ∧ p.eval x₁ = p.eval cc + aHat * η ^ 2 ∧
        p.eval x₂ = p.eval cc + aHat * η ^ 2 ∧
        ‖x₁ - cc‖ ≤ 5 / 4 * ‖η‖ ∧ ‖x₂ - cc‖ ≤ 5 / 4 * ‖η‖ := by
  have hηh : ‖η‖ < 4 / 5 * h := by linarith
  obtain ⟨zp, hzp, zm, hzm, hvp, hvm⟩ :=
    bottleneck_two_preimages p cc aHat h hh hdisk η hηh
  have hzpnorm : ‖zp‖ ≤ h :=
    le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hzp)
  have hzmnorm : ‖zm‖ ≤ h :=
    le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hzm)
  have hlowp := bottleneck_psi_norm_lower p cc aHat h hdisk zp hzpnorm
  rw [hvp] at hlowp
  have hlowm := bottleneck_psi_norm_lower p cc aHat h hdisk zm hzmnorm
  rw [hvm, norm_neg] at hlowm
  have hnear : ∀ w : ℂ, w ∈ Metric.ball (0 : ℂ) h → ‖bottleneckPsi p cc aHat w‖ < s →
      cc + w ∈ connectedComponentIn (Omega p) cc := by
    intro w hw hpsi
    exact bottleneckNear_shift_subset p cc aHat hcrit haHat h s δ hh hs hsh hsδ hδ hdisk
      ⟨w, ⟨hw, hpsi⟩, rfl⟩
  have hmem₁ := hnear zp hzp (by rw [hvp]; exact hηs)
  have hmem₂ := hnear zm hzm (by rw [hvm, norm_neg]; exact hηs)
  have hevp : p.eval (cc + zp) = p.eval cc + aHat * η ^ 2 := by
    have hx := bottleneck_psi_sq p cc hcrit aHat haHat zp
    rw [hvp] at hx
    exact sub_eq_iff_eq_add'.mp hx
  have hevm : p.eval (cc + zm) = p.eval cc + aHat * η ^ 2 := by
    have hx := bottleneck_psi_sq p cc hcrit aHat haHat zm
    rw [hvm] at hx
    have hx2 : p.eval (cc + zm) - p.eval cc = aHat * η ^ 2 := by rw [hx]; ring
    exact sub_eq_iff_eq_add'.mp hx2
  refine ⟨cc + zp, hmem₁, cc + zm, hmem₂, ?_, hevp, hevm, ?_, ?_⟩
  · intro hEq
    have hzz : zp = zm := add_left_cancel hEq
    rw [hzz, hvm] at hvp
    refine hη ?_
    have h2 : (2 : ℂ) * η = 0 := by linear_combination -hvp
    simpa using h2
  · rw [add_sub_cancel_left]; linarith
  · rw [add_sub_cancel_left]; linarith

/-- Paper Lemma 2.3, step one: the fibre of `p` over the critical value inside
the component is the single point `cc`.  A second preimage would be regular, and
its inverse chart would give a third preimage of a nearby slit point, which the
two-sheet count forbids. -/
theorem bottleneck_critical_fibre_singleton (p : Polynomial ℂ) (cc : ℂ)
    (hcrit : (Polynomial.derivative p).IsRoot cc) (hv : p.eval cc ≠ 0)
    (hcover : IsCoveringMap (bottleneckSlitProjection p cc))
    (aHat : ℂ) (haHat : aHat ≠ 0) (h s δ : ℝ) (hh : 0 < h) (hs : 0 < s)
    (hsh : 5 / 4 * s < h) (hsδ : ‖aHat‖ * s ^ 2 ≤ δ) (hδ : δ = 1 - ‖p.eval cc‖)
    (hδpos : 0 < δ)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (b₁ b₂ : ℂ)
    (hb₁ : b₁ ∈ connectedComponentIn (Omega p) cc)
    (hb₂ : b₂ ∈ connectedComponentIn (Omega p) cc)
    (hr₁ : p.IsRoot b₁) (hr₂ : p.IsRoot b₂)
    (hzeros : ∀ w ∈ connectedComponentIn (Omega p) cc, p.IsRoot w → w = b₁ ∨ w = b₂)
    (huniq : ∀ c' ∈ connectedComponentIn (Omega p) cc,
      (Polynomial.derivative p).IsRoot c' → c' = cc)
    (z : ℂ) (hz : z ∈ connectedComponentIn (Omega p) cc) (hpz : p.eval z = p.eval cc) :
    z = cc := by
  by_contra hne
  have hApos : 0 < ‖aHat‖ := norm_pos_iff.mpr haHat
  have hOopen : IsOpen (Omega p) := isOpen_lt p.continuous.norm continuous_const
  have hUopen : IsOpen (connectedComponentIn (Omega p) cc) := hOopen.connectedComponentIn
  have hreg : (Polynomial.derivative p).eval z ≠ 0 := fun hzero => hne (huniq z hz hzero)
  obtain ⟨c₀, hc₀, he₀⟩ : ∃ e : OpenPartialHomeomorph ℂ ℂ, z ∈ e.source ∧ p.eval = ⇑e := by
    have hd := (p.hasStrictDerivAt z).hasStrictFDerivAt_equiv hreg
    exact ⟨hd.toOpenPartialHomeomorph p.eval, hd.mem_toOpenPartialHomeomorph_source, rfl⟩
  have hρpos : 0 < ‖z - cc‖ / 3 := by
    have : 0 < ‖z - cc‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    linarith
  set ρ : ℝ := ‖z - cc‖ / 3 with hρdef
  set V : Set ℂ := c₀.source ∩ connectedComponentIn (Omega p) cc ∩ Metric.ball z ρ with hVdef
  have hVopen : IsOpen V := (c₀.open_source.inter hUopen).inter Metric.isOpen_ball
  have hzV : z ∈ V := ⟨⟨hc₀, hz⟩, Metric.mem_ball_self hρpos⟩
  have hWopen : IsOpen (c₀ '' V) :=
    c₀.isOpen_image_of_subset_source hVopen (fun x hx => hx.1.1)
  have hvW : p.eval cc ∈ c₀ '' V := ⟨z, hzV, (congrFun he₀ z).symm.trans hpz⟩
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hWopen _ hvW
  set ν : ℝ := min s (4 * ρ / 5) with hνdef
  have hνpos : 0 < ν := lt_min hs (by linarith)
  set t' : ℝ := min (min (ε / 2) (δ / 2)) (ν ^ 2 * ‖aHat‖ / 2) with ht'def
  have ht'pos : 0 < t' :=
    lt_min (lt_min (by linarith) (by linarith)) (by positivity)
  have ht'ε : t' ≤ ε / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have ht'δ : t' ≤ δ / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have ht'ν : t' ≤ ν ^ 2 * ‖aHat‖ / 2 := min_le_right _ _
  have hn : ‖p.eval cc‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hunit : ‖p.eval cc / (‖p.eval cc‖ : ℂ)‖ = 1 := by simp [hn]
  set u : ℂ := p.eval cc / (‖p.eval cc‖ : ℂ) with hudef
  set ξ' : ℂ := p.eval cc + (t' : ℂ) * u with hξ'def
  have hξ'slit : ξ' ∈ bottleneckSlit (p.eval cc) :=
    ⟨t', ht'pos.le, by rw [← hδ]; linarith, rfl⟩
  have hdistξ' : ‖ξ' - p.eval cc‖ = t' := by
    rw [hξ'def, add_sub_cancel_left, norm_mul, hunit, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht'pos]
  have hξ'v : ξ' ≠ p.eval cc := by
    intro hEq
    rw [hEq, sub_self, norm_zero] at hdistξ'
    exact ht'pos.ne hdistξ'
  -- the value `η` of the two branches
  set η : ℂ := Complex.sqrt (((t' : ℂ) * u) / aHat) with hηdef
  have hη2 : aHat * η ^ 2 = (t' : ℂ) * u := by
    rw [hηdef, bottleneck_sqrt_sq, mul_div_cancel₀ _ haHat]
  have hηnormsq : ‖η‖ ^ 2 = t' / ‖aHat‖ := by
    have : ‖η‖ ^ 2 = ‖η ^ 2‖ := (norm_pow η 2).symm
    rw [this, hηdef, bottleneck_sqrt_sq, norm_div, norm_mul, hunit, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht'pos]
  have hηlt : ‖η‖ < ν := by
    have hsq : ‖η‖ ^ 2 < ν ^ 2 := by
      rw [hηnormsq]
      rw [div_lt_iff₀ hApos]
      nlinarith
    nlinarith [norm_nonneg η, hνpos]
  have hηne : η ≠ 0 := by
    intro hzero
    rw [hzero] at hη2
    simp at hη2
    rcases hη2 with hcase | hcase
    · exact ht'pos.ne' hcase
    · rw [hcase, norm_zero] at hunit; norm_num at hunit
  obtain ⟨x₁, hx₁, x₂, hx₂, hne12, hp1, hp2, hb1, hb2⟩ :=
    bottleneck_two_local_preimages p cc hcrit aHat haHat h s δ hh hs hsh hsδ hδ hdisk
      η hηne (lt_of_lt_of_le hηlt (min_le_left _ _))
  rw [hη2, ← hξ'def] at hp1 hp2
  -- the third preimage, next to `z`
  have hξ'W : ξ' ∈ c₀ '' V := by
    refine hεsub ?_
    rw [Metric.mem_ball, dist_eq_norm, hdistξ']
    linarith
  obtain ⟨y, hyV, hy⟩ := hξ'W
  have hpy : p.eval y = ξ' := (congrFun he₀ y).trans hy
  have hxρ : ∀ x : ℂ, ‖x - cc‖ ≤ 5 / 4 * ‖η‖ → ‖x - cc‖ < ρ := by
    intro x hx
    have h1 : ‖η‖ < 4 * ρ / 5 := lt_of_lt_of_le hηlt (min_le_right _ _)
    linarith
  have hyfar : ρ < ‖y - cc‖ := by
    have hyz : ‖y - z‖ < ρ := by
      have hb := Metric.mem_ball.mp hyV.2
      rwa [dist_eq_norm] at hb
    have htri : ‖z - cc‖ ≤ ‖z - y‖ + ‖y - cc‖ := by
      simpa using norm_add_le (z - y) (y - cc)
    rw [norm_sub_rev z y] at htri
    have h3 : ‖z - cc‖ = 3 * ρ := by rw [hρdef]; ring
    rw [h3] at htri
    linarith
  have hy₁ : y ≠ x₁ := fun hEq => absurd (hEq ▸ hyfar) (not_lt.mpr (hxρ x₁ hb1).le)
  have hy₂ : y ≠ x₂ := fun hEq => absurd (hEq ▸ hyfar) (not_lt.mpr (hxρ x₂ hb2).le)
  exact bottleneck_no_three_preimages p cc hv hcover b₁ b₂ hb₁ hb₂ hr₁ hr₂ hzeros huniq
    ξ' hξ'slit hξ'v x₁ x₂ y hx₁ hx₂ hyV.1.2 hp1 hp2 hpy hne12
    (fun hEq => hy₁ hEq.symm) (fun hEq => hy₂ hEq.symm)

/-- Paper Lemma 2.3: **every** preimage of the slit inside the component lies in
the small disc about `cc`.  This replaces the connectedness route: the two
branches at `cc` already exhaust the fibre, by the two-sheet count. -/
theorem bottleneck_slit_preimage_near (p : Polynomial ℂ) (cc : ℂ)
    (hcrit : (Polynomial.derivative p).IsRoot cc) (hv : p.eval cc ≠ 0)
    (hcover : IsCoveringMap (bottleneckSlitProjection p cc))
    (aHat : ℂ) (haHat : aHat ≠ 0) (h : ℝ) (hh : 0 < h)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (δ : ℝ) (hδ : δ = 1 - ‖p.eval cc‖) (hδpos : 0 < δ)
    (hδsmall : δ < ‖aHat‖ * h ^ 2 / 4)
    (b₁ b₂ : ℂ)
    (hb₁ : b₁ ∈ connectedComponentIn (Omega p) cc)
    (hb₂ : b₂ ∈ connectedComponentIn (Omega p) cc)
    (hr₁ : p.IsRoot b₁) (hr₂ : p.IsRoot b₂)
    (hzeros : ∀ w ∈ connectedComponentIn (Omega p) cc, p.IsRoot w → w = b₁ ∨ w = b₂)
    (huniq : ∀ c' ∈ connectedComponentIn (Omega p) cc,
      (Polynomial.derivative p).IsRoot c' → c' = cc)
    (z : ℂ) (hz : z ∈ connectedComponentIn (Omega p) cc)
    (hslit : p.eval z ∈ bottleneckSlit (p.eval cc)) :
    ‖z - cc‖ < 4 / 3 * Real.sqrt (δ / ‖aHat‖) := by
  have hApos : 0 < ‖aHat‖ := norm_pos_iff.mpr haHat
  have hdivpos : 0 < δ / ‖aHat‖ := div_pos hδpos hApos
  set s : ℝ := Real.sqrt (δ / ‖aHat‖) with hsdef
  have hspos : 0 < s := Real.sqrt_pos.mpr hdivpos
  have hs2 : s ^ 2 = δ / ‖aHat‖ := Real.sq_sqrt hdivpos.le
  have hAs2 : ‖aHat‖ * s ^ 2 = δ := by
    rw [hs2, mul_div_cancel₀ _ (ne_of_gt hApos)]
  have hshalf : s < h / 2 := by
    have hlt : s ^ 2 < (h / 2) ^ 2 := by
      rw [hs2, div_lt_iff₀ hApos]
      nlinarith
    nlinarith [hspos, (by linarith : (0 : ℝ) < h / 2)]
  have hsh : 5 / 4 * s < h := by linarith
  by_cases hξv : p.eval z = p.eval cc
  · have hzc : z = cc :=
      bottleneck_critical_fibre_singleton p cc hcrit hv hcover aHat haHat h s δ hh hspos
        hsh (le_of_eq hAs2) hδ hδpos hdisk b₁ b₂ hb₁ hb₂ hr₁ hr₂ hzeros huniq z hz hξv
    rw [hzc, sub_self, norm_zero]
    positivity
  · have ht : ‖p.eval z - p.eval cc‖ < δ := by
      have hx := bottleneckSlit_norm_sub_lt (p.eval cc) (p.eval z) hv hslit
      rw [← hδ] at hx
      exact hx
    set η : ℂ := Complex.sqrt ((p.eval z - p.eval cc) / aHat) with hηdef
    have hη2 : aHat * η ^ 2 = p.eval z - p.eval cc := by
      rw [hηdef, bottleneck_sqrt_sq, mul_div_cancel₀ _ haHat]
    have hηnormsq : ‖η‖ ^ 2 = ‖p.eval z - p.eval cc‖ / ‖aHat‖ := by
      have hx : ‖η‖ ^ 2 = ‖η ^ 2‖ := (norm_pow η 2).symm
      rw [hx, hηdef, bottleneck_sqrt_sq, norm_div]
    have hηnorm2 : ‖aHat‖ * ‖η‖ ^ 2 = ‖p.eval z - p.eval cc‖ := by
      rw [hηnormsq, mul_div_cancel₀ _ (ne_of_gt hApos)]
    have hηs : ‖η‖ < s := by
      have hmul : ‖aHat‖ * ‖η‖ ^ 2 < ‖aHat‖ * s ^ 2 := by rw [hηnorm2, hAs2]; exact ht
      have hsq : ‖η‖ ^ 2 < s ^ 2 := by nlinarith
      nlinarith [norm_nonneg η, hspos]
    have hηne : η ≠ 0 := by
      intro hzero
      rw [hzero] at hη2
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at hη2
      exact hξv (sub_eq_zero.mp hη2.symm)
    obtain ⟨x₁, hx₁, x₂, hx₂, hne12, hp1, hp2, hbb1, hbb2⟩ :=
      bottleneck_two_local_preimages p cc hcrit aHat haHat h s δ hh hspos hsh
        (le_of_eq hAs2) hδ hdisk η hηne hηs
    rw [hη2] at hp1 hp2
    have hp1' : p.eval x₁ = p.eval z := by rw [hp1]; ring
    have hp2' : p.eval x₂ = p.eval z := by rw [hp2]; ring
    have hcase : z = x₁ ∨ z = x₂ := by
      by_contra hcon
      push_neg at hcon
      exact bottleneck_no_three_preimages p cc hv hcover b₁ b₂ hb₁ hb₂ hr₁ hr₂ hzeros
        huniq (p.eval z) hslit (fun hEq => hξv hEq) x₁ x₂ z hx₁ hx₂ hz hp1' hp2' rfl
        hne12 (fun hEq => hcon.1 hEq.symm) (fun hEq => hcon.2 hEq.symm)
    rcases hcase with hEq | hEq
    · rw [hEq]; linarith
    · rw [hEq]; linarith

/-! ## Lemma 2.3 and Corollary 2.4

Both topological inputs of the conditional reduction are now discharged: the
covering by `s3_bottleneck_isCoveringMap`, and the localisation of the slit
preimage by `bottleneck_slit_preimage_near`, which replaces preconnectedness of
the whole slit preimage by the sharper statement that the two branches at `cc`
already exhaust each slit fibre. -/

/-- Corollary 2.4 (the disk criterion) combined with Lemma 2.3, in the single
form S6 consumes: under the disk criterion at the critical point `cc` with
comparison coefficient `aHat` and radius `h`, every path inside the component
joining the two zeros has length at least
`‖b₁ - cc‖ + ‖b₂ - cc‖ - (8/3)√(δ/‖aHat‖)`.

Owner: slice S3. -/
theorem s3_bottleneck_length
    (p : Polynomial ℂ) (cc : ℂ) (hcc : cc ∈ Omega p)
    (hcrit : (Polynomial.derivative p).IsRoot cc)
    (hv : p.eval cc ≠ 0)
    (b₁ b₂ : ℂ) (hne : b₁ ≠ b₂)
    (hb₁ : b₁ ∈ connectedComponentIn (Omega p) cc)
    (hb₂ : b₂ ∈ connectedComponentIn (Omega p) cc)
    (hr₁ : p.IsRoot b₁) (hr₂ : p.IsRoot b₂)
    (hzeros : ∀ w ∈ connectedComponentIn (Omega p) cc, p.IsRoot w → w = b₁ ∨ w = b₂)
    (huniq : ∀ c' ∈ connectedComponentIn (Omega p) cc,
      (Polynomial.derivative p).IsRoot c' → c' = cc)
    (hsimple : Polynomial.rootMultiplicity cc (Polynomial.derivative p) = 1)
    (aHat : ℂ) (haHat : aHat ≠ 0) (h : ℝ) (hh : 0 < h)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (δ : ℝ) (hδ : δ = 1 - ‖p.eval cc‖) (hδpos : 0 < δ)
    (hδsmall : δ < ‖aHat‖ * h ^ 2 / 4)
    (γ : ℝ → ℂ) (hcont : ContinuousOn γ (Set.Icc 0 1))
    (hγ0 : γ 0 = b₁) (hγ1 : γ 1 = b₂)
    (hγmem : ∀ τ ∈ Set.Icc (0 : ℝ) 1, γ τ ∈ connectedComponentIn (Omega p) cc) :
    ENNReal.ofReal (‖b₁ - cc‖ + ‖b₂ - cc‖ - 8 / 3 * Real.sqrt (δ / ‖aHat‖))
      ≤ pathLength γ := by
  have hdeg := bottleneck_natDegree_pos p cc b₁ hv hr₁
  have hcover := s3_bottleneck_isCoveringMap p cc hcc hv hdeg huniq
  obtain ⟨τ, hτ, hmeet⟩ := bottleneck_path_meets_slit_of_covering p cc hv hcover
    b₁ b₂ hne hr₁ hr₂ γ hcont hγ0 hγ1 hγmem
  exact bottleneck_length_of_near_point γ b₁ b₂ cc hγ0 hγ1 δ aHat τ hτ
    (bottleneck_slit_preimage_near p cc hcrit hv hcover aHat haHat h hh hdisk δ hδ
      hδpos hδsmall b₁ b₂ hb₁ hb₂ hr₁ hr₂ hzeros huniq (γ τ) hmeet.1 hmeet.2)

end Erdos1041.Counterexample
