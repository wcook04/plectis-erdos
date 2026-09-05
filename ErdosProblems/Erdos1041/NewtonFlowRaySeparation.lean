import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Tactic

/-!
# Erdős #1041: Newton-flow ray separation

For `u = -log |f|`, the normalized gradient field away from the critical
points is the complex Newton field `-f / f'`.  Consequently the image of a
trajectory under `f` satisfies the scalar equation `w' = -w`: its argument is
constant and its modulus decays exponentially.

This is the exact algebraic input missing from the failed local-hole
decomposition in the March 2026 candidate proof.  It does not by itself prove
the full path theorem: the remaining producer is a planar Morse/Reeb
decomposition cut along the resulting ray-separated separatrices.
-/

namespace ErdosProblems.Erdos1041

open Set Metric
open AffineSubspace
open Polynomial

/-- The complex Newton vector associated with a value and its nonzero
derivative. -/
noncomputable def newtonFlowVector (value derivative : ℂ) : ℂ :=
  -value / derivative

/-- The defining cancellation of the Newton vector. -/
theorem derivative_mul_newtonFlowVector
    {value derivative : ℂ} (hderivative : derivative ≠ 0) :
    derivative * newtonFlowVector value derivative = -value := by
  change derivative * (-value / derivative) = -value
  calc
    derivative * (-value / derivative) =
        -(value * derivative / derivative) := by ring
    _ = -value := by rw [mul_div_cancel_right₀ value hderivative]

/-- Along a curve tangent to the Newton field, the polynomial value has
derivative equal to its own negative.  This is the local chain-rule form of
`f(z(t)) = exp(-t) f(z(0))`. -/
theorem newtonFlow_value_hasDerivAt
    {f f' z : ℂ → ℂ} {t : ℂ}
    (hf : HasDerivAt f (f' (z t)) (z t))
    (hz :
      HasDerivAt z
        (newtonFlowVector (f (z t)) (f' (z t))) t)
    (hcritical : f' (z t) ≠ 0) :
    HasDerivAt (fun s => f (z s)) (-f (z t)) t := by
  have hcomp := hf.comp t hz
  rw [derivative_mul_newtonFlowVector hcritical] at hcomp
  exact hcomp

/-- Multiplication by `exp(t)` turns the Newton-flow value equation into a
quantity with zero derivative. -/
theorem newtonFlow_scaledValue_hasDerivAt_zero
    {f f' z : ℂ → ℂ} {t : ℂ}
    (hf : HasDerivAt f (f' (z t)) (z t))
    (hz :
      HasDerivAt z
        (newtonFlowVector (f (z t)) (f' (z t))) t)
    (hcritical : f' (z t) ≠ 0) :
    HasDerivAt (fun s => Complex.exp s * f (z s)) 0 t := by
  have hvalue := newtonFlow_value_hasDerivAt hf hz hcritical
  convert Complex.hasDerivAt_exp t |>.mul hvalue using 1
  ring

/-- Two complex values lie on the same oriented ray from the origin. -/
def SamePositiveRay (a b : ℂ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ b = (r : ℂ) * a

theorem samePositiveRay_refl {a : ℂ} :
    SamePositiveRay a a := by
  exact ⟨1, by norm_num, by simp⟩

theorem samePositiveRay_symm
    {a b : ℂ} (h : SamePositiveRay a b) :
    SamePositiveRay b a := by
  rcases h with ⟨r, hr, rfl⟩
  refine ⟨r⁻¹, inv_pos.mpr hr, ?_⟩
  push_cast
  field_simp [ne_of_gt hr]

theorem samePositiveRay_trans
    {a b c : ℂ}
    (hab : SamePositiveRay a b)
    (hbc : SamePositiveRay b c) :
    SamePositiveRay a c := by
  rcases hab with ⟨r, hr, rfl⟩
  rcases hbc with ⟨s, hs, rfl⟩
  refine ⟨s * r, mul_pos hs hr, ?_⟩
  push_cast
  ring

/-- If two distinct values become positively ray-aligned after the same
translation, then the translation belongs to an explicit one-real-parameter
forbidden locus.  For a finite set of critical values, ray separation is
therefore a finite planar avoidance problem. -/
theorem translated_samePositiveRay_parameterization
    {a b shift : ℂ} (hab : a ≠ b)
    (hray : SamePositiveRay (a + shift) (b + shift)) :
    ∃ r : ℝ, 0 < r ∧ r ≠ 1 ∧
      shift = ((r : ℂ) * a - b) / ((1 - r : ℝ) : ℂ) := by
  rcases hray with ⟨r, hr, halign⟩
  have hrone : r ≠ 1 := by
    intro hr1
    subst r
    norm_num at halign
    exact hab halign.symm
  refine ⟨r, hr, hrone, ?_⟩
  have hdenom_real : (1 - r : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hrone)
  have hdenom : (((1 - r : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hdenom_real
  apply (eq_div_iff hdenom).2
  push_cast
  linear_combination halign

/-- The real affine line through `p` in direction `v`, viewed inside the
complex plane. -/
def realAffineLine (p v : ℂ) : Set ℂ :=
  Set.range fun t : ℝ => t • v + p

theorem realAffineLine_eq_affineSpan (p v : ℂ) :
    realAffineLine p v = (line[ℝ, p, p + v] : Set ℂ) := by
  apply Set.ext
  intro z
  change z ∈ realAffineLine p v ↔ z ∈ line[ℝ, p, p + v]
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  simp only [realAffineLine, mem_range]
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    rw [AffineMap.lineMap_apply_module]
    module
  · rintro ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    rw [AffineMap.lineMap_apply_module]
    module

theorem isClosed_realAffineLine (p v : ℂ) :
    IsClosed (realAffineLine p v) := by
  rw [realAffineLine_eq_affineSpan]
  exact AffineSubspace.closed_of_finiteDimensional _

theorem dense_compl_realAffineLine (p v : ℂ) :
    Dense (realAffineLine p v)ᶜ := by
  let f : ℝ → ℂ := fun t => t • v + p
  have hf : ContDiff ℝ 1 f := by fun_prop
  have hrank : Module.finrank ℝ ℝ < Module.finrank ℝ ℂ := by
    simp [Complex.finrank_real_complex]
  exact hf.dense_compl_range_of_finrank_lt_finrank hrank

/-- Finitely many real affine lines cannot fill any neighborhood in the
complex plane. -/
theorem exists_small_avoiding_finite_realAffineLines
    {κ : Type*} [Fintype κ] (p v : κ → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ z : ℂ, ‖z‖ < ε ∧ ∀ k, z ∉ realAffineLine (p k) (v k) := by
  have hopen : ∀ k, IsOpen (realAffineLine (p k) (v k))ᶜ :=
    fun k => (isClosed_realAffineLine (p k) (v k)).isOpen_compl
  have hdense : Dense (⋂ k, (realAffineLine (p k) (v k))ᶜ) :=
    dense_iInter_of_isOpen hopen
      (fun k => dense_compl_realAffineLine (p k) (v k))
  obtain ⟨z, hzball, hzavoid⟩ :=
    hdense.inter_open_nonempty (ball 0 ε) isOpen_ball
      (nonempty_ball.mpr hε)
  refine ⟨z, ?_, ?_⟩
  · simpa [mem_ball] using hzball
  · simpa only [mem_iInter, mem_compl_iff] using hzavoid

/-- The exact two-ray collision locus is contained in the corresponding real
affine line. -/
theorem samePositiveRay_imp_mem_realAffineLine
    {a b shift : ℂ} (hab : a ≠ b)
    (hray : SamePositiveRay (a + shift) (b + shift)) :
    shift ∈ realAffineLine (-b) (a - b) := by
  obtain ⟨r, hr, hr1, hshift⟩ :=
    translated_samePositiveRay_parameterization hab hray
  refine ⟨r / (1 - r), ?_⟩
  dsimp
  rw [hshift]
  have hdenR : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr1)
  have hdenC : (1 - (r : ℂ)) ≠ 0 := by exact_mod_cast hdenR
  push_cast
  field_simp [hdenC]
  ring

/-- An injective finite complex family admits an arbitrarily small common
translation after which every value is nonzero and all positive-ray
arguments are distinct. -/
theorem exists_small_translation_separating_arguments
    {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (hc : Function.Injective c) {ε : ℝ} (hε : 0 < ε) :
    ∃ shift : ℂ, ‖shift‖ < ε ∧
      (∀ i, c i + shift ≠ 0) ∧
      ∀ i j, i ≠ j →
        ¬ SamePositiveRay (c i + shift) (c j + shift) := by
  let p : ι ⊕ (ι × ι) → ℂ
    | Sum.inl i => -c i
    | Sum.inr ij => -c ij.2
  let v : ι ⊕ (ι × ι) → ℂ
    | Sum.inl _ => 1
    | Sum.inr ij => c ij.1 - c ij.2
  obtain ⟨shift, hsmall, havoid⟩ :=
    exists_small_avoiding_finite_realAffineLines p v hε
  refine ⟨shift, hsmall, ?_, ?_⟩
  · intro i hi
    have hmem :
        shift ∈ realAffineLine (p (Sum.inl i)) (v (Sum.inl i)) := by
      refine ⟨0, ?_⟩
      change (0 : ℝ) • (1 : ℂ) + -c i = shift
      simpa using (neg_eq_iff_add_eq_zero.mpr hi)
    exact havoid (Sum.inl i) hmem
  · intro i j hij hray
    have hmem :
        shift ∈ realAffineLine
          (p (Sum.inr (i, j))) (v (Sum.inr (i, j))) := by
      simpa [p, v] using
        samePositiveRay_imp_mem_realAffineLine (hc.ne hij) hray
    exact havoid (Sum.inr (i, j)) hmem

/-- Quantitative root-radius estimate used to preserve the open unit disk
under a sufficiently small constant perturbation. -/
theorem norm_lt_one_of_near_root
    {a b : ℂ} {ρ κ : ℝ}
    (hρ : 0 ≤ ρ) (_hκ : 0 ≤ κ) (hsum : κ + ρ < 1)
    (hb : ‖b‖ ≤ ρ) (hab : ‖a - b‖ < κ * max ‖a‖ 1) :
    ‖a‖ < 1 := by
  by_contra! ha
  have hmax : max ‖a‖ 1 = ‖a‖ := max_eq_left ha
  have ha_pos : 0 < ‖a‖ := lt_of_lt_of_le zero_lt_one ha
  have htri : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
    calc
      ‖a‖ = ‖(a - b) + b‖ := by ring_nf
      _ ≤ ‖a - b‖ + ‖b‖ := norm_add_le _ _
  have hlt : ‖a‖ < κ * ‖a‖ + ρ := by
    calc
      ‖a‖ ≤ ‖a - b‖ + ‖b‖ := htri
      _ < κ * max ‖a‖ 1 + ρ := add_lt_add_of_lt_of_le hab hb
      _ = κ * ‖a‖ + ρ := by rw [hmax]
  have hrho : ρ ≤ ρ * ‖a‖ := by
    nlinarith [mul_nonneg hρ (sub_nonneg.mpr ha)]
  have hle : κ * ‖a‖ + ρ ≤ (κ + ρ) * ‖a‖ := by
    nlinarith
  have hcontract : (κ + ρ) * ‖a‖ < ‖a‖ := by
    nlinarith
  linarith

/-- Every root of a constant perturbation of a monic polynomial is
quantitatively close to a root of the original split polynomial. -/
theorem constant_perturbation_root_near_original
    (f : ℂ[X]) (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hsplit : f.Splits) {shift : ℂ} {ε : ℝ}
    (hε : 0 < ε) (hshift : ‖shift‖ < ε) {a : ℂ}
    (ha : (f + C shift).eval a = 0) :
    ∃ b ∈ f.roots,
      ‖a - b‖ <
        ((f.natDegree + 1) * ε) ^ (f.natDegree : ℝ)⁻¹ *
          max ‖a‖ 1 := by
  have hfdeg :
      Polynomial.IsMonicOfDegree f f.natDegree := ⟨rfl, hf⟩
  have hCdeg : (C shift).natDegree < f.natDegree := by
    simpa using hdeg
  have hqdeg :
      Polynomial.IsMonicOfDegree (f + C shift) f.natDegree :=
    hfdeg.add_right hCdeg
  have hroot :=
    Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt
      (f := f + C shift) (g := f) hε ha hqdeg.monic hf
      hqdeg.natDegree_eq.symm
      (fun i => by
        by_cases hi : i = 0
        · subst i
          simpa [norm_neg] using hshift
        · simp [coeff_C, hi, hε])
      hsplit
  simpa [hqdeg.natDegree_eq] using hroot

/-- Under an explicit strict margin, a small constant perturbation preserves
the property that every polynomial root lies in the open unit disk. -/
theorem constant_perturbation_roots_in_unitDisk
    (f : ℂ[X]) (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hsplit : f.Splits) {ρ ε : ℝ} (hρ : 0 ≤ ρ)
    (hroots : ∀ b ∈ f.roots, ‖b‖ ≤ ρ)
    (hε : 0 < ε)
    (hmargin :
      ((f.natDegree + 1) * ε) ^ (f.natDegree : ℝ)⁻¹ + ρ < 1)
    {shift : ℂ} (hshift : ‖shift‖ < ε) :
    ∀ a : ℂ, (f + C shift).eval a = 0 → ‖a‖ < 1 := by
  intro a ha
  obtain ⟨b, hbroot, hab⟩ :=
    constant_perturbation_root_near_original
      f hf hdeg hsplit hε hshift ha
  apply norm_lt_one_of_near_root hρ
      (by positivity)
      hmargin (hroots b hbroot) hab

/-- A uniform derivative margin on a protected set excludes critical points
after a smaller linear-coefficient perturbation. -/
theorem noncritical_on_of_norm_lt_uniform_lower_bound
    {f' : ℂ → ℂ} {C : Set ℂ} {lower : ℝ} {shift : ℂ}
    (hlower : ∀ z ∈ C, lower ≤ ‖f' z‖)
    (hshift : ‖shift‖ < lower) :
    ∀ z ∈ C, f' z + shift ≠ 0 := by
  intro z hz hzero
  have heq : f' z = -shift := by
    calc
      f' z = (f' z + shift) - shift := by ring
      _ = -shift := by rw [hzero]; ring
  have hnorm : ‖f' z‖ = ‖shift‖ := by
    rw [heq, norm_neg]
  have hlt : ‖f' z‖ < lower := by
    rw [hnorm]
    exact hshift
  exact (not_lt_of_ge (hlower z hz)) hlt

/-- The exact endpoint relation supplied by an exponentially decaying
Newton-value orbit forces the endpoints onto one positive ray. -/
theorem samePositiveRay_of_real_exp_decay
    {a b : ℂ} {time : ℝ}
    (hdecay : b = (Real.exp (-time) : ℂ) * a) :
    SamePositiveRay a b := by
  exact ⟨Real.exp (-time), Real.exp_pos _, hdecay⟩

/-- Distinct critical-value rays exclude a Newton-flow connection.  The
topological repair uses this with all critical values chosen on pairwise
distinct rays. -/
theorem no_newtonConnection_of_not_samePositiveRay
    {startValue endValue : ℂ} {time : ℝ}
    (hrays : ¬ SamePositiveRay startValue endValue)
    (hconnection :
      endValue = (Real.exp (-time) : ℂ) * startValue) :
    False :=
  hrays (samePositiveRay_of_real_exp_decay hconnection)

/-! ## Convex-hull confinement at a supporting line

After rotating a supporting line so that its outward normal is the positive
real direction, every root displacement has nonnegative real part.  The
following three lemmas show that the Newton vector points into the supported
half-plane.  They are the algebraic core of the convex-hull invariance
argument recorded in `NewtonConvexHullInvariance.md`.
-/

/-- Inversion preserves the closed right half-plane.  This includes zero,
using Lean's totalized inverse. -/
theorem inv_re_nonneg_of_re_nonneg
    {z : ℂ} (hz : 0 ≤ z.re) :
    0 ≤ z⁻¹.re := by
  rw [Complex.inv_re]
  exact div_nonneg hz (Complex.normSq_nonneg z)

/-- A finite sum of reciprocals of right-half-plane displacements again has
nonnegative real part. -/
theorem reciprocal_sum_re_nonneg
    {ι : Type*} [Fintype ι] (w : ι → ℂ)
    (hw : ∀ i, 0 ≤ (w i).re) :
    0 ≤ (∑ i, (w i)⁻¹).re := by
  rw [Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => inv_re_nonneg_of_re_nonneg (hw i)

/-- Boundary rigidity behind the strict Gauss--Lucas alternative.  If every
displacement lies in a supported half-plane, none is zero, and their
reciprocals balance to zero, then every displacement lies on the supporting
line itself. -/
theorem re_eq_zero_of_reciprocal_sum_eq_zero
    {ι : Type*} [Fintype ι] (w : ι → ℂ)
    (hw : ∀ i, 0 ≤ (w i).re) (hne : ∀ i, w i ≠ 0)
    (hbalance : ∑ i, (w i)⁻¹ = 0) :
    ∀ i, (w i).re = 0 := by
  have hsum : ∑ i, ((w i)⁻¹).re = 0 := by
    have hre := congrArg Complex.re hbalance
    simpa using hre
  have heach : ∀ i, ((w i)⁻¹).re = 0 := by
    exact funext_iff.mp <|
      (Fintype.sum_eq_zero_iff_of_nonneg
        fun i => inv_re_nonneg_of_re_nonneg (hw i)).mp hsum
  intro i
  have hi := heach i
  rw [Complex.inv_re] at hi
  have hnormSq : Complex.normSq (w i) ≠ 0 := by
    exact mt Complex.normSq_eq_zero.mp (hne i)
  exact (div_eq_zero_iff.mp hi).resolve_right hnormSq

/-- The negative reciprocal of a right-half-plane number lies in the closed
left half-plane. -/
theorem neg_inv_re_nonpos_of_re_nonneg
    {z : ℂ} (hz : 0 ≤ z.re) :
    (-z⁻¹).re ≤ 0 := by
  simp only [Complex.neg_re]
  exact neg_nonpos.mpr (inv_re_nonneg_of_re_nonneg hz)

/-- Supporting-half-plane form of Newton convex-hull confinement.  If the
rotated displacements from the roots to the current point all have
nonnegative real part, then the rotated Newton vector
`-(∑ i, w i⁻¹)⁻¹` has nonpositive outward component. -/
theorem newtonReciprocalVector_supportingHalfPlane
    {ι : Type*} [Fintype ι] (w : ι → ℂ)
    (hw : ∀ i, 0 ≤ (w i).re) :
    (-(∑ i, (w i)⁻¹)⁻¹).re ≤ 0 := by
  apply neg_inv_re_nonpos_of_re_nonneg
  exact reciprocal_sum_re_nonneg w hw

/-- A strictly positive displacement makes the supported Newton vector point
strictly into the inward half-plane. -/
theorem newtonReciprocalVector_strictly_inside_of_some_strict_displacement
    {ι : Type*} [Fintype ι] (w : ι → ℂ)
    (hw : ∀ i, 0 ≤ (w i).re) {i₀ : ι} (hi₀ : 0 < (w i₀).re) :
    (-(∑ i, (w i)⁻¹)⁻¹).re < 0 := by
  have hsum : 0 < (∑ i, (w i)⁻¹).re := by
    rw [Complex.re_sum]
    refine Finset.sum_pos' ?_ ⟨i₀, Finset.mem_univ _, ?_⟩
    · intro i hi
      exact inv_re_nonneg_of_re_nonneg (hw i)
    · rw [Complex.inv_re]
      exact div_pos hi₀ (Complex.normSq_pos.mpr (by
        intro hzero
        rw [hzero] at hi₀
        norm_num at hi₀))
  have hsum_ne : (∑ i, (w i)⁻¹) ≠ 0 := by
    intro hzero
    rw [hzero] at hsum
    exact (lt_irrefl 0) hsum
  simp only [Complex.neg_re]
  apply neg_lt_zero.mpr
  rw [Complex.inv_re]
  exact div_pos hsum (Complex.normSq_pos.mpr hsum_ne)

end ErdosProblems.Erdos1041
