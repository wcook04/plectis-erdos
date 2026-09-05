import ErdosProblems.Erdos1041.NewtonFlowRaySeparation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Topology.Algebra.Order.Field

/-!
# Real-time Newton trajectories

The local cancellation law gives exact exponential decay on any interval
where a real-time trajectory exists and avoids critical points.  This bridges
the local derivative calculation to the positive-ray consumer.  It does not
construct trajectories, continue them through saddles, or bound their length.
-/

namespace ErdosProblems.Erdos1041

open Set

/-- The complex polynomial chain rule along a real-time Newton trajectory. -/
theorem newtonFlow_real_value_hasDerivAt
    {f f' : ℂ → ℂ} {z : ℝ → ℂ} {t : ℝ}
    (hf : HasDerivAt f (f' (z t)) (z t))
    (hz : HasDerivAt z (newtonFlowVector (f (z t)) (f' (z t))) t)
    (hcritical : f' (z t) ≠ 0) :
    HasDerivAt (fun s => f (z s)) (-f (z t)) t := by
  have h := hf.complexToReal_fderiv.comp_hasDerivAt t hz
  simpa only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
    smul_eq_mul, derivative_mul_newtonFlowVector hcritical] using h

/-- A complex-valued solution of `v' = -v` on a real interval has the exact
exponential endpoint relation.  All differentiability assumptions are local
to that interval. -/
theorem value_eq_exp_mul_of_hasDerivAt_neg
    {v : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (-v t) t) :
    v b = (Real.exp (a - b) : ℂ) * v a := by
  let g : ℝ → ℂ := fun t => Complex.exp (t : ℂ) * v t
  have hg (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt g 0 t := by
    have he := (Complex.hasDerivAt_exp (t : ℂ)).comp_ofReal
    convert he.mul (hv t ht) using 1 <;> simp [g] <;> ring
  have hnorm := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hg t ht).hasDerivWithinAt)
    (C := 0) (fun t ht => by simp)
    (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
  have heq : g b = g a := by
    simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hnorm
  have hfactor : (Real.exp (a - b) : ℂ) * Complex.exp (b : ℂ) =
      Complex.exp (a : ℂ) := by
    rw [← Complex.ofReal_exp, ← Complex.ofReal_mul, ← Real.exp_add]
    simp
  apply (mul_left_cancel₀ (Complex.exp_ne_zero (b : ℂ)))
  calc
    Complex.exp (b : ℂ) * v b = Complex.exp (a : ℂ) * v a := heq
    _ = Complex.exp (b : ℂ) * ((Real.exp (a - b) : ℂ) * v a) := by
      rw [← hfactor]
      ring

/-- Exact value decay for an existing nonsingular real-time Newton trajectory. -/
theorem newtonFlow_real_value_decay
    {f f' : ℂ → ℂ} {z : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' (z t)) (z t))
    (hz : ∀ t ∈ Icc a b,
      HasDerivAt z (newtonFlowVector (f (z t)) (f' (z t))) t)
    (hcritical : ∀ t ∈ Icc a b, f' (z t) ≠ 0) :
    f (z b) = (Real.exp (a - b) : ℂ) * f (z a) :=
  value_eq_exp_mul_of_hasDerivAt_neg hab
    (fun t ht => newtonFlow_real_value_hasDerivAt (hf t ht) (hz t ht) (hcritical t ht))

/-- Ray separation now follows directly from the trajectory equation rather
than from a separately supplied exponential endpoint identity. -/
theorem newtonFlow_real_samePositiveRay
    {f f' : ℂ → ℂ} {z : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' (z t)) (z t))
    (hz : ∀ t ∈ Icc a b,
      HasDerivAt z (newtonFlowVector (f (z t)) (f' (z t))) t)
    (hcritical : ∀ t ∈ Icc a b, f' (z t) ≠ 0) :
    SamePositiveRay (f (z a)) (f (z b)) :=
  ⟨Real.exp (a - b), Real.exp_pos _, newtonFlow_real_value_decay hab hf hz hcritical⟩

/-- Along a nonzero value trajectory, the potential `-log ‖v‖` increases
exactly by elapsed time.  This is the second scalar identity in the relative
global-flow problem; existence and endpoint classification are separate. -/
theorem neg_log_norm_eq_of_hasDerivAt_neg
    {v : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (-v t) t) (ha : v a ≠ 0) :
    -Real.log ‖v b‖ = -Real.log ‖v a‖ + (b - a) := by
  rw [value_eq_exp_mul_of_hasDerivAt_neg hab hv, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Real.log_mul (ne_of_gt (Real.exp_pos _)) (norm_ne_zero_iff.mpr ha), Real.log_exp]
  ring

/-- Nonzero value trajectories cannot return to the same value at a later
time. This excludes closed trajectories, without asserting the stronger
orbit-space or saddle-endpoint classification. -/
theorem value_ne_at_later_time_of_hasDerivAt_neg
    {v : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (-v t) t) (ha : v a ≠ 0) :
    v b ≠ v a := by
  intro heq
  have h := neg_log_norm_eq_of_hasDerivAt_neg hab.le hv ha
  rw [heq] at h
  linarith

/-- A value trajectory that exists for all future times tends to zero. -/
theorem tendsto_zero_of_hasDerivAt_neg
    {v : ℝ → ℂ} {a : ℝ}
    (hv : ∀ t, a ≤ t → HasDerivAt v (-v t) t) :
    Filter.Tendsto v Filter.atTop (nhds 0) := by
  have he : Filter.Tendsto (fun t : ℝ => Real.exp a / Real.exp t)
      Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds Real.tendsto_exp_atTop
  have hc := ((Complex.continuous_ofReal.tendsto 0).comp he).mul_const (v a)
  have hscaled : Filter.Tendsto
      (fun t : ℝ => ((Real.exp a / Real.exp t : ℝ) : ℂ) * v a)
      Filter.atTop (nhds 0) := by simpa using hc
  apply hscaled.congr'
  filter_upwards [Filter.eventually_ge_atTop a] with t ht
  simpa only [Real.exp_sub] using
    (value_eq_exp_mul_of_hasDerivAt_neg ht (fun s hs => hv s hs.1)).symm

/-- If an existing forward trajectory converges in the plane, its limit is
a root. No convergence or global existence is supplied by this theorem. -/
theorem limit_is_root_of_value_hasDerivAt_neg
    {f : ℂ → ℂ} {z : ℝ → ℂ} {a : ℝ} {l : ℂ}
    (hf : ContinuousAt f l)
    (hz : Filter.Tendsto z Filter.atTop (nhds l))
    (hv : ∀ t, a ≤ t → HasDerivAt (fun s => f (z s)) (-f (z t)) t) :
    f l = 0 :=
  tendsto_nhds_unique (hf.tendsto.comp hz) (tendsto_zero_of_hasDerivAt_neg hv)

end ErdosProblems.Erdos1041
