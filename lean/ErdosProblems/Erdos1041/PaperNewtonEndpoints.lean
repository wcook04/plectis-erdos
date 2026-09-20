import ErdosProblems.Erdos1041.NewtonFlowTrajectory
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Finite endpoint completion of the Newton positive-ray theorem

The pre-existing flow theorem assumes noncriticality even at the two
endpoints. A saddle connection only supplies that hypothesis on the open
parameter interval. This file passes the exact value law to continuous
endpoints. It constructs no trajectories and asserts no global existence.

New source, not elaborated in this environment.
-/

noncomputable section

namespace ErdosProblems.Erdos1041.PaperNewtonEndpoints

open Set Filter
open scoped Topology

/-- Exponential value decay with differentiability only in the interior.
The endpoint continuity is stated rather than hidden in a trajectory type. -/
theorem value_decay_at_continuous_endpoints
    {v : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn v (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt v (-v t) t) :
    v b = (Real.exp (a - b) : ℂ) * v a := by
  let e : ℕ → ℝ := fun k => (b - a) / ((k : ℝ) + 2)
  let x : ℕ → ℝ := fun k => a + e k
  let y : ℕ → ℝ := fun k => b - e k
  have hepos (k : ℕ) : 0 < e k := by
    dsimp [e]
    exact div_pos (sub_pos.mpr hab) (by positivity)
  have hele (k : ℕ) : e k ≤ (b - a) / 2 := by
    dsimp [e]
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
    nlinarith [show (0 : ℝ) ≤ k by positivity]
  have hxmem (k : ℕ) : x k ∈ Ioo a b := by
    dsimp [x]
    constructor <;> linarith [hepos k, hele k]
  have hymem (k : ℕ) : y k ∈ Ioo a b := by
    dsimp [y]
    constructor <;> linarith [hepos k, hele k]
  have hxy (k : ℕ) : x k ≤ y k := by
    dsimp [x, y]
    linarith [hele k]
  have hdecay (k : ℕ) :
      v (y k) = (Real.exp (x k - y k) : ℂ) * v (x k) := by
    apply value_eq_exp_mul_of_hasDerivAt_neg (hxy k)
    intro t ht
    exact hderiv t ⟨lt_of_lt_of_le (hxmem k).1 ht.1,
      lt_of_le_of_lt ht.2 (hymem k).2⟩
  have hden : Tendsto (fun k : ℕ => (k : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have he : Tendsto e atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hden
  have hx : Tendsto x atTop (𝓝 a) := by
    simpa [x] using tendsto_const_nhds.add he
  have hy : Tendsto y atTop (𝓝 b) := by
    simpa [y] using tendsto_const_nhds.sub he
  have hxw : Tendsto x atTop (𝓝[Icc a b] a) :=
    tendsto_nhdsWithin_iff.mpr ⟨hx, Eventually.of_forall fun k =>
      ⟨(hxmem k).1.le, (hxmem k).2.le⟩⟩
  have hyw : Tendsto y atTop (𝓝[Icc a b] b) :=
    tendsto_nhdsWithin_iff.mpr ⟨hy, Eventually.of_forall fun k =>
      ⟨(hymem k).1.le, (hymem k).2.le⟩⟩
  have hvx : Tendsto (fun k => v (x k)) atTop (𝓝 (v a)) :=
    (hcont a ⟨le_rfl, hab.le⟩).tendsto.comp hxw
  have hvy : Tendsto (fun k => v (y k)) atTop (𝓝 (v b)) :=
    (hcont b ⟨hab.le, le_rfl⟩).tendsto.comp hyw
  have hexp : Tendsto (fun k => (Real.exp (x k - y k) : ℂ)) atTop
      (𝓝 (Real.exp (a - b) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp
      ((Real.continuous_exp.tendsto _).comp (hx.sub hy))
  have hrhs := hexp.mul hvx
  exact tendsto_nhds_unique hvy
    (hrhs.congr' (Eventually.of_forall fun k => (hdecay k).symm))

/-- An existing Newton trajectory with possibly critical continuous endpoints
still has values on one positive ray. Endpoints may have zero value: the
relation then forces both values to be zero. -/
theorem newton_endpoint_samePositiveRay
    {f f' : ℂ → ℂ} {z : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn (fun t => f (z t)) (Icc a b))
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (f' (z t)) (z t))
    (hz : ∀ t ∈ Ioo a b,
      HasDerivAt z (newtonFlowVector (f (z t)) (f' (z t))) t)
    (hnoncritical : ∀ t ∈ Ioo a b, f' (z t) ≠ 0) :
    SamePositiveRay (f (z a)) (f (z b)) := by
  refine ⟨Real.exp (a - b), Real.exp_pos _, ?_⟩
  exact value_decay_at_continuous_endpoints hab hcont
    (fun t ht => newtonFlow_real_value_hasDerivAt
      (hf t ht) (hz t ht) (hnoncritical t ht))

/-- Include the degenerate compact interval as well: coincident endpoint
values satisfy the positive-ray relation with multiplier one. -/
theorem newton_endpoint_samePositiveRay_of_le
    {f f' : ℂ → ℂ} {z : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn (fun t => f (z t)) (Icc a b))
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (f' (z t)) (z t))
    (hz : ∀ t ∈ Ioo a b,
      HasDerivAt z (newtonFlowVector (f (z t)) (f' (z t))) t)
    (hnoncritical : ∀ t ∈ Ioo a b, f' (z t) ≠ 0) :
    SamePositiveRay (f (z a)) (f (z b)) := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · exact newton_endpoint_samePositiveRay hlt hcont hf hz hnoncritical
  · subst b
    exact ⟨1, by norm_num, by simp⟩

/-- The advertised obstruction to a finite saddle-to-saddle connection,
with all trajectory and endpoint premises explicit. -/
theorem no_finite_connection_of_distinct_value_rays
    {f f' : ℂ → ℂ} {z : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn (fun t => f (z t)) (Icc a b))
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (f' (z t)) (z t))
    (hz : ∀ t ∈ Ioo a b,
      HasDerivAt z (newtonFlowVector (f (z t)) (f' (z t))) t)
    (hnoncritical : ∀ t ∈ Ioo a b, f' (z t) ≠ 0)
    (hrays : ¬ SamePositiveRay (f (z a)) (f (z b))) : False :=
  hrays (newton_endpoint_samePositiveRay hab hcont hf hz hnoncritical)

#print axioms value_decay_at_continuous_endpoints
#print axioms newton_endpoint_samePositiveRay
#print axioms newton_endpoint_samePositiveRay_of_le

end ErdosProblems.Erdos1041.PaperNewtonEndpoints
