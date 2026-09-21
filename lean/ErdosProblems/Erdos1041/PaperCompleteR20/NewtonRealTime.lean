import ErdosProblems.Erdos1041.PaperNewtonEndpoints

/-! Complete real-time value and endpoint statements on arbitrary intervals.
Within-interval derivatives permit one-sided derivatives at included endpoints.
The trajectory is given; no existence or continuation assertion is made. -/

namespace ErdosProblems.Erdos1041.PaperCompleteR20

open Set

theorem newton_value_hasDerivWithinAt
    {f f' : ℂ → ℂ} {z : ℝ → ℂ} {I : Set ℝ} {t : ℝ}
    (hf : HasDerivAt f (f' (z t)) (z t))
    (hz : HasDerivWithinAt z (newtonFlowVector (f (z t)) (f' (z t))) I t)
    (hc : f' (z t) ≠ 0) :
    HasDerivWithinAt (fun s => f (z s)) (-f (z t)) I t := by
  have h := hf.complexToReal_fderiv.comp_hasDerivWithinAt t hz
  simpa only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
    smul_eq_mul, derivative_mul_newtonFlowVector hc] using h

private theorem value_decay_on_interval_of_lt
    {v : ℝ → ℂ} {I : Set ℝ} (hI : OrdConnected I)
    (hv : ∀ t ∈ I, HasDerivWithinAt v (-v t) I t)
    {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) (hab : a < b) :
    v b = (Real.exp (a - b) : ℂ) * v a := by
  have hcont : ContinuousOn v I := fun t ht => (hv t ht).continuousWithinAt
  apply PaperNewtonEndpoints.value_decay_at_continuous_endpoints hab
    (hcont.mono (hI.out ha hb))
  intro t ht
  have htI : t ∈ I := hI.out ha hb ⟨ht.1.le, ht.2.le⟩
  apply (hv t htI).hasDerivAt
  exact Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2)
    (fun u hu => hI.out ha hb ⟨hu.1.le, hu.2.le⟩)

/-- Both time orders, arbitrary intervals, and included endpoints. -/
theorem value_decay_on_interval
    {v : ℝ → ℂ} {I : Set ℝ} (hI : OrdConnected I)
    (hv : ∀ t ∈ I, HasDerivWithinAt v (-v t) I t)
    {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) :
    v b = (Real.exp (a - b) : ℂ) * v a := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact value_decay_on_interval_of_lt hI hv ha hb hab
  · subst b
    simp
  · have h := value_decay_on_interval_of_lt hI hv hb ha hab
    have he : (Real.exp (a - b) : ℂ) * (Real.exp (b - a) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      simp
    rw [h, ← mul_assoc, he, one_mul]

/-- The complete paper value equation, with the integrated identity included. -/
theorem newton_real_value_whole
    {f f' : ℂ → ℂ} {z : ℝ → ℂ} {I : Set ℝ} (hI : OrdConnected I)
    (hf : ∀ t ∈ I, HasDerivAt f (f' (z t)) (z t))
    (hz : ∀ t ∈ I,
      HasDerivWithinAt z (newtonFlowVector (f (z t)) (f' (z t))) I t)
    (hc : ∀ t ∈ I, f' (z t) ≠ 0) :
    (∀ t ∈ I, HasDerivWithinAt (fun s => f (z s)) (-f (z t)) I t) ∧
    (∀ t ∈ I, ∀ t₀ ∈ I,
      f (z t) = (Real.exp (-(t - t₀)) : ℂ) * f (z t₀)) := by
  have hv : ∀ t ∈ I, HasDerivWithinAt (fun s => f (z s)) (-f (z t)) I t :=
    fun t ht => newton_value_hasDerivWithinAt (hf t ht) (hz t ht) (hc t ht)
  refine ⟨hv, ?_⟩
  intro t ht t₀ ht₀
  simpa only [neg_sub] using value_decay_on_interval hI hv ht₀ ht

/-- The complete finite-endpoint ray statement uses only interior Newton data.
Continuity of the value curve suffices, including at critical endpoints. -/
theorem newton_real_endpoint_whole
    {f f' : ℂ → ℂ} {z : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn (fun t => f (z t)) (Icc a b))
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (f' (z t)) (z t))
    (hz : ∀ t ∈ Ioo a b,
      HasDerivAt z (newtonFlowVector (f (z t)) (f' (z t))) t)
    (hc : ∀ t ∈ Ioo a b, f' (z t) ≠ 0) :
    f (z b) = (Real.exp (a - b) : ℂ) * f (z a) ∧
      SamePositiveRay (f (z a)) (f (z b)) := by
  have he := PaperNewtonEndpoints.value_decay_at_continuous_endpoints hab hcont
    (fun t ht => newtonFlow_real_value_hasDerivAt (hf t ht) (hz t ht) (hc t ht))
  exact ⟨he, Real.exp (a - b), Real.exp_pos _, he⟩

#print axioms newton_real_value_whole
#print axioms newton_real_endpoint_whole
#print axioms newton_value_hasDerivWithinAt

end ErdosProblems.Erdos1041.PaperCompleteR20
