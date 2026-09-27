import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Covering.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Set.Card
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic

/-!
# The value domain obtained by removing outward slits

The unit disc minus any family of outward rays starting at nonzero points is
star-convex at zero, contractible, and simply connected. The family may be
infinite; distinct directions and distinct moduli are unnecessary here.

A nonconstant complex polynomial is a covering over any set of regular values.
In particular, when the slit starts include every critical value in the unit
disc, its restriction over this domain is a surjective covering.

The component restriction below uses only critical points in that component;
critical values belonging to other components need not be removed.

These are prerequisites of the attachment-aware Reeb paper claim. They do not
count or identify the sheets of one selected lemniscate component, prove monodromy,
Morse assertions, or the embedded inverse-arc tree. For an infinite family,
no openness of the remaining domain is asserted.
-/

noncomputable section

namespace ErdosProblems.Erdos1041.OutwardSlitDomain

private instance : ContinuousSMul ℝ ℂ where
  continuous_smul := by
    have hfun : (fun p : ℝ × ℂ => p.1 • p.2) =
        fun p : ℝ × ℂ => (p.1 : ℂ) * p.2 := by
      funext p
      exact Complex.real_smul
    rw [hfun]
    exact (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd

private instance : NormSMulClass ℝ ℂ where
  norm_smul r z := by
    rw [show r • z = (r : ℂ) * z from Complex.real_smul, norm_mul]
    simp

/-- Remove the part at or beyond each slit start. Intersecting these complete
rays with the unit disc gives exactly the outward slits in the paper. -/
def domain {ι : Type*} (v : ι → ℂ) : Set ℂ :=
  {z | ‖z‖ < 1 ∧ ∀ i, ¬ ∃ s : ℝ, 1 ≤ s ∧ z = s • v i}

theorem zero_mem {ι : Type*} (v : ι → ℂ) (hv : ∀ i, v i ≠ 0) :
    (0 : ℂ) ∈ domain v := by
  refine ⟨by simp, ?_⟩
  rintro i ⟨s, hs, heq⟩
  exact (smul_ne_zero (by linarith : s ≠ 0) (hv i)) heq.symm

/-- A contraction cannot enter an outward ray: if `b • z = s • v i`,
then the original point is `(s / b) • v i`, with `s / b ≥ 1`. -/
theorem starConvex {ι : Type*} (v : ι → ℂ) (hv : ∀ i, v i ≠ 0) :
    StarConvex ℝ (0 : ℂ) (domain v) := by
  intro z hz a b ha hb hab
  rw [show a • (0 : ℂ) = (a : ℂ) * 0 from Complex.real_smul, mul_zero, zero_add]
  have hb1 : b ≤ 1 := by linarith
  refine ⟨?_, ?_⟩
  · calc
      ‖b • z‖ = b * ‖z‖ := by rw [norm_smul, Real.norm_of_nonneg hb]
      _ ≤ ‖z‖ := by nlinarith [norm_nonneg z]
      _ < 1 := hz.1
  · rintro i ⟨s, hs, heq⟩
    by_cases hb0 : b = 0
    · exact (smul_ne_zero (by linarith : s ≠ 0) (hv i))
        (by simpa [hb0] using heq.symm)
    have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    apply hz.2 i
    refine ⟨s / b, (le_div_iff₀ hbp).2 (by linarith), ?_⟩
    have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb0
    apply mul_left_cancel₀ hbC
    calc
      (b : ℂ) * z = (s : ℂ) * v i := by
        simpa only [Complex.real_smul] using heq
      _ = (b : ℂ) * ((s / b) • v i) := by
        rw [Complex.real_smul, Complex.ofReal_div]
        field_simp [hbC]

theorem contractible {ι : Type*} (v : ι → ℂ) (hv : ∀ i, v i ≠ 0) :
    ContractibleSpace (domain v) :=
  (starConvex v hv).contractibleSpace ⟨0, zero_mem v hv⟩

theorem simplyConnected {ι : Type*} (v : ι → ℂ) (hv : ∀ i, v i ≠ 0) :
    SimplyConnectedSpace (domain v) := by
  letI : ContractibleSpace (domain v) := contractible v hv
  infer_instance

/-- Every fibre of a nonconstant polynomial is finite, including fibres over
critical values. Nonconstancy is essential here. -/
theorem polynomial_finite_fiber (p : Polynomial ℂ) (hp : 0 < p.natDegree) (w : ℂ) :
    (p.eval ⁻¹' {w}).Finite := by
  have hne : p - Polynomial.C w ≠ 0 := by
    intro h
    have heq := sub_eq_zero.mp h
    rw [heq] at hp
    simpa using hp
  simpa only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C,
    sub_eq_zero, Set.preimage, Set.mem_singleton_iff] using
    (Polynomial.finite_setOf_isRoot hne)

/-- Properness of polynomial evaluation, finite fibres, and the inverse function
theorem produce an actual covering over any set of regular values. -/
theorem polynomial_isCoveringMapOn (p : Polynomial ℂ) (hp : 0 < p.natDegree)
    (s : Set ℂ) (hregular : ∀ z, p.eval z ∈ s → p.derivative.eval z ≠ 0) :
    IsCoveringMapOn p.eval s := by
  refine p.isClosedMap_eval.isCoveringMapOn_of_openPartialHomeomorph
    (fun w _ => polynomial_finite_fiber p hp w) ?_
  intro z hz
  have hd := (p.hasStrictDerivAt z).hasStrictFDerivAt_equiv (hregular z hz)
  exact ⟨hd.toOpenPartialHomeomorph p.eval,
    hd.mem_toOpenPartialHomeomorph_source, hd.toOpenPartialHomeomorph_coe⟩

/-- Removing a slit starting at every critical value in the unit disc removes
all ramification from its polynomial preimage. No separation of the critical
values, and no simplicity assumption on critical points, is needed. -/
theorem polynomial_regular_over_domain {ι : Type*} (p : Polynomial ℂ) (v : ι → ℂ)
    (hcritical : ∀ z, p.derivative.eval z = 0 → ‖p.eval z‖ < 1 →
      ∃ i, p.eval z = v i) :
    ∀ z, p.eval z ∈ domain v → p.derivative.eval z ≠ 0 := by
  intro z hz hzero
  obtain ⟨i, hi⟩ := hcritical z hzero hz.1
  exact hz.2 i ⟨1, le_rfl, by simpa using hi⟩

/-- The polynomial restricted to the preimage of the outward-slit domain is a
covering map. This is a global preimage statement; selecting a lemniscate
component and counting its sheets are separate obligations. -/
theorem polynomial_isCoveringMap {ι : Type*} (p : Polynomial ℂ)
    (hp : 0 < p.natDegree) (v : ι → ℂ)
    (hcritical : ∀ z, p.derivative.eval z = 0 → ‖p.eval z‖ < 1 →
      ∃ i, p.eval z = v i) :
    IsCoveringMap ((domain v).restrictPreimage p.eval) :=
  (polynomial_isCoveringMapOn p hp (domain v)
    (polynomial_regular_over_domain p v hcritical)).isCoveringMap_restrictPreimage

/-- Every value in the slit domain has a polynomial preimage in the restricted
source. This supplies surjectivity separately from Mathlib's covering predicate,
which also permits empty fibres. -/
theorem polynomial_restrict_surjective {ι : Type*} (p : Polynomial ℂ)
    (hp : 0 < p.natDegree) (v : ι → ℂ) :
    Function.Surjective ((domain v).restrictPreimage p.eval) := by
  intro w
  obtain ⟨z, hz⟩ := IsAlgClosed.eval_surjective (ne_of_gt hp) w.val
  exact ⟨⟨z, by simpa [hz] using w.property⟩, Subtype.ext hz⟩

/-- A regular value of a degree-`n` complex polynomial has exactly `n` distinct
preimages. The count is without multiplicity. -/
theorem polynomial_fiber_ncard (p : Polynomial ℂ) (hp : 0 < p.natDegree)
    (w : ℂ) (hregular : ∀ z, p.eval z = w → p.derivative.eval z ≠ 0) :
    (p.eval ⁻¹' {w}).ncard = p.natDegree := by
  classical
  have hne : p - Polynomial.C w ≠ 0 := by
    intro h
    have heq := sub_eq_zero.mp h
    rw [heq] at hp
    simpa using hp
  have hnodup : (p - Polynomial.C w).roots.Nodup := by
    apply Multiset.nodup_iff_count_le_one.mpr
    intro z
    rw [Polynomial.count_roots]
    by_contra hn
    have hh := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hne).mp (by omega :
      1 < (p - Polynomial.C w).rootMultiplicity z)
    have hz : p.eval z = w := by
      simpa [Polynomial.IsRoot, sub_eq_zero] using hh.1
    exact hregular z hz (by simpa [Polynomial.IsRoot] using hh.2)
  have hset : p.eval ⁻¹' {w} = ((p - Polynomial.C w).roots.toFinset : Set ℂ) := by
    ext z
    simp [Polynomial.mem_roots hne, Polynomial.IsRoot, sub_eq_zero]
  rw [hset, Set.ncard_coe_finset, Multiset.toFinset_card_of_nodup hnodup,
    ← (IsAlgClosed.splits (p - Polynomial.C w)).natDegree_eq_card_roots,
    Polynomial.natDegree_sub_C]

/-- The unit disc, as a value space. Components below are formed in its full
polynomial preimage, so relative closedness does not assert closedness in ℂ. -/
def unitDisc : Set ℂ := Metric.ball 0 1

/-- Evaluation on one connected component of the strict unit sublevel. -/
def componentEval (p : Polynomial ℂ) (z : p.eval ⁻¹' unitDisc) :
    connectedComponent z → unitDisc :=
  fun e => unitDisc.restrictPreimage p.eval e.val

theorem componentEval_continuous (p : Polynomial ℂ) (z : p.eval ⁻¹' unitDisc) :
    Continuous (componentEval p z) :=
  (p.continuous_aeval.restrictPreimage).comp continuous_subtype_val

/-- A component is relatively closed in the full preimage. Restricting the
closed polynomial map twice therefore preserves closedness. -/
theorem componentEval_isClosedMap (p : Polynomial ℂ) (z : p.eval ⁻¹' unitDisc) :
    IsClosedMap (componentEval p z) :=
  (p.isClosedMap_eval.restrictPreimage unitDisc).restrict
    isClosed_connectedComponent

/-- Every individual sublevel component maps onto the entire disc. Its image
is nonempty and both open and closed in the connected value disc; a global
algebraic-closure preimage witness would not establish this statement. -/
theorem componentEval_surjective (p : Polynomial ℂ) (hp : 0 < p.natDegree)
    (z : p.eval ⁻¹' unitDisc) : Function.Surjective (componentEval p z) := by
  letI : LocallyConnectedSpace (p.eval ⁻¹' unitDisc) :=
    ((Metric.isOpen_ball : IsOpen unitDisc).preimage p.continuous_aeval).locallyConnectedSpace
  letI : PreconnectedSpace unitDisc :=
    Subtype.preconnectedSpace (convex_ball (0 : ℂ) (1 : ℝ)).isPreconnected
  let f := unitDisc.restrictPreimage p.eval
  have hclosed : IsClosed (f '' connectedComponent z) :=
    (p.isClosedMap_eval.restrictPreimage unitDisc) _ isClosed_connectedComponent
  have hopen : IsOpen (f '' connectedComponent z) :=
    ((p.isOpenQuotientMap_eval (ne_of_gt hp)).isOpenMap.restrictPreimage unitDisc)
      _ isOpen_connectedComponent
  have hall : f '' connectedComponent z = Set.univ :=
    (show IsClopen (f '' connectedComponent z) from ⟨hclosed, hopen⟩).eq_univ
      ⟨f z, z, mem_connectedComponent, rfl⟩
  intro w
  have hw : w ∈ f '' connectedComponent z := by rw [hall]; trivial
  obtain ⟨e, he, hew⟩ := hw
  exact ⟨⟨e, he⟩, hew⟩

/-- Restricting to a component cannot introduce infinitely many fibre points.
No equality with the global polynomial degree is asserted. -/
theorem componentEval_finite_fiber (p : Polynomial ℂ) (hp : 0 < p.natDegree)
    (z : p.eval ⁻¹' unitDisc) (w : unitDisc) :
    (componentEval p z ⁻¹' {w}).Finite := by
  letI : Finite (p.eval ⁻¹' {w.val}) := polynomial_finite_fiber p hp w.val
  let inclusion : (componentEval p z ⁻¹' {w}) → (p.eval ⁻¹' {w.val}) :=
    fun e => ⟨e.val.val.val, congrArg Subtype.val e.property⟩
  have hinj : Function.Injective inclusion := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : p.eval ⁻¹' {w.val} => x.val) hab
  haveI : Finite (componentEval p z ⁻¹' {w}) := Finite.of_injective inclusion hinj
  exact Set.toFinite _

/-- The regular-value covering theorem with the paper's component-local
hypothesis. Other components may have critical points over these same values. -/
theorem componentEval_isCoveringMapOn (p : Polynomial ℂ) (hp : 0 < p.natDegree)
    (z : p.eval ⁻¹' unitDisc) (s : Set unitDisc)
    (hregular : ∀ e : connectedComponent z,
      componentEval p z e ∈ s → p.derivative.eval e.val.val ≠ 0) :
    IsCoveringMapOn (componentEval p z) s := by
  letI : LocallyConnectedSpace (p.eval ⁻¹' unitDisc) :=
    ((Metric.isOpen_ball : IsOpen unitDisc).preimage p.continuous_aeval).locallyConnectedSpace
  let j : connectedComponent z → ℂ := fun e => e.val.val
  have hj : Topology.IsOpenEmbedding j :=
    (((Metric.isOpen_ball : IsOpen unitDisc).preimage p.continuous_aeval).isOpenEmbedding_subtypeVal).comp
      isOpen_connectedComponent.isOpenEmbedding_subtypeVal
  have hp_local : IsLocalHomeomorphOn p.eval
      (j '' (componentEval p z ⁻¹' s)) := by
    rintro _ ⟨e, he, rfl⟩
    have hd := (p.hasStrictDerivAt (j e)).hasStrictFDerivAt_equiv (hregular e he)
    exact ⟨hd.toOpenPartialHomeomorph p.eval,
      hd.mem_toOpenPartialHomeomorph_source, hd.toOpenPartialHomeomorph_coe.symm⟩
  have hcomp : IsLocalHomeomorphOn (p.eval ∘ j) (componentEval p z ⁻¹' s) :=
    hp_local.comp hj.isLocalHomeomorph.isLocalHomeomorphOn
      (fun e he => ⟨e, he, rfl⟩)
  change IsLocalHomeomorphOn (Subtype.val ∘ componentEval p z)
    (componentEval p z ⁻¹' s) at hcomp
  have hlocal : IsLocalHomeomorphOn (componentEval p z)
      (componentEval p z ⁻¹' s) :=
    hcomp.of_comp_left
      ((Metric.isOpen_ball : IsOpen unitDisc).isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn)
      (fun _ _ => (componentEval_continuous p z).continuousAt)
  refine (componentEval_isClosedMap p z).isCoveringMapOn_of_openPartialHomeomorph
    (fun w _ => componentEval_finite_fiber p hp z w) ?_
  intro e he
  obtain ⟨chart, hchart, heq⟩ := hlocal e he
  exact ⟨chart, hchart, heq.symm⟩

/-- Slits need cover only critical values attained by the selected component. -/
theorem componentEval_slit_covering {ι : Type*} (p : Polynomial ℂ)
    (hp : 0 < p.natDegree) (z : p.eval ⁻¹' unitDisc) (v : ι → ℂ)
    (hcritical : ∀ e : connectedComponent z,
      p.derivative.eval e.val.val = 0 → ∃ i, p.eval e.val.val = v i) :
    IsCoveringMapOn (componentEval p z) {w | w.val ∈ domain v} := by
  apply componentEval_isCoveringMapOn p hp z
  intro e he hzero
  obtain ⟨i, hi⟩ := hcritical e hzero
  exact he.2 i ⟨1, le_rfl, by simpa [componentEval] using hi⟩

/-- Each outward ray with a nonzero start is closed in the whole value plane. -/
theorem isClosed_outwardRay (v : ℂ) (hv : v ≠ 0) :
    IsClosed {z : ℂ | ∃ s : ℝ, 1 ≤ s ∧ z = s • v} := by
  have heq : {z : ℂ | ∃ s : ℝ, 1 ≤ s ∧ z = s • v} =
      {z : ℂ | (z / v).im = 0 ∧ 1 ≤ (z / v).re} := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      simp [Complex.real_smul, hv, hs]
    · rintro ⟨him, hre⟩
      refine ⟨(z / v).re, hre, ?_⟩
      have hc : ((z / v).re : ℂ) = z / v := by
        apply Complex.ext <;> simp [him]
      rw [Complex.real_smul, hc, div_mul_cancel₀ _ hv]
  rw [heq]
  exact (isClosed_eq (Complex.continuous_im.comp (continuous_id.div_const v))
    continuous_const).inter
    (isClosed_le continuous_const (Complex.continuous_re.comp (continuous_id.div_const v)))

/-- For finitely many nonzero slit starts the remaining value domain is open.
Finiteness is essential: infinitely many starts may accumulate at zero. -/
theorem isOpen_domain {ι : Type*} [Finite ι] (v : ι → ℂ) (hv : ∀ i, v i ≠ 0) :
    IsOpen (domain v) := by
  have heq : domain v = {z : ℂ | ‖z‖ < 1} ∩
      ⋂ i, {z : ℂ | ∃ s : ℝ, 1 ≤ s ∧ z = s • v i}ᶜ := by
    ext z
    simp [domain]
  rw [heq]
  exact (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_iInter_of_finite fun i => (isClosed_outwardRay (v i) (hv i)).isOpen_compl)

/-- Every root determines a unique continuous inverse branch on the finite
outward-slit domain. This proves branch existence, not yet the component-wise
conformal sheet decomposition or the monodromy tree. -/
theorem existsUnique_root_branch {ι : Type*} [Finite ι] (p : Polynomial ℂ)
    (hp : 0 < p.natDegree) (v : ι → ℂ) (hv : ∀ i, v i ≠ 0)
    (hcritical : ∀ z, p.derivative.eval z = 0 → ‖p.eval z‖ < 1 →
      ∃ i, p.eval z = v i) (a : ℂ) (ha : p.eval a = 0) :
    ∃! F : C(domain v, p.eval ⁻¹' domain v),
      F ⟨0, zero_mem v hv⟩ = ⟨a, by simpa [ha] using zero_mem v hv⟩ ∧
      (domain v).restrictPreimage p.eval ∘ F = ContinuousMap.id (domain v) := by
  letI : SimplyConnectedSpace (domain v) := simplyConnected v hv
  letI : LocPathConnectedSpace (domain v) := (isOpen_domain v hv).locPathConnectedSpace
  apply (polynomial_isCoveringMap p hp v hcritical).existsUnique_continuousMap_lifts
  exact Subtype.ext ha

#print axioms zero_mem
#print axioms starConvex
#print axioms contractible
#print axioms simplyConnected
#print axioms polynomial_finite_fiber
#print axioms polynomial_isCoveringMapOn
#print axioms polynomial_regular_over_domain
#print axioms polynomial_isCoveringMap
#print axioms polynomial_restrict_surjective
#print axioms polynomial_fiber_ncard
#print axioms componentEval_continuous
#print axioms componentEval_isClosedMap
#print axioms componentEval_surjective
#print axioms componentEval_finite_fiber
#print axioms componentEval_isCoveringMapOn
#print axioms componentEval_slit_covering
#print axioms isClosed_outwardRay
#print axioms isOpen_domain
#print axioms existsUnique_root_branch

end ErdosProblems.Erdos1041.OutwardSlitDomain
