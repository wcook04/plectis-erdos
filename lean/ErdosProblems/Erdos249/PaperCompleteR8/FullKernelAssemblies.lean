import ErdosProblems.Erdos249.PaperCompleteR8.KernelRelationBasis
import ErdosProblems.Erdos249.PaperCompleteR7.ArithmeticAssemblies
import Erdos249257.TotientMahlerDefect
import Mathlib

set_option autoImplicit false

/-!
# Full displayed basis statements

All finite-level arithmetic and the full odd-core independence theorem are
inherited from the repaired library. No new CRT or limiting assertion is
assumed. The full relation module uses finite-support coefficient vectors;
this is what makes passage to the union of all levels precise.

Mathlib API (pinned source opened):
* LinearAlgebra/Basis/Basic.lean: Module.Basis.span, coe_span_apply.
* Algebra/Module/Submodule/Equiv.lean: LinearEquiv.coe_ofEq_apply.
* LinearAlgebra/Finsupp/LinearCombination.lean: linearCombination_single,
  mem_span_range_iff_exists_finsupp.
* LinearAlgebra/LinearIndependent/Defs.lean: independence is injectivity
  of finite-support evaluation.

New uncompiled source; not a kernel receipt.
-/

namespace ErdosProblems.Erdos249.PaperCompleteR8

open scoped BigOperators
open Erdos249257
open ErdosProblems.Erdos249.PaperCompleteR7

/-- The paper's finite-level theorem, including basis VALUES, both reductions,
and the dimension, in one proposition. -/
theorem displayed_all_base_kernel (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    Module.finrank ℚ (Submodule.span ℚ (Set.range (allBaseThroughLevelFamily k e))) =
      k ^ e + 1 ∧
    (∃ b : Module.Basis (AllBaseCanonicalIndex k e) ℚ
        (Submodule.span ℚ (Set.range (allBaseThroughLevelFamily k e))),
      ∀ i, (b i : ℕ → ℚ) = allBaseCanonicalFamily k e i) ∧
    (∀ j : ℕ, 1 ≤ j →
      allBaseTotientKernelSeq k j 0 =
        (k ^ (j - 1) : ℚ) • allBaseTotientKernelSeq k 1 0) ∧
    (∀ j t u : ℕ, 1 ≤ t → t < j →
      allBaseTotientKernelSeq k j (k ^ t * u) =
        ((k : ℚ) ^ t * missingEulerProduct k u) •
          allBaseTotientKernelSeq k (j - t) u) := by
  refine ⟨finrank_allBaseThroughLevelFamily_eq k e hk he, ?_, ?_, ?_⟩
  · refine ⟨allBaseTotientKernelBasis k e hk he, ?_⟩
    intro i
    simp only [allBaseTotientKernelBasis, Module.Basis.map_apply,
      LinearEquiv.coe_ofEq_apply, Module.Basis.coe_span_apply]
  · intro j hj
    have h := allBaseTotientKernel_zero_residue k (by omega : 0 < k) (j - 1)
    rw [Nat.sub_add_cancel hj] at h
    exact h
  · intro j t u ht htj
    exact paper_maximal_power_reduction k j t u hk ht htj

/-- The literal embedding of the odd-core indices in the infinite kernel. -/
def fullRetainedChannel : TotientOddCoreIndex → TotientDyadicKernelIndex
  | Sum.inl i => ⟨i.val, ⟨0, by positivity⟩⟩
  | Sum.inr ⟨j, r⟩ => ⟨j + 1, ⟨2 * r.val + 1, by
      have hr := r.isLt
      rw [pow_succ]
      omega⟩⟩

theorem fullRetainedChannel_value (i : TotientOddCoreIndex) :
    fullTotientKernelFamily (fullRetainedChannel i) = oddCoreTotientKernelFamily i := by
  cases i with
  | inl i => rfl
  | inr i => cases i; rfl

noncomputable def fullNormalCoefficients (i : TotientDyadicKernelIndex) :
    TotientOddCoreIndex →₀ ℚ :=
  Classical.choose (Finsupp.mem_span_range_iff_exists_finsupp.mp
    (totientKernelSeq_mem_span_oddCore i.1 i.2.val i.2.isLt))

theorem fullNormalCoefficients_spec (i : TotientDyadicKernelIndex) :
    Finsupp.linearCombination ℚ oddCoreTotientKernelFamily (fullNormalCoefficients i) =
      fullTotientKernelFamily i :=
  Classical.choose_spec (Finsupp.mem_span_range_iff_exists_finsupp.mp
    (totientKernelSeq_mem_span_oddCore i.1 i.2.val i.2.isLt))

noncomputable def fullRelationSystem :
    UnitPivot.System ℚ TotientDyadicKernelIndex TotientOddCoreIndex (ℕ → ℚ) where
  value := fullTotientKernelFamily
  keep := fullRetainedChannel
  independent := by
    have h : (fun j => fullTotientKernelFamily (fullRetainedChannel j)) =
        oddCoreTotientKernelFamily := funext fullRetainedChannel_value
    rw [h]
    exact linearIndependent_oddCoreTotientKernelFamily
  coeff := fullNormalCoefficients
  reconstruct := by
    intro i
    have h : (fun j => fullTotientKernelFamily (fullRetainedChannel j)) =
        oddCoreTotientKernelFamily := funext fullRetainedChannel_value
    rw [h]
    exact fullNormalCoefficients_spec i

noncomputable abbrev FullRelations := LinearMap.ker fullRelationSystem.evaluation
abbrev FullOmitted := fullRelationSystem.Omitted

noncomputable def fullRelationBasis : Module.Basis FullOmitted ℚ FullRelations :=
  fullRelationSystem.relationBasis

/-- Convert the base-two version of the all-base canonical index to the
existing odd-core index. The redundant Fin(1) digit is forced to zero. -/
def twoCanonicalToOddCore (e : ℕ) : AllBaseCanonicalIndex 2 e → TotientOddCoreIndex
  | Sum.inl i => Sum.inl i
  | Sum.inr x => Sum.inr ⟨x.1.val, x.2.1⟩

theorem twoCanonicalToOddCore_value (e : ℕ) (i : AllBaseCanonicalIndex 2 e) :
    oddCoreTotientKernelFamily (twoCanonicalToOddCore e i) =
      allBaseCanonicalFamily 2 e i := by
  cases i with
  | inl i => rfl
  | inr x =>
      have hlast : x.2.2.val = 0 := by have hx := x.2.2.isLt; omega
      simp only [twoCanonicalToOddCore, oddCoreTotientKernelFamily,
        allBaseCanonicalFamily, allBaseCanonicalResidue, hlast, zero_add]
      rfl

/-- Every full-kernel channel is a scalar multiple of an odd-core channel.
This applies the finite theorem at the channel's OWN depth, not at a fixed
cutoff, so it is genuinely a statement about the infinite union. -/
theorem full_scalar_reduction (i : TotientDyadicKernelIndex) :
    ∃ j : TotientOddCoreIndex, ∃ a : ℕ,
      fullTotientKernelFamily i = (a : ℚ) • oddCoreTotientKernelFamily j := by
  obtain ⟨b, a, ha⟩ := scalar_canonical_reduction 2 i.1 (by omega)
    i.1 le_rfl i.2.val i.2.isLt
  refine ⟨twoCanonicalToOddCore i.1 b, a, ?_⟩
  rw [twoCanonicalToOddCore_value]
  funext n
  have hn := congrFun ha n
  simpa only [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul, Int.cast_natCast] using hn

/-- Every full relation-basis vector is an elementary scalar reduction. -/
theorem fullRelationBasis_two_term (o : FullOmitted) :
    ∃ j : TotientOddCoreIndex, ∃ a : ℕ,
      fullTotientKernelFamily o.val = (a : ℚ) • oddCoreTotientKernelFamily j ∧
      (fullRelationBasis o : TotientDyadicKernelIndex →₀ ℚ) =
        Finsupp.single o.val 1 - Finsupp.single (fullRetainedChannel j) (a : ℚ) := by
  obtain ⟨j, a, ha⟩ := full_scalar_reduction o.val
  refine ⟨j, a, ha, ?_⟩
  refine (fullRelationSystem.relationBasis_apply o).trans ?_
  apply fullRelationSystem.row_of_scalar_reduction
  change fullTotientKernelFamily o.val =
    (a : ℚ) • fullTotientKernelFamily (fullRetainedChannel j)
  rw [fullRetainedChannel_value]
  exact ha

/-- Full dyadic basis, elementary generation of EVERY finite rational
relation, all positive-depth ranks, and the genuine level-zero rank. -/
theorem displayed_full_dyadic_basis :
    (∃ b : Module.Basis TotientOddCoreIndex ℚ
        (Submodule.span ℚ (Set.range fullTotientKernelFamily)),
      ∀ i, (b i : ℕ → ℚ) = oddCoreTotientKernelFamily i) ∧
    (∃ b : Module.Basis FullOmitted ℚ FullRelations,
      ∀ o, ∃ j : TotientOddCoreIndex, ∃ a : ℕ,
        fullTotientKernelFamily o.val = (a : ℚ) • oddCoreTotientKernelFamily j ∧
        (b o : TotientDyadicKernelIndex →₀ ℚ) =
          Finsupp.single o.val 1 - Finsupp.single (fullRetainedChannel j) (a : ℚ)) ∧
    (∀ e : ℕ, 1 ≤ e → Module.finrank ℚ
      (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))) = 2 ^ e + 1) ∧
    Module.finrank ℚ (Submodule.span ℚ (Set.range (allBaseThroughLevelFamily 2 0))) = 1 := by
  refine ⟨?_, ⟨fullRelationBasis, fullRelationBasis_two_term⟩,
    finrank_totientKernelThroughLevelFamily_eq, complete_level_zero_rank 2⟩
  refine ⟨totientDyadicSectionBasis, ?_⟩
  intro i
  simp only [totientDyadicSectionBasis, Module.Basis.map_apply,
    LinearEquiv.coe_ofEq_apply, Module.Basis.coe_span_apply]

/-- The additional canonical-cardinality clause in long-record environment
036 is separate from the complete truncation at e=0. -/
theorem displayed_canonical_and_full_dyadic :
    (∀ e : ℕ, Fintype.card (TotientCanonicalIndex e) = 2 ^ e + 1 ∧
      LinearIndependent ℚ (canonicalTotientKernelFamily e)) ∧
    (∃ b : Module.Basis TotientOddCoreIndex ℚ
        (Submodule.span ℚ (Set.range fullTotientKernelFamily)),
      ∀ i, (b i : ℕ → ℚ) = oddCoreTotientKernelFamily i) ∧
    (∀ e : ℕ, 1 ≤ e → Module.finrank ℚ
      (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))) = 2 ^ e + 1) ∧
    Module.finrank ℚ (Submodule.span ℚ (Set.range (allBaseThroughLevelFamily 2 0))) = 1 := by
  refine ⟨?_, displayed_full_dyadic_basis.1,
    displayed_full_dyadic_basis.2.2.1, displayed_full_dyadic_basis.2.2.2⟩
  intro e
  exact ⟨card_totientCanonicalIndex e, linearIndependent_canonicalTotientKernelFamily e⟩

end ErdosProblems.Erdos249.PaperCompleteR8
