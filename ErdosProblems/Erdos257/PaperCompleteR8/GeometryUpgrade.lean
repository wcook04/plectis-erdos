import Erdos249257.GreedyAchievementSet
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# The precise achievement-set span and generic compactness

UNCOMPILED. Completes the numerical-span clauses omitted by the existing
geometry assembly and proves the genuinely transferable compactness theorem.
No statement here transfers the numerical measure one to arbitrary weights.
No Bernoulli law or periodic-stride dimension is claimed by these theorems.

Pinned API: Mathlib/Analysis/Normed/Group/FunctionSeries.lean,
`continuous_tsum`. The finite binary norm bound and compact-image argument
are exactly the method in the supplied GreedyAchievementSet.lean. The two
finite rational enclosures use norm_num (kernel proof generation), not an
untrusted native evaluation.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open scoped ENNReal
open Set MeasureTheory
open Erdos249257

/-- Generic binary achievement coding for absolutely summable real weights. -/
def binaryWeightValue (w : ℕ→ℝ) (b : ℕ→Fin 2) : ℝ :=
  ∑' n : ℕ, ((b n:ℕ):ℝ)*w n

theorem continuous_binaryWeightValue (w : ℕ→ℝ)
    (hs : Summable (fun n => ‖w n‖)) : Continuous (binaryWeightValue w) := by
  unfold binaryWeightValue
  apply continuous_tsum (fun n => by fun_prop) hs
  intro n b
  by_cases hb : b n=0
  · simp only [hb,Fin.val_zero,Nat.cast_zero,zero_mul,norm_zero]
    exact norm_nonneg _
  · have hb1 : b n=1 := Fin.eq_one_of_ne_zero (b n) hb
    simp only [hb1,Fin.val_one,Nat.cast_one,one_mul,le_refl]

/-- Compactness needs absolute convergence, not superincreasingness. -/
theorem generic_binary_achievement_compact_closed (w : ℕ→ℝ)
    (hs : Summable (fun n => ‖w n‖)) :
    IsCompact (Set.range (binaryWeightValue w)) ∧
    IsClosed (Set.range (binaryWeightValue w)) := by
  have hc : IsCompact (Set.range (binaryWeightValue w)) := by
    rw [←Set.image_univ]
    exact isCompact_univ.image (continuous_binaryWeightValue w hs)
  exact ⟨hc,hc.isClosed⟩

/-- Explicit rational lower enclosure for the actual first twenty weights. -/
theorem mersennePrefixMass_twenty_lower :
    (160669:ℝ)/100000 < mersennePrefixMass 20 := by
  norm_num [mersennePrefixMass,Finset.sum_range_succ,mersenneWeight]

/-- Explicit upper enclosure including the full infinite tail majorant. -/
theorem mersennePrefixMass_twenty_upper :
    mersennePrefixMass 20+2*mersenneWeight 21 < (160670:ℝ)/100000 := by
  norm_num [mersennePrefixMass,Finset.sum_range_succ,mersenneWeight]

/-- The decimal approximation in the displayed geometry theorem is replaced
by an exact rational enclosure. -/
theorem mersenne_span_rational_bounds :
    (160669:ℝ)/100000 < erdosBorweinMersenneConstant ∧
    erdosBorweinMersenneConstant < (160670:ℝ)/100000 := by
  have he := erdosBorweinMersenneConstant_eq_prefix_add_tail 20
  have ht0 := mersenneTail_nonneg 20
  have htu := mersenneTail_le_two_mul_weight 20
  have hlo := mersennePrefixMass_twenty_lower
  have hhi := mersennePrefixMass_twenty_upper
  constructor <;> linarith only [he,ht0,htu,hlo,hhi]

/-- The ambient interval containment, with the actual sum as its right end. -/
theorem mersenne_achievement_subset_span :
    mersenneAchievementSet ⊆ Set.Icc 0 erdosBorweinMersenneConstant := by
  intro x hx
  have h := mersenneAchievementSet_subset_cylinderStage 0 hx
  simpa only [mersenneCylinderStage,mersenneCylinderStageFrom,
    erdosBorweinMersenneConstant] using h

/-- Exact interpretation of the paper's approximate 62 percent relative
Lebesgue density. It is NOT a Bernoulli digit-distribution claim. -/
theorem mersenne_relative_density_bounds :
    (62:ℝ)/100 < 1/erdosBorweinMersenneConstant ∧
    1/erdosBorweinMersenneConstant < (63:ℝ)/100 := by
  have he := mersenne_span_rational_bounds
  have hepos : 0<erdosBorweinMersenneConstant := by linarith only [he.1]
  constructor
  · apply (lt_div_iff₀ hepos).mpr
    linarith only [he.2]
  · apply (div_lt_iff₀ hepos).mpr
    linarith only [he.1]

/-- Full row 006, including the span, relative density and uniqueness data.
The numerical prose is represented by explicit enclosing rationals. -/
theorem paper_achievement_geometry_with_span :
    IsCompact mersenneAchievementSet ∧
    IsClosed mersenneAchievementSet ∧
    Perfect mersenneAchievementSet ∧
    IsTotallyDisconnected mersenneAchievementSet ∧
    IsNowhereDense mersenneAchievementSet ∧
    volume mersenneAchievementSet=1 ∧
    Function.Injective positiveMersenneDigitValue ∧
    Set.range positiveMersenneDigitValue=mersenneAchievementSet ∧
    mersenneAchievementSet⊆Set.Icc 0 erdosBorweinMersenneConstant ∧
    ((160669:ℝ)/100000<erdosBorweinMersenneConstant ∧
      erdosBorweinMersenneConstant<(160670:ℝ)/100000) ∧
    ((62:ℝ)/100<1/erdosBorweinMersenneConstant ∧
      1/erdosBorweinMersenneConstant<(63:ℝ)/100) :=
  ⟨isCompact_mersenneAchievementSet,isClosed_mersenneAchievementSet,
    perfect_mersenneAchievementSet,isTotallyDisconnected_mersenneAchievementSet,
    isNowhereDense_mersenneAchievementSet,volume_mersenneAchievementSet,
    positiveMersenneDigitValue_injective,range_positiveMersenneDigitValue_eq,
    mersenne_achievement_subset_span,mersenne_span_rational_bounds,
    mersenne_relative_density_bounds⟩

/-- Both the Mersenne clauses and the generic compactness statement in
row 092. No unproved summability or superincreasingness assertion about the
actual totient sequence is introduced. -/
theorem paper_achievement_geometry_generic :
    (IsCompact mersenneAchievementSet ∧ IsClosed mersenneAchievementSet ∧
      Perfect mersenneAchievementSet ∧ IsTotallyDisconnected mersenneAchievementSet ∧
      IsNowhereDense mersenneAchievementSet ∧ volume mersenneAchievementSet=1) ∧
    (∀ w : ℕ→ℝ, Summable (fun n => ‖w n‖) →
      IsCompact (Set.range (binaryWeightValue w)) ∧
      IsClosed (Set.range (binaryWeightValue w))) :=
  ⟨⟨isCompact_mersenneAchievementSet,isClosed_mersenneAchievementSet,
    perfect_mersenneAchievementSet,isTotallyDisconnected_mersenneAchievementSet,
    isNowhereDense_mersenneAchievementSet,volume_mersenneAchievementSet⟩,
    generic_binary_achievement_compact_closed⟩

end ErdosProblems.Erdos257.PaperCompleteR8
end
