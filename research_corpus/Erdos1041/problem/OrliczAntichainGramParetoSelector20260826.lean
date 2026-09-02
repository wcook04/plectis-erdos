import ErdosProblems.Erdos1041.SparseDefectSurvivorSelector20260826

/-!
# Erdős 1041: Orlicz--Gram Pareto selector kernels

The companion note strengthens a returned individual-heavy selector by using
the exact overlap of edge-bad and Gram-bad roots and retaining a sharper
pair-product tier.  This module checks the scalar and finite-cardinality fan-in.
-/

namespace ErdosProblems.Erdos1041.OrliczAntichainGramParetoSelector20260826

/-- Removing at most `badCount` roots from `youngCount` candidates leaves two
when the young set has the exact `badCount + 2` reserve. -/
theorem two_survive_exact_union_count
    {youngCount badCount : ℕ}
    (hcount : badCount + 2 ≤ youngCount) :
    2 ≤ youngCount - badCount := by
  omega

/-- Reserving one additional young root leaves three after structural
exclusions, so one possible charge-light root can also be removed. -/
theorem three_survive_exact_union_count
    {youngCount badCount : ℕ}
    (hcount : badCount + 3 ≤ youngCount) :
    3 ≤ youngCount - badCount := by
  omega

/-- The pair-product tier pays one less unit in its age denominator than the
individual-heavy tier. -/
theorem pairTier_ageDenominator_strictly_better
    {componentSize badCount : ℕ}
    (hcount : badCount + 3 ≤ componentSize) :
    componentSize - badCount - 1 =
      (componentSize - badCount - 2) + 1 := by
  omega

/-- Exact bad-set union accounting is never worse than adding the two bad-set
cardinalities separately. -/
theorem exactUnionCount_le_separateCounts
    {edgeBad gramBad overlap badUnion : ℕ}
    (hunion : edgeBad + gramBad = overlap + badUnion) :
    badUnion ≤ edgeBad + gramBad := by
  omega

/-- The sharp pair tier is exactly the survivor-local product transport from
the preceding return, applied after structural exclusions select the pair. -/
theorem sharpPair_product_transport
    {survivorProductSq pairSq complementProductSq complementCardPow
      complementEnergyPow : ℝ}
    (hpair : 0 ≤ pairSq)
    (hfactor : survivorProductSq = pairSq * complementProductSq)
    (hamgm : complementProductSq * complementCardPow ≤ complementEnergyPow) :
    survivorProductSq * complementCardPow ≤ pairSq * complementEnergyPow := by
  exact
    SparseDefectSurvivorSelector20260826.survivorProductSq_le_pairSq_mul_energyPow
      hpair hfactor hamgm

/-- Once individual charge heaviness and the entrance-energy comparison are
available for the same root, the propagated-energy conclusion is transitive. -/
theorem individualHeavy_to_propagatedEnergy
    {heavySq chargeSq propagatedEnergy : ℝ}
    (hheavy : heavySq ≤ chargeSq)
    (hbridge : chargeSq ≤ propagatedEnergy) :
    heavySq ≤ propagatedEnergy := by
  exact hheavy.trans hbridge

end ErdosProblems.Erdos1041.OrliczAntichainGramParetoSelector20260826
